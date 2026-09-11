{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE QuasiQuotes #-}

{- |
A tiny tactic language for the calculus, and the engine which runs it.

A tactic is applied to a goal, a 'Sequent', and either fails or produces a
partial proof: a proof tree whose leaves are the goals left open, or the
premises a derived rule may appeal to.  The primitive tactics are the rules of
the calculus applied backwards — one per rule, read off 'ruleSpec', so a rule
added to "Language.Praxis.PRA.Rule.G3i" is a tactic without further ado.  A
handful of derived tactics compute the arguments a rule needs from the goal,
and 'Exact' appeals to a 'Lemma' certified before: a theorem, or a derived
rule, instantiated to the goal.

Nothing here is trusted.  'prove' hands the proof it built to the checker
and compares the sequent it infers with the goal, so a tactic which produced
the wrong proof is an error, not an unsound theorem; an appeal to a lemma is
checked against the lemma's statement, instantiated afresh.  See
"Language.Praxis.PRA.Tactic.Parser" for the textual syntax.
-}
module Language.Praxis.PRA.Tactic (
  -- * Tactics
  Tactic (..),
  Loc (..),
  applyWith,

  -- * Lemmas
  Lemma (..),
  Schematic (..),
  Certified (..),
  theorem,

  -- * Running
  prove,
  proveWith,
  proveOpen,
  proveOpenIn,
  proveOpenWith,
  runTactic,
  runTacticWith,
  Leaf (..),
  Step (..),
  Appeal (..),
  Partial,
  instantiateLemma,
  certify,

  -- * Errors
  TacticError (..),
  Failure (..),
  renderTacticError,
  renderTacticErrorWith,

  -- * Names
  Fresh (..),
  goalNames,
) where

import Control.Applicative ((<|>))
import Control.Exception (displayException)
import Control.Lens ((^?))
import Control.Monad (foldM, forM_, join, unless, when, (>=>))
import Control.Monad.Free (Free (..))
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (evalStateT, get, put)
import Data.Bifunctor (first)
import Data.Either (partitionEithers)
import Data.Foldable (toList)
import Data.Functor.Foldable (embed)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)
import Data.List (intercalate, nub, sort)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust, isNothing)
import Data.Multiset (Multiset)
import Data.Multiset qualified as MS
import Data.Set qualified as Set
import Data.Sized qualified as SV
import Data.Traversable (for)
import Data.Type.Equality qualified as TE
import Data.Type.Natural (sNat)
import Data.Type.Ordinal (od)
import GHC.Generics (Generic)
import Language.Praxis.Name (Fresh (..))
import Language.Praxis.PRA.Equality (defEqIn, defaultFuel)
import Language.Praxis.PRA.Pattern
import Language.Praxis.PRA.PrimitiveRecursion (Evalable (..), PRFCode (..))
import Language.Praxis.PRA.PrimitiveRecursion.Function (Function, KernelEnv, emptyKernelEnv)
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.Proof.Transform (argNames, substProof, weakenProof)
import Language.Praxis.PRA.Rule qualified as R
import Language.Praxis.PRA.Signature (Signature)
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Syntax.Pretty

-- * Names

-- | Every name occurring in a sequent.
goalNames :: (Hashable a) => Sequent a -> HashSet a
goalNames (ctx :|- c) = HS.fromList (foldMap toList ctx <> toList c)

{- |
Names some of which stand for metavariables, as in the statement of a derived
rule.  The engine reads a name of the goal as itself, whatever it stands for;
in the statement of a 'Lemma', a metavariable is a pattern to be instantiated.
Plain names stand for nothing.
-}
class (Fresh a) => Schematic a where
  -- | The metavariable a name stands for, with its sort.
  metaName :: a -> Maybe (R.Sort, String)

  -- | The metavariable of sort @atom@, @formula@ or @ctx@ an atom stands for.
  metaAtom :: Atomic a -> Maybe (R.Sort, String)

instance Schematic String where
  metaName _ = Nothing
  metaAtom _ = Nothing

-- * Tactics

-- | A position in the source of a tactic, for error reports.
data Loc = Loc {locLine :: !Int, locColumn :: !Int}
  deriving (Show, Eq, Ord, Generic)

{- |
The language.  A tactic maps a goal to the list of goals it leaves open, in
the order of the premises of the rules it applied, or fails.
-}
data Tactic a
  = {- | A rule of the calculus, applied backwards.  One argument per
    parameter of the rule, in the order of 'R.ruleParams'; an argument
    left 'Nothing' is inferred from the goal, and one given as a pattern
    with wildcards constrains the inference.  Context parameters are always
    inferred.
    -}
    Apply !RuleName ![Maybe (Arg (Hole a))]
  | {- | Close the goal @s = t@ when @s@ and @t@ are definitionally equal:
    @Defeq s t; Id@.
    -}
    Refl
  | -- | From the hypothesis @t = s@ selected by the pattern, add @s = t@.
    Symmetry !(Atomic (Hole a))
  | {- | @Rewrite eq h@: with the hypothesis @t = s@ selected by @eq@, add the
    atomic hypothesis selected by @h@ with every occurrence of @t@ replaced
    by @s@, by 'Subst'.
    -}
    Rewrite !(Atomic (Hole a)) !(Atomic (Hole a))
  | {- | @Induction t n@: prove the goal by 'Ind' on the term @t@, with the
    eigenvariable @n@, chosen fresh when it is not given.  The hypotheses
    mentioning @t@ are generalized into the induction formula, through 'Cut',
    and reintroduced in each case, where the induction hypothesis then is an
    implication from them.
    -}
    Induction !(Term a) !(Maybe a)
  | {- | Close a goal whose succedent is in the context, expanding the identity
    through the connectives down to 'Id'.
    -}
    Assumption
  | {- | @Exact name args@: close the goal by the named premise, whose sequent
    it must be, or appeal to the named 'Lemma', which leaves the premises of
    the lemma as goals.  The arguments are for the metavariables of the
    lemma, in the order of its binders, as for 'Apply'.
    -}
    Exact !String ![Maybe (Arg (Hole a))]
  | -- | Leave the goal open.
    Skip
  | -- | Abandon the whole proof, reporting the goal reached here.
    Sorry
  | -- | @t; u@: run @u@ on every goal @t@ leaves.
    Then !(Tactic a) !(Tactic a)
  | -- | @t | u@: @u@ when @t@ fails; committed, so no backtracking into @t@.
    OrElse !(Tactic a) !(Tactic a)
  | Try !(Tactic a)
  | -- | Apply the tactic as long as it succeeds, to every goal it leaves.
    Repeat !(Tactic a)
  | {- | @t { u1 } … { un }@: @t@ must leave exactly @n@ goals, and @ui@ is run
    on the @i@-th.
    -}
    Dispatch !(Tactic a) ![Tactic a]
  | -- | Attach a source position to the errors of a tactic.
    At !Loc !(Tactic a)
  deriving (Show, Eq, Generic)

-- | Apply a rule with the given leading arguments; the rest are inferred.
applyWith :: RuleName -> [Arg (Hole a)] -> Tactic a
applyWith name args =
  Apply name (map Just args <> replicate (length (R.ruleParams (ruleSpec name)) - length args) Nothing)

-- * Lemmas

{- |
A certified statement a script may appeal to by name, through 'Exact': a
theorem, or a derived rule with its binders.

An appeal instantiates the lemma to the goal.  The metavariables of a rule
are inferred by matching its statement against the goal, or given as
arguments; its context metavariable, if any, takes the hypotheses of the goal
the statement does not mention, and otherwise those are weakened in.  The free
variables of a theorem are instantiated by whatever the goal has in their
place.  The premises of a rule become goals.

Two shapes are refused, because instantiating them is not a matter of
applying the rule: a rule which has metavariables or premises besides free
variables in its statement — declare the variables as @term@ metavariables —
and a rule with premises but no context metavariable, under hypotheses it does
not mention.
-}
data Lemma a = Lemma
  { lemmaMetas :: ![(String, R.Sort)]
  -- ^ the metavariables, in the order of the binders
  , lemmaPremises :: ![(String, Sequent a)]
  -- ^ the premises, in the order of the binders
  , lemmaGoal :: !(Sequent a)
  , lemmaBound :: ![String]
  {- ^ the metavariables of sort @var@ the proof binds, as eigenvariables;
  their instantiation must not occur in the goal or the other arguments
  -}
  }
  deriving (Show, Eq, Generic)

{- |
A lemma with its proof: given the arguments for its metavariables, in order,
and the proofs of its premises, in order, the proof of the instance.
-}
data Certified a = Certified
  { certifiedLemma :: !(Lemma a)
  , certifiedProof :: [Arg a] -> [Proof a] -> Proof a
  }

-- | A closed proof, as the lemma it certifies.
theorem :: Sequent a -> Proof a -> Certified a
theorem s p = Certified (Lemma [] [] s []) (\_ _ -> p)

-- * Partial proofs

-- | What a partial proof may end in.
data Leaf a
  = -- | a goal not yet proved
    Open !(Sequent a)
  | -- | a premise of the derived rule being proved, with its declared sequent
    Premise !String !(Sequent a)
  deriving (Show, Eq, Generic)

{- |
An appeal to a lemma, instantiated: the arguments for its metavariables, the
terms for the free variables of its statement, and the hypotheses weakened
in.  The proof of the instance is the lemma's proof at the arguments, under
'substProof' and then 'weakenProof'.
-}
data Appeal a = Appeal
  { appealName :: !String
  , appealArgs :: ![Arg a]
  -- ^ one per metavariable, in the order of the binders
  , appealSubst :: ![(a, Term a)]
  -- ^ every free variable of the statement, and the term in its place
  , appealWeakening :: !(Multiset (Formula a))
  -- ^ the hypotheses added to every sequent of the instance
  }
  deriving (Show, Eq, Generic)

-- | A step of a partial proof: a rule of the calculus, or a lemma with the proofs of its premises.
data Step a x
  = RuleStep !(ProofF a x)
  | LemmaStep !(Appeal a) ![x]
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic)

type Partial a = Free (Step a) (Leaf a)

-- * Errors

data TacticError a = TacticError
  { errorLoc :: !(Maybe Loc)
  , errorGoal :: !(Sequent a)
  , errorFailure :: !(Failure a)
  }
  deriving (Show, Eq, Generic)

data Failure a
  = -- | the succedent does not have the shape the rule concludes
    WrongSuccedent !RuleName ![Maybe (Arg (Hole a))]
  | -- | no hypothesis has the shape of the rule's principal formula
    NoHypothesis !RuleName ![Maybe (Arg (Hole a))] !R.FormPat
  | -- | more than one hypothesis does, and the arguments do not decide
    AmbiguousHypothesis !RuleName ![Maybe (Arg (Hole a))] !R.FormPat ![Formula a]
  | -- | parameters neither given nor determined by the goal
    CannotInfer !RuleName ![R.MetaRef]
  | SideCondition !RuleName !(ProofErrorReason a)
  | -- | 'Refl' on a goal which is not an equation
    NotAnEquation !(Formula a)
  | -- | no hypothesis matches the pattern of a derived tactic
    NoMatch !(Atomic (Hole a))
  | AmbiguousMatch !(Atomic (Hole a)) ![Formula a]
  | -- | the term does not occur in the hypothesis to be rewritten
    NothingToRewrite !(Term a) !(Atomic a)
  | -- | a hypothesis cannot be rewritten with itself
    RewriteWithItself !(Atomic a)
  | -- | the eigenvariable given to 'Induction' occurs in the goal
    NotFresh !a
  | -- | 'Assumption' on a succedent absent from the context
    NotInContext !(Formula a)
  | -- | 'Exact' on a name which is neither a premise nor a lemma
    UnknownPremise !String
  | -- | the goal is not the declared sequent of the premise
    PremiseMismatch !String !(Sequent a)
  | -- | the goal is not an instance of the statement of the lemma
    NotAnInstance !String !(Sequent a)
  | -- | more than one hypothesis instantiates a hypothesis of the lemma
    AmbiguousInstance !String !(Formula a) ![Formula a]
  | -- | metavariables of the lemma neither given nor determined by the goal
    CannotInstantiate !String ![R.MetaRef]
  | -- | the lemma has premises but no context metavariable to take the hypotheses
    CannotWeaken !String !(Multiset (Formula a))
  | -- | the lemma has metavariables or premises, so its free variables cannot be instantiated
    NotClosed !String ![a]
  | -- | a metavariable the lemma binds, instantiated by a name occurring in the goal
    NotEigen !String !String !a
  | -- | 'Dispatch' with the wrong number of blocks: expected, actual
    WrongGoalCount !Int !Int
  | -- | every alternative of an 'OrElse' failed
    Alternatives ![TacticError a]
  | -- | the goals left open at the end
    Unsolved ![Sequent a]
  | RepeatLimit
  | -- | 'Sorry': the proof was abandoned at this goal
    Unfinished
  | -- | the checker rejected the proof the tactic built: a bug in a tactic
    Rejected !(NonEmpty (ProofError a))
  | -- | a premise of a lemma was proved with the wrong sequent: expected, actual; a bug in a tactic
    WrongPremise !String !(Sequent a) !(Sequent a)
  | -- | the checker accepted the proof, but of another sequent: a bug in a tactic
    WrongConclusion !(Sequent a)
  | -- | a malformed tactic, such as an ill-sorted argument
    Malformed !String
  deriving (Show, Eq, Generic)

-- * Running

-- | Prove a closed sequent.
prove :: (Schematic a) => Sequent a -> Tactic a -> Either (TacticError a) (Proof a)
prove = proveWith emptyKernelEnv Map.empty

{- |
Prove a closed sequent, appealing to lemmas.  The proof is closed with the
proofs of the lemmas, and checked once more when it appealed to any, since
instantiating them is a transformation of their proofs.
-}
proveWith :: forall a. (Schematic a) => KernelEnv -> Map String (Certified a) -> Sequent a -> Tactic a -> Either (TacticError a) (Proof a)
proveWith env certified goal t = do
  p <- proveOpenWith env (fmap certifiedLemma certified) Map.empty goal t
  proof <- close p
  when (appeals p) case inferConclusionIn env proof of
    Left errs -> failWith (Rejected errs)
    Right s
      | s /= goal -> failWith (WrongConclusion s)
      | otherwise -> pure ()
  pure proof
  where
    failWith :: forall x. Failure a -> Either (TacticError a) x
    failWith = Left . TacticError Nothing goal

    close :: Free (Step a) String -> Either (TacticError a) (Proof a)
    close = \case
      Pure d -> failWith (Malformed ("the premise " <> d <> " in a closed proof"))
      Free (RuleStep step) -> embed <$> traverse close step
      Free (LemmaStep appeal subs) -> do
        c <- maybe (failWith (UnknownPremise (appealName appeal))) Right (Map.lookup (appealName appeal) certified)
        subs' <- traverse close subs
        pure (weakenProof (appealWeakening appeal) (substProof (appealSubst appeal) (certifiedProof c (appealArgs appeal) subs')))

    appeals :: Free (Step a) String -> Bool
    appeals = \case
      Pure _ -> False
      Free (RuleStep step) -> any appeals step
      Free (LemmaStep _ _) -> True

{- |
Prove a sequent from declared premises, as a derived rule does.  Every open
leaf of the result is one of the premises.  The proof is checked before it is
returned.
-}
proveOpen ::
  (Schematic a) =>
  -- | the premises, with the sequents they are declared to establish
  Map String (Sequent a) ->
  Sequent a ->
  Tactic a ->
  Either (TacticError a) (Free (Step a) String)
proveOpen = proveOpenIn emptyKernelEnv

-- | Run and certify a tactic against checked, shared PRF definitions.
proveOpenIn :: (Schematic a) => KernelEnv -> Map String (Sequent a) -> Sequent a -> Tactic a -> Either (TacticError a) (Free (Step a) String)
proveOpenIn env = proveOpenWith env Map.empty

-- | 'proveOpenIn', with lemmas to appeal to.
proveOpenWith :: (Schematic a) => KernelEnv -> Map String (Lemma a) -> Map String (Sequent a) -> Sequent a -> Tactic a -> Either (TacticError a) (Free (Step a) String)
proveOpenWith env lemmas prems goal t = do
  p <- runTacticWith env lemmas prems t goal
  let opens = [g | Open g <- toList p]
  unless (null opens) $ Left (TacticError Nothing goal (Unsolved opens))
  let p' =
        p >>= \case
          Open g -> Pure ("", g)
          Premise d g -> Pure (d, g)
  s <- first (TacticError Nothing goal) (certify env lemmas snd p')
  if s == goal
    then Right (fmap fst p')
    else Left (TacticError Nothing goal (WrongConclusion s))

{- |
Check a partial proof: the steps of the calculus by the checker, and an
appeal to a lemma against the lemma's statement instantiated at the
appeal, once the proofs of its premises are checked.  The leaves are assumed
to establish the sequents the function assigns them.
-}
certify :: forall a h. (Schematic a) => KernelEnv -> Map String (Lemma a) -> (h -> Sequent a) -> Free (Step a) h -> Either (Failure a) (Sequent a)
certify env lemmas leaf = check
  where
    check :: Free (Step a) h -> Either (Failure a) (Sequent a)
    check p = collapse p >>= first Rejected . inferConclusionOpenIn env id

    -- An appeal becomes a leaf with its conclusion, once its premises are checked.
    collapse :: Free (Step a) h -> Either (Failure a) (Free (ProofF a) (Sequent a))
    collapse = \case
      Pure h -> Right (Pure (leaf h))
      Free (RuleStep step) -> Free <$> traverse collapse step
      Free (LemmaStep appeal subs) -> do
        let name = appealName appeal
        lemma <- maybe (Left (UnknownPremise name)) Right (Map.lookup name lemmas)
        (premises, conclusion) <- instantiateLemma lemma appeal
        when (length premises /= length subs) $
          Left (Malformed (name <> " has " <> show (length premises) <> " premises"))
        proved <- traverse check subs
        forM_ (zip premises proved) \(expected, actual) ->
          unless (expected == actual) $ Left (WrongPremise name expected actual)
        pure (Pure conclusion)

-- | The limit on the iterations of 'Repeat' along any branch.
repeatLimit :: Int
repeatLimit = 1000

-- | Run a tactic on a goal, without checking what it built.
runTactic ::
  (Schematic a) =>
  Map String (Sequent a) ->
  Tactic a ->
  Sequent a ->
  Either (TacticError a) (Partial a)
runTactic = runTacticWith emptyKernelEnv Map.empty

-- | 'runTactic', with definitions and lemmas.
runTacticWith :: forall a. (Schematic a) => KernelEnv -> Map String (Lemma a) -> Map String (Sequent a) -> Tactic a -> Sequent a -> Either (TacticError a) (Partial a)
runTacticWith env lemmas prems = go
  where
    go :: Tactic a -> Sequent a -> Either (TacticError a) (Partial a)
    go tac goal@(ctx :|- c) = case tac of
      At loc t -> first (located loc) (go t goal)
      Skip -> Right (Pure (Open goal))
      Sorry -> failWith Unfinished
      Then t u -> go t goal >>= continue (go u)
      OrElse t u -> case go t goal of
        Right p -> Right p
        Left e1 | abandoned e1 -> Left e1
        Left e1 -> case go u goal of
          Right p -> Right p
          Left e2 -> failWith (Alternatives (alternatives e1 <> alternatives e2))
      Try t -> go (OrElse t Skip) goal
      Repeat t -> repeatFrom 0 t goal
      Dispatch t us -> do
        p <- go t goal
        let opens = length [() | Open _ <- toList p]
        when (opens /= length us) $ failWith (WrongGoalCount (length us) opens)
        fmap join . flip evalStateT us $ for p \case
          Open g ->
            get >>= \case
              u : rest -> put rest *> lift (go u g)
              [] -> lift (Left (TacticError Nothing goal (WrongGoalCount (length us) opens)))
          leaf -> pure (Pure leaf)
      Exact d args -> case (Map.lookup d prems, Map.lookup d lemmas) of
        (Just s, _)
          | any isJust args -> failWith (Malformed ("the premise " <> d <> " takes no arguments"))
          | s == goal -> Right (Pure (Premise d s))
          | otherwise -> failWith (PremiseMismatch d s)
        (Nothing, Just lemma) -> first (TacticError Nothing goal) (useLemma d lemma args goal)
        (Nothing, Nothing) -> failWith (UnknownPremise d)
      Apply name args -> first (TacticError Nothing goal) (applyRule env name args goal)
      Refl -> case c of
        Atm (s :=== t) ->
          go (applyWith DefeqRule [term s, term t] `Then` applyWith IdRule []) goal
        _ -> failWith (NotAnEquation c)
      Symmetry pat -> do
        t :=== s <- select pat
        let x = freshen (goalNames goal) anyName
        go
          ( applyWith DefeqRule [term t, term t]
              `Then` applyWith SubstRule [ArgVar (Named x), term t, term s, atom (Var x :=== t)]
          )
          goal
      Rewrite eqPat hPat -> do
        t :=== s <- select eqPat
        h <- select hPat
        when (h == (t :=== s)) $ failWith (RewriteWithItself h)
        unless (t `occursIn` h) $ failWith (NothingToRewrite t h)
        let x = freshen (goalNames goal) anyName
        go (applyWith SubstRule [ArgVar (Named x), term t, term s, atom (abstract t x h)]) goal
      Induction t given -> do
        let names = goalNames goal
        n <- case given of
          Just n
            | n `HS.member` names -> failWith (NotFresh n)
            | otherwise -> pure n
          Nothing -> pure (freshen names (case t of Var y -> y; _ -> anyName))
        -- The hypotheses mentioning the term join the induction formula, by Cut,
        -- and are reintroduced in each case; modus ponens on them discharges the cut.
        let dependent = nub [h | h <- toList ctx, t `occursInFormula` h]
            motive = foldr (:==>) c dependent
            induction = applyWith IndRule [ArgVar (Named n), form (abstractIn t n motive), term t]
            reintroduce = foldr (\_ u -> applyWith ImplRRule [] `Then` u) Skip dependent
            discharge [] = Assumption
            discharge (h : hs) = Dispatch (applyWith ImplLRule [form h, form (foldr (:==>) c hs)]) [Assumption, discharge hs]
        if null dependent
          then go induction goal
          else go (Dispatch (applyWith CutRule [form motive]) [induction `Then` reintroduce, discharge dependent]) goal
      Assumption
        | not (MS.member c ctx) -> failWith (NotInContext c)
        | otherwise -> case c of
            Atm _ -> go (applyWith IdRule []) goal
            Bot -> go (applyWith ExFalsoRule []) goal
            p :/\ q ->
              go
                ( Dispatch
                    (applyWith ConjLRule [form p, form q] `Then` applyWith ConjRRule [])
                    [Assumption, Assumption]
                )
                goal
            p :\/ q ->
              go
                ( Dispatch
                    (applyWith DisjLRule [form p, form q])
                    [ applyWith DisjR2Rule [] `Then` Assumption
                    , applyWith DisjR1Rule [] `Then` Assumption
                    ]
                )
                goal
            p :==> q ->
              go
                ( applyWith ImplRRule []
                    `Then` Dispatch (applyWith ImplLRule [form p, form q]) [Assumption, Assumption]
                )
                goal
      where
        failWith :: forall x. Failure a -> Either (TacticError a) x
        failWith = Left . TacticError Nothing goal

        -- The unique hypothesis matching an atomic pattern.  A formula or
        -- context metavariable, opaque, is never selected.
        select :: Atomic (Hole a) -> Either (TacticError a) (Atomic a)
        select pat = case [p | Atm p <- HS.toList (MS.toHashSet ctx), isAtom p, matchAtomic pat p] of
          [p] -> Right p
          [] -> failWith (NoMatch pat)
          ps -> failWith (AmbiguousMatch pat (map Atm ps))

    continue k =
      fmap join . traverse \case
        Open g -> k g
        leaf -> Right (Pure leaf)

    repeatFrom :: Int -> Tactic a -> Sequent a -> Either (TacticError a) (Partial a)
    repeatFrom n t goal
      | n >= repeatLimit = Left (TacticError Nothing goal RepeatLimit)
      | otherwise = case go t goal of
          Left e | abandoned e -> Left e
          Left _ -> Right (Pure (Open goal))
          Right p -> continue (repeatFrom (n + 1) t) p

    located loc e = e {errorLoc = errorLoc e <|> Just loc}
    alternatives (TacticError _ _ (Alternatives es)) = es
    alternatives e = [e]
    abandoned (TacticError _ _ Unfinished) = True
    abandoned _ = False

    term = ArgTerm . fmap Named
    atom = ArgAtom . fmap Named
    form = ArgForm . fmap Named

-- | Whether an atom is one, rather than an opaque formula or context metavariable.
isAtom :: (Schematic a) => Atomic a -> Bool
isAtom p = maybe True ((== R.AtomS) . fst) (metaAtom p)

-- * Rule application

data Bindings a = Bindings
  { bVars :: !(Map String a)
  , bTerms :: !(Map String (Term a))
  , bAtoms :: !(Map String (Atomic a))
  , bForms :: !(Map String (Formula a))
  , bCtxs :: !(Map String (Multiset (Formula a)))
  , bFree :: !(HashMap a (Term a))
  -- ^ the free variables of a lemma
  }

emptyBindings :: Bindings a
emptyBindings = Bindings Map.empty Map.empty Map.empty Map.empty Map.empty HM.empty

isBound :: R.MetaRef -> Bindings a -> Bool
isBound (R.MetaRef s n) b = case s of
  R.VarS -> Map.member n (bVars b)
  R.TermS -> Map.member n (bTerms b)
  R.AtomS -> Map.member n (bAtoms b)
  R.FormS -> Map.member n (bForms b)
  R.CtxS -> Map.member n (bCtxs b)

-- | The patterns the user gave for parameters, to be checked when they are bound.
data Constraints a = Constraints
  { cTerms :: !(Map String (Term (Hole a)))
  , cAtoms :: !(Map String (Atomic (Hole a)))
  , cForms :: !(Map String (Formula (Hole a)))
  }

noConstraints :: Constraints a
noConstraints = Constraints Map.empty Map.empty Map.empty

data Match a = Matched !(Bindings a) | Deferred | Mismatch

-- | A discharge of a principal formula, or the matching of the succedent.
data Obligation = MatchSuccedent !R.FormPat | Discharge !R.FormPat

-- | Record an argument the user gave for a metavariable: a closed one binds it, a pattern constrains it.
seedArg :: (String, R.Sort) -> Maybe (Arg (Hole a)) -> (Bindings a, Constraints a) -> Either (Failure a) (Bindings a, Constraints a)
seedArg (n, s) arg (b, cons) = case (s, arg) of
  (_, Nothing) -> Right (b, cons)
  (R.VarS, Just (ArgVar h)) -> case h of
    Wild -> Right (b, cons)
    Named v -> Right (b {bVars = Map.insert n v (bVars b)}, cons)
  (R.TermS, Just (ArgTerm p)) -> case closed p of
    Just t -> Right (b {bTerms = Map.insert n t (bTerms b)}, cons)
    Nothing -> Right (b, cons {cTerms = Map.insert n p (cTerms cons)})
  (R.AtomS, Just (ArgAtom p)) -> case closed p of
    Just t -> Right (b {bAtoms = Map.insert n t (bAtoms b)}, cons)
    Nothing -> Right (b, cons {cAtoms = Map.insert n p (cAtoms cons)})
  (R.FormS, Just (ArgForm p)) -> case closed p of
    Just t -> Right (b {bForms = Map.insert n t (bForms b)}, cons)
    Nothing -> Right (b, cons {cForms = Map.insert n p (cForms cons)})
  (R.CtxS, Just _) -> Left (Malformed "a context parameter cannot be given")
  _ -> Left (Malformed ("ill-sorted argument for " <> n))

applyRule ::
  forall a.
  (Schematic a) =>
  KernelEnv ->
  RuleName ->
  [Maybe (Arg (Hole a))] ->
  Sequent a ->
  Either (Failure a) (Partial a)
applyRule env name userArgs (ctx :|- c) = do
  when (length userArgs /= length params) $
    Left (Malformed (show name <> " takes " <> show (length params) <> " arguments"))
  (b0, cons) <- foldM (\acc (p, arg) -> seedArg (R.refName (R.paramRef p), R.paramSort p) arg acc) (emptyBindings, noConstraints) (zip params userArgs)
  let fs R.:+ R.CtxM g R.:|- cpat = R.ruleConclusion rule
  (b1, rest) <- resolve cons b0 ctx (MatchSuccedent cpat : map Discharge fs)
  let b2 = b1 {bCtxs = Map.insert g rest (bCtxs b1)}
      unbound = [ref | ref <- Set.toList (R.metas rule) <> map R.paramRef params, not (isBound ref b2)]
  unless (null unbound) $ Left (CannotInfer name unbound)
  mapM_ (checkSide b2) (R.ruleSides rule)
  args <- traverse (argOf b2) params
  premises <- traverse (instSeq b2) (R.rulePremises rule)
  maybe (Left (Malformed "mkStep")) (Right . Free . RuleStep) (mkStep name args (map (Pure . Open) premises))
  where
    rule = ruleSpec name
    params = R.ruleParams rule

    -- Resolve the obligations to a fixpoint: each pass commits every
    -- obligation which is decided, and stops when a pass decides nothing.
    resolve cons b hyps obls = do
      (b', hyps', pending, progressed) <- foldM (step cons) (b, hyps, [], False) obls
      case reverse pending of
        [] -> Right (b', hyps')
        pending'@(first' : _)
          | progressed -> resolve cons b' hyps' pending'
          | otherwise -> Left (stuck cons b' hyps' first')

    step cons (b, hyps, pending, progressed) obl = case obl of
      MatchSuccedent pat -> case matchForm cons b pat c of
        Matched b' -> Right (b', hyps, pending, True)
        Deferred -> Right (b, hyps, obl : pending, progressed)
        Mismatch -> Left (WrongSuccedent name userArgs)
      Discharge pat -> case candidates cons b hyps pat of
        (_, [(f, b')]) -> case MS.removeOne f hyps of
          Just hyps' -> Right (b', hyps', pending, True)
          Nothing -> Left (NoHypothesis name userArgs pat)
        (False, []) -> Left (NoHypothesis name userArgs pat)
        _ -> Right (b, hyps, obl : pending, progressed)

    -- Whether some hypothesis deferred, and those which matched.
    candidates cons b hyps pat =
      foldr
        ( \f (deferred, ms) -> case matchForm cons b pat f of
            Matched b' -> (deferred, (f, b') : ms)
            Deferred -> (True, ms)
            Mismatch -> (deferred, ms)
        )
        (False, [])
        (HS.toList (MS.toHashSet hyps))

    stuck cons b hyps = \case
      MatchSuccedent pat -> CannotInfer name (unboundIn b pat)
      Discharge pat -> case candidates cons b hyps pat of
        (False, ms@(_ : _ : _)) -> AmbiguousHypothesis name userArgs pat (map fst ms)
        _ -> CannotInfer name (unboundIn b pat)

    unboundIn b pat = [ref | ref <- Set.toList (R.metas pat), not (isBound ref b)]

    checkSide b = \case
      R.DefEq sp tp -> do
        s <- instTermE b sp
        t <- instTermE b tp
        equal <- either (Left . SideCondition name . DefinitionResolutionFailed) Right (defEqIn env defaultFuel s t)
        unless equal $ Left (SideCondition name (EqualityCheckFailed s t))
      R.NotFreeIn (R.VarM xn) target -> do
        x <- maybe (Left (CannotInfer name [R.MetaRef R.VarS xn])) Right (Map.lookup xn (bVars b))
        case target of
          R.InTerm tp -> do
            t <- instTermE b tp
            when (x `elem` t) $ Left (SideCondition name (TermEigenVariableViolation x t))
          R.InCtx (R.CtxM gn) -> do
            g <- maybe (Left (CannotInfer name [R.MetaRef R.CtxS gn])) Right (Map.lookup gn (bCtxs b))
            when (any (elem x) g) $ Left (SideCondition name (AssumptionEigenVariableViolation x g))

    instTermE b p = maybe (Left (CannotInfer name (unboundIn b p))) Right (instTerm b p)

    instSeq b (fs R.:+ R.CtxM g R.:|- s) = do
      hyps <- traverse (instFormE b) fs
      tl <- maybe (Left (CannotInfer name [R.MetaRef R.CtxS g])) Right (Map.lookup g (bCtxs b))
      s' <- instFormE b s
      pure (foldr MS.insertOne tl hyps :|- s')

    instFormE b p = maybe (Left (CannotInfer name (unboundIn b p))) Right (instForm b p)

    argOf b = \case
      R.PVar (R.VarM x) -> ArgVar <$> look R.VarS x (bVars b)
      R.PTerm (R.TermM n) -> ArgTerm <$> look R.TermS n (bTerms b)
      R.PAtom (R.AtomM n) -> ArgAtom <$> look R.AtomS n (bAtoms b)
      R.PForm (R.FormM n) -> ArgForm <$> look R.FormS n (bForms b)
      R.PCtx (R.CtxM n) -> ArgCtx <$> look R.CtxS n (bCtxs b)

    look :: forall v. R.Sort -> String -> Map String v -> Either (Failure a) v
    look s n = maybe (Left (CannotInfer name [R.MetaRef s n])) Right . Map.lookup n

-- ** Matching rule patterns against the goal

bindTerm :: (Eq a) => Constraints a -> Bindings a -> String -> Term a -> Match a
bindTerm cons b n t = case Map.lookup n (bTerms b) of
  Just t'
    | t' == t -> Matched b
    | otherwise -> Mismatch
  Nothing
    | maybe True (`matchTerm` t) (Map.lookup n (cTerms cons)) ->
        Matched b {bTerms = Map.insert n t (bTerms b)}
    | otherwise -> Mismatch

bindVar :: (Eq a) => Bindings a -> String -> a -> Match a
bindVar b x v = case Map.lookup x (bVars b) of
  Just v'
    | v' == v -> Matched b
    | otherwise -> Mismatch
  Nothing -> Matched b {bVars = Map.insert x v (bVars b)}

bindAtom :: (Eq a) => Constraints a -> Bindings a -> String -> Atomic a -> Match a
bindAtom cons b n p = case Map.lookup n (bAtoms b) of
  Just p'
    | p' == p -> Matched b
    | otherwise -> Mismatch
  Nothing
    | maybe True (`matchAtomic` p) (Map.lookup n (cAtoms cons)) ->
        Matched b {bAtoms = Map.insert n p (bAtoms b)}
    | otherwise -> Mismatch

bindForm :: (Eq a) => Constraints a -> Bindings a -> String -> Formula a -> Match a
bindForm cons b n f = case Map.lookup n (bForms b) of
  Just f'
    | f' == f -> Matched b
    | otherwise -> Mismatch
  Nothing
    | maybe True (`matchFormula` f) (Map.lookup n (cForms cons)) ->
        Matched b {bForms = Map.insert n f (bForms b)}
    | otherwise -> Mismatch

matchTermPat :: (Eq a) => Constraints a -> Bindings a -> R.TermPat -> Term a -> Match a
matchTermPat cons b pat t = case pat of
  R.TMeta (R.TermM n) -> bindTerm cons b n t
  R.TOfVar (R.VarM x) -> case canonicalise t of
    Var v -> bindVar b x v
    _ -> Mismatch
  R.TLit n
    | t == Lit n -> Matched b
    | otherwise -> Mismatch
  R.TSuc p -> case t ^? _Succ of
    Just t' -> matchTermPat cons b p t'
    Nothing -> Mismatch

{- |
An opaque metavariable has no structure, so only an atom metavariable of the
rule matches it: a formula metavariable under @Id@ is expanded into the
identity through its connectives once instantiated, and a context
metavariable is never an atom.
-}
matchAtomPat :: (Schematic a) => Constraints a -> Bindings a -> R.AtomPat -> Atomic a -> Match a
matchAtomPat cons b pat p@(s :=== t) = case (pat, metaAtom p) of
  (R.AMeta _, Just (R.CtxS, _)) -> Mismatch
  (R.AMeta (R.AtomM n), _) -> bindAtom cons b n p
  (_, Just _) -> Mismatch
  (sp R.:=== tp, Nothing) -> case matchTermPat cons b sp s of
    Matched b' -> matchTermPat cons b' tp t
    other -> other

matchForm :: (Schematic a) => Constraints a -> Bindings a -> R.FormPat -> Formula a -> Match a
matchForm cons b pat f = case (pat, f) of
  (R.FMeta (R.FormM n), _) -> bindForm cons b n f
  (R.FAtm ap, Atm p) -> matchAtomPat cons b ap p
  (R.FAtm _, _) -> Mismatch
  (R.FBot, Bot) -> Matched b
  (R.FBot, _) -> Mismatch
  (p R.:/\ q, g :/\ h) -> both p g q h
  ((R.:/\) {}, _) -> Mismatch
  (p R.:\/ q, g :\/ h) -> both p g q h
  ((R.:\/) {}, _) -> Mismatch
  (p R.:==> q, g :==> h) -> both p g q h
  ((R.:==>) {}, _) -> Mismatch
  (R.FSubst (R.VarM xn) tp body, _) -> case (Map.lookup xn (bVars b), instForm b body) of
    (Just x, Just bodyV) -> case instTerm b tp of
      Just t
        | subst x t bodyV == f -> Matched b
        | otherwise -> Mismatch
      Nothing -> case abstractMatch x bodyV f of
        Nothing -> Mismatch
        Just Nothing -> Matched b
        Just (Just t) -> matchTermPat cons b tp t
    _ -> Deferred
  where
    both p g q h = case matchForm cons b p g of
      Matched b' -> matchForm cons b' q h
      other -> other

{- |
@abstractMatch x body f@ finds the @t@ with @body[x := t] == f@: 'Nothing'
when there is none, @'Just' 'Nothing'@ when @x@ does not occur in @body@ and
@body == f@, so that any @t@ would do.
-}
abstractMatch :: forall a. (Eq a) => a -> Formula a -> Formula a -> Maybe (Maybe (Term a))
abstractMatch x = goF
  where
    goF :: Formula a -> Formula a -> Maybe (Maybe (Term a))
    goF (Atm (s :=== t)) (Atm (s' :=== t')) = goT s s' `merge` goT t t'
    goF Bot Bot = Just Nothing
    goF (p :/\ q) (p' :/\ q') = goF p p' `merge` goF q q'
    goF (p :\/ q) (p' :\/ q') = goF p p' `merge` goF q q'
    goF (p :==> q) (p' :==> q') = goF p p' `merge` goF q q'
    goF _ _ = Nothing

    goT :: Term a -> Term a -> Maybe (Maybe (Term a))
    goT p u = go (canonicalise p) (canonicalise u)

    go :: Term a -> Term a -> Maybe (Maybe (Term a))
    go (Var y) u
      | y == x = Just (Just u)
      | u == Var y = Just Nothing
      | otherwise = Nothing
    go (Lit n) u
      | u == Lit n = Just Nothing
      | otherwise = Nothing
    go (Succ :$ ps) u = case u ^? _Succ of
      Just u' -> go (SV.sIndex [od|0|] ps) u'
      Nothing -> Nothing
    go (App (f :: Function n) ps) (App (g :: Function m) us) =
      case TE.testEquality (sNat @n) (sNat @m) of
        Just TE.Refl
          | f == g -> foldr merge (Just Nothing) (zipWith go (SV.toList ps) (SV.toList us))
        _ -> Nothing
    go (App _ _) _ = Nothing

    merge Nothing _ = Nothing
    merge _ Nothing = Nothing
    merge (Just Nothing) r = r
    merge l (Just Nothing) = l
    merge (Just (Just u)) (Just (Just v))
      | u == v = Just (Just u)
      | otherwise = Nothing

-- ** Instantiating rule patterns

instTerm :: Bindings a -> R.TermPat -> Maybe (Term a)
instTerm b = \case
  R.TMeta (R.TermM n) -> Map.lookup n (bTerms b)
  R.TOfVar (R.VarM x) -> Var <$> Map.lookup x (bVars b)
  R.TLit n -> Just (Lit n)
  R.TSuc p -> suc <$> instTerm b p

instAtom :: Bindings a -> R.AtomPat -> Maybe (Atomic a)
instAtom b = \case
  R.AMeta (R.AtomM n) -> Map.lookup n (bAtoms b)
  s R.:=== t -> (:===) <$> instTerm b s <*> instTerm b t

instForm :: (Eq a) => Bindings a -> R.FormPat -> Maybe (Formula a)
instForm b = \case
  R.FMeta (R.FormM n) -> Map.lookup n (bForms b)
  R.FAtm p -> Atm <$> instAtom b p
  R.FBot -> Just Bot
  p R.:/\ q -> (:/\) <$> instForm b p <*> instForm b q
  p R.:\/ q -> (:\/) <$> instForm b p <*> instForm b q
  p R.:==> q -> (:==>) <$> instForm b p <*> instForm b q
  R.FSubst (R.VarM x) t p -> subst <$> Map.lookup x (bVars b) <*> instTerm b t <*> instForm b p

-- * Appeals to lemmas

-- | The free variables of a lemma: the names of its statement which are not metavariables.
freeVariables :: (Schematic a) => Lemma a -> HashSet a
freeVariables lemma =
  HS.filter (isNothing . metaName) (HS.unions (map goalNames (lemmaGoal lemma : map snd (lemmaPremises lemma))))

{- |
Appeal to a lemma at a goal: match its statement against the goal, binding
its metavariables and free variables, and leave its premises open.
-}
useLemma :: forall a. (Schematic a) => String -> Lemma a -> [Maybe (Arg (Hole a))] -> Sequent a -> Either (Failure a) (Partial a)
useLemma name lemma userArgs goal@(ctx :|- c) = do
  when (length userArgs /= length metas) $
    Left (Malformed (name <> " takes " <> show (length metas) <> " arguments"))
  unless (null metas && null premises || HS.null free) $
    Left (NotClosed name (HS.toList free))
  (b0, cons) <- foldM (\acc (m, arg) -> seedArg m arg acc) (emptyBindings, noConstraints) (zip metas userArgs)
  b1 <- case matchFormL cons b0 lemmaSucc c of
    Matched b -> Right b
    _ -> Left (NotAnInstance name (lemmaGoal lemma))
  let (ctxMetas, hyps) = partitionEithers [maybe (Right f) Left (contextMeta f) | f <- toList lemmaCtx]
  (b2, rest) <- discharge cons b1 ctx hyps
  -- The first context metavariable takes what is left; without one, it is weakened in.
  let (b3, weakening) = case ctxMetas of
        [] -> (b2, rest)
        n : ns -> (b2 {bCtxs = Map.insert n rest (foldr (\m -> Map.insert m MS.empty) (bCtxs b2) ns)}, MS.empty)
  unless (MS.population weakening == 0 || null premises) $ Left (CannotWeaken name weakening)
  let unbound = [ref | (n, s) <- metas, let ref = R.MetaRef s n, not (isBound ref b3)]
  unless (null unbound) $ Left (CannotInstantiate name unbound)
  args <- traverse (argOfSort b3) metas
  forM_ (lemmaBound lemma) \x -> case Map.lookup x (bVars b3) of
    Just v
      | v `HS.member` goalNames goal || or [v `HS.member` argNames arg | ((n, _), arg) <- zip metas args, n /= x] ->
          Left (NotEigen name x v)
    _ -> pure ()
  let sigma = [(v, HM.lookupDefault (Var v) v (bFree b3)) | v <- HS.toList free]
      appeal = Appeal name args sigma weakening
  (goals, conclusion) <- instantiateLemma lemma appeal
  when (conclusion /= goal) $ Left (Malformed ("the instance of " <> name <> " is not the goal"))
  pure (Free (LemmaStep appeal (map (Pure . Open) goals)))
  where
    metas = lemmaMetas lemma
    premises = lemmaPremises lemma
    lemmaCtx :|- lemmaSucc = lemmaGoal lemma
    free = freeVariables lemma

    contextMeta = \case
      Atm p | Just (R.CtxS, n) <- metaAtom p -> Just n
      _ -> Nothing

    -- Each hypothesis of the lemma instantiates to a distinct hypothesis of
    -- the goal; the ones decided are committed pass by pass, as in 'applyRule'.
    discharge _ b hyps [] = Right (b, hyps)
    discharge cons b hyps pending = do
      (b', hyps', pending', progressed) <- foldM (step cons) (b, hyps, [], False) pending
      case reverse pending' of
        [] -> Right (b', hyps')
        again@(f : _)
          | progressed -> discharge cons b' hyps' again
          | otherwise -> Left (AmbiguousInstance name f (map fst (instances cons b' hyps' f)))

    step cons (b, hyps, pending, progressed) f = case instances cons b hyps f of
      [(h, b')] -> case MS.removeOne h hyps of
        Just hyps' -> Right (b', hyps', pending, True)
        Nothing -> Left (NotAnInstance name (lemmaGoal lemma))
      [] -> Left (NotAnInstance name (lemmaGoal lemma))
      _ -> Right (b, hyps, f : pending, progressed)

    instances cons b hyps f = [(h, b') | h <- HS.toList (MS.toHashSet hyps), Matched b' <- [matchFormL cons b f h]]

    argOfSort b (n, s) = case s of
      R.VarS -> ArgVar <$> look s n (bVars b)
      R.TermS -> ArgTerm <$> look s n (bTerms b)
      R.AtomS -> ArgAtom <$> look s n (bAtoms b)
      R.FormS -> ArgForm <$> look s n (bForms b)
      R.CtxS -> ArgCtx <$> look s n (bCtxs b)

    look :: forall v. R.Sort -> String -> Map String v -> Either (Failure a) v
    look s n = maybe (Left (CannotInstantiate name [R.MetaRef s n])) Right . Map.lookup n

-- ** Matching the statement of a lemma against the goal

bindFree :: (Hashable a) => Bindings a -> a -> Term a -> Match a
bindFree b v t = case HM.lookup v (bFree b) of
  Just t'
    | t' == t -> Matched b
    | otherwise -> Mismatch
  Nothing -> Matched b {bFree = HM.insert v t (bFree b)}

matchTermL :: forall a. (Schematic a) => Constraints a -> Bindings a -> Term a -> Term a -> Match a
matchTermL cons b pat t = case canonicalise pat of
  Var v -> case metaName v of
    Just (R.TermS, n) -> bindTerm cons b n t
    Just (R.VarS, n) -> case canonicalise t of
      Var w | maybe True ((/= R.TermS) . fst) (metaName w) -> bindVar b n w
      _ -> Mismatch
    Just _ -> Mismatch
    Nothing -> bindFree b v t
  Lit n
    | t == Lit n -> Matched b
    | otherwise -> Mismatch
  Succ :$ ps -> case t ^? _Succ of
    Just t' -> matchTermL cons b (SV.sIndex [od|0|] ps) t'
    Nothing -> Mismatch
  App (f :: Function n) ps -> case canonicalise t of
    App (g :: Function m) us -> case TE.testEquality (sNat @n) (sNat @m) of
      Just TE.Refl
        | f == g -> matchAll (matchTermL cons) b (zip (SV.toList ps) (SV.toList us))
      _ -> Mismatch
    _ -> Mismatch

matchAll :: (Bindings a -> x -> y -> Match a) -> Bindings a -> [(x, y)] -> Match a
matchAll m = foldM' \b (x, y) -> m b x y
  where
    foldM' _ b [] = Matched b
    foldM' k b ((x, y) : rest) = case k b (x, y) of
      Matched b' -> foldM' k b' rest
      other -> other

matchAtomL :: (Schematic a) => Constraints a -> Bindings a -> Atomic a -> Atomic a -> Match a
matchAtomL cons b pat@(ps :=== pt) q@(s :=== t) = case metaAtom pat of
  Just (R.AtomS, n)
    | isAtom q -> bindAtom cons b n q
  Just _ -> Mismatch
  Nothing -> case metaAtom q of
    Just _ -> Mismatch
    Nothing -> case matchTermL cons b ps s of
      Matched b' -> matchTermL cons b' pt t
      other -> other

matchFormL :: (Schematic a) => Constraints a -> Bindings a -> Formula a -> Formula a -> Match a
matchFormL cons b pat f = case (pat, f) of
  -- A context metavariable of the goal is opaque; it is never an instance of anything.
  (_, Atm q) | Just (R.CtxS, _) <- metaAtom q -> Mismatch
  (Atm p, _) | Just (R.FormS, n) <- metaAtom p -> bindForm cons b n f
  (Atm p, _) | Just (R.CtxS, _) <- metaAtom p -> Mismatch
  (Atm p, Atm q) -> matchAtomL cons b p q
  (Atm _, _) -> Mismatch
  (Bot, Bot) -> Matched b
  (Bot, _) -> Mismatch
  (p :/\ q, g :/\ h) -> both p g q h
  ((:/\) {}, _) -> Mismatch
  (p :\/ q, g :\/ h) -> both p g q h
  ((:\/) {}, _) -> Mismatch
  (p :==> q, g :==> h) -> both p g q h
  ((:==>) {}, _) -> Mismatch
  where
    both p g q h = case matchFormL cons b p g of
      Matched b' -> matchFormL cons b' q h
      other -> other

-- ** Instantiating the statement of a lemma

{- |
The sequents an appeal to a lemma establishes: the premises it leaves, and
its conclusion, both with the weakening.  What 'useLemma' computed is not
trusted; the certifier instantiates the statement again from the appeal.
-}
instantiateLemma :: forall a. (Schematic a) => Lemma a -> Appeal a -> Either (Failure a) ([Sequent a], Sequent a)
instantiateLemma lemma appeal = do
  when (length args /= length metas) $
    Left (Malformed (name <> " takes " <> show (length metas) <> " arguments"))
  -- The proofs of the premises cannot be weakened after the fact.
  unless (null (lemmaPremises lemma) || MS.population extra == 0) $ Left (CannotWeaken name extra)
  b <- foldM bind emptyBindings (zip metas args)
  premises <- traverse (instSequent b . snd) (lemmaPremises lemma)
  conclusion <- instSequent b (lemmaGoal lemma)
  pure (premises, conclusion)
  where
    name = appealName appeal
    args = appealArgs appeal
    metas = lemmaMetas lemma
    sigma = HM.fromList (appealSubst appeal)
    extra = appealWeakening appeal

    bind b ((n, s), arg) = case (s, arg) of
      (R.VarS, ArgVar v) -> Right b {bVars = Map.insert n v (bVars b)}
      (R.TermS, ArgTerm t) -> Right b {bTerms = Map.insert n t (bTerms b)}
      (R.AtomS, ArgAtom p) -> Right b {bAtoms = Map.insert n p (bAtoms b)}
      (R.FormS, ArgForm f) -> Right b {bForms = Map.insert n f (bForms b)}
      (R.CtxS, ArgCtx g) -> Right b {bCtxs = Map.insert n g (bCtxs b)}
      _ -> Left (Malformed ("ill-sorted argument for " <> n <> " of " <> name))

    instSequent b (hyps :|- s) = do
      hyps' <- foldM (\acc f -> (<> acc) <$> instHypothesis b f) extra (toList hyps)
      s' <- instF b s
      pure (hyps' :|- s')

    instHypothesis b f = case f of
      Atm p | Just (R.CtxS, n) <- metaAtom p -> look R.CtxS n (bCtxs b)
      _ -> (`MS.insertOne` MS.empty) <$> instF b f

    instF b = \case
      Atm p -> case metaAtom p of
        Just (R.FormS, n) -> look R.FormS n (bForms b)
        Just (R.CtxS, n) -> Left (Malformed (n <> " is a ctx metavariable, but stands as a formula in " <> name))
        _ -> Atm <$> instA b p
      f :/\ g -> (:/\) <$> instF b f <*> instF b g
      f :\/ g -> (:\/) <$> instF b f <*> instF b g
      f :==> g -> (:==>) <$> instF b f <*> instF b g
      Bot -> pure Bot

    instA b p@(s :=== t) = case metaAtom p of
      Just (R.AtomS, n) -> look R.AtomS n (bAtoms b)
      Just (_, n) -> Left (Malformed (n <> " is not an atom metavariable, but stands as an atom in " <> name))
      Nothing -> (:===) <$> instT b s <*> instT b t

    instT b = \case
      Var v -> case metaName v of
        Just (R.TermS, n) -> look R.TermS n (bTerms b)
        Just (R.VarS, n) -> Var <$> look R.VarS n (bVars b)
        Just (_, n) -> Left (Malformed (n <> " is not a term metavariable, but stands as a term in " <> name))
        Nothing -> pure (HM.lookupDefault (Var v) v sigma)
      Lit n -> pure (Lit n)
      App f xs -> App f <$> traverse (instT b) xs

    look :: forall v. R.Sort -> String -> Map String v -> Either (Failure a) v
    look s n = maybe (Left (CannotInstantiate name [R.MetaRef s n])) Right . Map.lookup n

-- * Terms

-- | Whether the term occurs in the atomic formula, as a subterm.
occursIn :: (Eq a) => Term a -> Atomic a -> Bool
occursIn t (s :=== u) = go s || go u
  where
    go v =
      v == t || case v of
        App _ args -> any go args
        _ -> False

-- | Whether the term occurs in the formula, as a subterm of an atom.
occursInFormula :: (Eq a) => Term a -> Formula a -> Bool
occursInFormula t = go
  where
    go = \case
      Atm p -> t `occursIn` p
      p :/\ q -> go p || go q
      p :\/ q -> go p || go q
      p :==> q -> go p || go q
      Bot -> False

-- | Replace every occurrence of the term by the variable.
abstract :: (Eq a) => Term a -> a -> Atomic a -> Atomic a
abstract t x (s :=== u) = go s :=== go u
  where
    go v
      | v == t = Var x
      | otherwise = case v of
          App f args -> App f (fmap go args)
          _ -> v

-- | Replace every occurrence of the term by the variable, throughout a formula.
abstractIn :: (Eq a) => Term a -> a -> Formula a -> Formula a
abstractIn t x = go
  where
    go = \case
      Atm p -> Atm (abstract t x p)
      p :/\ q -> go p :/\ go q
      p :\/ q -> go p :\/ go q
      p :==> q -> go p :==> go q
      Bot -> Bot

-- * Rendering

-- | Render an error for a human, naming symbols through the signature.
renderTacticError :: forall a. Signature -> (a -> String) -> TacticError a -> String
renderTacticError sig name = renderTacticErrorWith sig name (const Nothing)

-- | Render an error, showing an atom the hook names, such as a metavariable, as that name.
renderTacticErrorWith :: forall a. Signature -> (a -> String) -> (Atomic a -> Maybe String) -> TacticError a -> String
renderTacticErrorWith sig name hook = intercalate "\n" . render
  where
    render (TacticError loc goal failure) =
      (maybe "" (\(Loc l col) -> show l <> ":" <> show col <> ": ") loc <> headline failure)
        : map ("  " <>) (details failure <> state failure goal)

    -- A proof abandoned by sorry shows its state: the assumptions, then the succedent.
    state :: Failure a -> Sequent a -> [String]
    state Unfinished (ctx :|- c) = sort (map rf (toList ctx)) <> ["|- " <> rf c]
    state _ goal = ["goal: " <> rs goal]

    headline :: Failure a -> String
    headline = \case
      WrongSuccedent r _ ->
        label r <> "the succedent does not have the form " <> succedentOf r
      NoHypothesis r _ pat -> label r <> "no hypothesis of the form " <> R.renderFormPat pat
      AmbiguousHypothesis r _ pat _ ->
        label r <> "more than one hypothesis of the form " <> R.renderFormPat pat
      CannotInfer r refs ->
        label r <> "cannot infer " <> intercalate ", " (map R.refName refs) <> "; supply it"
      SideCondition r reason -> label r <> side reason
      NotAnEquation f -> "refl: the goal " <> rf f <> " is not an equation"
      NoMatch pat -> "no hypothesis matches " <> rap pat
      AmbiguousMatch pat _ -> "more than one hypothesis matches " <> rap pat
      NothingToRewrite t h -> "rewrite: " <> rt t <> " does not occur in " <> ra h
      RewriteWithItself h -> "rewrite: cannot rewrite " <> ra h <> " with itself"
      NotFresh x -> "induction: " <> name x <> " occurs in the goal"
      NotInContext f -> "assumption: " <> rf f <> " is not in the context"
      UnknownPremise d -> "exact: no premise or lemma named " <> d
      PremiseMismatch d s -> "exact: the premise " <> d <> " establishes " <> rs s
      NotAnInstance d s -> "exact: the goal is not an instance of " <> d <> ", which proves " <> rs s
      AmbiguousInstance d f _ -> "exact: more than one hypothesis is an instance of " <> rf f <> ", a hypothesis of " <> d
      CannotInstantiate d refs ->
        "exact: cannot infer " <> intercalate ", " (map R.refName refs) <> " of " <> d <> "; supply it"
      CannotWeaken d g ->
        "exact: " <> d <> " has premises but no context metavariable, so it cannot take the hypotheses " <> rc g
      NotClosed d vs ->
        "exact: "
          <> d
          <> " has metavariables or premises, so the free variables "
          <> intercalate ", " (map name vs)
          <> " of its statement cannot be instantiated; declare them as term metavariables"
      NotEigen d x v ->
        "exact: " <> d <> " binds " <> x <> ", so " <> name v <> " must not occur in the goal or the other arguments"
      WrongGoalCount expected actual ->
        show expected <> " blocks given for " <> show actual <> " goals"
      Alternatives _ -> "every alternative failed"
      Unsolved _ -> "goals left unsolved"
      RepeatLimit -> "repeat: no end after " <> show repeatLimit <> " iterations"
      Unfinished -> "sorry: the proof stops here"
      Rejected _ -> "the checker rejected the proof a tactic built (a bug in the tactic)"
      WrongPremise d expected actual ->
        "the proof built for a premise of " <> d <> " proves " <> rs actual <> " instead of " <> rs expected <> " (a bug in a tactic)"
      WrongConclusion s -> "the proof a tactic built proves " <> rs s <> " instead (a bug in a tactic)"
      Malformed msg -> "malformed tactic: " <> msg

    details :: Failure a -> [String]
    details = \case
      WrongSuccedent r args -> given r args
      NoHypothesis r args _ -> given r args
      AmbiguousHypothesis r args _ fs -> given r args <> ["candidates: " <> intercalate "; " (map rf fs)]
      AmbiguousMatch _ fs -> ["candidates: " <> intercalate "; " (map rf fs)]
      AmbiguousInstance _ _ fs -> ["candidates: " <> intercalate "; " (map rf fs)]
      Alternatives es -> concatMap (map ("| " <>) . render) es
      Unsolved gs -> map (("- " <>) . rs) gs
      Rejected errs -> ["- " <> show (context e) <> ": " <> side (reason e) | e <- NE.toList errs]
      _ -> []

    given r args =
      [ "with " <> intercalate ", " gs
      | let gs = [R.refName (R.paramRef p) <> " := " <> renderArg arg | (p, Just arg) <- zip (R.ruleParams (ruleSpec r)) args]
      , not (null gs)
      ]

    renderArg = \case
      ArgVar h -> renderHole name h
      ArgTerm t -> rtp t
      ArgAtom p -> rap p
      ArgForm f -> renderFormulaWith (closed >=> hook) sig (renderHole name) f
      ArgCtx g -> renderContextWith (closed >=> hook) sig (renderHole name) g

    side = \case
      EqualityCheckFailed s t -> rt s <> " and " <> rt t <> " are not definitionally equal"
      DefinitionResolutionFailed err -> displayException err
      TermEigenVariableViolation x t -> name x <> " occurs in " <> rt t
      AssumptionEigenVariableViolation x g -> name x <> " occurs in the context " <> rc g
      MissingAssumption f g -> rf f <> " is not among " <> rc g
      AssumptionMismatch g h -> "the contexts " <> rc g <> " and " <> rc h <> " differ"
      ConsequentMismatch f g -> "expected the succedent " <> rf f <> ", found " <> rf g

    label r = R.ruleLabel (ruleSpec r) <> ": "
    succedentOf r = let _ R.:|- s = R.ruleConclusion (ruleSpec r) in R.renderFormPat s

    rt = renderTerm sig name
    ra = renderAtomicWith hook sig name
    rf = renderFormulaWith hook sig name
    rc = renderContextWith hook sig name
    rs = renderSequentWith hook sig name
    rtp = renderTerm sig (renderHole name)
    rap = renderAtomicWith (closed >=> hook) sig (renderHole name)
