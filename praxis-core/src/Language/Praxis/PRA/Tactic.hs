{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE QuasiQuotes #-}

{- |
A tiny tactic language for the calculus, and the engine which runs it.

A tactic is applied to a goal, a 'Sequent', and either fails or produces a
partial proof: a proof tree whose leaves are the goals left open, or the
premises a derived rule may appeal to.  The primitive tactics are the rules of
the calculus applied backwards — one per rule, read off 'ruleSpec', so a rule
added to "Language.Praxis.PRA.Rule.G3i" is a tactic without further ado.  A
handful of derived tactics compute the arguments a rule needs from the goal.

Nothing here is trusted.  'prove' hands the proof it built to
'inferConclusionOpen' and compares the sequent the checker infers with the
goal, so a tactic which produced the wrong proof is an error, not an unsound
theorem.  See "Language.Praxis.PRA.Tactic.Parser" for the textual syntax.
-}
module Language.Praxis.PRA.Tactic (
  -- * Tactics
  Tactic (..),
  Loc (..),
  applyWith,

  -- * Running
  prove,
  proveOpen,
  runTactic,
  Leaf (..),
  Partial,

  -- * Errors
  TacticError (..),
  Failure (..),
  renderTacticError,

  -- * Names
  Fresh (..),
  goalNames,
) where

import Control.Applicative ((<|>))
import Control.Lens ((^?))
import Control.Monad (foldM, join, unless, when)
import Control.Monad.Free (Free (..), iter)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (evalStateT, get, put)
import Data.Bifunctor (first)
import Data.Foldable (toList)
import Data.Functor.Foldable (embed)
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Multiset (Multiset)
import Data.Multiset qualified as MS
import Data.Set qualified as Set
import Data.Sized qualified as SV
import Data.Traversable (for)
import Data.Type.Equality qualified as TE
import Data.Type.Natural (sNat)
import Data.Type.Ordinal (od)
import GHC.Generics (Generic)
import Language.Praxis.PRA.Equality (defEq)
import Language.Praxis.PRA.Pattern
import Language.Praxis.PRA.PrimitiveRecursion (Evalable (..), PRFCode (..))
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.Rule qualified as R
import Language.Praxis.PRA.Signature (Signature)
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Syntax.Pretty

-- * Names

-- | Names which can be chosen apart from any finite set of others.
class (Hashable a) => Fresh a where
  -- | A name not in the set, derived from the hint.
  freshen :: HashSet a -> a -> a

  -- | The hint to start from when nothing suggests one.
  anyName :: a

-- | Primes are appended until the name is new: @x@, @x'@, @x''@, and so on.
instance Fresh String where
  freshen used = go
    where
      go n
        | n `HS.member` used = go (n <> "'")
        | otherwise = n
  anyName = "x"

-- | Every name occurring in a sequent.
goalNames :: (Hashable a) => Sequent a -> HashSet a
goalNames (ctx :|- c) = HS.fromList (foldMap toList ctx <> toList c)

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
  | {- | @Induction y n@: prove the goal by 'Ind' on the variable @y@, with the
    eigenvariable @n@, chosen fresh when it is not given.
    -}
    Induction !a !(Maybe a)
  | {- | Close a goal whose succedent is in the context, expanding the identity
    through the connectives down to 'Id'.
    -}
    Assumption
  | -- | Close a goal which is exactly the sequent of the named premise.
    Exact !String
  | -- | Leave the goal open.
    Skip
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

-- * Partial proofs

-- | What a partial proof may end in.
data Leaf a
  = -- | a goal not yet proved
    Open !(Sequent a)
  | -- | a premise of the derived rule being proved, with its declared sequent
    Premise !String !(Sequent a)
  deriving (Show, Eq, Generic)

type Partial a = Free (ProofF a) (Leaf a)

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
  | UnknownPremise !String
  | -- | the goal is not the declared sequent of the premise
    PremiseMismatch !String !(Sequent a)
  | -- | 'Dispatch' with the wrong number of blocks: expected, actual
    WrongGoalCount !Int !Int
  | -- | every alternative of an 'OrElse' failed
    Alternatives ![TacticError a]
  | -- | the goals left open at the end
    Unsolved ![Sequent a]
  | RepeatLimit
  | -- | the checker rejected the proof the tactic built: a bug in a tactic
    Rejected !(NonEmpty (ProofError a))
  | -- | the checker accepted the proof, but of another sequent: a bug in a tactic
    WrongConclusion !(Sequent a)
  | -- | a malformed tactic, such as an ill-sorted argument
    Malformed !String
  deriving (Show, Eq, Generic)

-- * Running

-- | Prove a closed sequent.
prove :: (Fresh a) => Sequent a -> Tactic a -> Either (TacticError a) (Proof a)
prove goal t = do
  p <- proveOpen Map.empty goal t
  closeProof <$> traverse (const (Left (TacticError Nothing goal (Malformed "premise in a closed proof")))) p
  where
    closeProof = iter embed

{- |
Prove a sequent from declared premises, as a derived rule does.  Every open
leaf of the result is one of the premises.  The proof is checked before it is
returned.
-}
proveOpen ::
  (Fresh a) =>
  -- | the premises, with the sequents they are declared to establish
  Map String (Sequent a) ->
  Sequent a ->
  Tactic a ->
  Either (TacticError a) (Free (ProofF a) String)
proveOpen prems goal t = do
  p <- runTactic prems t goal
  let opens = [g | Open g <- toList p]
  unless (null opens) $ Left (TacticError Nothing goal (Unsolved opens))
  let p' =
        p >>= \case
          Open g -> Pure ("", g)
          Premise d g -> Pure (d, g)
  case inferConclusionOpen snd p' of
    Left errs -> Left (TacticError Nothing goal (Rejected errs))
    Right s
      | s == goal -> Right (fmap fst p')
      | otherwise -> Left (TacticError Nothing goal (WrongConclusion s))

-- | The limit on the iterations of 'Repeat' along any branch.
repeatLimit :: Int
repeatLimit = 1000

-- | Run a tactic on a goal, without checking what it built.
runTactic ::
  forall a.
  (Fresh a) =>
  Map String (Sequent a) ->
  Tactic a ->
  Sequent a ->
  Either (TacticError a) (Partial a)
runTactic prems = go
  where
    go :: Tactic a -> Sequent a -> Either (TacticError a) (Partial a)
    go tac goal@(ctx :|- c) = case tac of
      At loc t -> first (located loc) (go t goal)
      Skip -> Right (Pure (Open goal))
      Then t u -> go t goal >>= continue (go u)
      OrElse t u -> case go t goal of
        Right p -> Right p
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
      Exact d -> case Map.lookup d prems of
        Nothing -> failWith (UnknownPremise d)
        Just s
          | s == goal -> Right (Pure (Premise d s))
          | otherwise -> failWith (PremiseMismatch d s)
      Apply name args -> first (TacticError Nothing goal) (applyRule name args goal)
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
      Induction y given -> do
        let names = goalNames goal
        n <- case given of
          Just n
            | n `HS.member` names -> failWith (NotFresh n)
            | otherwise -> pure n
          Nothing -> pure (freshen names y)
        go (applyWith IndRule [ArgVar (Named n), form (subst y (Var n) c), term (Var y)]) goal
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

        -- The unique hypothesis matching an atomic pattern.
        select :: Atomic (Hole a) -> Either (TacticError a) (Atomic a)
        select pat = case [p | Atm p <- HS.toList (MS.toHashSet ctx), matchAtomic pat p] of
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
          Left _ -> Right (Pure (Open goal))
          Right p -> continue (repeatFrom (n + 1) t) p

    located loc e = e {errorLoc = errorLoc e <|> Just loc}
    alternatives (TacticError _ _ (Alternatives es)) = es
    alternatives e = [e]

    term = ArgTerm . fmap Named
    atom = ArgAtom . fmap Named
    form = ArgForm . fmap Named

-- * Rule application

data Bindings a = Bindings
  { bVars :: !(Map String a)
  , bTerms :: !(Map String (Term a))
  , bAtoms :: !(Map String (Atomic a))
  , bForms :: !(Map String (Formula a))
  , bCtxs :: !(Map String (Multiset (Formula a)))
  }

emptyBindings :: Bindings a
emptyBindings = Bindings Map.empty Map.empty Map.empty Map.empty Map.empty

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

data Match a = Matched !(Bindings a) | Deferred | Mismatch

-- | A discharge of a principal formula, or the matching of the succedent.
data Obligation = MatchSuccedent !R.FormPat | Discharge !R.FormPat

applyRule ::
  forall a.
  (Fresh a) =>
  RuleName ->
  [Maybe (Arg (Hole a))] ->
  Sequent a ->
  Either (Failure a) (Partial a)
applyRule name userArgs (ctx :|- c) = do
  when (length userArgs /= length params) $
    Left (Malformed (show name <> " takes " <> show (length params) <> " arguments"))
  (b0, cons) <- foldM seed (emptyBindings, Constraints Map.empty Map.empty Map.empty) (zip params userArgs)
  let fs R.:+ R.CtxM g R.:|- cpat = R.ruleConclusion rule
  (b1, rest) <- resolve cons b0 ctx (MatchSuccedent cpat : map Discharge fs)
  let b2 = b1 {bCtxs = Map.insert g rest (bCtxs b1)}
      unbound = [ref | ref <- Set.toList (R.metas rule) <> map R.paramRef params, not (isBound ref b2)]
  unless (null unbound) $ Left (CannotInfer name unbound)
  mapM_ (checkSide b2) (R.ruleSides rule)
  args <- traverse (argOf b2) params
  premises <- traverse (instSeq b2) (R.rulePremises rule)
  maybe (Left (Malformed "mkStep")) (Right . Free) (mkStep name args (map (Pure . Open) premises))
  where
    rule = ruleSpec name
    params = R.ruleParams rule

    seed (b, cons) (param, arg) = case (param, arg) of
      (_, Nothing) -> Right (b, cons)
      (R.PVar (R.VarM x), Just (ArgVar h)) -> case h of
        Wild -> Right (b, cons)
        Named v -> Right (b {bVars = Map.insert x v (bVars b)}, cons)
      (R.PTerm (R.TermM n), Just (ArgTerm p)) -> case closed p of
        Just t -> Right (b {bTerms = Map.insert n t (bTerms b)}, cons)
        Nothing -> Right (b, cons {cTerms = Map.insert n p (cTerms cons)})
      (R.PAtom (R.AtomM n), Just (ArgAtom p)) -> case closed p of
        Just t -> Right (b {bAtoms = Map.insert n t (bAtoms b)}, cons)
        Nothing -> Right (b, cons {cAtoms = Map.insert n p (cAtoms cons)})
      (R.PForm (R.FormM n), Just (ArgForm p)) -> case closed p of
        Just t -> Right (b {bForms = Map.insert n t (bForms b)}, cons)
        Nothing -> Right (b, cons {cForms = Map.insert n p (cForms cons)})
      (R.PCtx _, Just _) -> Left (Malformed "a context parameter cannot be given")
      _ -> Left (Malformed ("ill-sorted argument for " <> R.refName (R.paramRef param)))

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
        unless (defEq s t) $ Left (SideCondition name (EqualityCheckFailed s t))
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

matchAtomPat :: (Eq a) => Constraints a -> Bindings a -> R.AtomPat -> Atomic a -> Match a
matchAtomPat cons b pat p@(s :=== t) = case pat of
  R.AMeta (R.AtomM n) -> bindAtom cons b n p
  sp R.:=== tp -> case matchTermPat cons b sp s of
    Matched b' -> matchTermPat cons b' tp t
    other -> other

matchForm :: (Eq a) => Constraints a -> Bindings a -> R.FormPat -> Formula a -> Match a
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
    go ((f :: PRFCode n) :$ ps) ((g :: PRFCode m) :$ us) =
      case TE.testEquality (sNat @n) (sNat @m) of
        Just TE.Refl
          | f == g -> foldr merge (Just Nothing) (zipWith go (SV.toList ps) (SV.toList us))
        _ -> Nothing
    go (_ :$ _) _ = Nothing

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

-- * Terms

-- | Whether the term occurs in the atomic formula, as a subterm.
occursIn :: (Eq a) => Term a -> Atomic a -> Bool
occursIn t (s :=== u) = go s || go u
  where
    go v =
      v == t || case v of
        _ :$ args -> any go args
        _ -> False

-- | Replace every occurrence of the term by the variable.
abstract :: (Eq a) => Term a -> a -> Atomic a -> Atomic a
abstract t x (s :=== u) = go s :=== go u
  where
    go v
      | v == t = Var x
      | otherwise = case v of
          f :$ args -> f :$ fmap go args
          _ -> v

-- * Rendering

-- | Render an error for a human, naming symbols through the signature.
renderTacticError :: forall a. Signature -> (a -> String) -> TacticError a -> String
renderTacticError sig name = intercalate "\n" . render
  where
    render (TacticError loc goal failure) =
      (maybe "" (\(Loc l col) -> show l <> ":" <> show col <> ": ") loc <> headline failure)
        : map ("  " <>) (details failure <> ["goal: " <> rs goal])

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
      UnknownPremise d -> "exact: no premise named " <> d
      PremiseMismatch d s -> "exact: the premise " <> d <> " establishes " <> rs s
      WrongGoalCount expected actual ->
        show expected <> " blocks given for " <> show actual <> " goals"
      Alternatives _ -> "every alternative failed"
      Unsolved _ -> "goals left unsolved"
      RepeatLimit -> "repeat: no end after " <> show repeatLimit <> " iterations"
      Rejected _ -> "the checker rejected the proof a tactic built (a bug in the tactic)"
      WrongConclusion s -> "the proof a tactic built proves " <> rs s <> " instead (a bug in the tactic)"
      Malformed msg -> "malformed tactic: " <> msg

    details :: Failure a -> [String]
    details = \case
      WrongSuccedent r args -> given r args
      NoHypothesis r args _ -> given r args
      AmbiguousHypothesis r args _ fs -> given r args <> ["candidates: " <> intercalate "; " (map rf fs)]
      AmbiguousMatch _ fs -> ["candidates: " <> intercalate "; " (map rf fs)]
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
      ArgForm f -> renderFormula sig (renderHole name) f
      ArgCtx g -> renderContext sig (renderHole name) g

    side = \case
      EqualityCheckFailed s t -> rt s <> " and " <> rt t <> " are not definitionally equal"
      TermEigenVariableViolation x t -> name x <> " occurs in " <> rt t
      AssumptionEigenVariableViolation x g -> name x <> " occurs in the context " <> rc g
      MissingAssumption f g -> rf f <> " is not among " <> rc g
      AssumptionMismatch g h -> "the contexts " <> rc g <> " and " <> rc h <> " differ"
      ConsequentMismatch f g -> "expected the succedent " <> rf f <> ", found " <> rf g

    label r = R.ruleLabel (ruleSpec r) <> ": "
    succedentOf r = let _ R.:|- s = R.ruleConclusion (ruleSpec r) in R.renderFormPat s

    rt = renderTerm sig name
    ra = renderAtomic sig name
    rf = renderFormula sig name
    rc = renderContext sig name
    rs = renderSequent sig name
    rtp = renderTerm sig (renderHole name)
    rap = renderAtomic sig (renderHole name)
