{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE QuasiQuotes #-}

{- |
A tiny tactic language for the calculus, and the engine which runs it.

A tactic is applied to a goal, a 'Goal': a 'Sequent' whose hypotheses are
named, @H1@, @H2@, … as the engine numbers them, a context metavariable by
its own name.  It either fails or produces a partial proof: a proof tree
whose leaves are the goals left open, or the premises a derived rule may
appeal to.  The primitive tactics are the rules of the calculus applied
backwards — one per rule, read off 'ruleSpec', so a rule added to
"Language.Praxis.PRA.Rule.G3i" is a tactic without further ado.  A handful of
derived tactics compute the arguments a rule needs from the goal, and
'Exact' appeals to a 'Lemma' certified before: a theorem, or a derived rule,
instantiated to the goal.

A hypothesis keeps its name for as long as it stands; one a step introduces
is named as the script says, by 'As', or by the next number the branch has
not used.  'On' picks the hypotheses a rule acts on by name, where the
engine would otherwise look for the unique one of the right shape.

Nothing here is trusted.  'prove' hands the proof it built to the checker
and compares the sequent it infers with the goal, so a tactic which produced
the wrong proof is an error, not an unsound theorem; an appeal to a lemma is
checked against the lemma's statement, instantiated afresh.  See
"Language.Praxis.PRA.Tactic.Parser" for the textual syntax.
-}
module Language.Praxis.PRA.Tactic (
  -- * Tactics
  Tactic (..),
  Selector (..),
  Loc (..),
  applyWith,

  -- * Goals
  Goal (..),
  Hypothesis (..),
  mkGoal,
  goalOf,
  goalSequent,
  goalNames,

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
) where

import Control.Applicative ((<|>))
import Control.Exception (displayException)
import Control.Lens ((^?))
import Control.Monad (foldM, forM_, join, unless, when, (>=>))
import Control.Monad.Free (Free (..))
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (evalStateT, get, put)
import Data.Bifunctor (first)
import Data.Char (isDigit)
import Data.Either (partitionEithers)
import Data.Foldable (toList)
import Data.Functor.Foldable (embed)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)
import Data.List (find, intercalate, nub, nubBy)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust, isNothing, listToMaybe, mapMaybe)
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

-- | Whether an atom is one, rather than an opaque formula or context metavariable.
isAtom :: (Schematic a) => Atomic a -> Bool
isAtom p = maybe True ((== R.AtomS) . fst) (metaAtom p)

-- | The context metavariable a hypothesis stands for.
contextMeta :: (Schematic a) => Formula a -> Maybe String
contextMeta = \case
  Atm p | Just (R.CtxS, n) <- metaAtom p -> Just n
  _ -> Nothing

-- * Goals

-- | A hypothesis, by the name the script refers to it by.
data Hypothesis a = Hypothesis
  { hypothesisName :: !String
  , hypothesisFormula :: !(Formula a)
  }
  deriving (Show, Eq, Generic)

{- |
A sequent with its hypotheses named, in the order they were introduced.  A
context metavariable is a hypothesis named by the metavariable; every other
hypothesis is @H@ and a number, and the goal remembers the next number, so a
name is never reused along a branch.
-}
data Goal a = Goal
  { goalHypotheses :: ![Hypothesis a]
  , goalSuccedent :: !(Formula a)
  , goalFresh :: !Int
  }
  deriving (Show, Eq, Generic)

-- | The goal with the hypotheses given, in that order, numbered from @H1@.
mkGoal :: (Schematic a) => [Formula a] -> Formula a -> Goal a
mkGoal fs c = Goal (reverse named) c next
  where
    (named, next) = foldl step ([], 1) fs
    step (acc, i) f = case contextMeta f of
      Just n -> (Hypothesis n f : acc, i)
      Nothing -> (Hypothesis ("H" <> show i) f : acc, i + 1 :: Int)

-- | The goal for a sequent, its hypotheses in no particular order.
goalOf :: (Schematic a) => Sequent a -> Goal a
goalOf (ctx :|- c) = mkGoal (toList ctx) c

-- | The sequent a goal is.
goalSequent :: (Hashable a) => Goal a -> Sequent a
goalSequent (Goal hs c _) = goalContext (Goal hs c 0) :|- c

goalContext :: (Hashable a) => Goal a -> Multiset (Formula a)
goalContext = foldr (MS.insertOne . hypothesisFormula) MS.empty . goalHypotheses

-- | The hypothesis of the name, if any.
hypothesisNamed :: String -> Goal a -> Maybe (Hypothesis a)
hypothesisNamed n = find ((== n) . hypothesisName) . goalHypotheses

{- |
The hypotheses of a premise, given those of the conclusion: the ones
discharged are dropped, but one the premise states again keeps its name and
its place; the genuinely new ones follow, named as given and then freshly.
Returns the names left unused and the next number.
-}
nameHypotheses :: (Eq a) => Goal a -> [String] -> [Formula a] -> [String] -> Either (Failure a) ([Hypothesis a], [String], Int)
nameHypotheses conclusion dischargedNames stated given = do
  (names, given', counter') <- allocate (map hypothesisName kept) (goalFresh conclusion) given (length new)
  pure (kept <> zipWith Hypothesis names new, given', counter')
  where
    discharged = [h | h <- goalHypotheses conclusion, hypothesisName h `elem` dischargedNames]
    (restated, new) = foldl claim ([], []) stated
    claim (taken, fresh) f = case [h | h <- discharged, hypothesisFormula h == f, hypothesisName h `notElem` map hypothesisName taken] of
      h : _ -> (taken <> [h], fresh)
      [] -> (taken, fresh <> [f])
    kept = [h | h <- goalHypotheses conclusion, hypothesisName h `notElem` dischargedNames || hypothesisName h `elem` map hypothesisName restated]

    -- The names given first, then fresh ones, none in use; a given name of
    -- the engine's own form moves the counter past it.
    allocate :: [String] -> Int -> [String] -> Int -> Either (Failure a) ([String], [String], Int)
    allocate _ counter names 0 = Right ([], names, counter)
    allocate inUse counter (n : names) k
      | n `elem` inUse = Left (NameInUse n)
      | otherwise = do
          (ns, names', counter') <- allocate (n : inUse) (bumpPast n counter) names (k - 1)
          pure (n : ns, names', counter')
    allocate inUse counter [] k
      | n `elem` inUse = allocate inUse (counter + 1) [] k
      | otherwise = do
          (ns, names', counter') <- allocate (n : inUse) (counter + 1) [] (k - 1)
          pure (n : ns, names', counter')
      where
        n = "H" <> show counter

-- | The counter moved past a name of the engine's own form, @H<n>@.
bumpPast :: String -> Int -> Int
bumpPast n counter = case n of
  'H' : ds | not (null ds), all isDigit ds -> max counter (read ds + 1)
  _ -> counter

{- |
Reserve the names given for a later step: the counter of the goal is moved
past them, so that a step before it does not take them.
-}
reserve :: [String] -> Goal a -> Goal a
reserve names goal = goal {goalFresh = foldr bumpPast (goalFresh goal) names}

-- * Tactics

-- | A position in the source of a tactic, for error reports.
data Loc = Loc {locLine :: !Int, locColumn :: !Int}
  deriving (Show, Eq, Ord, Generic)

-- | How a derived tactic picks a hypothesis: by name, or as the unique one matching a pattern.
data Selector a
  = ByName !String
  | ByPattern !(Atomic (Hole a))
  deriving (Show, Eq, Generic)

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
  | {- | From the hypothesis @t = s@ selected, add @s = t@.  The selector may
    also name a lemma stating an equation, as for 'Cong', a closed one here.
    -}
    Symmetry !(Selector a)
  | {- | @Rewrite eq h@: with the hypothesis @t = s@ selected by @eq@, add the
    atomic hypothesis selected by @h@ with every occurrence of @t@ replaced
    by @s@, by 'Subst'.  @eq@ may also name a lemma stating an equation, as
    for 'Cong': its instance is the first subterm of @h@ its left side
    matches.
    -}
    Rewrite !(Selector a) !(Selector a)
  | {- | @Cong sel@: close the goal @u = v@ by the hypothesis @t = s@ selected,
    or by the first hypothesis which fits when none is, where @v@ is @u@ with
    occurrences of @t@ replaced by @s@; the hypothesis may state the equation
    either way round.  The context of the occurrences is inferred by
    comparing the sides, and the proof is 'Defeq' on @u = u@, 'Subst' and
    'Id'.  The selector may also name a lemma stating an equation, @|- t = s@
    under no hypotheses but a context metavariable: its instance is found
    where the sides of the goal differ, cut in, proved by the lemma, and
    used as the hypothesis.
    -}
    Cong !(Maybe (Selector a))
  | {- | @Induction t n@: prove the goal by 'Ind' on the term @t@, with the
    eigenvariable @n@, chosen fresh when it is not given.  The hypotheses
    mentioning @t@ are generalized into the induction formula, through 'Cut',
    and reintroduced in each case, where the induction hypothesis then is an
    implication from them.  Under 'As', the first name is for the induction
    hypothesis and the rest for the hypotheses reintroduced, in order.
    -}
    Induction !(Term a) !(Maybe a)
  | {- | Close a goal whose succedent is in the context, expanding the identity
    through the connectives down to 'Id'.
    -}
    Assumption
  | {- | @Exact name args@: close the goal by the named premise, whose sequent
    it must be, or by the named hypothesis, which must be the succedent, or
    appeal to the named 'Lemma', which leaves the premises of the lemma as
    goals.  The arguments are for the metavariables of the lemma, in the
    order of its binders, as for 'Apply'.
    -}
    Exact !String ![Maybe (Arg (Hole a))]
  | {- | @Calc t0 [(t1, u1), …, (tn, un)]@: prove the goal @t0 = tn@ as a
    chain of equations, each step @t(i-1) = ti@ proved by @ui@ under the
    hypotheses of the goal.  The steps are cut in as one conjunction, split
    by 'ConjL' and chained by 'Subst' down to 'Id'.
    -}
    Calc !(Term a) ![(Term a, Tactic a)]
  | {- | @Have name f u@: prove @f@ by @u@ and go on with it as a hypothesis,
    named @name@, or @H@ when no name is given, or the next @H<n>@ when @H@ is
    taken: @Cut f { u } { skip }@, with the name.
    -}
    Have !(Maybe String) !(Formula a) !(Tactic a)
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
  | {- | @t on H…@: the principal formulas of the rule, or the hypotheses of
    the lemma, @t@ applies are the named hypotheses, in order.
    -}
    On ![String] !(Tactic a)
  | -- | @t as H…@: the hypotheses @t@ introduces take the names, in order.
    As ![String] !(Tactic a)
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
    Open !(Goal a)
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
  , errorGoal :: !(Goal a)
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
  | -- | the named hypothesis does not have the shape of the principal formula it was given for
    NotPrincipal !RuleName !String !R.FormPat
  | -- | parameters neither given nor determined by the goal
    CannotInfer !RuleName ![R.MetaRef]
  | SideCondition !RuleName !(ProofErrorReason a)
  | -- | 'Refl' or 'Cong', named, on a goal which is not an equation
    NotAnEquation !String !(Formula a)
  | -- | no hypothesis matches the pattern of a derived tactic
    NoMatch !(Atomic (Hole a))
  | AmbiguousMatch !(Atomic (Hole a)) ![Formula a]
  | -- | no hypothesis of the name
    UnknownHypothesis !String
  | -- | the named hypothesis is not atomic, where a derived tactic needs an atom
    NotAtomic !String !(Formula a)
  | -- | the term does not occur in the hypothesis to be rewritten
    NothingToRewrite !(Term a) !(Atomic a)
  | -- | a hypothesis cannot be rewritten with itself
    RewriteWithItself !(Atomic a)
  | -- | 'Cong' with no equation, among those tried, turning the left side of the goal into the right
    NoCongruence !(Atomic a) ![Atomic a]
  | -- | a lemma named where a hypothesis is expected, which does not state an equation
    LemmaNotEquation !String !(Sequent a)
  | -- | variables of the equation of a lemma which its use does not determine
    Undetermined !String ![a]
  | -- | the eigenvariable given to 'Induction' occurs in the goal
    NotFresh !a
  | -- | 'Assumption' on a succedent absent from the context
    NotInContext !(Formula a)
  | -- | 'Exact' on a name which is neither a premise, a lemma nor a hypothesis
    UnknownPremise !String
  | -- | the goal is not the declared sequent of the premise
    PremiseMismatch !String !(Sequent a)
  | -- | 'Exact' on a hypothesis which is not the succedent
    HypothesisMismatch !String !(Formula a)
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
  | -- | names given by 'As' for hypotheses the tactic did not introduce
    NamesUnused ![String]
  | -- | a name given by 'As' which a hypothesis of the goal already has
    NameInUse !String
  | -- | 'On' or 'As' on a tactic which acts on no hypothesis
    NothingToName
  | -- | 'Calc' on a goal which is not the equation between the ends of the chain
    CalcMismatch !(Term a) !(Term a)
  | -- | 'Dispatch' with the wrong number of blocks: expected, actual
    WrongGoalCount !Int !Int
  | -- | every alternative of an 'OrElse' failed
    Alternatives ![TacticError a]
  | -- | the goals left open at the end
    Unsolved ![Goal a]
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

-- | Prove a closed goal.
prove :: (Schematic a) => Goal a -> Tactic a -> Either (TacticError a) (Proof a)
prove = proveWith emptyKernelEnv Map.empty

{- |
Prove a closed goal, appealing to lemmas.  The proof is closed with the
proofs of the lemmas, and checked once more when it appealed to any, since
instantiating them is a transformation of their proofs.
-}
proveWith :: forall a. (Schematic a) => KernelEnv -> Map String (Certified a) -> Goal a -> Tactic a -> Either (TacticError a) (Proof a)
proveWith env certified goal t = do
  p <- proveOpenWith env (fmap certifiedLemma certified) Map.empty goal t
  proof <- close p
  when (appeals p) case inferConclusionIn env proof of
    Left errs -> failWith (Rejected errs)
    Right s
      | s /= goalSequent goal -> failWith (WrongConclusion s)
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
Prove a goal from declared premises, as a derived rule does.  Every open
leaf of the result is one of the premises.  The proof is checked before it is
returned.
-}
proveOpen ::
  (Schematic a) =>
  -- | the premises, with the sequents they are declared to establish
  Map String (Sequent a) ->
  Goal a ->
  Tactic a ->
  Either (TacticError a) (Free (Step a) String)
proveOpen = proveOpenIn emptyKernelEnv

-- | Run and certify a tactic against checked, shared PRF definitions.
proveOpenIn :: (Schematic a) => KernelEnv -> Map String (Sequent a) -> Goal a -> Tactic a -> Either (TacticError a) (Free (Step a) String)
proveOpenIn env = proveOpenWith env Map.empty

-- | 'proveOpenIn', with lemmas to appeal to.
proveOpenWith :: (Schematic a) => KernelEnv -> Map String (Lemma a) -> Map String (Sequent a) -> Goal a -> Tactic a -> Either (TacticError a) (Free (Step a) String)
proveOpenWith env lemmas prems goal t = do
  p <- runTacticWith env lemmas prems t goal
  let opens = [g | Open g <- toList p]
  unless (null opens) $ Left (TacticError Nothing goal (Unsolved opens))
  let p' =
        p >>= \case
          Open g -> Pure ("", goalSequent g)
          Premise d s -> Pure (d, s)
  s <- first (TacticError Nothing goal) (certify env lemmas snd p')
  if s == goalSequent goal
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

-- | What 'On' and 'As' told the next step: the hypotheses to act on, and the names for those introduced.
data Hints = Hints
  { hintOn :: ![String]
  , hintAs :: ![String]
  }

noHints :: Hints
noHints = Hints [] []

unhinted :: Hints -> Bool
unhinted (Hints on as) = null on && null as

-- | Run a tactic on a goal, without checking what it built.
runTactic ::
  (Schematic a) =>
  Map String (Sequent a) ->
  Tactic a ->
  Goal a ->
  Either (TacticError a) (Partial a)
runTactic = runTacticWith emptyKernelEnv Map.empty

-- | 'runTactic', with definitions and lemmas.
runTacticWith :: forall a. (Schematic a) => KernelEnv -> Map String (Lemma a) -> Map String (Sequent a) -> Tactic a -> Goal a -> Either (TacticError a) (Partial a)
runTacticWith env lemmas prems = go noHints
  where
    go :: Hints -> Tactic a -> Goal a -> Either (TacticError a) (Partial a)
    go hints tac goal = case tac of
      At loc t -> first (located loc) (go hints t goal)
      On names t -> go hints {hintOn = names} t goal
      As names t -> go hints {hintAs = names} t goal
      Skip -> plain (Right (Pure (Open goal)))
      Sorry -> plain (failWith Unfinished)
      Then t u -> go hints t goal >>= continue (go noHints u)
      OrElse t u -> case go hints t goal of
        Right p -> Right p
        Left e1 | abandoned e1 -> Left e1
        Left e1 -> case go hints u goal of
          Right p -> Right p
          Left e2 -> failWith (Alternatives (alternatives e1 <> alternatives e2))
      Try t -> case go hints t goal of
        Right p -> Right p
        Left e | abandoned e -> Left e
        Left _ -> Right (Pure (Open goal))
      Repeat t -> plain (repeatFrom 0 t goal)
      Dispatch t us -> do
        p <- go hints t goal
        let opens = length [() | Open _ <- toList p]
        when (opens /= length us) $ failWith (WrongGoalCount (length us) opens)
        fmap join . flip evalStateT us $ for p \case
          Open g ->
            get >>= \case
              u : rest -> put rest *> lift (go noHints u g)
              [] -> lift (Left (TacticError Nothing goal (WrongGoalCount (length us) opens)))
          leaf -> pure (Pure leaf)
      Exact d args -> case (Map.lookup d prems, Map.lookup d lemmas, hypothesisNamed d goal) of
        (Just s, _, _)
          | any isJust args -> failWith (Malformed ("the premise " <> d <> " takes no arguments"))
          | s == goalSequent goal -> plain (Right (Pure (Premise d s)))
          | otherwise -> failWith (PremiseMismatch d s)
        (Nothing, Just lemma, _) -> first (TacticError Nothing goal) (useLemma hints d lemma args goal)
        (Nothing, Nothing, Just h)
          | any isJust args -> failWith (Malformed ("the hypothesis " <> d <> " takes no arguments"))
          | hypothesisFormula h == c -> plain (go noHints Assumption goal)
          | otherwise -> failWith (HypothesisMismatch d (hypothesisFormula h))
        (Nothing, Nothing, Nothing) -> failWith (UnknownPremise d)
      Apply name args -> first (TacticError Nothing goal) (applyRule env hints name args goal)
      Refl -> plain case c of
        Atm (s :=== t) ->
          go noHints (applyWith DefeqRule [term s, term t] `Then` applyWith IdRule []) goal
        _ -> failWith (NotAnEquation "refl" c)
      Symmetry sel -> do
        unless (null (hintOn hints)) $ failWith NothingToName
        equation sel >>= \case
          OfHypothesis (t :=== s) -> do
            let x = freshen (goalNames (goalSequent goal)) anyName
            -- The name given is for the symmetric equation, which Subst introduces; Defeq must not take it.
            go noHints (applyWith DefeqRule [term t, term t]) (reserve (hintAs hints) goal)
              >>= continue (go hints (applyWith SubstRule [ArgVar (Named x), term t, term s, atom (Var x :=== t)]))
          OfLemma n lemma p -> do
            let open = undetermined emptyBindings p
            unless (null open) $ failWith (Undetermined n open)
            viaLemma n lemma p Symmetry
      Rewrite eqSel hSel -> do
        unless (null (hintOn hints)) $ failWith NothingToName
        h <- select hSel
        equation eqSel >>= \case
          OfHypothesis (t :=== s) -> do
            when (h == (t :=== s)) $ failWith (RewriteWithItself h)
            unless (t `occursIn` h) $ failWith (NothingToRewrite t h)
            let x = freshen (goalNames (goalSequent goal)) anyName
            go hints (applyWith SubstRule [ArgVar (Named x), term t, term s, atom (abstract t x h)]) goal
          OfLemma n lemma p@(t :=== _) -> do
            b <- maybe (failWith (NothingToRewrite t h)) Right (firstInstance t h)
            let open = undetermined b p
            unless (null open) $ failWith (Undetermined n open)
            inst <- first (TacticError Nothing goal) (instantiateAtom n b p)
            viaLemma n lemma inst (`Rewrite` hSel)
      Cong sel -> plain do
        (u, v) <- case c of
          Atm (u :=== v) -> pure (u, v)
          _ -> failWith (NotAnEquation "cong" c)
        let x = freshen (goalNames (goalSequent goal)) anyName
            -- The equation as the hypothesis states it, or turned around first, as Symmetry does.
            oriented p@(a :=== b) =
              [(Skip, a, b, context) | Just context <- [congruence x a b u v]]
                <> [(turned p, b, a, context) | Just context <- [congruence x b a u v]]
            turned (a :=== b) =
              applyWith DefeqRule [term a, term a]
                `Then` applyWith SubstRule [ArgVar (Named x), term a, term b, atom (Var x :=== a)]
            byHypotheses candidates = case concatMap oriented candidates of
              [] -> failWith (NoCongruence (u :=== v) candidates)
              (turn, t, s, context) : _ ->
                go
                  noHints
                  ( turn
                      `Then` applyWith DefeqRule [term u, term u]
                      `Then` applyWith SubstRule [ArgVar (Named x), term t, term s, atom (u :=== context)]
                      `Then` applyWith IdRule []
                  )
                  goal
            -- The instance of a lemma's equation: the pair its sides match where the sides of the goal differ.
            matching l r (b, seen) u' v' = case matchTermL noConstraints b l u' of
              Matched b' | Matched b'' <- matchTermL noConstraints b' r v' -> Just (b'', seen <|> Just (u', v'))
              _ -> Nothing
        case sel of
          Nothing -> byHypotheses [p | Hypothesis _ (Atm p) <- goalHypotheses goal, isAtom p]
          Just chosen ->
            equation chosen >>= \case
              OfHypothesis p -> byHypotheses [p]
              OfLemma n lemma p@(t :=== s) ->
                case (congruenceWith (matching t s) (emptyBindings, Nothing) x u v, congruenceWith (matching s t) (emptyBindings, Nothing) x u v) of
                  (Just ((_, Just (a, b)), _), _) -> viaLemma n lemma (a :=== b) (Cong . Just)
                  (_, Just ((_, Just (a, b)), _)) -> viaLemma n lemma (b :=== a) (Cong . Just)
                  (Just ((_, Nothing), _), _) -> go noHints Refl goal
                  _ -> failWith (NoCongruence (u :=== v) [p])
      Induction t given -> do
        unless (null (hintOn hints)) $ failWith NothingToName
        let names = goalNames (goalSequent goal)
        n <- case given of
          Just n
            | n `HS.member` names -> failWith (NotFresh n)
            | otherwise -> pure n
          Nothing -> pure (freshen names (case t of Var y -> y; _ -> anyName))
        -- The hypotheses mentioning the term join the induction formula, by Cut,
        -- and are reintroduced in each case; modus ponens on them discharges the cut.
        let dependent = nub [h | h <- map hypothesisFormula (goalHypotheses goal), t `occursInFormula` h]
            motive = foldr (:==>) c dependent
            (ihNames, reintroNames) = splitAt 1 (hintAs hints)
            induction = As ihNames (applyWith IndRule [ArgVar (Named n), form (abstractIn t n motive), term t])
            reintroduce = foldr (\name u -> As name (applyWith ImplRRule []) `Then` u) Skip (map toList reintroNames')
            reintroNames' = take (length dependent) (map Just reintroNames <> repeat Nothing)
            discharge [] = Assumption
            discharge (h : hs) = Dispatch (applyWith ImplLRule [form h, form (foldr (:==>) c hs)]) [Assumption, discharge hs]
        when (length reintroNames > length dependent) $ failWith (NamesUnused (drop (length dependent) reintroNames))
        if null dependent
          then go noHints induction goal
          else go noHints (Dispatch (applyWith CutRule [form motive]) [induction `Then` reintroduce, discharge dependent]) goal
      Calc t0 steps -> plain do
        let ts = t0 : map fst steps
            tn = last ts
            equations = zipWith (:===) ts (drop 1 ts)
        case c of
          Atm (s :=== u) | s == t0 && u == tn -> pure ()
          _ -> failWith (CalcMismatch t0 tn)
        case zip equations (map snd steps) of
          [] -> failWith (Malformed "calc: no step")
          [(_, u)] -> go noHints u goal
          pairs -> do
            let x = freshen (goalNames (goalSequent goal) <> HS.fromList (concatMap toList ts)) anyName
                conjunction = foldr1 (:/\) (map Atm equations)
                -- Each step under the hypotheses of the goal, as a conjunct.
                proveSteps [(_, u)] = u
                proveSteps ((_, u) : rest) = Dispatch (applyWith ConjRRule []) [u, proveSteps rest]
                proveSteps [] = Skip
                -- The conjunction split into its equations, which Subst chains.
                split = foldr (\(e, rest) u -> applyWith ConjLRule [form (Atm e), form rest] `Then` u) Skip (conjuncts equations)
                conjuncts (e : rest@(_ : _)) = (e, foldr1 (:/\) (map Atm rest)) : conjuncts rest
                conjuncts _ = []
                chain = foldr (\(u :=== v) k -> applyWith SubstRule [ArgVar (Named x), term u, term v, atom (t0 :=== Var x)] `Then` k) (applyWith IdRule []) (drop 1 equations)
            go noHints (Dispatch (applyWith CutRule [form conjunction]) [proveSteps pairs, split `Then` chain]) goal
      Have given f u -> plain do
        let taken = map hypothesisName (goalHypotheses goal)
            names = case given of
              Just n -> [n]
              Nothing -> ["H" | "H" `notElem` taken]
        go noHints (Dispatch (As names (applyWith CutRule [form f])) [u, Skip]) goal
      Assumption
        | not (MS.member c ctx) -> failWith (NotInContext c)
        | otherwise -> plain case c of
            Atm _ -> go noHints (applyWith IdRule []) goal
            Bot -> go noHints (applyWith ExFalsoRule []) goal
            p :/\ q ->
              go
                noHints
                ( Dispatch
                    (applyWith ConjLRule [form p, form q] `Then` applyWith ConjRRule [])
                    [Assumption, Assumption]
                )
                goal
            p :\/ q ->
              go
                noHints
                ( Dispatch
                    (applyWith DisjLRule [form p, form q])
                    [ applyWith DisjR2Rule [] `Then` Assumption
                    , applyWith DisjR1Rule [] `Then` Assumption
                    ]
                )
                goal
            p :==> q ->
              go
                noHints
                ( applyWith ImplRRule []
                    `Then` Dispatch (applyWith ImplLRule [form p, form q]) [Assumption, Assumption]
                )
                goal
      where
        c = goalSuccedent goal
        ctx = goalContext goal

        failWith :: forall x. Failure a -> Either (TacticError a) x
        failWith = Left . TacticError Nothing goal

        -- A tactic which names nothing refuses hints.
        plain :: forall x. Either (TacticError a) x -> Either (TacticError a) x
        plain k
          | unhinted hints = k
          | otherwise = failWith NothingToName

        -- The hypothesis selected: by name, or the unique one matching an
        -- atomic pattern.  A formula or context metavariable, opaque, is
        -- never selected.
        select :: Selector a -> Either (TacticError a) (Atomic a)
        select = \case
          ByName n -> case hypothesisNamed n goal of
            Nothing -> failWith (UnknownHypothesis n)
            Just (Hypothesis _ (Atm p)) | isAtom p -> Right p
            Just (Hypothesis _ f) -> failWith (NotAtomic n f)
          ByPattern pat -> case [p | Atm p <- HS.toList (MS.toHashSet ctx), isAtom p, matchAtomic pat p] of
            [p] -> Right p
            [] -> failWith (NoMatch pat)
            ps -> failWith (AmbiguousMatch pat (map Atm ps))

        -- The equation a selector stands for: an atomic hypothesis, or a
        -- lemma stating an equation, whose instance the tactic finds where
        -- it uses it.
        equation :: Selector a -> Either (TacticError a) (Equation a)
        equation = \case
          ByName n
            | Nothing <- hypothesisNamed n goal
            , Just lemma <- Map.lookup n lemmas ->
                case lemmaEquation lemma of
                  Just p -> Right (OfLemma n lemma p)
                  Nothing -> failWith (LemmaNotEquation n (lemmaGoal lemma))
          sel -> OfHypothesis <$> select sel

        -- The instance of the equation of a lemma, cut in and proved by the
        -- lemma; the tactic then selects it by its pattern, as a hypothesis.
        viaLemma :: String -> Lemma a -> Atomic a -> (Selector a -> Tactic a) -> Either (TacticError a) (Partial a)
        viaLemma n lemma inst tactic =
          go
            noHints
            ( Dispatch
                (applyWith CutRule [form (Atm inst)])
                [Exact n (map (const Nothing) (lemmaMetas lemma)), As (hintAs hints) (tactic (ByPattern (fmap Named inst)))]
            )
            (reserve (hintAs hints) goal)

        instantiateAtom :: String -> Bindings a -> Atomic a -> Either (Failure a) (Atomic a)
        instantiateAtom n b p =
          instantiateFormula n (bFree b) b (Atm p) >>= \case
            Atm q -> Right q
            _ -> Left (Malformed ("the instance of " <> n <> " is not an atom"))

    continue k =
      fmap join . traverse \case
        Open g -> k g
        leaf -> Right (Pure leaf)

    repeatFrom :: Int -> Tactic a -> Goal a -> Either (TacticError a) (Partial a)
    repeatFrom n t goal
      | n >= repeatLimit = Left (TacticError Nothing goal RepeatLimit)
      | otherwise = case go noHints t goal of
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

-- | A discharge of a principal formula, pinned to a hypothesis or not, or the matching of the succedent.
data Obligation = MatchSuccedent !R.FormPat | Discharge !R.FormPat !(Maybe String)

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

-- | The hypotheses the names pin, in order; each must exist.
pinned :: Goal a -> [String] -> Either (Failure a) [Hypothesis a]
pinned goal = traverse \n -> maybe (Left (UnknownHypothesis n)) Right (hypothesisNamed n goal)

applyRule ::
  forall a.
  (Schematic a) =>
  KernelEnv ->
  Hints ->
  RuleName ->
  [Maybe (Arg (Hole a))] ->
  Goal a ->
  Either (Failure a) (Partial a)
applyRule env hints name userArgs goal = do
  when (length userArgs /= length params) $
    Left (Malformed (show name <> " takes " <> show (length params) <> " arguments"))
  let fs R.:+ R.CtxM g R.:|- cpat = R.ruleConclusion rule
  when (length (hintOn hints) > length fs) $
    Left (Malformed ("on: " <> R.ruleLabel rule <> " acts on " <> show (length fs) <> " hypotheses"))
  pins <- pinned goal (hintOn hints)
  (b0, cons) <- foldM (\acc (p, arg) -> seedArg (R.refName (R.paramRef p), R.paramSort p) arg acc) (emptyBindings, noConstraints) (zip params userArgs)
  let obligations = MatchSuccedent cpat : zipWith Discharge fs (map (Just . hypothesisName) pins <> repeat Nothing)
  (b1, rest) <- resolve cons b0 (goalHypotheses goal) obligations
  let dischargedNames = [hypothesisName h | h <- goalHypotheses goal, hypothesisName h `notElem` map hypothesisName rest]
      b2 = b1 {bCtxs = Map.insert g (hypothesesContext rest) (bCtxs b1)}
      unbound = [ref | ref <- Set.toList (R.metas rule) <> map R.paramRef params, not (isBound ref b2)]
  unless (null unbound) $ Left (CannotInfer name unbound)
  mapM_ (checkSide b2) (R.ruleSides rule)
  args <- traverse (argOf b2) params
  (premises, leftover) <- premiseGoals b2 dischargedNames (hintAs hints) (R.rulePremises rule)
  unless (null leftover) $ Left (NamesUnused leftover)
  maybe (Left (Malformed "mkStep")) (Right . Free . RuleStep) (mkStep name args (map (Pure . Open) premises))
  where
    rule = ruleSpec name
    params = R.ruleParams rule
    c = goalSuccedent goal

    hypothesesContext :: [Hypothesis a] -> Multiset (Formula a)
    hypothesesContext = foldr (MS.insertOne . hypothesisFormula) MS.empty

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
      Discharge pat (Just n) -> case find ((== n) . hypothesisName) hyps of
        Nothing -> Left (UnknownHypothesis n)
        Just h -> case matchForm cons b pat (hypothesisFormula h) of
          Matched b' -> Right (b', without n hyps, pending, True)
          Deferred -> Right (b, hyps, obl : pending, progressed)
          Mismatch -> Left (NotPrincipal name n pat)
      Discharge pat Nothing -> case candidates cons b hyps pat of
        (_, [(h, b')]) -> Right (b', without (hypothesisName h) hyps, pending, True)
        (False, []) -> Left (NoHypothesis name userArgs pat)
        _ -> Right (b, hyps, obl : pending, progressed)

    without n = filter ((/= n) . hypothesisName)

    -- Whether some hypothesis deferred, and those which matched, one per
    -- formula; a hypothesis pinned for another obligation is not a candidate.
    candidates cons b hyps pat =
      foldr
        ( \h (deferred, ms) -> case matchForm cons b pat (hypothesisFormula h) of
            Matched b' -> (deferred, (h, b') : ms)
            Deferred -> (True, ms)
            Mismatch -> (deferred, ms)
        )
        (False, [])
        (nubBy (\x y -> hypothesisFormula x == hypothesisFormula y) [h | h <- hyps, hypothesisName h `notElem` hintOn hints])

    stuck cons b hyps = \case
      MatchSuccedent pat -> CannotInfer name (unboundIn b pat)
      Discharge pat _ -> case candidates cons b hyps pat of
        (False, ms@(_ : _ : _)) -> AmbiguousHypothesis name userArgs pat (map (hypothesisFormula . fst) ms)
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

    -- The goals of the premises, their new hypotheses named from the names
    -- given, which the premises consume in order.
    premiseGoals b dischargedNames given = foldM one ([], given) >=> \(gs, left) -> pure (reverse gs, left)
      where
        one (acc, names) (fs R.:+ R.CtxM g R.:|- s) = do
          stated <- traverse (instFormE b) fs
          unless (Map.member g (bCtxs b)) $ Left (CannotInfer name [R.MetaRef R.CtxS g])
          s' <- instFormE b s
          (hs, names', counter) <- nameHypotheses goal dischargedNames stated names
          pure (Goal hs s' counter : acc, names')

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
useLemma :: forall a. (Schematic a) => Hints -> String -> Lemma a -> [Maybe (Arg (Hole a))] -> Goal a -> Either (Failure a) (Partial a)
useLemma hints name lemma userArgs goal = do
  when (length userArgs /= length metas) $
    Left (Malformed (name <> " takes " <> show (length metas) <> " arguments"))
  unless (null metas && null premises || HS.null free) $
    Left (NotClosed name (HS.toList free))
  let (ctxMetas, hyps) = partitionEithers [maybe (Right f) Left (contextMeta f) | f <- toList lemmaCtx]
  when (length (hintOn hints) > length hyps) $
    Left (Malformed ("on: " <> name <> " has " <> show (length hyps) <> " hypotheses"))
  pins <- pinned goal (hintOn hints)
  (b0, cons) <- foldM (\acc (m, arg) -> seedArg m arg acc) (emptyBindings, noConstraints) (zip metas userArgs)
  b1 <- case matchFormL cons b0 lemmaSucc (goalSuccedent goal) of
    Matched b -> Right b
    _ -> Left (NotAnInstance name (lemmaGoal lemma))
  (b2, rest) <- discharge cons b1 (goalHypotheses goal) (zip hyps (map (Just . hypothesisName) pins <> repeat Nothing))
  let dischargedNames = [hypothesisName h | h <- goalHypotheses goal, hypothesisName h `notElem` map hypothesisName rest]
      restCtx = foldr (MS.insertOne . hypothesisFormula) MS.empty rest
  -- The first context metavariable takes what is left; without one, it is weakened in.
  let (b3, weakening) = case ctxMetas of
        [] -> (b2, restCtx)
        n : ns -> (b2 {bCtxs = Map.insert n restCtx (foldr (\m -> Map.insert m MS.empty) (bCtxs b2) ns)}, MS.empty)
  unless (MS.population weakening == 0 || null premises) $ Left (CannotWeaken name weakening)
  let unbound = [ref | (n, s) <- metas, let ref = R.MetaRef s n, not (isBound ref b3)]
  unless (null unbound) $ Left (CannotInstantiate name unbound)
  args <- traverse (argOfSort b3) metas
  forM_ (lemmaBound lemma) \x -> case Map.lookup x (bVars b3) of
    Just v
      | v `HS.member` goalNames (goalSequent goal) || or [v `HS.member` argNames arg | ((n, _), arg) <- zip metas args, n /= x] ->
          Left (NotEigen name x v)
    _ -> pure ()
  let sigma = [(v, HM.lookupDefault (Var v) v (bFree b3)) | v <- HS.toList free]
      appeal = Appeal name args sigma weakening
  (premiseSequents, conclusion) <- instantiateLemma lemma appeal
  when (conclusion /= goalSequent goal) $ Left (Malformed ("the instance of " <> name <> " is not the goal"))
  -- The premises, named: the goal's hypotheses stay, and each premise's own are new.
  (goals, leftover) <- premiseGoals appeal dischargedNames (hintAs hints) premiseSequents
  unless (null leftover) $ Left (NamesUnused leftover)
  pure (Free (LemmaStep appeal (map (Pure . Open) goals)))
  where
    metas = lemmaMetas lemma
    premises = lemmaPremises lemma
    lemmaCtx :|- lemmaSucc = lemmaGoal lemma
    free = freeVariables lemma

    -- Each hypothesis of the lemma instantiates to a distinct hypothesis of
    -- the goal, the pinned one when it is pinned; the ones decided are
    -- committed pass by pass, as in 'applyRule'.
    discharge _ b hyps [] = Right (b, hyps)
    discharge cons b hyps pending = do
      (b', hyps', pending', progressed) <- foldM (step cons) (b, hyps, [], False) pending
      case reverse pending' of
        [] -> Right (b', hyps')
        again@((f, _) : _)
          | progressed -> discharge cons b' hyps' again
          | otherwise -> Left (AmbiguousInstance name f (map (hypothesisFormula . fst) (instances cons b' hyps' f)))

    step cons (b, hyps, pending, progressed) (f, pin) = case pin of
      Just n -> case find ((== n) . hypothesisName) hyps of
        Nothing -> Left (UnknownHypothesis n)
        Just h -> case matchFormL cons b f (hypothesisFormula h) of
          Matched b' -> Right (b', filter ((/= n) . hypothesisName) hyps, pending, True)
          _ -> Left (NotAnInstance name (lemmaGoal lemma))
      Nothing -> case instances cons b hyps f of
        [(h, b')] -> Right (b', filter ((/= hypothesisName h) . hypothesisName) hyps, pending, True)
        [] -> Left (NotAnInstance name (lemmaGoal lemma))
        _ -> Right (b, hyps, (f, pin) : pending, progressed)

    instances cons b hyps f =
      [ (h, b')
      | h <- nubBy (\x y -> hypothesisFormula x == hypothesisFormula y) [h | h <- hyps, hypothesisName h `notElem` hintOn hints]
      , Matched b' <- [matchFormL cons b f (hypothesisFormula h)]
      ]

    -- The instantiated premises, as goals: the hypotheses of the goal stay,
    -- and those the statement's premise lists besides the context
    -- metavariable are new, in order.
    premiseGoals appeal dischargedNames given sequents = do
      b <- appealBindings lemma appeal
      let sigma = HM.fromList (appealSubst appeal)
          one (acc, names) (stated :|- _, hyps' :|- s) = do
            explicit <- traverse (instantiateFormula name sigma b) [f | f <- toList stated, isNothing (contextMeta f)]
            (hs, names', counter) <- nameHypotheses goal dischargedNames explicit names
            let g = Goal hs s counter
            when (goalSequent g /= (hyps' :|- s)) $ Left (Malformed ("the premise of " <> name <> " is not what it was instantiated to"))
            pure (g : acc, names')
      (gs, left) <- foldM one ([], given) (zip (map snd premises) sequents)
      pure (reverse gs, left)

    argOfSort b (n, s) = case s of
      R.VarS -> ArgVar <$> look s n (bVars b)
      R.TermS -> ArgTerm <$> look s n (bTerms b)
      R.AtomS -> ArgAtom <$> look s n (bAtoms b)
      R.FormS -> ArgForm <$> look s n (bForms b)
      R.CtxS -> ArgCtx <$> look s n (bCtxs b)

    look :: forall v. R.Sort -> String -> Map String v -> Either (Failure a) v
    look s n = maybe (Left (CannotInstantiate name [R.MetaRef s n])) Right . Map.lookup n

-- | What a hypothesis selector stands for: a hypothesis, or a lemma stating an equation.
data Equation a = OfHypothesis !(Atomic a) | OfLemma !String !(Lemma a) !(Atomic a)

-- | The equation a lemma states: no premises, and no hypotheses but a context metavariable.
lemmaEquation :: (Schematic a) => Lemma a -> Maybe (Atomic a)
lemmaEquation lemma = case lemmaGoal lemma of
  ctx :|- Atm p
    | null (lemmaPremises lemma)
    , isNothing (metaAtom p)
    , all (isJust . contextMeta) (toList ctx) ->
        Just p
  _ -> Nothing

-- | The variables and metavariables of an equation the bindings leave open.
undetermined :: (Schematic a) => Bindings a -> Atomic a -> [a]
undetermined b (t :=== s) = nub [v | v <- toList t <> toList s, open v]
  where
    open v = case metaName v of
      Just (sort, n) -> not (isBound (R.MetaRef sort n) b)
      Nothing -> not (HM.member v (bFree b))

-- | The bindings under which the pattern matches the first subterm of the atom it matches at all, in order.
firstInstance :: (Schematic a) => Term a -> Atomic a -> Maybe (Bindings a)
firstInstance pat (s :=== u) = listToMaybe (mapMaybe attempt (subterms s <> subterms u))
  where
    attempt t = case matchTermL noConstraints emptyBindings pat t of
      Matched b -> Just b
      _ -> Nothing
    subterms t =
      t : case t of
        App _ args -> concatMap subterms (toList args)
        _ -> []

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
  -- The proofs of the premises cannot be weakened after the fact.
  unless (null (lemmaPremises lemma) || MS.population extra == 0) $ Left (CannotWeaken name extra)
  b <- appealBindings lemma appeal
  premises <- traverse (instantiateSequent name sigma extra b . snd) (lemmaPremises lemma)
  conclusion <- instantiateSequent name sigma extra b (lemmaGoal lemma)
  pure (premises, conclusion)
  where
    name = appealName appeal
    sigma = HM.fromList (appealSubst appeal)
    extra = appealWeakening appeal

-- | The bindings the arguments of an appeal make for the metavariables of the lemma.
appealBindings :: Lemma a -> Appeal a -> Either (Failure a) (Bindings a)
appealBindings lemma appeal = do
  when (length args /= length metas) $
    Left (Malformed (name <> " takes " <> show (length metas) <> " arguments"))
  foldM bind emptyBindings (zip metas args)
  where
    name = appealName appeal
    args = appealArgs appeal
    metas = lemmaMetas lemma
    bind b ((n, s), arg) = case (s, arg) of
      (R.VarS, ArgVar v) -> Right b {bVars = Map.insert n v (bVars b)}
      (R.TermS, ArgTerm t) -> Right b {bTerms = Map.insert n t (bTerms b)}
      (R.AtomS, ArgAtom p) -> Right b {bAtoms = Map.insert n p (bAtoms b)}
      (R.FormS, ArgForm f) -> Right b {bForms = Map.insert n f (bForms b)}
      (R.CtxS, ArgCtx g) -> Right b {bCtxs = Map.insert n g (bCtxs b)}
      _ -> Left (Malformed ("ill-sorted argument for " <> n <> " of " <> name))

-- | A sequent of the lemma's statement at the bindings, the free variables substituted and the weakening added.
instantiateSequent :: (Schematic a) => String -> HashMap a (Term a) -> Multiset (Formula a) -> Bindings a -> Sequent a -> Either (Failure a) (Sequent a)
instantiateSequent name sigma extra b (hyps :|- s) = do
  hyps' <- foldM (\acc f -> (<> acc) <$> hypothesis f) extra (toList hyps)
  s' <- instantiateFormula name sigma b s
  pure (hyps' :|- s')
  where
    hypothesis f = case f of
      Atm p | Just (R.CtxS, n) <- metaAtom p -> maybe (Left (CannotInstantiate name [R.MetaRef R.CtxS n])) Right (Map.lookup n (bCtxs b))
      _ -> (`MS.insertOne` MS.empty) <$> instantiateFormula name sigma b f

-- | A formula of the lemma's statement at the bindings, the free variables substituted.
instantiateFormula :: forall a. (Schematic a) => String -> HashMap a (Term a) -> Bindings a -> Formula a -> Either (Failure a) (Formula a)
instantiateFormula name sigma b = instF
  where
    instF = \case
      Atm p -> case metaAtom p of
        Just (R.FormS, n) -> look R.FormS n (bForms b)
        Just (R.CtxS, n) -> Left (Malformed (n <> " is a ctx metavariable, but stands as a formula in " <> name))
        _ -> Atm <$> instA p
      f :/\ g -> (:/\) <$> instF f <*> instF g
      f :\/ g -> (:\/) <$> instF f <*> instF g
      f :==> g -> (:==>) <$> instF f <*> instF g
      Bot -> pure Bot

    instA p@(s :=== t) = case metaAtom p of
      Just (R.AtomS, n) -> look R.AtomS n (bAtoms b)
      Just (_, n) -> Left (Malformed (n <> " is not an atom metavariable, but stands as an atom in " <> name))
      Nothing -> (:===) <$> instT s <*> instT t

    instT = \case
      Var v -> case metaName v of
        Just (R.TermS, n) -> look R.TermS n (bTerms b)
        Just (R.VarS, n) -> Var <$> look R.VarS n (bVars b)
        Just (_, n) -> Left (Malformed (n <> " is not a term metavariable, but stands as a term in " <> name))
        Nothing -> pure (HM.lookupDefault (Var v) v sigma)
      Lit n -> pure (Lit n)
      App f xs -> App f <$> traverse instT xs

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

{- |
@congruence x t s u v@ finds the context @C@ with @C[x := t] == u@ and
@C[x := s] == v@, when @v@ is @u@ with some occurrences of @t@ replaced by
@s@: the sides are compared in step, and an occurrence of @t@ against one of
@s@ becomes @x@.
-}
congruence :: forall a. (Eq a) => a -> Term a -> Term a -> Term a -> Term a -> Maybe (Term a)
congruence x t s u v = snd <$> congruenceWith hole () x u v
  where
    hole () u' v'
      | u' == t && v' == s = Just ()
      | otherwise = Nothing

{- |
'congruence' with a hole test of its own, threading a state through the
holes: a pair of subterms the test accepts becomes @x@, with the state it
returns.
-}
congruenceWith :: forall a b. (Eq a) => (b -> Term a -> Term a -> Maybe b) -> b -> a -> Term a -> Term a -> Maybe (b, Term a)
congruenceWith hole b0 x = go b0
  where
    go :: b -> Term a -> Term a -> Maybe (b, Term a)
    go b u v
      | Just b' <- hole b u v = Just (b', Var x)
      | u == v = Just (b, u)
      | otherwise = case (canonicalise u, canonicalise v) of
          (App (f :: Function n) us, App (g :: Function m) vs)
            | Just TE.Refl <- TE.testEquality (sNat @n) (sNat @m)
            , f == g -> do
                (b', ws) <- goArgs b (toList us) (toList vs)
                args <- SV.fromList' ws
                pure (b', App f args)
          (u', v')
            | Just u'' <- u' ^? _Succ
            , Just v'' <- v' ^? _Succ ->
                fmap suc <$> go b u'' v''
          _ -> Nothing

    goArgs :: b -> [Term a] -> [Term a] -> Maybe (b, [Term a])
    goArgs b [] [] = Just (b, [])
    goArgs b (u : us) (v : vs) = do
      (b', w) <- go b u v
      (b'', ws) <- goArgs b' us vs
      pure (b'', w : ws)
    goArgs _ _ _ = Nothing

-- * Rendering

-- | Render an error for a human, naming symbols through the signature.
renderTacticError :: forall a. (Schematic a) => Signature -> (a -> String) -> TacticError a -> String
renderTacticError sig name = renderTacticErrorWith sig name (const Nothing)

-- | Render an error, showing an atom the hook names, such as a metavariable, as that name.
renderTacticErrorWith :: forall a. (Schematic a) => Signature -> (a -> String) -> (Atomic a -> Maybe String) -> TacticError a -> String
renderTacticErrorWith sig name hook = intercalate "\n" . render
  where
    render (TacticError loc goal failure) =
      (maybe "" (\(Loc l col) -> show l <> ":" <> show col <> ": ") loc <> headline failure)
        : map ("  " <>) (details failure <> state failure goal)

    -- A proof abandoned by sorry shows its state: the hypotheses by name, then the succedent.
    state :: Failure a -> Goal a -> [String]
    state Unfinished goal = map hypothesis (goalHypotheses goal) <> ["|- " <> rf (goalSuccedent goal)]
    state _ goal = ["goal: " <> rg goal]

    -- A context metavariable is its name; anything else is named.
    hypothesis (Hypothesis n f)
      | isJust (contextMeta f) = n
      | otherwise = n <> " : " <> rf f

    rg goal = concatMap ((<> " ") . (<> ",")) (init' (map hypothesis (goalHypotheses goal))) <> lastHypothesis goal <> "|- " <> rf (goalSuccedent goal)
    init' xs = if null xs then [] else init xs
    lastHypothesis goal = case goalHypotheses goal of
      [] -> ""
      hs -> hypothesis (last hs) <> " "

    headline :: Failure a -> String
    headline = \case
      WrongSuccedent r _ ->
        label r <> "the succedent does not have the form " <> succedentOf r
      NoHypothesis r _ pat -> label r <> "no hypothesis of the form " <> R.renderFormPat pat
      AmbiguousHypothesis r _ pat _ ->
        label r <> "more than one hypothesis of the form " <> R.renderFormPat pat
      NotPrincipal r n pat -> label r <> n <> " does not have the form " <> R.renderFormPat pat
      CannotInfer r refs ->
        label r <> "cannot infer " <> intercalate ", " (map R.refName refs) <> "; supply it"
      SideCondition r reason -> label r <> side reason
      NotAnEquation t f -> t <> ": the goal " <> rf f <> " is not an equation"
      NoMatch pat -> "no hypothesis matches " <> rap pat
      AmbiguousMatch pat _ -> "more than one hypothesis matches " <> rap pat
      UnknownHypothesis n -> "no hypothesis named " <> n
      NotAtomic n f -> n <> " is " <> rf f <> ", not an atomic hypothesis"
      NothingToRewrite t h -> "rewrite: " <> rt t <> " does not occur in " <> ra h
      RewriteWithItself h -> "rewrite: cannot rewrite " <> ra h <> " with itself"
      NoCongruence (u :=== v) [p] -> "cong: " <> ra p <> " does not rewrite " <> rt u <> " into " <> rt v
      NoCongruence (u :=== v) _ -> "cong: no hypothesis rewrites " <> rt u <> " into " <> rt v
      LemmaNotEquation n s -> n <> " does not state an equation, so it cannot stand for a hypothesis; it proves " <> rs s
      Undetermined n vs -> "cannot instantiate " <> intercalate ", " (map name vs) <> " of " <> n <> " from where it is used; state the instance with have"
      NotFresh x -> "induction: " <> name x <> " occurs in the goal"
      NotInContext f -> "assumption: " <> rf f <> " is not in the context"
      UnknownPremise d -> "exact: no premise, lemma or hypothesis named " <> d
      PremiseMismatch d s -> "exact: the premise " <> d <> " establishes " <> rs s
      HypothesisMismatch d f -> "exact: " <> d <> " is " <> rf f <> ", not the succedent"
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
      NamesUnused ns -> "as: no hypothesis introduced to name " <> intercalate ", " ns
      NameInUse n -> "as: a hypothesis is already named " <> n
      NothingToName -> "on/as: the tactic acts on no hypothesis"
      CalcMismatch s t -> "calc: the chain proves " <> rt s <> " = " <> rt t <> ", which is not the goal"
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
      NoCongruence _ ps@(_ : _ : _) -> ["candidates: " <> intercalate "; " (map ra ps)]
      Alternatives es -> concatMap (map ("| " <>) . render) es
      Unsolved gs -> map (("- " <>) . rg) gs
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
