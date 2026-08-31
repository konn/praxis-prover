{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeAbstractions #-}

{- |
The inference machinery the compiled checker runs in, and the vocabulary of
primitive checks it is built from.

Every failure the checker can report is raised by exactly one combinator in
this module, so the mapping from a 'Language.Praxis.PRA.Rule.Rule' to the
errors it can produce is fixed here rather than per rule.
-}
module Language.Praxis.PRA.Proof.Internal (
  -- * Rule names
  RuleName (..),
  HasRuleName (..),

  -- * Errors
  ProofErrorReason (..),
  ProofContext (..),
  ProofError (..),

  -- * The inference machine
  InferenceMachine,
  runInferenceMachine,
  withRule,
  asSubproof,

  -- * Primitive checks
  dischargeIn,
  checkConsequent,
  checkAssumptions,
  checkDefEq,
  checkNotFreeInTerm,
  checkNotFreeInCtx,
) where

import Control.Exception (Exception)
import Control.Monad.Trans.Reader (Reader, ReaderT (..), local, reader, runReader)
import Data.Coerce (coerce)
import Data.DList.DNonEmpty (DNonEmpty)
import Data.DList.DNonEmpty qualified as DLNE
import Data.Functor.Compose (Compose (..))
import Data.Functor.Identity (Identity)
import Data.Hashable (Hashable)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Multiset (Multiset)
import Data.Multiset qualified as MS
import GHC.Generics (Generic)
import Language.Praxis.PRA.Equality (defEq)
import Language.Praxis.PRA.Rule.G3i (allRules)
import Language.Praxis.PRA.Rule.TH.Name (deriveRuleName)
import Language.Praxis.PRA.Syntax

$(deriveRuleName allRules)

-- | Recover the rule a proof step appeals to.
class HasRuleName a where
  ruleName :: a -> RuleName

data ProofErrorReason a
  = MissingAssumption
      -- | expected
      !(Formula a)
      -- | actual
      !(Multiset (Formula a))
  | AssumptionMismatch
      -- | left
      !(Multiset (Formula a))
      -- | right
      !(Multiset (Formula a))
  | ConsequentMismatch
      -- | expected
      !(Formula a)
      -- | actual
      !(Formula a)
  | EqualityCheckFailed
      -- | left
      !(Term a)
      -- | right
      !(Term a)
  | TermEigenVariableViolation
      -- | eigen variable
      !a
      -- | term
      !(Term a)
  | AssumptionEigenVariableViolation
      -- | eigen variable
      !a
      -- | assumptions
      !(Multiset (Formula a))
  deriving (Show, Eq, Generic)

data ProofContext
  = CheckingRule !RuleName
  | Subproof !Word
  deriving (Show, Eq, Generic)

data ProofError a = ProofError
  { context :: !(NonEmpty ProofContext)
  , reason :: !(ProofErrorReason a)
  }
  deriving (Show, Eq, Generic)
  deriving anyclass (Exception)

{- |
'Try' is a monad transformer which behaves like 'ExceptT', but accumulates
exceptions in 'Applicative' operations like 'Validation'.
Note that this is invalid 'Monad' if we assume the _strong_ equality on errors - that is, we consider two 'Failures' if and only if they have the same value.
Hence, we assume the _weak_ equality on errors: we consider two 'Failures'
@es@ and @es'@ equal if they have a nonempty _intersection_.
-}
data Try e a = Success a | Failure (DNonEmpty e)
  deriving (Show, Eq, Ord, Generic, Functor)

runTry :: Try e a -> Either (NonEmpty e) a
runTry (Success x) = Right x
runTry (Failure es) = Left $ DLNE.toNonEmpty es

instance Applicative (Try e) where
  pure = Success
  Success f <*> Success x = Success (f x)
  Failure es <*> Success _ = Failure es
  Success _ <*> Failure es = Failure es
  Failure es1 <*> Failure es2 = Failure (es1 <> es2)

instance Monad (Try e) where
  Success x >>= f = f x
  Failure es >>= _ = Failure es

newtype InferenceMachine a x = IM {unIM :: Reader [ProofContext] (Try (ProofError a) x)}
  deriving (Functor)
  deriving (Applicative) via Compose (Reader [ProofContext]) (Try (ProofError a))

instance Monad (InferenceMachine a) where
  m >>= f = IM $ reader \ctx ->
    case runReader (unIM m) ctx of
      Success x -> runReader (unIM (f x)) ctx
      Failure es -> Failure es

addContext :: ProofContext -> InferenceMachine a x -> InferenceMachine a x
addContext @a @x ctx = coerce $ local @_ @Identity @(Try (ProofError a) x) (ctx :)

-- | Report everything raised inside as having been raised while checking this rule.
withRule :: RuleName -> InferenceMachine a x -> InferenceMachine a x
withRule = addContext . CheckingRule

-- | Report everything raised inside as belonging to the given premise.
asSubproof :: Word -> InferenceMachine a x -> InferenceMachine a x
asSubproof = addContext . Subproof

runInferenceMachine :: InferenceMachine a x -> Either (NonEmpty (ProofError a)) x
runInferenceMachine = runTry . flip runReader [] . unIM

reportError :: ProofErrorReason a -> InferenceMachine a x
reportError r = IM $ reader \ctx ->
  let err = ProofError (NE.fromList ctx) r
   in Failure (DLNE.singleton err)

failIf :: ProofErrorReason a -> Bool -> InferenceMachine a ()
failIf _ False = pure ()
failIf r True = reportError r

-- * Primitive checks

--

{- $checks
The compiled checker is a chain of calls to these and nothing else.
-}

{- |
Remove one occurrence of the formula from the context, or report that it was
not there to remove.
-}
dischargeIn ::
  (Hashable a) =>
  Formula a ->
  Multiset (Formula a) ->
  InferenceMachine a (Multiset (Formula a))
dischargeIn f g = case MS.removeOne f g of
  Just g' -> pure g'
  Nothing -> reportError (MissingAssumption f g)

-- | The succedent a premise concluded must be the one the rule determined.
checkConsequent :: (Hashable a) => Formula a -> Formula a -> InferenceMachine a ()
checkConsequent expected actual =
  failIf (ConsequentMismatch expected actual) (expected /= actual)

-- | Two premises which share a context tail must leave the same one behind.
checkAssumptions ::
  (Hashable a) =>
  Multiset (Formula a) ->
  Multiset (Formula a) ->
  InferenceMachine a ()
checkAssumptions expected actual =
  failIf (AssumptionMismatch expected actual) (expected /= actual)

-- | The trusted evaluator must identify the two terms.
checkDefEq :: (Hashable a) => Term a -> Term a -> InferenceMachine a ()
checkDefEq s t = failIf (EqualityCheckFailed s t) (not (defEq s t))

-- | The eigenvariable must not occur in the term.
checkNotFreeInTerm :: (Hashable a) => a -> Term a -> InferenceMachine a ()
checkNotFreeInTerm z t = failIf (TermEigenVariableViolation z t) (z `elem` t)

-- | The eigenvariable must not occur anywhere in the context.
checkNotFreeInCtx :: (Hashable a) => a -> Multiset (Formula a) -> InferenceMachine a ()
checkNotFreeInCtx z g =
  failIf (AssumptionEigenVariableViolation z g) (z `elem` Compose g)
