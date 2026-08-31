{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeAbstractions #-}
{-# OPTIONS_GHC -foptimal-applicative-do #-}

module Language.Praxis.PRA.Proof (
  Proof (..),
  inferConclusion,
  ProofError (..),
  ProofErrorReason (..),
  ProofContext (..),
  isProofOf,
) where

import Control.Exception (Exception)
import Control.Monad.Trans.Reader (Reader, ReaderT (..), local, reader, runReader)
import Data.Coerce (coerce)
import Data.DList.DNonEmpty (DNonEmpty)
import Data.DList.DNonEmpty qualified as DLNE
import Data.Functor.Compose
import Data.Functor.Foldable (cata)
import Data.Functor.Identity (Identity)
import Data.Generics.Labels ()
import Data.Hashable (Hashable (..))
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Multiset (Multiset)
import Data.Multiset qualified as MS
import GHC.Generics
import Language.Praxis.PRA.Equality
import Language.Praxis.PRA.Syntax

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
  | FormulaEigenVariableViolation
      -- | eigen variable
      !a
      -- | formula
      !(Formula a)
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

withRule :: RuleName -> InferenceMachine a x -> InferenceMachine a x
withRule = addContext . CheckingRule

asSubproof :: Word -> InferenceMachine a x -> InferenceMachine a x
asSubproof = addContext . Subproof

runInferenceMachine :: InferenceMachine a x -> Either (NonEmpty (ProofError a)) x
runInferenceMachine = runTry . flip runReader [] . unIM

reportError :: ProofErrorReason a -> InferenceMachine a x
reportError reason = IM $ reader \ctx ->
  let err = ProofError (NE.fromList ctx) reason
   in Failure (DLNE.singleton err)

failIf :: ProofErrorReason a -> Bool -> InferenceMachine a ()
failIf _ False = pure ()
failIf reason True = reportError reason

fromMaybeM :: ProofErrorReason a -> Maybe x -> InferenceMachine a x
fromMaybeM _ (Just x) = pure x
fromMaybeM reason Nothing = reportError reason

discharge ::
  (Hashable a) =>
  ProofErrorReason a ->
  Formula a ->
  Multiset (Formula a) ->
  InferenceMachine a (Multiset (Formula a))
discharge reason f g = fromMaybeM reason $ MS.removeOne f g

inferConclusion ::
  forall a.
  (Hashable a) =>
  Proof a -> Either (NonEmpty (ProofError a)) (Sequent a)
inferConclusion = runInferenceMachine . cata infer
  where
    infer prf = withRule (ruleName prf) $ infer0 prf

    infer0 (IdF a g) = pure $ MS.insertOne (Atm a) g |- Atm a
    infer0 (ExFalsoF g c) = pure $ MS.insertOne Bot g |- c
    infer0 (ConjLF a b prf) = do
      γ :|- c <- asSubproof 0 prf
      γ' <- discharge (MissingAssumption a γ) a γ
      γ'' <- discharge (MissingAssumption b γ') b γ'
      pure $ MS.insertOne (a /\ b) γ'' |- c
    infer0 (ConjRF prf1 prf2) = do
      γ1 :|- a <- asSubproof 0 prf1
      γ2 :|- b <- asSubproof 1 prf2
      failIf (AssumptionMismatch γ1 γ2) $ γ1 /= γ2
      pure $ γ1 |- a /\ b
    infer0 (DisjLF a b prf1 prf2) = do
      γ1 :|- c1 <- asSubproof 0 prf1
      γ1' <- discharge (MissingAssumption a γ1) a γ1
      γ2 :|- c2 <- asSubproof 1 prf2
      γ2' <- discharge (MissingAssumption b γ2) b γ2
      failIf (ConsequentMismatch c1 c2) $ c1 /= c2
      failIf (AssumptionMismatch γ1' γ2') $ γ1' /= γ2'
      pure $ MS.insertOne (a \/ b) γ1' |- c1
    infer0 (DisjR1F a prf) = do
      γ :|- b <- asSubproof 0 prf
      pure $ γ |- a \/ b
    infer0 (DisjR2F a prf) = do
      γ :|- b <- asSubproof 0 prf
      pure $ γ |- b \/ a
    infer0 (ImplLF a b prf1 prf2) = do
      γ1 <- asSubproof 0 do
        γ1 :|- a' <- prf1
        failIf (ConsequentMismatch a a') $ a /= a'
        γ1' <- discharge (MissingAssumption (a ==> b) γ1) (a ==> b) γ1
        pure γ1'
      (c, γ2) <- asSubproof 1 do
        γ2 :|- c <- prf2
        γ2' <- discharge (MissingAssumption b γ2) b γ2
        pure (c, γ2')
      failIf (AssumptionMismatch γ1 γ2) $ γ1 /= γ2
      pure $ MS.insertOne (a ==> b) γ1 |- c
    infer0 (ImplRF a prf) = do
      γ :|- b <- asSubproof 0 prf
      γ' <- discharge (MissingAssumption a γ) a γ
      pure $ γ' |- a ==> b
    infer0 (SubstF x t s p prf) = do
      let p' = Atm p
          pt = subst x t p'
          ps = subst x s p'
      γ :|- c <- asSubproof 0 prf
      -- NOTE: in case of pt and ps coincides, we need to remove all the matching
      -- premises once, then push back appropriate ones.
      γ' <- discharge (MissingAssumption (t === s) γ) (t === s) γ
      γ'' <- discharge (MissingAssumption pt γ') pt γ'
      γ''' <- discharge (MissingAssumption ps γ'') ps γ''
      pure $ MS.insertOne (t === s) (MS.insertOne pt γ''') |- c
    infer0 (DefeqF s t prf) = do
      γ :|- c <- asSubproof 0 prf
      γ' <- discharge (MissingAssumption (s === t) γ) (s === t) γ
      failIf (EqualityCheckFailed s t) $ not $ defEq s t
      pure $ γ' |- c
    infer0 (SuccNonZeroF t γ a) = do
      pure $ MS.insertOne (suc t === lit 0) γ |- a
    infer0 (SuccInjF t1 t2 prf) = do
      γ :|- c <- asSubproof 0 prf
      γ' <- discharge (MissingAssumption (suc t1 === suc t2) γ) (suc t1 === suc t2) γ
      γ'' <- discharge (MissingAssumption (t1 === t2) γ') (t1 === t2) γ'
      pure $ MS.insertOne (suc t1 === suc t2) γ'' |- c
    infer0 (IndF z a t base step) = do
      failIf (TermEigenVariableViolation z t) $ z `elem` t
      failIf (FormulaEigenVariableViolation z a) $ z `elem` a
      let a0 = subst z (lit 0) a
          aS = subst z (suc (var z)) a
      γ :|- c1 <- asSubproof 0 base
      failIf (ConsequentMismatch a0 c1) $ a0 /= c1
      γ2 :|- c2 <- asSubproof 1 step
      failIf (ConsequentMismatch aS c2) $ aS /= c2
      let stepAssumps = MS.insertOne a γ
      failIf (AssumptionMismatch γ2 stepAssumps) $ γ2 /= stepAssumps
      pure $ γ |- subst z t a

-- TODO: more efficient and direct implementation.
isProofOf :: (Hashable a) => Proof a -> Sequent a -> Bool
isProofOf prf p = inferConclusion prf == Right p
