-- | Shared slot and term operations for elaboration.
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Internal (
  slotIndices,
  replaceSlot,
  successorTerm,
  substituteSlot,
  patternTerm,
  sameTerm,
  functionCalls,
) where

import Data.Foldable (toList)
import Data.Set qualified as Set
import Data.Sized qualified as SV
import Data.Text qualified as T
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Type.Natural (sNat)
import Data.Type.Ordinal (Ordinal)
import GHC.TypeNats (KnownNat)
import Language.Praxis.PRA.PrimitiveRecursion.Code (V)
import Language.Praxis.PRA.PrimitiveRecursion.Code qualified as PR
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax

-- | Unlike enumOrdinal, this also handles an empty context.
slotIndices :: forall n. (KnownNat n) => V n (Ordinal n)
slotIndices = SV.generate (sNat @n) id

replaceSlot :: (KnownNat n) => Ordinal n -> a -> V n a -> V n a
replaceSlot index value xs = fmap (\i -> if i == index then value else SV.sIndex i xs) slotIndices

successorTerm :: FunctionalTerm n -> FunctionalTerm n
successorTerm (LitFT n) = LitFT (n + 1)
successorTerm t = AppFT (Primitive PR.Succ) (t SV.:< SV.Nil)

-- Substitution is simultaneous: do not traverse a replacement a second time.
substituteSlot :: Ordinal n -> FunctionalTerm n -> FunctionalTerm n -> FunctionalTerm n
substituteSlot index replacement = go
  where
    go (VarFT i) | i == index = replacement
    go (AppFT f xs) = AppFT f (fmap go xs)
    go t = t

-- | Reconstruct an original argument from the variable bound at its slot.
patternTerm :: Ordinal n -> Pattern IrrelevantName -> FunctionalTerm n
patternTerm i (VarP _) = VarFT i
patternTerm _ ZeroP = LitFT 0
patternTerm i (SuccP p) = successorTerm (patternTerm i p)

-- S(0) and the literal 1 must compare alike when checking unchanged arguments.
-- No arbitrary evaluation or definitional-equality search is performed.
sameTerm :: FunctionalTerm n -> FunctionalTerm n -> Bool
sameTerm a b = case (canonical a, canonical b) of
  (LitFT x, LitFT y) -> x == y
  (VarFT x, VarFT y) -> x == y
  (AppFT (f :: Function k) xs, AppFT (g :: Function l) ys) ->
    case testEquality (sNat @k) (sNat @l) of
      Just Refl -> sameFunction f g && and (zipWith sameTerm (toList xs) (toList ys))
      Nothing -> False
  _ -> False
  where
    sameFunction (Defined x) (Defined y) = x == y
    sameFunction (Primitive x) (Primitive y) = x == y
    sameFunction (Bound x) (Bound y) = x == y
    sameFunction (SchemaApp s1 ps1) (SchemaApp s2 ps2) = s1 == s2 && ps1 == ps2
    sameFunction _ _ = False
    canonical (AppFT (Primitive PR.Succ) xs) = successorTerm (canonical (SV.head xs))
    canonical t = t

functionCalls :: FunctionalTerm n -> Set.Set T.Text
functionCalls (AppFT f xs) = headCall f <> foldMap functionCalls xs
  where
    headCall (Defined ident) = Set.singleton ident
    headCall (Primitive _) = Set.empty
    headCall (Bound _) = Set.empty
    headCall (SchemaApp sName pArgs) = Set.fromList (sName : pArgs)
functionCalls _ = Set.empty
