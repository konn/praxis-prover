{-# LANGUAGE OverloadedStrings #-}

-- | Clause specialization, coverage checking, and disjoint case trees.
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration.CaseTree (
  EquationRow (..),
  CaseTree (..),
  specializeRows,
  buildCaseTree,
) where

import Data.Foldable (toList)
import Data.List (find)
import Data.Maybe (mapMaybe)
import Data.Sized qualified as SV
import Data.Type.Ordinal (Ordinal)
import GHC.TypeNats (KnownNat)
import Language.Praxis.PRA.PrimitiveRecursion.Code (V)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Error
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Internal
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax

-- | A fixed-width clause matrix row. The identifier refers to its source equation.
data EquationRow n = EquationRow
  { rowId :: !Int
  , rowPatterns :: !(V n (Pattern IrrelevantName))
  , rowBody :: !(FunctionalTerm n)
  }

deriving instance (KnownNat n) => Show (EquationRow n)

{- | An exhaustive, disjoint case tree. In a successor branch the selected
slot denotes the predecessor. Leaf bodies have already been substituted.
-}
data CaseTree n
  = Leaf !Int !(FunctionalTerm n)
  | Split !(Ordinal n) !(CaseTree n) !(CaseTree n)

deriving instance (KnownNat n) => Show (CaseTree n)

-- False selects zero; True selects successor. A wildcard binds the whole
-- scrutinee, whereas a successor pattern already binds its predecessor.
specializeRows :: (KnownNat n) => Ordinal n -> Bool -> [EquationRow n] -> [EquationRow n]
specializeRows index successor = mapMaybe specialize
  where
    specialize (EquationRow ident ps body) = case (SV.sIndex index ps, successor) of
      (VarP _, False) -> Just (EquationRow ident ps (substituteSlot index (LitFT 0) body))
      (VarP _, True) -> Just (EquationRow ident ps (substituteSlot index (successorTerm (VarFT index)) body))
      (ZeroP, False) -> Just (EquationRow ident (replaceSlot index (VarP "_") ps) body)
      (SuccP p, True) -> Just (EquationRow ident (replaceSlot index p ps) body)
      _ -> Nothing

{- | Specialize the matrix, rejecting both holes and overlaps. A hole is
reported with a missing input pattern, an overlap with the two source clause
identifiers. Display names need no erasure: IrrelevantName already ignores them.
-}
buildCaseTree :: forall n. (KnownNat n) => [EquationRow n] -> Either ElaborationError (CaseTree n)
buildCaseTree = go (fmap (const (VarP "_")) (slotIndices @n))
  where
    go :: V n (Pattern IrrelevantName) -> [EquationRow n] -> Either ElaborationError (CaseTree n)
    go witness [] = Left (NonExhaustivePatterns (toList witness))
    go witness rows
      | (before, row : after) <- break (all isVariable . rowPatterns) rows =
          case before <> after of
            other : _ -> Left (OverlappingClauses (rowId row) (rowId other))
            [] -> Right (Leaf (rowId row) (rowBody row))
      | Just index <- find (\i -> any (not . isVariable . SV.sIndex i . rowPatterns) rows) (toList (slotIndices @n)) =
          Split index
            <$> go (refine index ZeroP witness) (specializeRows index False rows)
            <*> go (refine index (SuccP (VarP "_")) witness) (specializeRows index True rows)
      | otherwise = Left (InternalError "buildCaseTree: a clause matrix with neither a variable row nor a constructor column")
    isVariable VarP {} = True
    isVariable _ = False
    refine index p witness = replaceSlot index (replaceLeaf p (SV.sIndex index witness)) witness
    replaceLeaf p (SuccP q) = SuccP (replaceLeaf p q)
    replaceLeaf p _ = p
