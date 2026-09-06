{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

-- | Primitive-recursion reconstruction and dependency-ordered compilation.
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Compile (
  ElaboratedDefinition (..),
  definitionCode,
  SomeProgram (..),
  elaborateDefinition,
  elaborateRenamedEquations,
  elaborateEquations,
  elaborateEquationsWith,
) where

import Control.Monad (foldM, unless)
import Data.Foldable (toList)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Proxy (Proxy (..))
import Data.Set qualified as Set
import Data.Sized qualified as SV
import Data.Text qualified as T
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Type.Natural (sNat)
import Data.Type.Ordinal (Ordinal, ordToNatural)
import GHC.TypeNats (KnownNat, SomeNat (..), natVal, someNatVal, type (+))
import Language.Praxis.PRA.PrimitiveRecursion.Code (V)
import Language.Praxis.PRA.PrimitiveRecursion.Code qualified as PR
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.CaseTree
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Internal
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Rename (renameEquations)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax
import Language.Praxis.PRA.PrimitiveRecursion.Function (Program)
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Numeric.Natural (Natural)

{- | Compilation evidence retained for subsequent unfolding-lemma generation.
The tree describes ordinary pattern matching; the separate recursion argument
identifies which split implements source recursion.
-}
data ElaboratedDefinition = forall n. (KnownNat n) => ElaboratedDefinition
  { compiledName :: !T.Text
  , compiledCode :: !(Program n)
  , compiledRows :: ![EquationRow n]
  , compiledTree :: !(CaseTree n)
  , compiledRecursionArgument :: !(Maybe (Ordinal n))
  }

deriving instance Show ElaboratedDefinition

data SomeProgram = forall n. (KnownNat n) => SomeProgram !(Program n)

deriving instance Show SomeProgram

projection :: Data.Type.Ordinal.Ordinal n -> Program n
projection = F.Base . PR.Proj

definitionCode :: ElaboratedDefinition -> SomeProgram
definitionCode (ElaboratedDefinition _ code _ _ _) = SomeProgram code

-- Check against the original patterns, before case-tree substitutions.
checkCandidate :: (KnownNat n) => T.Text -> Ordinal n -> [EquationRow n] -> Either String ()
checkCandidate self index = mapM_ checkRow
  where
    checkRow row = case SV.sIndex index (rowPatterns row) of
      ZeroP -> unless (Set.notMember self (functionCalls (rowBody row))) (Left "recursive call in base case")
      SuccP VarP {} -> checkCalls row (rowBody row)
      _ -> Left "recursion column must contain only 0 and S(variable)"
    checkCalls row (AppFT (Defined ident) xs) | ident == self = do
      let expected = fmap (\i -> if i == index then VarFT i else patternTerm i (SV.sIndex i (rowPatterns row))) slotIndices
      unless (length xs == length expected && and (zipWith sameTerm (toList xs) (toList expected))) $
        Left ("recursive call changes a parameter or does not use the immediate predecessor in clause " <> show (rowId row))
    checkCalls row (AppFT _ xs) = mapM_ (checkCalls row) xs
    checkCalls _ _ = Right ()

literalCode :: Natural -> Program n
literalCode 0 = (F.Base PR.Zero)
literalCode n = F.Comp (F.Base PR.Succ) (literalCode (n - 1) SV.:< SV.Nil)

lookupCode :: forall n. (KnownNat n) => Map T.Text SomeProgram -> T.Text -> Either String (Program n)
lookupCode env ident = case Map.lookup ident env of
  Nothing -> Left ("No compiled code for " <> T.unpack ident)
  Just (SomeProgram (code :: Program m)) -> case testEquality (sNat @n) (sNat @m) of
    Just Refl -> Right code
    Nothing -> Left ("Compiled arity mismatch for " <> T.unpack ident)

-- The recursive-result code is separate from the source slot vector, and is
-- lifted along with it beneath parameter case splits.
compileBody :: Map T.Text SomeProgram -> T.Text -> Maybe (Program k) -> V n (Program k) -> FunctionalTerm n -> Either String (Program k)
compileBody env self previous slots = go
  where
    go (LitFT n) = Right (literalCode n)
    go (VarFT i) = Right (SV.sIndex i slots)
    go (AppFT (Defined ident) _)
      | ident == self =
          maybe (Left "Unexpected recursive call") Right previous
    go (AppFT fun xs) = do
      code <- case fun of
        Primitive code -> Right (F.Base code)
        Bound bound -> Right (F.functionProgram bound)
        Defined ident -> lookupCode env ident
      F.Comp code <$> traverse go xs

-- Ordinary case analysis retains all current inputs as parameters. Its local
-- recursor ignores its own recursive result; any outer result is passed through.
compileTree :: forall n k. (KnownNat n, KnownNat k) => Map T.Text SomeProgram -> T.Text -> Maybe (Program k) -> V n (Program k) -> CaseTree n -> Either String (Program k)
compileTree env self previous slots = \case
  Leaf _ body -> compileBody env self previous slots body
  Split index z s -> do
    base <- compileTree env self previous (replaceSlot index (F.Base PR.Zero) slots) z
    let lifted :: V k (Program (k + 2))
        lifted = fmap (\i -> projection (fromIntegral (ordToNatural i + 2))) (slotIndices @k)
        liftCode code = F.Comp code lifted
    step <-
      compileTree
        env
        self
        (fmap liftCode previous)
        (replaceSlot index (projection 0) (fmap liftCode slots))
        s
    pure (F.Comp (F.Rec base step) (SV.sIndex index slots SV.:< fmap projection (slotIndices @k)))

{- | Compile one function, retaining its matrix, case tree, and selected recursor.
Candidates are tried in argument order. Selected recursion patterns must be
shallow; other columns may contain arbitrarily nested successor patterns.
-}
elaborateDefinition :: Map T.Text SomeProgram -> [RenamedEquation] -> Either String ElaboratedDefinition
elaborateDefinition _ [] = Left "Empty function definition"
elaborateDefinition env equations@(RenamedEquation self (_ :: V n (Pattern IrrelevantName)) _ : _) = do
  rows <- traverse unpack (zip [0 ..] equations)
  tree <- buildCaseTree rows
  if all (Set.notMember self . functionCalls . rowBody) rows
    then do
      code <- compileTree env self Nothing (fmap projection (slotIndices @n)) tree
      pure (ElaboratedDefinition self code rows tree Nothing)
    else choose rows tree [] (toList (slotIndices @n))
  where
    unpack (ident, RenamedEquation other (ps :: V m (Pattern IrrelevantName)) body)
      | other /= self = Left "Mixed function names in definition"
      | otherwise = case testEquality (sNat @n) (sNat @m) of
          Just Refl -> Right (EquationRow ident ps body)
          Nothing -> Left ("Inconsistent arity for " <> T.unpack self)
    choose _ _ failures [] = Left ("No primitive recursion argument for " <> T.unpack self <> ": " <> unwords (reverse failures))
    choose rows tree failures (index : rest) = case candidate rows index of
      Left err -> choose rows tree (("argument " <> show (ordToNatural index) <> ": " <> err <> ";") : failures) rest
      Right code -> Right (ElaboratedDefinition self code rows tree (Just index))
    candidate rows index = do
      checkCandidate self index rows
      baseTree <- buildCaseTree (specializeRows index False rows)
      stepTree <- buildCaseTree (specializeRows index True rows)
      -- Reify the number of fixed parameters; the candidate guarantees n > 0.
      case someNatVal (natVal (Proxy @n) - 1) of
        SomeNat (_ :: Proxy k) -> do
          let parameterIndices = filter (/= index) (toList (slotIndices @n))
          baseSlots <- vector $ map (\i -> if i == index then (F.Base PR.Zero) else projection (parameterSlot index i)) (toList (slotIndices @n))
          base <- compileTree env self Nothing (baseSlots :: V n (Program k)) baseTree
          stepSlots <- vector $ map (\i -> if i == index then projection 0 else projection (fromIntegral (ordToNatural (parameterSlot index i :: Ordinal k) + 2))) (toList (slotIndices @n))
          step <- compileTree env self (Just (projection 1)) (stepSlots :: V n (Program (k + 2))) stepTree
          inputs <- vector (projection index : map projection parameterIndices)
          -- No permutation is needed when the source already recurses on its
          -- first argument. Avoid an identity composition, which otherwise
          -- introduces extra reductions and changes residual code shapes.
          case testEquality (sNat @n) (sNat @(k + 1)) of
            Just Refl | ordToNatural index == 0 -> pure (F.Rec base step)
            _ -> pure (F.Comp (F.Rec base step) inputs)
    parameterSlot index i = fromIntegral (ordToNatural i - if i > index then 1 else 0)

vector :: (KnownNat n) => [a] -> Either String (V n a)
vector = maybe (Left "Internal elaborator vector arity mismatch") Right . SV.fromList'

{- | Resolve definitions in dependency order, including forward references.
Self recursion is handled by elaborateDefinition; other cycles are rejected.
The result contains only newly elaborated definitions, not the initial codes.
-}
elaborateRenamedEquations :: Map T.Text SomeProgram -> [RenamedEquation] -> Either String (Map T.Text ElaboratedDefinition)
elaborateRenamedEquations = elaborateRenamedEquationsWith id

elaborateRenamedEquationsWith :: (T.Text -> T.Text) -> Map T.Text SomeProgram -> [RenamedEquation] -> Either String (Map T.Text ElaboratedDefinition)
elaborateRenamedEquationsWith qualify initial equations = foldM (visit Set.empty) Map.empty (Map.keys groups)
  where
    groups = foldr (\eq -> Map.insertWith (<>) (renamedName eq) [eq]) Map.empty equations
    visit active done ident
      | Map.member ident done = Right done
      | Set.member ident active = Left ("Mutual recursion is unsupported: " <> T.unpack ident)
      | Map.member ident initial = Left ("Function already defined: " <> T.unpack ident)
      | otherwise = case Map.lookup ident groups of
          Nothing -> Left ("No definition for " <> T.unpack ident)
          Just clauses -> do
            let dependencies = Set.delete ident (foldMap (\(RenamedEquation _ _ body) -> functionCalls body) clauses)
            done' <- foldM (dependency (Set.insert ident active)) done (Set.toList dependencies)
            result <- elaborateDefinition (Map.mapWithKey reference done' <> initial) clauses
            pure (Map.insert ident result done')
    reference ident (ElaboratedDefinition _ (_ :: Program n) _ _ _) = SomeProgram (F.Call (F.DefId (qualify ident) :: F.DefId n))
    dependency active done ident
      | Map.member ident groups = visit active done ident
      | Map.member ident initial = Right done
      | otherwise = Left ("No compiled code for " <> T.unpack ident)

{- | Rename and compile a program. Environmental primitive codes are available
to every definition. Unresolved environmental names must be supplied as code
before use. Coverage and overlap checks precede recursive-call compilation.
-}
elaborateEquations :: Env -> [Equation T.Text] -> Either String (Map T.Text ElaboratedDefinition)
elaborateEquations = elaborateEquationsWith id

elaborateEquationsWith :: (T.Text -> T.Text) -> Env -> [Equation T.Text] -> Either String (Map T.Text ElaboratedDefinition)
elaborateEquationsWith qualify env equations = do
  renamed <- renameEquations env equations
  elaborateRenamedEquationsWith qualify (Map.mapMaybe primitive env) renamed
  where
    primitive (SomeFunction (Primitive code)) = Just (SomeProgram (F.Base code))
    primitive (SomeFunction (Bound fun)) = Just (SomeProgram (F.functionProgram fun))
    primitive _ = Nothing
