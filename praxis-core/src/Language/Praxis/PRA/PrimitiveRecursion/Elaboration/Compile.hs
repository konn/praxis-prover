{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

-- | Primitive-recursion reconstruction and dependency-ordered compilation.
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Compile (
  ElaboratedDefinition (..),
  definitionCode,
  SomeProgram (..),
  ElaboratedSchema (..),
  ElaboratedFamily (..),
  CompiledSchema (..),
  substProgram,
  instantiateSchemaFunction,
  instantiateLocal,
  elaborateDefinition,
  elaborateDefinitionWith,
  elaborateRenamedEquations,
  elaborateRenamedEquationsWith,
  elaborateRenamedEquationsAndSchemasWith,
  elaborateFamilyWith,
  elaborateInstances,
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
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Rename (equationEnv, renameEquation)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Variadic
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

data ElaboratedSchema = ElaboratedSchema
  { compiledSchemaName :: !T.Text
  , compiledSchemaParams :: ![T.Text]
  , compiledSchemaParamArity :: !Natural
  , compiledSchemaDefinition :: !ElaboratedDefinition
  }

deriving instance Show ElaboratedSchema

{- | A compiled family. Instances of variadic templates are inlined where they
are applied and are not retained, except those explicitly demanded.
-}
data ElaboratedFamily = ElaboratedFamily
  { familyDefinitions :: !(Map T.Text ElaboratedDefinition)
  , familySchemas :: !(Map T.Text ElaboratedSchema)
  , familyVariadics :: !(Map T.Text VariadicTemplate)
  , familyInstances :: !(Map T.Text ElaboratedSchema)
  }

data CompiledSchema = CompiledSchema
  { cSchemaParams :: ![T.Text]
  , cSchemaParamArity :: !Natural
  , cSchemaArity :: !Natural
  , cSchemaInstantiate :: !([F.SomeFunction] -> Either String F.SomeFunction)
  }

substProgram :: forall k m. (KnownNat k, KnownNat m) => F.DefId k -> F.Program k -> F.Program m -> F.Program m
substProgram target replacement = go
  where
    go :: forall j. (KnownNat j) => F.Program j -> F.Program j
    go (F.Base code) = F.Base code
    go (F.Call (ident :: F.DefId j))
      | F.definitionName ident == F.definitionName target =
          case testEquality (sNat @j) (sNat @k) of
            Just Refl -> replacement
            Nothing -> F.Call ident
      | otherwise = F.Call ident
    go (F.Comp f xs) = F.Comp (go f) (fmap go xs)
    go (F.Rec b s) = F.Rec (go b) (go s)

instantiateLocal ::
  [T.Text] ->
  Natural ->
  ElaboratedDefinition ->
  [F.SomeFunction] ->
  Either String F.SomeFunction
instantiateLocal params pArity (ElaboratedDefinition _ (code :: F.Program sArity) _ _ _) pFuns =
  case someNatVal pArity of
    SomeNat (_ :: Proxy p) -> do
      unless (length params == length pFuns) (Left "Schema parameter count mismatch")
      instCode <- foldM subst (SomeProgram code) (zip params pFuns)
      case instCode of
        SomeProgram (finalCode :: F.Program m) ->
          case testEquality (sNat @m) (sNat @sArity) of
            Just Refl -> Right (F.SomeFunction (F.Inline finalCode :: F.Function sArity))
            Nothing -> Left "Instantiated schema arity mismatch"
  where
    subst (SomeProgram (curr :: F.Program m)) (paramName, F.SomeFunction (pFun :: F.Function k)) =
      case someNatVal pArity of
        SomeNat (_ :: Proxy expectedP) ->
          case testEquality (sNat @k) (sNat @expectedP) of
            Just Refl ->
              Right (SomeProgram (substProgram (F.DefId paramName :: F.DefId k) (F.functionProgram pFun) curr))
            Nothing ->
              Left ("Schema parameter arity mismatch for " <> T.unpack paramName <> ": expected " <> show pArity <> ", given " <> show (natVal (Proxy @k)))

instantiateSchemaFunction :: ElaboratedSchema -> F.SomeFunction -> Either String F.SomeFunction
instantiateSchemaFunction (ElaboratedSchema _ params pArity def) p =
  instantiateLocal params pArity def [p]

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

lookupFunctionAsSomeFunction :: Map T.Text SomeProgram -> T.Text -> Either String F.SomeFunction
lookupFunctionAsSomeFunction env ident = case Map.lookup ident env of
  Nothing -> Left ("No compiled code for schema argument: " <> T.unpack ident)
  Just (SomeProgram (code :: Program k)) -> Right (F.SomeFunction (F.Inline code :: F.Function k))

-- The recursive-result code is separate from the source slot vector, and is
-- lifted along with it beneath parameter case splits. A lambda parameter is
-- closed, so it is compiled in its own context of projections and may not
-- recurse: its calls would escape the recursor being reconstructed.
compileBody ::
  Map T.Text CompiledSchema ->
  Map T.Text SomeProgram ->
  T.Text ->
  Maybe (Program k) ->
  V n (Program k) ->
  FunctionalTerm n ->
  Either String (Program k)
compileBody schemas env self previous slots = go
  where
    go (LitFT n) = Right (literalCode n)
    go (VarFT i) = Right (SV.sIndex i slots)
    go (AppFT (Defined ident) _)
      | ident == self =
          maybe (Left "Unexpected recursive call") Right previous
    go (AppFT (SchemaApp sName pArgs :: Function m) xs) = do
      case Map.lookup sName schemas of
        Nothing -> Left ("Unknown schema: " <> T.unpack sName)
        Just sch -> do
          unless (length pArgs == length (cSchemaParams sch)) $
            Left ("Schema " <> T.unpack sName <> " expects " <> show (length (cSchemaParams sch)) <> " parameters, given " <> show (length pArgs))
          pFuns <- traverse parameter pArgs
          instSome <- cSchemaInstantiate sch pFuns
          args <- traverse go xs
          case instSome of
            F.SomeFunction (instFun :: F.Function instM) ->
              case testEquality (sNat @instM) (sNat @m) of
                Just Refl -> pure (F.Comp (F.functionProgram instFun) args)
                Nothing -> Left ("Schema application arity mismatch for " <> T.unpack sName)
    go (AppFT fun xs) = do
      code <- case fun of
        Primitive code -> Right (F.Base code)
        Bound bound -> Right (F.functionProgram bound)
        Defined ident -> lookupCode env ident
        SchemaApp {} -> error "impossible: handled above"
      F.Comp code <$> traverse go xs
    parameter (NamedArg p) = lookupFunctionAsSomeFunction env p
    parameter (LambdaArg (_ :: V p IrrelevantName) body) = do
      unless (Set.notMember self (functionCalls body)) $
        Left ("recursive call to " <> T.unpack self <> " inside a lambda")
      code <- compileBody schemas env self Nothing (fmap projection (slotIndices @p)) body
      pure (F.SomeFunction (F.Inline code :: F.Function p))

-- Ordinary case analysis retains all current inputs as parameters. Its local
-- recursor ignores its own recursive result; any outer result is passed through.
compileTree ::
  forall n k.
  (KnownNat n, KnownNat k) =>
  Map T.Text CompiledSchema ->
  Map T.Text SomeProgram ->
  T.Text ->
  Maybe (Program k) ->
  V n (Program k) ->
  CaseTree n ->
  Either String (Program k)
compileTree schemas env self previous slots = \case
  Leaf _ body -> compileBody schemas env self previous slots body
  Split index z s -> do
    base <- compileTree schemas env self previous (replaceSlot index (F.Base PR.Zero) slots) z
    let lifted :: V k (Program (k + 2))
        lifted = fmap (\i -> projection (fromIntegral (ordToNatural i + 2))) (slotIndices @k)
        liftCode code = F.Comp code lifted
    step <-
      compileTree
        schemas
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
elaborateDefinition ::
  Map T.Text SomeProgram ->
  [RenamedEquation] ->
  Either String ElaboratedDefinition
elaborateDefinition = elaborateDefinitionWith Map.empty

elaborateDefinitionWith ::
  Map T.Text CompiledSchema ->
  Map T.Text SomeProgram ->
  [RenamedEquation] ->
  Either String ElaboratedDefinition
elaborateDefinitionWith _ _ [] = Left "Empty function definition"
elaborateDefinitionWith schemas env equations@(RenamedEquation self (_ :: V n (Pattern IrrelevantName)) _ : _) = do
  rows <- traverse unpack (zip [0 ..] equations)
  tree <- buildCaseTree rows
  if all (Set.notMember self . functionCalls . rowBody) rows
    then do
      code <- compileTree schemas env self Nothing (fmap projection (slotIndices @n)) tree
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
          base <- compileTree schemas env self Nothing (baseSlots :: V n (Program k)) baseTree
          stepSlots <- vector $ map (\i -> if i == index then projection 0 else projection (fromIntegral (ordToNatural (parameterSlot index i :: Ordinal k) + 2))) (toList (slotIndices @n))
          step <- compileTree schemas env self (Just (projection 1)) (stepSlots :: V n (Program (k + 2))) stepTree
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
elaborateRenamedEquationsWith qualify initial equations =
  fst <$> elaborateRenamedEquationsAndSchemasWith qualify Map.empty initial Set.empty Map.empty equations

-- A schema's parameters are placeholders bound only while compiling its own
-- clauses, at its own parameter arity; other schemas may reuse the names.
elaborateRenamedEquationsAndSchemasWith ::
  (T.Text -> T.Text) ->
  Map T.Text CompiledSchema ->
  Map T.Text SomeProgram ->
  Set.Set T.Text ->
  Map T.Text ([T.Text], Natural, Natural) ->
  [RenamedEquation] ->
  Either String (Map T.Text ElaboratedDefinition, Map T.Text CompiledSchema)
elaborateRenamedEquationsAndSchemasWith qualify externalSchemas initial schemaNames schemaMeta equations =
  foldM (visit Set.empty) (Map.empty, externalSchemas) (Map.keys groups)
  where
    groups = foldr (\eq -> Map.insertWith (<>) (renamedName eq) [eq]) Map.empty equations
    parameterCodes ident = case Map.lookup ident schemaMeta of
      Just (params, pArity, _) -> case someNatVal pArity of
        SomeNat (_ :: Proxy p) -> Map.fromList [(p, SomeProgram (F.Call (F.DefId p :: F.DefId p))) | p <- params]
      Nothing -> Map.empty
    visit active (doneDefs, doneSchemas) ident
      | Map.member ident doneDefs = Right (doneDefs, doneSchemas)
      | Set.member ident active = Left ("Mutual recursion is unsupported: " <> T.unpack ident)
      | Map.member ident initial = Left ("Function already defined: " <> T.unpack ident)
      | otherwise = case Map.lookup ident groups of
          Nothing -> Left ("No definition for " <> T.unpack ident)
          Just clauses -> do
            let parameters = parameterCodes ident
                dependencies =
                  Set.delete ident (foldMap (\(RenamedEquation _ _ body) -> functionCalls body) clauses)
                    `Set.difference` Map.keysSet parameters
            (doneDefs', doneSchemas') <- foldM (dependency (Set.insert ident active)) (doneDefs, doneSchemas) (Set.toList dependencies)
            let envCodes = parameters <> Map.mapWithKey reference doneDefs' <> initial
            result <- elaborateDefinitionWith doneSchemas' envCodes clauses
            let doneDefs'' = Map.insert ident result doneDefs'
                doneSchemas'' = case Map.lookup ident schemaMeta of
                  Just (params, pArity, sArity) ->
                    Map.insert
                      ident
                      ( CompiledSchema
                          { cSchemaParams = params
                          , cSchemaParamArity = pArity
                          , cSchemaArity = sArity
                          , cSchemaInstantiate = instantiateLocal params pArity result
                          }
                      )
                      doneSchemas'
                  Nothing -> doneSchemas'
            pure (doneDefs'', doneSchemas'')
    reference ident (ElaboratedDefinition _ (code :: Program n) _ _ _)
      | Set.member ident schemaNames = SomeProgram code
      | otherwise = SomeProgram (F.Call (F.DefId (qualify ident) :: F.DefId n))
    dependency active (doneDefs, doneSchemas) ident
      | Map.member ident groups = visit active (doneDefs, doneSchemas) ident
      | Map.member ident initial = Right (doneDefs, doneSchemas)
      | Map.member ident externalSchemas = Right (doneDefs, doneSchemas)
      | otherwise = Left ("No compiled code for " <> T.unpack ident)

{- | Expand, rename and compile a program. Environmental primitive codes are
available to every definition. Unresolved environmental names must be
supplied as code before use. Coverage and overlap checks precede
recursive-call compilation. Variadic templates are checked at zero and one
variadic argument besides the instances the program applies.
-}
elaborateFamilyWith :: (T.Text -> T.Text) -> Env -> [Equation T.Text] -> Either String ElaboratedFamily
elaborateFamilyWith qualify env equations = do
  expanded <- expandFamily True env [] equations
  elaborateExpanded qualify [] expanded

{- | The demanded instances of the variadic templates among the equations,
compiled against an environment of existing codes; templates are not checked
again, as at their definition site.
-}
elaborateInstances :: Env -> [(T.Text, Natural)] -> [Equation T.Text] -> Either String (Map T.Text ElaboratedSchema)
elaborateInstances env demands equations = do
  expanded <- expandFamily False env demands equations
  familyInstances <$> elaborateExpanded id demands expanded

elaborateExpanded :: (T.Text -> T.Text) -> [(T.Text, Natural)] -> ExpandedFamily -> Either String ElaboratedFamily
elaborateExpanded qualify demands expanded = do
  let equations = expandedEquations expanded
  env' <- equationEnv (expandedEnv expanded) equations
  renamed <- traverse (renameEquation env') equations
  let initialCodes = Map.mapMaybe primitive env'
      externalSchemas =
        Map.fromList
          [ ( sName
            , CompiledSchema
                { cSchemaParams = ["P"]
                , cSchemaParamArity = pArity
                , cSchemaArity = sArity
                , cSchemaInstantiate = \case
                    [pArg] -> instFun pArg
                    _ -> Left ("Schema " <> T.unpack sName <> " expects 1 parameter")
                }
            )
          | (_, ImportedSchema sName pArity sArity instFun) <- Map.toList env'
          ]
      schemaMeta =
        Map.fromList
          [ (sName, (params, pArity, sArity))
          | eq <- equations
          , not (null (schemaParams eq))
          , let sName = name eq
          , Just (SchemaDef _ params pArity sArity) <- [Map.lookup sName env']
          ]
      schemaNames = Map.keysSet schemaMeta
  (defs, _compiledSchemas) <-
    elaborateRenamedEquationsAndSchemasWith qualify externalSchemas initialCodes schemaNames schemaMeta renamed
  let (schemaDefs, regularDefs) = Map.partitionWithKey (\k _ -> Set.member k schemaNames) defs
      toSchema ident def = case Map.lookup ident schemaMeta of
        Just (params, pArity, _) ->
          Just (ElaboratedSchema ident params pArity def)
        _ -> Nothing
      schemas = Map.mapMaybeWithKey toSchema schemaDefs
      instances = expandedInstances expanded
      demanded = Set.fromList [instanceName ident k | (ident, k) <- demands]
  pure
    ElaboratedFamily
      { familyDefinitions = regularDefs
      , familySchemas = Map.withoutKeys schemas instances
      , familyVariadics = expandedTemplates expanded
      , familyInstances = Map.restrictKeys schemas demanded
      }
  where
    primitive (SomeFunction (Primitive code)) = Just (SomeProgram (F.Base code))
    primitive (SomeFunction (Bound fun)) = Just (SomeProgram (F.functionProgram fun))
    primitive _ = Nothing

elaborateEquations :: Env -> [Equation T.Text] -> Either String (Map T.Text ElaboratedDefinition)
elaborateEquations = elaborateEquationsWith id

elaborateEquationsWith :: (T.Text -> T.Text) -> Env -> [Equation T.Text] -> Either String (Map T.Text ElaboratedDefinition)
elaborateEquationsWith qualify env equations = familyDefinitions <$> elaborateFamilyWith qualify env equations
