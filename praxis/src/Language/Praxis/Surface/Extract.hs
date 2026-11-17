{-# LANGUAGE OverloadedStrings #-}

-- | Extraction of checked Surface computations, independent of PRA execution.
module Language.Praxis.Surface.Extract (extractProgram, haskellModule) where

import Bound (Var (..), instantiate)
import Control.Monad (unless)
import Data.List (elemIndex, find)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (absurd)
import Language.Praxis.Runtime.Program qualified as R
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Core qualified as Core
import Language.Praxis.Surface.Engine (Knowledge (..))
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Mangle (demangle)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Term qualified as Term
import Language.Praxis.Surface.Types

extractProgram :: Text -> Checked -> Either String R.Program
extractProgram entry checked = do
  unless (all ((/= SevError) . reportSeverity) (checkedReports checked)) $ Left "cannot extract a module with checking errors"
  (knowledge, core) <- maybe (Left "no checked module to extract") Right (checkedFinal checked)
  let env = knowEnv knowledge
      globals = Map.elems (envGlobals env)
      functions = Map.fromList [(demangle (funCore f), f) | GFun f <- globals]
      constructors = [c | GCtor c <- globals]
      projections = Map.fromList [(demangle name, i) | GData d <- globals, Just names <- [indexFunctionCores env (renderQualName (dataQual d))], (name, i) <- zip names [0 ..]]
  root <- maybe (Left ("unknown entry point: " <> T.unpack entry)) Right (find ((== entry) . demangle . funCore) (Map.elems functions))
  unless (null (funProofs root)) $ Left "export a wrapper with discharged proof preconditions"
  unless (null (schemeParams (funScheme root))) $ Left "export a monomorphic wrapper for a polymorphic entry point"
  unless (null (funSlots root)) $ Left "export a wrapper with a concrete dictionary"
  let scheme = funScheme root
      domains (TArrow a b) = a : domains b
      domains _ = []
      inputTypes = [snd (schemeValues scheme !! i) | i <- funRuntime root] <> domains (schemeType scheme)
  inputs <- traverse translateType inputTypes
  cs <- Map.fromList <$> traverse (\c -> (demangle (ctorCore c),) <$> translateConstructor c) constructors
  -- Only functions reachable from the export or membership checks enter the target.
  let bodies = Map.mapWithKey (compileFunction core) functions
      guardCalls = concatMap (maybe [] (concatMap predicateCalls) . R.constructorGuards) (Map.elems cs)
      indexCalls = concatMap (concatMap termCalls . R.constructorIndices) (Map.elems cs)
      inputCalls = concatMap typeCalls inputs
      available = Map.filter (either (const False) (const True)) bodies
      -- Internal constructors may have guards outside the executable fragment;
      -- those guards are never silently accepted at the input boundary.
      auxiliary = filter (`Map.member` available) (guardCalls <> indexCalls)
      visit seen [] = Right seen
      visit seen (name : rest)
        | Map.member name seen || Map.member name projections || name `elem` ["S", "add", "sub", "mul"] = visit seen rest
        | otherwise = do
            compiled <- maybe (Left ("no extractable definition for " <> T.unpack name)) id (Map.lookup name bodies)
            let R.Function clauses = compiled
            visit (Map.insert name compiled seen) (concatMap (\(R.Clause _ body) -> termCalls body) clauses <> rest)
  fs <- visit Map.empty (entry : inputCalls <> auxiliary)
  pure
    R.Program
      { R.programEntry = entry
      , R.programInputs = inputs
      , R.programParameters = [elemIndex i (funRuntime root) | i <- [0 .. length (schemeValues scheme) - 1]]
      , R.programFunctions = fs
      , R.programConstructors = cs
      , R.programProjections = projections
      }

compileFunction :: Core -> Text -> FunInfo -> Either String R.Function
compileFunction core name info = do
  unless (null (funSlots info)) $ Left ("runtime dictionaries are not yet extractable: " <> T.unpack name)
  bodies <- maybe (Left ("missing checked bodies: " <> T.unpack name)) Right (Map.lookup (funCore info) (coreBodies core))
  patterns <- maybe (Left ("missing runtime patterns: " <> T.unpack name)) Right (Map.lookup (funCore info) (corePatterns core))
  unless (length bodies == length patterns) $ Left "pattern/body count mismatch"
  R.Function <$> sequence [R.Clause (map translatePattern ps) <$> translateTerm (Core.computation body) | (ps, body) <- zip patterns bodies]

translatePattern :: Pattern -> R.Pattern
translatePattern = \case
  PVar _ -> R.Bind
  PWild -> R.Wild
  PNat n -> R.NumberPattern n
  PSucc p -> R.Successor (translatePattern p)
  PCon r ps -> R.ConstructorPattern (demangle (refName r)) (map translatePattern ps)
  PAbsurd -> R.Impossible

translateTerm :: Term.Term Int -> Either String R.Term
translateTerm = \case
  Term.Variable i -> Right (R.Variable i)
  Term.Literal n -> Right (R.Literal n)
  Term.Call ref args -> do
    xs <- traverse translateTerm args
    case refKind ref of
      RefConstructor -> Right (R.Construct (demangle (refName ref)) xs)
      RefFunction -> Right (R.Call (demangle (refName ref)) xs)
      RefBuiltin -> Right (R.Call (refName ref) xs)
      _ -> Left ("unsupported extraction reference: " <> show ref)
  Term.Parameter _ environment -> translateTerm environment
  Term.Closure arity body -> R.Lambda arity <$> translateTerm (fmap (\case B i -> i; F i -> arity + i) body)
  Term.PackedClosure hints body environment -> R.Packed (length hints - 1) <$> translateTerm body <*> translateTerm environment
  Term.Invoke callback args -> R.Apply <$> translateTerm callback <*> traverse translateTerm args
  Term.PackedPredicate {} -> Left "packed dictionary predicates are not yet extractable"

translateType :: Ty -> Either String R.Type
translateType = \case
  TNat -> Right R.NaturalType
  TParam i [] -> Right (R.TypeParameter i)
  TData name types indices -> R.DataType name <$> traverse translateType types <*> traverse translateIndex indices
  ty -> Left ("type is not a closed first-order JSON domain: " <> show ty)

translateIndex :: Ix -> Either String R.Term
translateIndex = \case
  IxParam i -> Right (R.Variable i)
  IxNat n -> Right (R.Literal n)
  IxSucc n -> R.Call "S" . (: []) <$> translateIndex n
  IxCon name xs -> R.Construct (demangle name) <$> traverse translateIndex xs
  IxFun name xs -> R.Call (demangle name) <$> traverse translateIndex xs
  ix -> Left ("index is not executable: " <> show ix)

translateConstructor :: CtorInfo -> Either String R.Constructor
translateConstructor c = do
  let signature = ctorSignature c
  fields <- traverse (\e -> R.Field <$> translateType (teType e) <*> pure (location (teRole e))) (constructorTele signature)
  indices <- traverse translateIndex (constructorIndices signature)
  let guards = traverse (translatePredicate . instantiate Var . fmap absurd . snd) (constructorProofs signature)
  pure (R.Constructor (renderQualName (ctorData c)) (length (ctorFields c)) fields indices (either (const Nothing) Just guards))
  where
    location (Explicit i) = R.Stored i
    location (Stored i) = R.Stored i
    location (Recovered i j) = R.Recovered i j

translatePredicate :: Expr Int -> Either String R.Predicate
translatePredicate expression = case stripLocations expression of
  Rel relation a b -> do
    l <- computational a
    r <- computational b
    pure $ case relation of
      RelEq -> R.Equal l r
      RelNe -> R.Negation (R.Equal l r)
      RelLt -> R.Less l r
      RelLe -> R.LessEqual l r
      RelGt -> R.Less r l
      RelGe -> R.LessEqual r l
  Conn And a b -> R.Conjunction <$> translatePredicate a <*> translatePredicate b
  Conn Or a b -> R.Disjunction <$> translatePredicate a <*> translatePredicate b
  Conn Iff a b -> do
    l <- translatePredicate a
    r <- translatePredicate b
    pure (R.Conjunction (R.Disjunction (R.Negation l) r) (R.Disjunction (R.Negation r) l))
  Arrow a b -> R.Disjunction <$> (R.Negation <$> translatePredicate a) <*> translatePredicate b
  Not a -> R.Negation <$> translatePredicate a
  Top -> Right (R.Truth True)
  Bottom -> Right (R.Truth False)
  _ -> Left "proof precondition is outside the executable quantifier-free fragment"
  where
    computational e = Term.prepareTerm e >>= Term.withoutObligations >>= translateTerm

termCalls :: R.Term -> [Text]
termCalls = \case
  R.Call name xs -> name : concatMap termCalls xs
  R.Construct _ xs -> concatMap termCalls xs
  R.Lambda _ body -> termCalls body
  R.Packed _ body environment -> termCalls body <> termCalls environment
  R.Apply f xs -> termCalls f <> concatMap termCalls xs
  _ -> []

predicateCalls :: R.Predicate -> [Text]
predicateCalls = \case
  R.Equal a b -> termCalls a <> termCalls b
  R.Less a b -> termCalls a <> termCalls b
  R.LessEqual a b -> termCalls a <> termCalls b
  R.Conjunction a b -> predicateCalls a <> predicateCalls b
  R.Disjunction a b -> predicateCalls a <> predicateCalls b
  R.Negation a -> predicateCalls a
  R.Truth _ -> []

typeCalls :: R.Type -> [Text]
typeCalls (R.DataType _ ts xs) = concatMap typeCalls ts <> concatMap termCalls xs
typeCalls _ = []

-- | Haskell is the compilation target; no Praxis source parser ships to JS.
haskellModule :: R.Program -> Text
haskellModule program =
  T.unlines
    [ "{-# LANGUAGE OverloadedStrings #-}"
    , "module Extracted (program) where"
    , "import Data.Map.Strict (fromList)"
    , "import Language.Praxis.Runtime.Program"
    , "program :: Program"
    , "program = " <> T.pack (show program)
    ]
