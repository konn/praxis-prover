{-# LANGUAGE OverloadedStrings #-}

{- | An experimental evaluator for the checked first-order surface core.
Constructor trees are interned and calls memoized; it never iterates up to a
Gödel code. Evaluation is not evidence: no result is installed as a theorem,
and the generated PRA definitions and certificates remain authoritative.
-}
module Language.Praxis.Surface.Eval (
  Value (..),
  EvalResult (..),
  evaluateEntry,
  evaluateEntryWithNats,
  renderValue,
) where

import Control.Monad (unless, zipWithM)
import Control.Monad.State.Strict
import Data.IntMap.Lazy qualified as Lazy
import Data.IntMap.Strict qualified as IM
import Data.List (find)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Core qualified as Core
import Language.Praxis.Surface.Engine (Knowledge (..))
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Mangle (demangle)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Term qualified as Term
import Language.Praxis.Surface.Types (Scheme (..), Ty (..))
import Numeric.Natural (Natural)

-- | The observable result, preserving sharing of equal constructor subtrees.
data Value = NatValue !Natural | DataValue !Text [Value]
  deriving stock (Show, Eq)

{- | Evaluation statistics count cached calls and allocated nodes, not the
potentially much larger unfolded tree displayed to the user.
-}
data EvalResult = EvalResult
  { evalValue :: Value
  , evalCalls :: !Int
  , evalNodes :: !Int
  }
  deriving stock (Show, Eq)

data Node = Number !Natural | Constructor !Text ![Int]
  deriving stock (Eq, Ord)

data Runtime = Runtime
  { remaining :: !Int
  , nodes :: !(IM.IntMap Node)
  , interned :: !(Map.Map Node Int)
  , calls :: !(Map.Map (Ref, [Int]) Int)
  }

type Eval = StateT Runtime (Either String)

{- | Evaluate a named nullary definition in an entirely successful check.
Arbitrary raw proof codes cannot be supplied through this interface.
Callbacks and dictionaries are deliberately outside this first evaluator.
-}
evaluateEntry :: Int -> Text -> Checked -> Either String EvalResult
evaluateEntry fuel entry = evaluateEntryWithNats fuel entry []

{- | Apply an entry point to natural arguments in runtime order (stored
implicit indices first). Other input types and proof preconditions are
rejected: this API cannot fabricate a typed derivation from a raw number.
-}
evaluateEntryWithNats :: Int -> Text -> [Natural] -> Checked -> Either String EvalResult
evaluateEntryWithNats fuel entry arguments checked = do
  unless (fuel > 0) $ Left "evaluation fuel must be positive"
  unless (all ((/= SevError) . reportSeverity) (checkedReports checked)) $ Left "cannot evaluate a module with checking errors"
  (knowledge, core) <- maybe (Left "no checked module to evaluate") Right (checkedFinal checked)
  let globals = Map.elems (envGlobals (knowEnv knowledge))
      functions = Map.fromList [(funCore f, f) | GFun f <- globals]
      constructors = Map.fromList [(ctorCore c, length (ctorFields c)) | GCtor c <- globals]
  root <- maybe (Left ("unknown entry point: " <> T.unpack entry)) Right (find ((== entry) . demangle . funCore) (Map.elems functions))
  unless (null (funProofs root)) $ Left "the entry point requires proof arguments"
  let scheme = funScheme root
      domains (TArrow a b) = a : domains b
      domains _ = []
      inputs = [snd (schemeValues scheme !! i) | i <- funRuntime root] <> domains (schemeType scheme)
  unless (inputs == replicate (length arguments) TNat) $ Left "entry arguments must match its natural-number runtime parameters"
  (result, final) <- runStateT (traverse (intern . Number) arguments >>= call core functions constructors (Ref RefFunction (funCore root))) (Runtime fuel IM.empty Map.empty Map.empty)
  let values = Lazy.map (\case Number n -> NatValue n; Constructor name fields -> DataValue (demangle name) (map (values Lazy.!) fields)) (nodes final)
  pure (EvalResult (values Lazy.! result) (Map.size (calls final)) (IM.size (nodes final)))

tick :: Eval ()
tick = do
  left <- gets remaining
  unless (left > 0) $ lift (Left "evaluation fuel exhausted")
  modify' (\st -> st {remaining = left - 1})

intern :: Node -> Eval Int
intern node = do
  known <- gets (Map.lookup node . interned)
  case known of
    Just i -> pure i
    Nothing -> do
      i <- gets (IM.size . nodes)
      modify' (\st -> st {nodes = IM.insert i node (nodes st), interned = Map.insert node i (interned st)})
      pure i

getNode :: Int -> Eval Node
getNode i = gets (IM.lookup i . nodes) >>= maybe (lift (Left "internal: missing evaluation node")) pure

call :: Core -> Map.Map Text FunInfo -> Map.Map Text Int -> Ref -> [Int] -> Eval Int
call core functions constructors ref args = do
  tick
  cached <- gets (Map.lookup (ref, args) . calls)
  case cached of
    Just value -> pure value
    Nothing -> do
      value <- case refKind ref of
        RefConstructor -> case Map.lookup (refName ref) constructors of
          Just arity | arity == length args -> intern (Constructor (refName ref) args)
          _ -> lift (Left "constructor arity mismatch during evaluation")
        RefFunction -> do
          info <- maybe (lift (Left "unknown function during evaluation")) pure (Map.lookup (refName ref) functions)
          unless (null (funSlots info)) $ lift (Left "surface evaluation does not yet support dictionaries")
          bodies <- maybe (lift (Left "missing checked function bodies")) pure (Map.lookup (refName ref) (coreBodies core))
          patterns <- maybe (lift (Left "missing runtime function patterns")) pure (Map.lookup (refName ref) (corePatterns core))
          unless (length patterns == length bodies) $ lift (Left "internal: pattern/body count mismatch")
          choose (zip patterns bodies)
        RefBuiltin -> builtin (refName ref) args
        _ -> lift (Left ("unsupported evaluation reference: " <> show ref))
      modify' (\st -> st {calls = Map.insert (ref, args) value (calls st)})
      pure value
  where
    choose [] = lift (Left ("no matching clause or wrong arity: " <> T.unpack (demangle (refName ref))))
    choose ((ps, body) : rest)
      | length ps /= length args = choose rest
      | otherwise = do
          matched <- sequence <$> zipWithM match ps args
          maybe (choose rest) (term . concat) matched
      where
        term context = evaluateTerm context (Core.computation body)
    evaluateTerm context term = do
      tick
      case term of
        Term.Variable i -> case drop i context of
          value : _ | i >= 0 -> pure value
          _ -> lift (Left "internal: unbound runtime variable")
        Term.Literal n -> intern (Number n)
        Term.Call r xs -> traverse (evaluateTerm context) xs >>= call core functions constructors r
        _ -> lift (Left "surface evaluation does not yet support callbacks or closures")

match :: Pattern -> Int -> Eval (Maybe [Int])
match pattern' value = do
  tick
  case pattern' of
    PVar _ -> pure (Just [value])
    PWild -> pure (Just [])
    PNat n -> getNode value >>= \case Number m | n == m -> pure (Just []); _ -> pure Nothing
    PSucc p ->
      getNode value >>= \case
        Number n | n > 0 -> intern (Number (n - 1)) >>= match p
        _ -> pure Nothing
    PCon ref fields ->
      getNode value >>= \case
        Constructor name values | name == refName ref && length fields == length values -> fmap concat . sequence <$> zipWithM match fields values
        _ -> pure Nothing
    PAbsurd -> pure Nothing

builtin :: Text -> [Int] -> Eval Int
builtin name args = do
  ns <- traverse (\i -> getNode i >>= \case Number n -> pure n; _ -> lift (Left "arithmetic on a constructor value")) args
  n <- case (name, ns) of
    ("S", [x]) -> pure (x + 1)
    ("add", [x, y]) -> pure (x + y)
    ("mul", [x, y]) -> pure (x * y)
    ("sub", [x, y]) -> pure (if x >= y then x - y else 0)
    _ -> lift (Left ("unsupported evaluation builtin or arity: " <> T.unpack name))
  intern (Number n)

-- | Bounded display; this does not force the entire unfolded proof tree.
renderValue :: Int -> Value -> Text
renderValue depth = \case
  NatValue n -> T.pack (show n)
  DataValue name [] -> name
  DataValue name fields
    | depth <= 0 -> name <> " ..."
    | otherwise -> "(" <> T.unwords (name : map (renderValue (depth - 1)) fields) <> ")"
