{-# LANGUAGE OverloadedStrings #-}

-- | Shared evaluator and checked JSON boundary for native and WASM targets.
module Language.Praxis.Runtime (
  Value (..),
  Result (..),
  evaluate,
  evaluateJSON,
  evaluateJSONText,
) where

import Control.Monad (foldM, unless, zipWithM, zipWithM_)
import Control.Monad.State.Strict
import Data.Aeson qualified as J
import Data.Aeson.KeyMap qualified as KM
import Data.ByteString.Lazy qualified as BL
import Data.IntMap.Lazy qualified as Lazy
import Data.IntMap.Strict qualified as IM
import Data.Map.Strict qualified as Map
import Data.Scientific (base10Exponent, floatingOrInteger)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Vector qualified as V
import Language.Praxis.Runtime.Program
import Numeric.Natural (Natural)

data Value = NatValue !Natural | DataValue !Text [Value]
  deriving stock (Show, Eq)

data Result = Result {resultValue :: Value, resultCalls :: !Int, resultNodes :: !Int}
  deriving stock (Show, Eq)

data Node = Number !Natural | Data !Text ![Int] | Closure !Int !Term ![Int] | PackedClosure !Int !Term !Int
  deriving stock (Eq, Ord)

data ResolvedType = RNat | RData !Text ![ResolvedType] ![Int]
  deriving stock (Eq, Ord)

data Runtime = Runtime
  { remaining :: !Int
  , nodes :: !(IM.IntMap Node)
  , interned :: !(Map.Map Node Int)
  , calls :: !(Map.Map (Text, [Int]) Int)
  , members :: !(Set.Set (ResolvedType, Int))
  }

type Eval = StateT Runtime (Either String)

failure :: String -> Eval a
failure = lift . Left

tick :: Eval ()
tick = do
  n <- gets remaining
  unless (n > 0) $ failure "evaluation fuel exhausted"
  modify' (\s -> s {remaining = n - 1})

at :: [a] -> Int -> Eval a
at xs i = case drop i xs of
  x : _ | i >= 0 -> pure x
  _ -> failure "invalid runtime argument position"

intern :: Node -> Eval Int
intern node = do
  tick
  known <- gets (Map.lookup node . interned)
  case known of
    Just i -> pure i
    Nothing -> do
      i <- gets (IM.size . nodes)
      modify' (\s -> s {nodes = IM.insert i node (nodes s), interned = Map.insert node i (interned s)})
      pure i

nodeAt :: Int -> Eval Node
nodeAt i = gets (IM.lookup i . nodes) >>= maybe (failure "missing runtime node") pure

number :: Int -> Eval Natural
number i =
  nodeAt i >>= \case
    Number n -> pure n
    _ -> failure "expected a natural number"

constructor :: Program -> Text -> Eval Constructor
constructor p name = maybe (failure ("unknown constructor: " <> T.unpack name)) pure (Map.lookup name (programConstructors p))

term :: Program -> [Int] -> Term -> Eval Int
term p context expression = do
  tick
  case expression of
    Variable i -> at context i
    Literal n -> intern (Number n)
    Call name xs -> traverse (term p context) xs >>= call p name
    Construct name xs -> do
      c <- constructor p name
      unless (length xs == constructorArity c) $ failure "constructor arity mismatch"
      traverse (term p context) xs >>= intern . Data name
    Lambda arity body -> intern (Closure arity body context)
    Packed arity body env -> term p context env >>= intern . PackedClosure arity body
    Apply f xs -> do
      fun <- term p context f >>= nodeAt
      args <- traverse (term p context) xs
      case fun of
        Closure arity body captured | arity == length args -> term p (args <> captured) body
        PackedClosure arity body env | arity == length args -> term p (env : args) body
        _ -> failure "callback arity mismatch or non-function application"

call :: Program -> Text -> [Int] -> Eval Int
call p name args = do
  tick
  cached <- gets (Map.lookup (name, args) . calls)
  case cached of
    Just value -> pure value
    Nothing -> do
      value <- case Map.lookup name (programProjections p) of
        Just i -> case args of
          [value] -> project p value i
          _ -> failure "index projection arity mismatch"
        Nothing -> case Map.lookup name (programFunctions p) of
          Just (Function clauses) -> choose clauses
          Nothing -> builtin name args
      modify' (\s -> s {calls = Map.insert (name, args) value (calls s)})
      pure value
  where
    choose [] = failure ("no matching clause or wrong arity: " <> T.unpack name)
    choose (Clause patterns body : rest)
      | length patterns /= length args = choose rest
      | otherwise = do
          matched <- sequence <$> zipWithM match patterns args
          maybe (choose rest) (\context -> term p (concat context) body) matched

match :: Pattern -> Int -> Eval (Maybe [Int])
match pat value = do
  tick
  case pat of
    Bind -> pure (Just [value])
    Wild -> pure (Just [])
    Impossible -> pure Nothing
    NumberPattern n ->
      nodeAt value >>= \case
        Number m | n == m -> pure (Just [])
        _ -> pure Nothing
    Successor child ->
      nodeAt value >>= \case
        Number n | n > 0 -> intern (Number (n - 1)) >>= match child
        _ -> pure Nothing
    ConstructorPattern name ps ->
      nodeAt value >>= \case
        Data other xs | name == other && length ps == length xs -> fmap concat . sequence <$> zipWithM match ps xs
        _ -> pure Nothing

builtin :: Text -> [Int] -> Eval Int
builtin name args = do
  ns <- traverse number args
  value <- case (name, ns) of
    ("S", [n]) -> pure (n + 1)
    ("add", [a, b]) -> pure (a + b)
    ("sub", [a, b]) -> pure (if a >= b then a - b else 0)
    ("mul", [a, b]) -> pure (a * b)
    _ -> failure ("unsupported builtin or missing function: " <> T.unpack name)
  intern (Number value)

telescope :: Program -> Constructor -> [Int] -> Eval [Int]
telescope p c fields = traverse locate (constructorFields c)
  where
    locate (Field _ (Stored i)) = at fields i
    locate (Field _ (Recovered i j)) = at fields i >>= \v -> project p v j

project :: Program -> Int -> Int -> Eval Int
project p value i = do
  tick
  nodeAt value >>= \case
    Data name fields -> do
      c <- constructor p name
      context <- telescope p c fields
      expression <- at (constructorIndices c) i
      term p context expression
    _ -> failure "index projection requires a constructor value"

resolveType :: Program -> [ResolvedType] -> [Int] -> Type -> Eval ResolvedType
resolveType p types context = \case
  NaturalType -> pure RNat
  TypeParameter i -> at types i
  DataType name ts indices -> RData name <$> traverse (resolveType p types context) ts <*> traverse (term p context) indices

member :: Program -> ResolvedType -> Int -> Eval ()
member p ty value = do
  tick
  known <- gets (Set.member (ty, value) . members)
  unless known $ do
    case ty of
      RNat -> number value >> pure ()
      RData owner parameters indices ->
        nodeAt value >>= \case
          Data name fields -> do
            c <- constructor p name
            unless (constructorType c == owner && constructorArity c == length fields) $ failure "value is outside the function's datatype domain"
            guards <- maybe (failure "this datatype's proof preconditions are not executable") pure (constructorGuards c)
            context <- telescope p c fields
            zipWithM_ (\(Field fieldType _) v -> resolveType p parameters context fieldType >>= \t -> member p t v) (constructorFields c) context
            actual <- traverse (term p context) (constructorIndices c)
            unless (indices == actual) $ failure "value does not satisfy the datatype's index equations"
            valid <- and <$> traverse (predicate p context) guards
            unless valid $ failure "value does not satisfy the constructor's proof preconditions"
          _ -> failure "expected a datatype constructor"
    modify' (\s -> s {members = Set.insert (ty, value) (members s)})

predicate :: Program -> [Int] -> Predicate -> Eval Bool
predicate p context = \case
  Equal a b -> (==) <$> term p context a <*> term p context b
  Less a b -> (<) <$> natural a <*> natural b
  LessEqual a b -> (<=) <$> natural a <*> natural b
  Conjunction a b -> (&&) <$> predicate p context a <*> predicate p context b
  Disjunction a b -> (||) <$> predicate p context a <*> predicate p context b
  Negation a -> not <$> predicate p context a
  Truth b -> pure b
  where
    natural t = term p context t >>= number

-- | Domain membership is checked before any invocation of the entry point.
evaluate :: Int -> Program -> [Value] -> Either String Result
evaluate fuel p arguments = do
  unless (fuel > 0) $ Left "evaluation fuel must be positive"
  unless (length arguments == length (programInputs p)) $ Left "wrong number of input arguments"
  (root, final) <- runStateT run (Runtime fuel IM.empty Map.empty Map.empty Set.empty)
  let values = Lazy.map (\case Number n -> NatValue n; Data name xs -> DataValue name (map (values Lazy.!) xs); _ -> error "internal: callback escaped first-order result") (nodes final)
  pure (Result (values Lazy.! root) (Map.size (calls final)) (IM.size (nodes final)))
  where
    input depth _ | depth > (512 :: Int) = failure "input nesting limit exceeded"
    input _ (NatValue n) = intern (Number n)
    input depth (DataValue name xs) = do
      c <- constructor p name
      unless (length xs == constructorArity c) $ failure "constructor arity mismatch"
      traverse (input (depth + 1)) xs >>= intern . Data name
    run = do
      args <- traverse (input 0) arguments
      context <- traverse (maybe (pure (-1)) (at args)) (programParameters p)
      zipWithM_ (\ty arg -> resolveType p [] context ty >>= \t -> member p t arg) (programInputs p) args
      result <- call p (programEntry p) args
      _ <- firstOrder Set.empty result
      pure result
    firstOrder seen value
      | Set.member value seen = pure seen
      | otherwise = do
          tick
          nodeAt value >>= \case
            Number _ -> pure (Set.insert value seen)
            Data _ xs -> foldM firstOrder (Set.insert value seen) xs
            _ -> failure "function-valued results cannot be encoded as JSON"

{- | Requests have exactly one field: @{"value": [argument, ...]}@.
Naturals use decimal strings (safe JSON integers are also accepted), and
constructors use @["qualified.Constructor", field, ...]@ in physical order.
A failure is @{"error":{"message":"..."}}@, never an unchecked result.
-}
evaluateJSON :: Int -> Program -> J.Value -> J.Value
evaluateJSON fuel p request = either errorJSON (\value -> J.object ["value" J..= value]) $ do
  inputs <- case request of
    J.Object o | KM.keys o == ["value"], Just (J.Array xs) <- KM.lookup "value" o -> traverse (decodeValue 0) (V.toList xs)
    _ -> Left "expected exactly {\"value\": [argument, ...]}"
  result <- evaluate fuel p inputs
  evalStateT (encodeValue 0 (resultValue result)) (min fuel 100000)

errorJSON :: String -> J.Value
errorJSON message = J.object ["error" J..= J.object ["message" J..= message]]

-- Count unfolded output nodes as well as shared evaluation nodes. A tiny DAG
-- can otherwise expand into an exponentially large JSON response.
encodeValue :: Int -> Value -> StateT Int (Either String) J.Value
encodeValue depth value = do
  left <- get
  unless (left > 0 && depth <= 512) $ lift (Left "JSON output limit exceeded")
  put (left - 1)
  case value of
    NatValue n -> pure (J.String (T.pack (show n)))
    DataValue name xs -> J.Array . V.fromList . (J.String name :) <$> traverse (encodeValue (depth + 1)) xs

decodeValue :: Int -> J.Value -> Either String Value
decodeValue depth _ | depth > 512 = Left "input nesting limit exceeded"
decodeValue _ (J.String n)
  | not (T.null n), T.length n <= 4096, T.all (\c -> c >= '0' && c <= '9') n = Right (NatValue (read (T.unpack n)))
decodeValue _ (J.Number n)
  | base10Exponent n >= -16
  , base10Exponent n <= 16
  , Right i <- floatingOrInteger n :: Either Double Integer
  , i >= 0
  , i <= 9007199254740991 =
      Right (NatValue (fromInteger i))
decodeValue depth (J.Array xs) = case V.toList xs of
  J.String name : fields -> DataValue name <$> traverse (decodeValue (depth + 1)) fields
  _ -> Left "a constructor must start with its qualified name"
decodeValue _ _ = Left "expected a natural decimal string, safe natural integer, or constructor array"

evaluateJSONText :: Int -> Program -> Text -> Text
evaluateJSONText fuel p input =
  T.decodeUtf8 . BL.toStrict . J.encode $
    if T.length input > 1048576
      then errorJSON "request exceeds one MiB"
      else either errorJSON (evaluateJSON fuel p) (J.eitherDecodeStrict' (T.encodeUtf8 input))
