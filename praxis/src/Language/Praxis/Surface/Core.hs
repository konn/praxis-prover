{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

{- | The explicit value core. Construction checks the elaborator's annotations;
consumers can only inspect its types, lower its values, or translate all of
its evidence. The PRA checker remains the authority for that evidence.
-}
module Language.Praxis.Surface.Core (
  Body,
  elaborate,
  elaborateNamed,
  emptyBranch,
  computation,
  obligations,
  mapObligations,
  traverseObligations,
  mapComputation,
  bodyType,
  dump,
  pretty,
) where

import Bound (Var (..), fromScope)
import Control.Monad (foldM, unless)
import Data.Bifunctor (first)
import Data.Foldable (toList)
import Data.Functor.Identity (Identity (..))
import Data.IntMap.Strict qualified as IM
import Data.Map.Strict qualified as Map
import Data.Maybe (listToMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Type.Equality ((:~:) (..))
import Data.Void (Void, absurd)
import Language.Praxis.Surface.Core.Types
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Pretty qualified as Pretty
import Language.Praxis.Surface.Syntax qualified as S
import Language.Praxis.Surface.Term qualified as Tm
import Language.Praxis.Surface.Types qualified as Ty
import Numeric.Natural (Natural)
import Text.Read (readMaybe)

-- Variables are membership proofs in a heterogeneous context.
data Variable ctx t where
  Here :: Variable (t ': ctx) t
  There :: Variable ctx t -> Variable (s ': ctx) t

-- A fully instantiated global signature, created only by this module from
-- checked elaboration annotations. There is no instance search in the core.
data Signature args result = Signature S.Ref [Ty.Ty] [(Int, Ty.Ix)] (List SType args) (SType result)

data Value o ctx t where
  Variable :: Variable ctx t -> Value o ctx t
  Literal :: Natural -> Value o ctx 'Natural
  Apply :: Signature args t -> List (Value o ctx) args -> [o] -> Value o ctx t
  Dictionary :: SType t -> Tm.Term Void -> Value o ctx t
  Callback :: SType t -> Tm.Term Int -> Value o ctx t
  Invoke :: SType t -> Value o ctx u -> List (Value o ctx) args -> Value o ctx t
  Transport :: SType t -> Value o ctx u -> [o] -> Value o ctx t
  Absurd :: SType t -> o -> Value o ctx t

data SomeVariable ctx where
  SomeVariable :: SType t -> Variable ctx t -> SomeVariable ctx

data SomeValue o ctx where
  SomeValue :: SType t -> Value o ctx t -> SomeValue o ctx

data Arguments o ctx where
  Arguments :: List SType ts -> List (Value o ctx) ts -> Arguments o ctx

data Context where
  Context :: List SType ctx -> Context

{- | A closed clause over an explicit heterogeneous variable context. The final
rewrite is a code-generation optimization (dictionary pruning); it cannot
remove evidence from the typed value.
-}
data Body o where
  Body :: List SType ctx -> SType t -> Value o ctx t -> (Tm.Term Int -> Tm.Term Int) -> Body o
  EmptyBranch :: SType t -> Body o

{- | A clause with a checked impossible pattern has no value term. Its result
type is retained, and PRA lowering must discharge the pattern's impossible
membership case. Zero is only the total numerical implementation of that
unreachable branch, never an inhabitant of its source result type.
-}
emptyBranch :: Ty.Ty -> Either String (Body o)
emptyBranch ty = do
  SomeType result <- reflectType (complete ty)
  pure (EmptyBranch result)

{- | Check annotations at the explicit boundary. Unconstrained, computationally
irrelevant type arguments are instantiated at Nat; value indices must be
determined. This instantiation is recorded in the core signature.
-}
elaborate :: Env -> [Slot] -> [Ty.Ty] -> S.Expr Int -> Either String (Body (Tm.ProofArgument Int))
elaborate env slots tys = elaborateNamed env slots [("v" <> T.pack (show i), ty) | (i, ty) <- zip [0 :: Int ..] tys]

-- | The named context also identifies the terms denoted by source type indices.
elaborateNamed :: Env -> [Slot] -> [(Text, Ty.Ty)] -> S.Expr Int -> Either String (Body (Tm.ProofArgument Int))
elaborateNamed env slots variables expression = do
  Context ctx <- context (map snd variables)
  SomeValue ty value <- infer ctx expression
  pure (Body ctx ty value id)
  where
    context [] = Right (Context Nil)
    context (t : ts) = do
      SomeType ty <- first (\message -> message <> " in " <> show t) (reflectType (complete t))
      Context rest <- context ts
      pure (Context (Cons ty rest))
    infer :: List SType ctx -> S.Expr Int -> Either String (SomeValue (Tm.ProofArgument Int) ctx)
    infer ctx (S.At _ e) = infer ctx e
    infer ctx (S.Typed t ts is e) = do
      SomeType ty <- first (\message -> message <> " in " <> show t) (reflectType (complete t))
      value <- check ctx ty (map complete ts) is e
      pure (SomeValue ty value)
    infer ctx (S.Transport target child proofs) = do
      SomeType ty <- reflectType (complete target)
      SomeValue actual value <- infer ctx child
      pairs <- maybe (Left "an index transport changes the type structure") Right (Ty.transportIndices (forgetType actual) (forgetType ty))
      expected <- traverse (\(x, y) -> S.Rel S.RelEq <$> indexTerm x <*> indexTerm y) pairs
      evidence <- traverse transportProof proofs
      unless (map fst evidence == expected) $ Left "index transport evidence does not match its index equalities"
      pure (SomeValue ty (Transport ty value evidence))
    infer ctx (S.SchemaParameter source ref child) = do
      SomeType ty <- reflectType (complete source)
      _ <- callbackSignature source
      i <- case S.stripLocations child of
        S.Var position -> Right position
        _ -> Left "a callback parameter must keep its original environment variable"
      SomeVariable actual _ <- variable ctx i
      unless (forgetType ty == forgetType actual) $ Left "a callback environment has the wrong source signature"
      unless (any (\(name, known, signature) -> known == ref && name == fst (variables !! i) && complete signature == forgetType ty) (envSchemas env)) $
        Left "an unknown callback parameter at the explicit core boundary"
      pure (SomeValue ty (Callback ty (Tm.Parameter ref (Tm.Variable i))))
    infer _ S.SchemaPacked {} = Left "an internal packed callback cannot be supplied as a source term"
    infer _ (S.SchemaClosure source child) = do
      SomeType ty <- reflectType (complete source)
      (domains, result) <- callbackSignature source
      (hints, scope) <- case S.stripLocations child of
        S.Lam hs body -> Right (hs, body)
        _ -> Left "a callback closure must contain a lambda"
      let count = length domains
      unless (length hints == count) $ Left "a callback lambda has the wrong arity"
      let binders = zip (map S.hintText hints) domains
          opened = fmap (\case B i -> i; F i -> count + i) (fromScope scope)
      body <- elaborateNamed env slots (binders <> variables) opened
      unless (null (obligations body)) $ Left "proof obligations inside a callback lambda are not supported"
      unless (bodyType body == complete result) $ Left "a callback lambda returns the wrong type"
      let closed = fmap (\i -> if i < count then B i else F (i - count)) (computation body)
      pure (SomeValue ty (Callback ty (Tm.Closure count closed)))
    infer _ (S.Nat n) = Right (SomeValue SNatural (Literal n))
    infer ctx (S.Var i) = do
      SomeVariable t v <- variable ctx i
      unless (Ty.firstOrder (forgetType t)) $ Left "a callback variable requires its fixed schema identity"
      pure (SomeValue t (Variable v))
    infer _ (S.Dictionary t e) = do
      SomeType ty <- first (\message -> message <> " in " <> show t) (reflectType (complete t))
      p <- Tm.prepareTerm e
      code <- Tm.withoutObligations p
      closed <- traverse (const (Left "a dictionary contains a free value variable")) code
      validateDictionary env slots (forgetType ty) closed
      pure (SomeValue ty (Dictionary ty closed))
    infer _ _ = Left "a value without a checked type at the explicit core boundary"
    callbackSignature source = case arrows source of
      ([], _) -> Left "a callback needs a function signature"
      (domains, result)
        | all Ty.firstOrder (result : domains) -> Right (domains, result)
        | otherwise -> Left "callbacks take and return first-order values"
    arrows (Ty.TArrow a b) = let (rest, result) = arrows b in (a : rest, result)
    arrows t = ([], t)
    indexTerm ix = maybe (Left "an index transport has no scoped index term") Right (indexTermIn env [(name, (i, ty)) | (i, (name, ty)) <- zip [0 ..] variables] ix)
    transportProof e = case S.stripLocations e of
      S.ProofArg prop (S.Irrelevant raw)
        | all (\i -> i >= 0 && i < length variables) (toList prop) -> Right (prop, raw)
      _ -> Left "an index transport without scoped equality evidence"
    check :: List SType ctx -> SType t -> [Ty.Ty] -> [(Int, Ty.Ix)] -> S.Expr Int -> Either String (Value (Tm.ProofArgument Int) ctx t)
    check ctx ty _types is e = case S.spine e of
      (transport@S.Transport {}, []) -> do
        SomeValue actual value <- infer ctx transport
        equal ty actual value
      (callback@S.SchemaParameter {}, args) -> invocation ctx ty callback args
      (callback@S.SchemaClosure {}, args) -> invocation ctx ty callback args
      (S.Var i, []) -> do
        SomeVariable actual v <- variable ctx i
        unless (Ty.firstOrder (forgetType actual)) $ Left "a callback variable requires its fixed schema identity"
        equal ty actual (Variable v)
      (S.Nat n, []) -> equal ty SNatural (Literal n)
      (S.Absurd (S.Irrelevant raw), []) -> pure (Absurd ty (S.Bottom, raw))
      (S.Global ref, args) -> do
        (Arguments domains values, proofs) <- arguments ctx args
        -- Reflection checks that explicit instantiations contain no index holes.
        _ <- traverse (reflectType . Ty.TData "#index" [] . pure . snd) is
        (types, indices) <- validateGlobal env slots ref (length proofs) is [sourceIndex argument | argument <- args, not (proofArgument argument)] (mapTypes forgetType domains) (forgetType ty)
        pure (Apply (Signature ref types indices domains ty) values proofs)
      _ -> Left "a non-first-order value at the explicit core boundary"
    proofArgument argument = case S.stripLocations argument of
      S.ProofArg {} -> True
      _ -> False
    sourceIndex = expressionIndex (\i -> Ty.IxVar . fst <$> listToMaybe (drop i variables))
    invocation :: List SType ctx -> SType t -> S.Expr Int -> [S.Expr Int] -> Either String (Value (Tm.ProofArgument Int) ctx t)
    invocation ctx expected callback [] = do
      SomeValue actual value <- infer ctx callback
      equal expected actual value
    invocation ctx expected callback args = do
      SomeValue callbackTy value <- infer ctx callback
      (domains, result) <- callbackSignature (forgetType callbackTy)
      (Arguments actual values, proofs) <- arguments ctx args
      unless (null proofs) $ Left "a callback application cannot take proof arguments"
      unless (domains == mapTypes forgetType actual && complete result == forgetType expected) $
        Left "a callback application disagrees with its checked signature"
      pure (Invoke expected value values)
    equal :: SType t -> SType u -> Value o ctx u -> Either String (Value o ctx t)
    equal expected actual v = case sameType expected actual of
      Just Refl -> Right v
      Nothing -> Left ("core type mismatch: expected " <> show (forgetType expected) <> ", got " <> show (forgetType actual))
    arguments :: List SType ctx -> [S.Expr Int] -> Either String (Arguments (Tm.ProofArgument Int) ctx, [Tm.ProofArgument Int])
    arguments _ [] = Right (Arguments Nil Nil, [])
    arguments ctx (a : as) = do
      (Arguments domains values, proofs) <- arguments ctx as
      case S.stripLocations a of
        S.ProofArg prop (S.Irrelevant raw)
          | all (\i -> i >= 0 && i < length (mapTypes (const ()) ctx)) (toList prop) ->
              pure (Arguments domains values, (prop, raw) : proofs)
          | otherwise -> Left "an out-of-scope variable in core evidence"
        _ -> do
          SomeValue ty v <- infer ctx a
          pure (Arguments (Cons ty domains) (Cons v values), proofs)
    variable :: List SType ctx -> Int -> Either String (SomeVariable ctx)
    variable Nil _ = Left "an out-of-scope core variable"
    variable (Cons t _) 0 = Right (SomeVariable t Here)
    variable (Cons _ ts) i | i > 0 = do
      SomeVariable t v <- variable ts (i - 1)
      pure (SomeVariable t (There v))
    variable _ _ = Left "a negative core variable"

-- Check global applications against the declaration environment before making
-- an intrinsically typed signature. In particular an annotation alone cannot
-- turn a numeral operation or an arbitrary name into a value of any type.
validateGlobal :: Env -> [Slot] -> S.Ref -> Int -> [(Int, Ty.Ix)] -> [Maybe Ty.Ix] -> [Ty.Ty] -> Ty.Ty -> Either String ([Ty.Ty], [(Int, Ty.Ix)])
validateGlobal env slots ref proofCount explicitIndices actualValues actual result = case S.refKind ref of
  S.RefBuiltin | S.refName ref == "S" -> check 0 (0, 0) [Ty.TNat] Ty.TNat
  S.RefBuiltin | S.refName ref `elem` ["add", "sub", "mul", "pow"] -> check 0 (0, 0) [Ty.TNat, Ty.TNat] Ty.TNat
  S.RefFunction -> case [f | GFun f <- globals, funCore f == S.refName ref] of
    f : _ -> do
      let scheme = funScheme f
          runtime = [snd (Ty.schemeValues scheme !! i) | i <- funRuntime f]
          offset = length runtime + funArity f
      dictionary <- traverse (dictionaryMethodType env (funSlots f)) (funSlots f)
      instantiated <- instantiateDictionary (funSlots f) (drop offset actualValues) (Ty.schemeType scheme : dictionary)
      case instantiated of
        signature : entries ->
          let (args, r) = arrows signature
           in check (length (funProofs f)) (length (Ty.schemeParams scheme), length (Ty.schemeValues scheme)) (runtime <> args <> entries) r
        [] -> Left "a dictionary lost its function signature"
    [] -> missing
  S.RefConstructor -> case [c | GCtor c <- globals, ctorCore c == S.refName ref] of
    c : _
      | Just d <- dataOfCtor env c ->
          let n = length (dataParams d)
              sig = ctorSignature c
           in check (length (constructorProofs sig)) (n, length (constructorTele sig)) (constructorValueTypes c) (Ty.TData (renderQualName (dataQual d)) [Ty.TParam i [] | i <- [0 .. n - 1]] (constructorResult sig))
    _ -> missing
  S.RefStatic -> case [s | (s, r) <- places, r == ref] of
    s : _ -> checkSlot s
    [] -> missing
  S.RefValueParam -> case [s | (s, r) <- places, r == ref] of
    s : _ -> checkSlot s
    [] -> missing
  _ -> missing
  where
    globals = Map.elems (envGlobals env)
    missing = Left ("an unknown value reference in the explicit core: " <> show ref)
    check required n ds r = do
      unless (proofCount == required) $ Left ("core evidence arity mismatch for " <> show ref)
      unless (length ds == length actual) $ Left ("core application arity mismatch for " <> show ref)
      let match a b s = maybe (Left ("core application type mismatch for " <> show ref <> ": " <> show a <> " against " <> show b)) Right (Ty.matchTy n a b s)
      let seed = Ty.emptyAssignment {Ty.asValues = IM.fromList [(i, x) | (i, x) <- explicitIndices, i >= 0, i < snd n]}
      initial <- match r result seed
      assignment <- foldM (\s (a, b) -> match a b s) initial (zip ds actual)
      unless (all Ty.firstOrder (IM.elems (Ty.asTypes assignment))) $ Left "type parameters cannot contain fixed callbacks"
      unless (Ty.firstOrder result) $ Left "a global value cannot return a fixed callback"
      pure ([complete (Ty.substScheme n assignment (Ty.TParam i [])) | i <- [0 .. fst n - 1]], IM.toList (Ty.asValues assignment))
    arrows (Ty.TArrow a b) = let (as, r) = arrows b in (a : as, r)
    arrows t = ([], t)
    places = place 1 0 slots
    place _ _ [] = []
    place i j (s : ss)
      | slotArity s > 0 = (s, S.Ref S.RefStatic (staticName i)) : place (i + 1) j ss
      | otherwise = (s, S.Ref S.RefValueParam (T.pack (show j))) : place i (j + 1 :: Int) ss
    checkSlot slot = do
      ty <- dictionaryMethodType env slots slot
      let (domains, r) = arrows ty
      check 0 (0, 0) domains r

-- Dictionary entries are closed static functions or closed nullary values.
-- Their captured dictionaries are checked against the instantiated slots;
-- no untyped application tree is accepted merely because it is annotated.
validateDictionary :: Env -> [Slot] -> Ty.Ty -> Tm.Term Void -> Either String ()
validateDictionary env slots expected = \case
  Tm.Call ref captures
    | Just _ <- lookup ref places -> do
        unless (null captures) $ Left "a dictionary place cannot capture arguments"
        let (ds, r) = arrows expected
        () <$ validateGlobal env slots ref 0 [] (replicate (length ds) Nothing) ds r
    | f : _ <- [f | GFun f <- Map.elems (envGlobals env), funCore f == S.refName ref] -> do
        let scheme = funScheme f
            arity = funArity f
            n = (length (Ty.schemeParams scheme), length (Ty.schemeValues scheme))
            correctRole = case S.refKind ref of
              S.RefStatic -> arity > 0 && null captures
              S.RefPartial a -> a == arity && arity > 0
              S.RefFunction -> arity == 0
              _ -> False
        unless (correctRole && length captures == length (funSlots f)) $ Left "a dictionary has the wrong static arity"
        dictionary <- traverse (dictionaryMethodType env (funSlots f)) (funSlots f)
        instantiated <- instantiateDictionary (funSlots f) (map (expressionIndex absurd . Tm.toExpr) captures) (Ty.schemeType scheme : dictionary)
        case instantiated of
          signature : entries -> do
            assignment <- maybe (Left "a dictionary implementation has the wrong type") Right (Ty.matchTy n signature expected Ty.emptyAssignment)
            sequence_ [validateDictionary env slots (Ty.substScheme n assignment ty) entry | (ty, entry) <- zip entries captures]
          [] -> Left "a dictionary lost its implementation signature"
    | otherwise -> Left ("an unknown dictionary reference: " <> show ref)
  _ -> Left "a dictionary entry must be a resolved reference"
  where
    arrows (Ty.TArrow a b) = let (as, r) = arrows b in (a : as, r)
    arrows t = ([], t)
    places = place 1 0 slots
    place _ _ [] = []
    place i j (slot : rest)
      | slotArity slot > 0 = (S.Ref S.RefStatic (staticName i), slot) : place (i + 1) j rest
      | otherwise = (S.Ref S.RefValueParam (T.pack (show j)), slot) : place i (j + 1 :: Int) rest

{- | Dictionary indices are tied to the actual value arguments. The typed
annotation alone never chooses a different cardinality for a dictionary.
-}
instantiateDictionary :: [Slot] -> [Maybe Ty.Ix] -> [Ty.Ty] -> Either String [Ty.Ty]
instantiateDictionary slots values types = do
  let used = [i | name <- concatMap (concatMap Ty.ixVars . Ty.tyIndices) types, Just i <- [T.stripPrefix "#d" name >>= readMaybe . T.unpack]]
      positions = [position | (position, slot) <- zip [0 ..] slots, slotArity slot == 0]
      at i = listToMaybe (drop i positions) >>= (\position -> listToMaybe (drop position values)) >>= id
  replacements <- traverse (\i -> maybe (Left "a dependent dictionary value has no checked index term") (Right . (i,)) (at i)) used
  let rewrite original@(Ty.IxVar name)
        | Just i <- T.stripPrefix "#d" name >>= readMaybe . T.unpack = maybe original id (lookup i replacements)
      rewrite (Ty.IxSucc x) = Ty.IxSucc (rewrite x)
      rewrite (Ty.IxCon name xs) = Ty.IxCon name (map rewrite xs)
      rewrite (Ty.IxFun name xs) = Ty.IxFun name (map rewrite xs)
      rewrite x = x
  pure (map (Ty.mapIx rewrite) types)

-- | The code denoted by a checked first-order source expression.
expressionIndex :: (a -> Maybe Ty.Ix) -> S.Expr a -> Maybe Ty.Ix
expressionIndex variable = go
  where
    go (S.At _ value) = go value
    go (S.Typed _ _ _ value) = go value
    go (S.Dictionary _ value) = go value
    go (S.Var value) = variable value
    go (S.Nat n) = Just (Ty.IxNat n)
    go expression = case S.spine expression of
      (S.Global (S.Ref S.RefValueParam name), []) -> Just (Ty.IxVar ("#d" <> name))
      (S.Global (S.Ref S.RefBuiltin "S"), [value]) -> Ty.IxSucc <$> go value
      (S.Global (S.Ref kind name), arguments)
        | kind `elem` [S.RefBuiltin, S.RefFunction, S.RefConstructor] ->
            (if kind == S.RefConstructor then Ty.IxCon else Ty.IxFun) name <$> traverse go arguments
      _ -> Nothing

complete :: Ty.Ty -> Ty.Ty
complete = \case
  Ty.THole -> Ty.TNat
  Ty.TParam n ts -> Ty.TParam n (map complete ts)
  Ty.TData n ts is -> Ty.TData n (map complete ts) (map Ty.normIx is)
  Ty.TArrow a b -> Ty.TArrow (complete a) (complete b)
  t -> t

number :: Variable ctx t -> Int
number Here = 0
number (There v) = 1 + number v

lower :: Value o ctx t -> Tm.Term Int
lower = \case
  Variable v -> Tm.Variable (number v)
  Literal n -> Tm.Literal n
  Apply (Signature r _ _ _ _) vs _ -> Tm.Call r (lowerArgs vs)
  Dictionary _ code -> fmap absurd code
  Callback _ code -> code
  Invoke _ callback arguments -> Tm.Invoke (lower callback) (lowerArgs arguments)
  Transport _ child _ -> lower child
  Absurd _ _ -> Tm.Literal 0
  where
    lowerArgs :: List (Value o ctx) ts -> [Tm.Term Int]
    lowerArgs Nil = []
    lowerArgs (Cons v vs) = lower v : lowerArgs vs

{- | Lower only the computation; the driver must certify every 'obligations'
entry before publishing the function's membership or index contracts.
-}
computation :: Body o -> Tm.Term Int
computation (Body _ _ v optimize) = optimize (lower v)
computation (EmptyBranch _) = Tm.Literal 0

obligations :: Body o -> [o]
obligations (EmptyBranch _) = []
obligations (Body _ _ v _) = evidence v
  where
    evidence :: Value o ctx t -> [o]
    evidence = \case
      Apply _ vs os -> children vs <> os
      Invoke _ callback args -> evidence callback <> children args
      Transport _ child os -> evidence child <> os
      Absurd _ o -> [o]
      _ -> []
    children :: List (Value o ctx) ts -> [o]
    children Nil = []
    children (Cons x xs) = evidence x <> children xs

mapObligations :: (o -> p) -> Body o -> Body p
mapObligations f = runIdentity . traverseObligations (Identity . f)

{- | Translate every evidence object without changing the typed computation.
The checking driver uses this to replace scoped proof obligations by the
certificates which discharge them.
-}
traverseObligations :: forall f o p. (Applicative f) => (o -> f p) -> Body o -> f (Body p)
traverseObligations _ (EmptyBranch ty) = pure (EmptyBranch ty)
traverseObligations f (Body ctx t value optimize) = (\v -> Body ctx t v optimize) <$> go value
  where
    go :: Value o ctx t -> f (Value p ctx t)
    go = \case
      Variable x -> pure (Variable x)
      Literal n -> pure (Literal n)
      Apply s vs os -> Apply s <$> args vs <*> traverse f os
      Dictionary ty code -> pure (Dictionary ty code)
      Callback ty code -> pure (Callback ty code)
      Invoke ty callback values -> Invoke ty <$> go callback <*> args values
      Transport ty child os -> Transport ty <$> go child <*> traverse f os
      Absurd ty o -> Absurd ty <$> f o
    args :: List (Value o ctx) ts -> f (List (Value p ctx) ts)
    args Nil = pure Nil
    args (Cons v vs) = Cons <$> go v <*> args vs

-- | Optimize lowered code while retaining the original typed term and evidence.
mapComputation :: (Tm.Term Int -> Tm.Term Int) -> Body o -> Body o
mapComputation _ (EmptyBranch ty) = EmptyBranch ty
mapComputation f (Body ctx t v opt) = Body ctx t v (f . opt)

bodyType :: Body o -> Ty.Ty
bodyType (Body _ t _ _) = forgetType t
bodyType (EmptyBranch t) = forgetType t

-- | A readable view of an anonymous body, with its explicit local context.
dump :: Body o -> Text
dump b = case b of
  EmptyBranch _ -> rendered
  Body ctx _ _ _ ->
    let binders = ["(v" <> T.pack (show i) <> " : " <> Pretty.typeText emptyEnv Pretty.emptyScope 0 ty <> ")" | (i, ty) <- zip [0 :: Int ..] (mapTypes forgetType ctx)]
     in if null binders then rendered else "\\" <> T.unwords binders <> " -> " <> rendered
  where
    rendered = "(" <> pretty emptyEnv Pretty.emptyScope (const "<evidence>") b <> " : " <> Pretty.typeText emptyEnv Pretty.emptyScope 0 (bodyType b) <> ")"

{- | Inspect the typed value before numerical lowering or dictionary pruning.
Evidence is rendered by its caller-supplied, certified declaration name.
-}
pretty :: forall o. Env -> Pretty.Scope -> (o -> Text) -> Body o -> Text
pretty _ _ _ (EmptyBranch _) = "unreachable"
pretty env sc proofName (Body _ _ value _) = term 0 value
  where
    term :: Int -> Value o ctx t -> Text
    term p = \case
      Variable v -> Pretty.nameAt "v" (Pretty.variableNames sc) (number v)
      Literal n -> T.pack (show n)
      Apply (Signature ref ts is _ _) values proofs ->
        let values' = arguments values
            (names, runtime, explicit, proofPositions) = layout ref
            -- A stored implicit value is printed once, in braces, using its
            -- actual computation (which may be a recovered index projection).
            indices = IM.union (IM.fromList [(i, values' !! j) | (i, j) <- runtime]) (IM.fromList [(i, Pretty.indexText sc 0 x) | (i, x) <- is, i `notElem` explicit])
            explicitValues = [x | (j, x) <- zip [0 ..] values', j `notElem` map snd runtime]
            evidence = ["[proof " <> proofName proof <> "]" | proof <- proofs]
            args =
              map (("@" <>) . Pretty.typeText env sc 11) ts
                <> ["{" <> Pretty.nameAt "i" names i <> " = " <> x <> "}" | (i, x) <- IM.toAscList indices]
                <> Pretty.interleave (zip proofPositions evidence) explicitValues
                <> drop (length proofPositions) evidence
            flat = Pretty.application p (Pretty.reference ref) args
         in if p == 0 && T.length flat > 88
              then T.intercalate "\n  " (Pretty.reference ref : args)
              else flat
      Callback _ _ -> "[fixed callback]"
      Invoke _ callback values -> Pretty.application p (term 11 callback) (arguments values)
      Dictionary ty code -> "[dict (" <> dictionary code <> " : " <> Pretty.typeText env sc 0 (forgetType ty) <> ")]"
      Transport ty child proofs -> Pretty.parens (p > 0) ("transport " <> term 11 child <> " [" <> T.intercalate ", " (map proofName proofs) <> "] : " <> Pretty.typeText env sc 0 (forgetType ty))
      Absurd ty proof -> Pretty.parens (p > 0) ("absurd [proof " <> proofName proof <> "] : " <> Pretty.typeText env sc 0 (forgetType ty))
    arguments :: List (Value o ctx) ts -> [Text]
    arguments Nil = []
    arguments (Cons v vs) = term 11 v : arguments vs
    dictionary = \case
      Tm.Variable v -> absurd v
      Tm.Literal n -> T.pack (show n)
      Tm.Call r xs -> Pretty.application 0 (Pretty.reference r) ["[dict " <> dictionary x <> "]" | x <- xs]
      Tm.Parameter _ _ -> "[fixed callback]"
      Tm.Closure _ _ -> "[callback lambda]"
      Tm.PackedClosure _ _ _ -> "[callback closure]"
      Tm.Invoke _ _ -> "[callback application]"
    layout ref = case [g | g <- Map.elems (envGlobals env), matches ref g] of
      GFun f : _ -> (map fst (Ty.schemeValues (funScheme f)), zip (funRuntime f) [0 ..], [], map fst (funProofs f))
      GCtor c : _ ->
        let tele = constructorTele (ctorSignature c)
         in (map teName tele, [(i, j) | (i, TeleEntry _ _ (Stored j)) <- zip [0 ..] tele], [i | (i, TeleEntry _ _ (Explicit _)) <- zip [0 ..] tele], map fst (constructorProofs (ctorSignature c)))
      _ -> ([], [], [], [])
    matches ref = \case
      GFun f -> funCore f == S.refName ref
      GCtor c -> ctorCore c == S.refName ref
      _ -> False
