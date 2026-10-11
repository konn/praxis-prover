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

import Control.Monad (foldM, unless)
import Data.Bifunctor (first)
import Data.Foldable (toList)
import Data.Functor.Identity (Identity (..))
import Data.IntMap.Strict qualified as IM
import Data.Map.Strict qualified as Map
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
elaborate env slots tys expression = do
  Context ctx <- context tys
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
    infer _ (S.Nat n) = Right (SomeValue SNatural (Literal n))
    infer ctx (S.Var i) = do
      SomeVariable t v <- variable ctx i
      pure (SomeValue t (Variable v))
    infer _ (S.Dictionary t e) = do
      SomeType ty <- first (\message -> message <> " in " <> show t) (reflectType (complete t))
      p <- Tm.prepareTerm e
      code <- Tm.withoutObligations p
      closed <- traverse (const (Left "a dictionary contains a free value variable")) code
      validateDictionary env slots (forgetType ty) closed
      pure (SomeValue ty (Dictionary ty closed))
    infer _ _ = Left "a value without a checked type at the explicit core boundary"
    check :: List SType ctx -> SType t -> [Ty.Ty] -> [(Int, Ty.Ix)] -> S.Expr Int -> Either String (Value (Tm.ProofArgument Int) ctx t)
    check ctx ty _types is e = case S.spine e of
      (S.Var i, []) -> do
        SomeVariable actual v <- variable ctx i
        equal ty actual (Variable v)
      (S.Nat n, []) -> equal ty SNatural (Literal n)
      (S.Absurd (S.Irrelevant raw), []) -> pure (Absurd ty (S.Bottom, raw))
      (S.Global ref, args) -> do
        (Arguments domains values, proofs) <- arguments ctx args
        -- Reflection checks that explicit instantiations contain no index holes.
        _ <- traverse (reflectType . Ty.TData "#index" [] . pure . snd) is
        (types, indices) <- validateGlobal env slots ref (length proofs) is (mapTypes forgetType domains) (forgetType ty)
        pure (Apply (Signature ref types indices domains ty) values proofs)
      _ -> Left "a non-first-order value at the explicit core boundary"
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
validateGlobal :: Env -> [Slot] -> S.Ref -> Int -> [(Int, Ty.Ix)] -> [Ty.Ty] -> Ty.Ty -> Either String ([Ty.Ty], [(Int, Ty.Ix)])
validateGlobal env slots ref proofCount explicitIndices actual result = case S.refKind ref of
  S.RefBuiltin | S.refName ref == "S" -> check 0 (0, 0) [Ty.TNat] Ty.TNat
  S.RefBuiltin | S.refName ref `elem` ["add", "sub", "mul", "pow"] -> check 0 (0, 0) [Ty.TNat, Ty.TNat] Ty.TNat
  S.RefFunction -> case [f | GFun f <- globals, funCore f == S.refName ref] of
    f : _ ->
      let scheme = funScheme f
          (args, r) = arrows (Ty.schemeType scheme)
          runtime = [snd (Ty.schemeValues scheme !! i) | i <- funRuntime f]
       in check (length (funProofs f)) (length (Ty.schemeParams scheme), length (Ty.schemeValues scheme)) (runtime <> args <> map dictionaryType (funSlots f)) r
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
      pure ([complete (Ty.substScheme n assignment (Ty.TParam i [])) | i <- [0 .. fst n - 1]], IM.toList (Ty.asValues assignment))
    arrows (Ty.TArrow a b) = let (as, r) = arrows b in (a : as, r)
    arrows t = ([], t)
    places = place 1 0 slots
    place _ _ [] = []
    place i j (s : ss)
      | slotArity s > 0 = (s, S.Ref S.RefStatic (staticName i)) : place (i + 1) j ss
      | otherwise = (s, S.Ref S.RefValueParam (T.pack (show j))) : place i (j + 1 :: Int) ss
    dictionaryType slot
      | isMembershipSlot slot = Ty.TArrow (Ty.TParam (slotParam slot) []) Ty.TNat
      | Just (GMethod m) <- Map.lookup (slotMethod slot) (envGlobals env) =
          Ty.substScheme (length (Ty.schemeParams (methodScheme m)), 0) Ty.emptyAssignment {Ty.asTypes = IM.singleton 0 (Ty.TParam (slotParam slot) [])} (Ty.schemeType (methodScheme m))
      | otherwise = Ty.THole
    checkSlot slot = case Map.lookup (slotMethod slot) (envGlobals env) of
      Just (GMethod m) ->
        let sch = methodScheme m
            (ds, r) = arrows (Ty.substScheme (length (Ty.schemeParams sch), 0) Ty.emptyAssignment {Ty.asTypes = IM.singleton 0 (Ty.TParam (slotParam slot) [])} (Ty.schemeType sch))
         in check 0 (0, 0) ds r
      _ -> missing

-- Dictionary entries are closed static functions or closed nullary values.
-- Their captured dictionaries are checked against the instantiated slots;
-- no untyped application tree is accepted merely because it is annotated.
validateDictionary :: Env -> [Slot] -> Ty.Ty -> Tm.Term Void -> Either String ()
validateDictionary env slots expected = \case
  Tm.Call ref captures
    | Just _ <- lookup ref places -> do
        unless (null captures) $ Left "a dictionary place cannot capture arguments"
        let (ds, r) = arrows expected
        () <$ validateGlobal env slots ref 0 [] ds r
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
        assignment <- maybe (Left "a dictionary implementation has the wrong type") Right (Ty.matchTy n (Ty.schemeType scheme) expected Ty.emptyAssignment)
        sequence_ [validateDictionary env slots (Ty.substScheme n assignment (slotType slot)) entry | (slot, entry) <- zip (funSlots f) captures]
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
    slotType slot
      | isMembershipSlot slot = Ty.TArrow (Ty.TParam (slotParam slot) []) Ty.TNat
      | Just (GMethod method) <- Map.lookup (slotMethod slot) (envGlobals env) =
          let scheme = methodScheme method
           in Ty.substScheme (length (Ty.schemeParams scheme), 0) Ty.emptyAssignment {Ty.asTypes = IM.singleton 0 (Ty.TParam (slotParam slot) [])} (Ty.schemeType scheme)
      | otherwise = Ty.THole

complete :: Ty.Ty -> Ty.Ty
complete = \case
  Ty.THole -> Ty.TNat
  Ty.TParam n ts -> Ty.TParam n (map complete ts)
  Ty.TData n ts is -> Ty.TData n (map complete ts) is
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
    let binders = ["(v" <> T.pack (show i) <> " : " <> Pretty.typeText Pretty.emptyScope 0 ty <> ")" | (i, ty) <- zip [0 :: Int ..] (mapTypes forgetType ctx)]
     in if null binders then rendered else "\\" <> T.unwords binders <> " -> " <> rendered
  where
    rendered = "(" <> pretty emptyEnv Pretty.emptyScope (const "<evidence>") b <> " : " <> Pretty.typeText Pretty.emptyScope 0 (bodyType b) <> ")"

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
              map (("@" <>) . Pretty.typeText sc 11) ts
                <> ["{" <> Pretty.nameAt "i" names i <> " = " <> x <> "}" | (i, x) <- IM.toAscList indices]
                <> Pretty.interleave (zip proofPositions evidence) explicitValues
                <> drop (length proofPositions) evidence
            flat = Pretty.application p (Pretty.reference ref) args
         in if p == 0 && T.length flat > 88
              then T.intercalate "\n  " (Pretty.reference ref : args)
              else flat
      Dictionary ty code -> "[dict (" <> dictionary code <> " : " <> Pretty.typeText sc 0 (forgetType ty) <> ")]"
      Absurd ty proof -> Pretty.parens (p > 0) ("absurd [proof " <> proofName proof <> "] : " <> Pretty.typeText sc 0 (forgetType ty))
    arguments :: List (Value o ctx) ts -> [Text]
    arguments Nil = []
    arguments (Cons v vs) = term 11 v : arguments vs
    dictionary = \case
      Tm.Variable v -> absurd v
      Tm.Literal n -> T.pack (show n)
      Tm.Call r xs -> Pretty.application 0 (Pretty.reference r) ["[dict " <> dictionary x <> "]" | x <- xs]
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
