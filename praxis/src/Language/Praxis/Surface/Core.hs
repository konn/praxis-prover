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
  indexDependencies,
  mapObligations,
  traverseObligations,
  mapComputation,
  bodyType,
  dump,
  pretty,
) where

import Bound (Scope, Var (..), fromScope, instantiate)
import Control.Monad (foldM, unless, when)
import Data.Bifunctor (first)
import Data.Foldable (toList, traverse_)
import Data.Functor.Identity (Identity (..))
import Data.IntMap.Strict qualified as IM
import Data.List (nub)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Type.Equality ((:~:) (..))
import Data.Void (absurd)
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
data Signature args result = Signature S.Ref [Ty.Ty] [(Int, Ty.Ix)] (Set Text) (List SType args) (SType result)

data Value o ctx t where
  Variable :: Variable ctx t -> Value o ctx t
  Literal :: Natural -> Value o ctx 'Natural
  Apply :: Signature args t -> List (Value o ctx) args -> [o] -> Value o ctx t
  Dictionary :: SType t -> Tm.Term Int -> Set Text -> Value o ctx t
  Callback :: SType t -> Tm.Term Int -> Set Text -> Value o ctx t
  Invoke :: SType t -> Value o ctx u -> List (Value o ctx) args -> Set Text -> Value o ctx t
  Transport :: SType t -> Value o ctx u -> [o] -> Set Text -> Value o ctx t
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
elaborate env slots tys = elaborateNamed env slots [Ty.hiddenBinder ("v" <> T.pack (show i)) ty | (i, ty) <- zip [0 :: Int ..] tys]

{- | Check a closed body over the telescope binding it: the clause's variables,
outermost first, which the indices of the types refer to by 'Ty.IxBound' —
the clause being one binder group, the k-th variable is @IxBound 0 k@ at the
top of the body.  The telescope identifies the terms denoted by source type
indices by position; its hints are for display only.
-}
elaborateNamed :: Env -> [Slot] -> Ty.Telescope -> S.Expr Int -> Either String (Body (Tm.ProofArgument Int))
elaborateNamed env slots telescope = elaborateScoped env slots [(Ty.IxBound 0 k, b) | (k, b) <- zip [0 ..] telescope]

{- | A variable context as the body's positions see it: at each position, the
bound occurrence referring to the variable there from where the body is, and
its binder, the type as seen from there too.  At the top the positions are
the clause's; under a callback lambda the lambda's parameters come first, as
'S.SchemaClosure' flattens them, and the enclosing variables are one binder
group further out.
-}
type Scoped = [(Ty.Ix, Ty.Binder)]

elaborateScoped :: Env -> [Slot] -> Scoped -> S.Expr Int -> Either String (Body (Tm.ProofArgument Int))
elaborateScoped env slots variables expression = do
  Context ctx <- context (map (Ty.binderTy . snd) variables)
  SomeValue ty value <- infer ctx expression
  pure (Body ctx ty value id)
  where
    reflectChecked t = do
      let completed = complete t
      validateTy env completed
      first (\message -> message <> " in " <> show t) (reflectType completed)
    context [] = Right (Context Nil)
    context (t : ts) = do
      SomeType ty <- reflectChecked t
      Context rest <- context ts
      pure (Context (Cons ty rest))
    infer :: List SType ctx -> S.Expr Int -> Either String (SomeValue (Tm.ProofArgument Int) ctx)
    infer ctx (S.At _ e) = infer ctx e
    infer ctx (S.Typed t ts is e) = do
      SomeType ty <- reflectChecked t
      value <- check ctx ty (map complete ts) is e
      pure (SomeValue ty value)
    infer ctx (S.Transport target child proofs) = do
      SomeType ty <- reflectChecked target
      SomeValue actual value <- infer ctx child
      pairs <- maybe (Left "an index transport changes the type structure") Right (Ty.transportIndices (forgetType actual) (forgetType ty))
      converted <-
        traverse
          ( \(x, y) -> do
              (left, fromLeft) <- indexTerm x
              (right, fromRight) <- indexTerm y
              pure (S.Rel S.RelEq left right, fromLeft <> fromRight)
          )
          pairs
      let (expected, dependencies) = unzip converted
      evidence <- traverse transportProof proofs
      unless (map fst evidence == expected) $ Left "index transport evidence does not match its index equalities"
      pure (SomeValue ty (Transport ty value evidence (Set.unions dependencies)))
    infer ctx (S.SchemaParameter source ref child) = do
      SomeType ty <- reflectChecked source
      _ <- callbackSignature source
      i <- case S.stripLocations child of
        S.Var position -> Right position
        _ -> Left "a callback parameter must keep its original environment variable"
      SomeVariable actual _ <- variable ctx i
      unless (forgetType ty == forgetType actual) $ Left "a callback environment has the wrong source signature"
      -- The schema parameters are registered by the names the source writes for them, with their signatures as the
      -- clause's telescope states them: the variable holding the environment must be the one written by the name the
      -- reference is registered under, of that signature seen from here — under as many lambdas as its reference counts.
      let (reference, binder) = variables !! i
          depth = case reference of
            Ty.IxBound d _ -> d
            _ -> 0
          seen signature = iterate (Ty.mapIx Ty.liftIx) signature !! depth
      unless (any (\(name, known, signature) -> known == ref && Ty.writtenName binder == Just name && complete (seen signature) == forgetType ty) (envSchemas env)) $
        Left "an unknown callback parameter at the explicit core boundary"
      pure (SomeValue ty (Callback ty (Tm.Parameter ref (Tm.Variable i)) Set.empty))
    infer _ S.SchemaPacked {} = Left "an internal packed callback cannot be supplied as a source term"
    infer _ S.PredicatePacked {} = Left "an internal predicate cannot be supplied as a source term"
    infer _ (S.SchemaClosure source child) = do
      SomeType ty <- reflectChecked source
      (domains, result) <- callbackSignature source
      (hints, scope) <- case S.stripLocations child of
        S.Lam hs body -> Right (hs, body)
        _ -> Left "a callback closure must contain a lambda"
      let count = length domains
      unless (length hints == count) $ Left "a callback lambda has the wrong arity"
      -- Under the lambda, its parameters are the innermost binder group, at the positions in front, and the
      -- enclosing variables are one group further out, their types seen from under it.
      let under = Ty.mapIx Ty.liftIx
          binders = [(Ty.IxBound 0 i, Ty.hiddenBinder (S.hintText hint) (under domain)) | (i, (hint, domain)) <- zip [0 ..] (zip hints domains)]
          outer = [(Ty.liftIx ref, b {Ty.binderTy = under (Ty.binderTy b)}) | (ref, b) <- variables]
          opened = fmap (\case B i -> i; F i -> count + i) (fromScope scope)
      body <- elaborateScoped env slots (binders <> outer) opened
      unless (null (obligations body)) $ Left "proof obligations inside a callback lambda are not supported"
      -- The result as seen from under the lambda: the enclosing variables are one binder group further out there.
      unless (bodyType body == complete (under result)) $ Left "a callback lambda returns the wrong type"
      let closed = fmap (\i -> if i < count then B i else F (i - count)) (computation body)
      pure (SomeValue ty (Callback ty (Tm.Closure count closed) (indexDependencies body)))
    infer _ (S.Nat n) = Right (SomeValue SNatural (Literal n))
    infer ctx (S.Var i) = do
      SomeVariable t v <- variable ctx i
      unless (Ty.firstOrder (forgetType t)) $ Left "a callback variable requires its fixed schema identity"
      pure (SomeValue t (Variable v))
    infer _ (S.Dictionary t e) = do
      SomeType ty <- reflectChecked t
      p <- Tm.prepareTerm e
      code <- Tm.withoutObligations p
      dependencies <- validateDictionary env slots variables (forgetType ty) e
      pure (SomeValue ty (Dictionary ty code dependencies))
    infer _ _ = Left "a value without a checked type at the explicit core boundary"
    callbackSignature source = case arrows source of
      ([], _) -> Left "a callback needs a function signature"
      (domains, result)
        | all Ty.firstOrder (result : domains) -> Right (domains, result)
        | otherwise -> Left "callbacks take and return first-order values"
    arrows (Ty.TArrow a b) = let (rest, result) = arrows b in (a : rest, result)
    arrows t = ([], t)
    indexTerm ix = maybe (Left "an index transport has no scoped index term") Right (indexTermInWithDependencies env (scopedCtx variables) ix)
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
        let compArgs = [argument | argument <- args, not (proofArgument argument)]
        (types, indices, dependencies) <- validateGlobal env slots variables ref proofs is compArgs (mapTypes forgetType domains) (forgetType ty)
        pure (Apply (Signature ref types indices dependencies domains ty) values proofs)
      _ -> Left "a non-first-order value at the explicit core boundary"
    proofArgument argument = case S.stripLocations argument of
      S.ProofArg {} -> True
      _ -> False
    invocation :: List SType ctx -> SType t -> S.Expr Int -> [S.Expr Int] -> Either String (Value (Tm.ProofArgument Int) ctx t)
    invocation ctx expected callback [] = do
      SomeValue actual value <- infer ctx callback
      equal expected actual value
    invocation ctx expected callback args = do
      SomeValue callbackTy value <- infer ctx callback
      (domains, result) <- callbackSignature (forgetType callbackTy)
      (Arguments actual values, proofs) <- arguments ctx args
      unless (null proofs) $ Left "a callback application cannot take proof arguments"
      let actualTys = mapTypes forgetType actual
          expectedTy = forgetType expected
          resultTy = complete result
          (normDomains, depsDomains) = unzip (map (normalizeTypeIndices env) domains)
          (normActual, depsActual) = unzip (map (normalizeTypeIndices env) actualTys)
          (normResult, depsResult) = normalizeTypeIndices env resultTy
          (normExpected, depsExpected) = normalizeTypeIndices env expectedTy
      unless (normDomains == normActual && normResult == normExpected) $
        Left "a callback application disagrees with its checked signature"
      let deps = Set.unions (depsResult : depsExpected : depsDomains <> depsActual)
      pure (Invoke expected value values deps)
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

-- Check well-kindedness and index-arity of declared datatypes in the explicit core.
validateTy :: Env -> Ty.Ty -> Either String ()
validateTy env = validateTyWithKind env Ty.KType

validateTyWithKind :: Env -> Ty.Kind -> Ty.Ty -> Either String ()
validateTyWithKind env expected = \case
  Ty.TNat ->
    unless (expected == Ty.KType) $ Left "Nat used where a higher-kinded type was expected in explicit core"
  Ty.TArrow a b -> do
    unless (expected == Ty.KType) $ Left "function type used where a higher-kinded type was expected in explicit core"
    validateTyWithKind env Ty.KType a
    validateTyWithKind env Ty.KType b
  Ty.TParam _ ts ->
    traverse_ (validateTyAnyKind env) ts
  Ty.TData dn ts is -> case [d | GData d <- Map.elems (envGlobals env), renderQualName (dataQual d) == dn] of
    d : _ -> do
      let paramKinds = map snd (dataParams d)
      when (length ts > length paramKinds) $
        Left ("too many type arguments to " <> T.unpack dn <> " in explicit core")
      let (appliedKinds, remainingKinds) = splitAt (length ts) paramKinds
      sequence_ [validateTyWithKind env k t | (k, t) <- zip appliedKinds ts]
      let remaining = foldr Ty.KArrow Ty.KType remainingKinds
      unless (remaining == expected) $
        Left ("kind mismatch for " <> T.unpack dn <> " in explicit core")
      if expected == Ty.KType
        then
          unless (length is == length (dataIndices d)) $
            Left ("index arity mismatch for " <> T.unpack dn <> " in explicit core")
        else
          unless (null is && null (dataIndices d)) $
            Left ("indexed datatype " <> T.unpack dn <> " cannot be partially applied in explicit core")
    [] -> traverse_ (validateTyAnyKind env) ts
  Ty.THole -> Right ()

validateTyAnyKind :: Env -> Ty.Ty -> Either String ()
validateTyAnyKind env = \case
  Ty.TNat -> Right ()
  Ty.TArrow a b -> validateTyWithKind env Ty.KType a *> validateTyWithKind env Ty.KType b
  Ty.TParam _ ts -> traverse_ (validateTyAnyKind env) ts
  Ty.TData dn ts is -> case [d | GData d <- Map.elems (envGlobals env), renderQualName (dataQual d) == dn] of
    d : _ -> do
      let paramKinds = map snd (dataParams d)
      when (length ts > length paramKinds) $
        Left ("too many type arguments to " <> T.unpack dn <> " in explicit core")
      let (appliedKinds, remainingKinds) = splitAt (length ts) paramKinds
      sequence_ [validateTyWithKind env k t | (k, t) <- zip appliedKinds ts]
      if null remainingKinds
        then
          unless (length is == length (dataIndices d)) $
            Left ("index arity mismatch for " <> T.unpack dn <> " in explicit core")
        else
          unless (null is && null (dataIndices d)) $
            Left ("indexed datatype " <> T.unpack dn <> " cannot be partially applied in explicit core")
    [] -> traverse_ (validateTyAnyKind env) ts
  Ty.THole -> Right ()

placeSlots :: [Slot] -> [(Slot, S.Ref)]
placeSlots = go 1 0
  where
    go _ _ [] = []
    go i j (s : ss)
      | slotArity s > 0 = (s, S.Ref S.RefStatic (staticName i)) : go (i + 1) j ss
      | otherwise = (s, S.Ref S.RefValueParam (T.pack (show j))) : go i (j + 1 :: Int) ss

methodExtraKinds :: Env -> Slot -> [Ty.Kind]
methodExtraKinds env slot = case Map.lookup (slotMethod slot) (envGlobals env) of
  Just (GMethod m) -> map snd (drop 1 (Ty.schemeParams (methodScheme m)))
  _ -> []

ixParamsOf :: Ty.Ix -> [Int]
ixParamsOf = \case
  Ty.IxParam i -> [i]
  Ty.IxSucc x -> ixParamsOf x
  Ty.IxCon _ xs -> concatMap ixParamsOf xs
  Ty.IxFun _ xs -> concatMap ixParamsOf xs
  Ty.IxPartial _ _ _ xs -> concatMap ixParamsOf xs
  _ -> []

unshiftTypeParams :: Int -> Ty.Ty -> Either String Ty.Ty
unshiftTypeParams 0 t = Right t
unshiftTypeParams d t = go t
  where
    go (Ty.TParam i ts)
      | i >= d = Ty.TParam (i - d) <$> traverse go ts
      | otherwise = Left "escaping method type parameter in explicit core"
    go (Ty.TData n ts is) = (\ts' -> Ty.TData n ts' is) <$> traverse go ts
    go (Ty.TArrow a b) = Ty.TArrow <$> go a <*> go b
    go other = Right other

-- Map a slot's dictionaryMethodScheme (where method-local params are 0..extra-1
-- and enclosing params are extra + p) into a combined scheme where enclosing
-- params remain 0..base-1 and this slot's method-local params sit at
-- slotOffset..slotOffset+extra-1.
remapSlotScheme :: Int -> Int -> Ty.Ty -> Ty.Ty
remapSlotScheme extra slotOffset = go
  where
    go (Ty.TParam i ts)
      | i < extra = Ty.TParam (slotOffset + i) (map go ts)
      | otherwise = Ty.TParam (i - extra) (map go ts)
    go (Ty.TData n ts is) = Ty.TData n (map go ts) is
    go (Ty.TArrow a b) = Ty.TArrow (go a) (go b)
    go other = other

data ProofSlotInfo
  = BoundSlot (S.Expr Int) Int
  | ProofOnlySlot Slot Int Ty.Ty

-- Check global applications against the declaration environment before making
-- an intrinsically typed signature. In particular an annotation alone cannot
-- turn a numeral operation or an arbitrary name into a value of any type.
validateGlobal :: Env -> [Slot] -> Scoped -> S.Ref -> [Tm.ProofArgument Int] -> [(Int, Ty.Ix)] -> [S.Expr Int] -> [Ty.Ty] -> Ty.Ty -> Either String ([Ty.Ty], [(Int, Ty.Ix)], Set Text)
validateGlobal env slots variables ref proofs explicitIndices compArgs actual result = case S.refKind ref of
  S.RefBuiltin | S.refName ref == "S" -> check 0 (0, 0) [] [Ty.TNat] Ty.TNat
  S.RefBuiltin | S.refName ref `elem` ["add", "sub", "mul", "pow"] -> check 0 (0, 0) [] [Ty.TNat, Ty.TNat] Ty.TNat
  S.RefFunction -> case [f | GFun f <- globals, funCore f == S.refName ref] of
    f : _ -> case [(d, j) | GData d <- globals, (j, q) <- zip [0 ..] (dataIndexFns d), q == funQual f] of
      (d, j) : _ -> do
        unless (null proofs) $ Left ("core evidence arity mismatch for " <> show ref)
        case actual of
          [Ty.TData dn ts indices]
            | dn == renderQualName (dataQual d)
            , length ts == length (dataParams d)
            , length indices == length (dataIndices d) -> do
                let n = (length (dataParams d), length (dataIndices d))
                    assignment = Ty.Assignment (IM.fromList (zip [0 ..] ts)) (IM.fromList (zip [0 ..] indices))
                    projected = Ty.substScheme n assignment (dataIndices d !! j)
                    (normProj, depsProj) = normalizeTypeIndices env projected
                    (normRes, depsRes) = normalizeTypeIndices env result
                unless (normProj == normRes) $
                  Left ("core index projection type mismatch for " <> show ref <> ": " <> show normProj <> " against " <> show normRes)
                unless (all Ty.firstOrder ts) $ Left "type parameters cannot contain fixed callbacks"
                unless (Ty.firstOrder result) $ Left "a global value cannot return a fixed callback"
                pure (map complete ts, [], depsProj <> depsRes)
          _ -> Left ("core index projection argument mismatch for " <> show ref)
      [] -> do
        let scheme = funScheme f
            baseParams = length (Ty.schemeParams scheme)
            valCount = length (Ty.schemeValues scheme)
            runtime = [snd (Ty.schemeValues scheme !! i) | i <- funRuntime f]
            offset = length runtime + funArity f
            dictArgs = drop offset compArgs
        rawSlots <- traverse (dictionaryMethodScheme env (funSlots f)) (funSlots f)
        let (slotRanges, remappedDicts, totalParams) =
              foldl
                ( \(ranges, tys, next) (slot, (extra, rawTy)) ->
                    let remapped = remapSlotScheme extra next rawTy
                     in (ranges <> [(slot, next, extra)], tys <> [remapped], next + extra)
                )
                ([], [], baseParams)
                (zip (funSlots f) rawSlots)
            slotKinds = concat [methodExtraKinds env slot | slot <- funSlots f]
            allKinds = map snd (Ty.schemeParams scheme) <> slotKinds
        instantiated <- instantiateDictionary (funSlots f) (drop offset actualValues) (Ty.schemeType scheme : remappedDicts)
        captured <- sequence [maybe (Left "a runtime argument has no scoped index") (Right . (i,)) value | (i, value) <- zip (funRuntime f) actualValues]
        case instantiated of
          signature : entries -> do
            let (args, r) = arrows signature
            (allTypes, indices, assignment, deps) <- checkWithSolve captured (length (funProofs f)) (totalParams, valCount) allKinds (runtime <> args <> entries) r actual result
            let funTypes = take baseParams allTypes
            -- For polymorphic dictionary slots, verify each method-local type parameter
            -- stayed parametric (matched a distinct rigid TParam not occurring in the class type).
            sequence_
              [ do
                  let classTy = complete (Ty.substScheme (totalParams, valCount) assignment (Ty.TParam (slotParam slot) []))
                      forbidden = Ty.tyParams classTy
                  params <-
                    traverse
                      ( \j -> case IM.lookup j (Ty.asTypes assignment) of
                          Just (Ty.TParam p []) | p `notElem` forbidden -> Right p
                          _ -> Left ("polymorphic dictionary method is not parametric for " <> show ref)
                      )
                      [start .. start + extra - 1]
                  unless (length params == length (nub params)) $
                    Left ("polymorphic dictionary method conflates distinct type parameters for " <> show ref)
              | (slot, start, extra) <- slotRanges
              , extra > 0
              ]
            proofDeps <- verifyFunctionProofs f assignment funTypes dictArgs
            pure (funTypes, indices, deps <> proofDeps)
          [] -> Left "a dictionary lost its function signature"
    [] -> missing
  S.RefConstructor -> case [c | GCtor c <- globals, ctorCore c == S.refName ref] of
    c : _
      | Just d <- dataOfCtor env c -> do
          -- Lower the uniform constructor at its defining indices. Any
          -- other instantiation needs a Transport with the exact equality
          -- evidence checked above; an annotation cannot supply it.
          let n = length (dataParams d)
              sig = ctorSignature c
              tele = constructorTele sig
              referenced =
                Set.fromList
                  ( concatMap ixParamsOf (constructorIndices sig <> concatMap (Ty.tyIndices . teType) tele)
                      <> [i | (_, prop) <- constructorProofs sig, B i <- toList (fromScope prop)]
                  )
              runtimePositions =
                [ (i, pos)
                | (i, entry) <- zip [0 ..] tele
                , pos <- case teRole entry of
                    Stored k -> [k]
                    Explicit k | i `Set.member` referenced -> [k]
                    _ -> []
                ]
          captured <-
            sequence
              [ maybe
                  (Left "a constructor index argument has no scoped index")
                  (Right . (i,))
                  (listToMaybe (drop pos actualValues) >>= id)
              | (i, pos) <- runtimePositions
              ]
          let paramKinds = map snd (dataParams d)
          (types, indices, assignment, deps) <-
            checkWithSolve
              captured
              (length (constructorProofs sig))
              (n, length tele)
              paramKinds
              (constructorValueTypes c)
              (Ty.TData (renderQualName (dataQual d)) [Ty.TParam i [] | i <- [0 .. n - 1]] (constructorIndices sig))
              actual
              result
          proofDeps <- verifyConstructorProofs sig assignment
          pure (types, indices, deps <> proofDeps)
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
    actualValues = map (expressionIndex env variables) compArgs
    missing = Left ("an unknown value reference in the explicit core: " <> show ref)
    places = placeSlots slots
    check required n kinds ds r = do
      (types, indices, _, deps) <- checkWithSolve [] required n kinds ds r actual result
      pure (types, indices, deps)
    checkWithSolve captured required n kinds ds r actualTys resultTy = do
      unless (length proofs == required) $ Left ("core evidence arity mismatch for " <> show ref)
      unless (length ds == length actualTys) $ Left ("core application arity mismatch for " <> show ref)
      let normalizedType = fst . normalizeTypeIndices env
          normalizedIndex = fst . normalizeIndex env
          dependencies = Set.unions (map (snd . normalizeTypeIndices env) (r : resultTy : ds <> actualTys) <> map (snd . normalizeIndex env . snd) (explicitIndices <> captured))
          match a b s = maybe (Left ("core application type mismatch for " <> show ref <> ": " <> show a <> " against " <> show b)) Right (Ty.matchTyStrict n (normalizedType a) (normalizedType b) s)
      let stated = IM.fromList [(i, normalizedIndex x) | (i, x) <- explicitIndices, i >= 0, i < snd n]
      indices <-
        foldM
          ( \known (i, x) -> case IM.lookup i known of
              Nothing -> Right (IM.insert i x known)
              Just y -> maybe (Left "a runtime argument disagrees with its stated index") (\value -> Right (IM.insert i value known)) (Ty.mergeIx x y)
          )
          stated
          [(i, normalizedIndex x) | (i, x) <- captured]
      let seed = Ty.emptyAssignment {Ty.asValues = indices}
      initial <- match r resultTy seed
      assignment <- foldM (\s (a, b) -> match a b s) initial (zip ds actualTys)
      unless (all Ty.firstOrder (IM.elems (Ty.asTypes assignment))) $ Left "type parameters cannot contain fixed callbacks"
      unless (Ty.firstOrder resultTy) $ Left "a global value cannot return a fixed callback"
      let solvedTypes = [complete (Ty.substScheme n assignment (Ty.TParam i [])) | i <- [0 .. fst n - 1]]
      sequence_ [validateTyWithKind env k t | (k, t) <- zip kinds solvedTypes]
      pure (solvedTypes, IM.toList (Ty.asValues assignment), assignment, dependencies)
    arrows (Ty.TArrow a b) = let (as, r) = arrows b in (a : as, r)
    arrows t = ([], t)
    checkSlot slot = do
      (extra, ty) <- dictionaryMethodScheme env slots slot
      let (domains, r) = arrows ty
          shiftedActual = map (Ty.shiftTypeParams extra) actual
          shiftedResult = Ty.shiftTypeParams extra result
      (shiftedTypes, indices, _, deps) <- checkWithSolve [] 0 (extra, 0) (methodExtraKinds env slot) domains r shiftedActual shiftedResult
      unshiftedTypes <- traverse (unshiftTypeParams extra) shiftedTypes
      pure (unshiftedTypes, indices, deps)
    verifyConstructorProofs sig assignment = do
      deps <-
        sequence
          [ do
              (expectedProp, idxDeps) <- instantiateProp assignment prop
              matchDeps <- matchProofExpr Map.empty expectedProp actualProp
              pure (idxDeps <> matchDeps)
          | ((_, prop), (actualProp, _)) <- zip (constructorProofs sig) proofs
          ]
      pure (Set.unions deps)
    verifyFunctionProofs f assignment funTypes dictArgs = do
      let proofSlots = funProofSlots f
          boundMap = zip (funSlots f) dictArgs
          freshBase = max (1 + maximum (-1 : concatMap Ty.tyParams (funTypes <> map (Ty.binderTy . snd) variables))) 0
      slotEntries <-
        sequence
          [ case lookup slot boundMap of
              Just dictExpr -> Right (slotRef, BoundSlot dictExpr (slotArity slot))
              Nothing -> do
                (extra, rawTy) <- dictionaryMethodScheme env proofSlots slot
                let mapping =
                      IM.fromList
                        ( [(k, Ty.TParam (freshBase + k) []) | k <- [0 .. extra - 1]]
                            <> [(extra + i, t) | (i, t) <- zip [0 ..] funTypes]
                        )
                    instTy = Ty.substScheme (extra + length funTypes, 0) Ty.emptyAssignment {Ty.asTypes = mapping} rawTy
                Right (slotRef, ProofOnlySlot slot extra instTy)
          | (slot, slotRef) <- placeSlots proofSlots
          , not (isMembershipSlot slot)
          ]
      let slotTable = Map.fromList slotEntries
      deps <-
        sequence
          [ do
              (expectedProp, idxDeps) <- instantiateProp assignment prop
              matchDeps <- matchProofExpr slotTable expectedProp actualProp
              pure (idxDeps <> matchDeps)
          | ((_, prop), (actualProp, _)) <- zip (funProofs f) proofs
          ]
      pure (Set.unions deps)
    instantiateProp assignment prop = do
      pairs <-
        traverse
          ( \i -> case IM.lookup i (Ty.asValues assignment) of
              Nothing -> Left ("a precondition index is undetermined for " <> show ref)
              Just ix -> case indexTermInWithDependencies env (scopedCtx variables) ix of
                Nothing -> Left ("a precondition index has no scoped term for " <> show ref)
                Just (term, deps) -> Right ((i, term), deps)
          )
          (nub [i | B i <- toList (fromScope prop)])
      let (terms, deps) = unzip pairs
      pure (instantiate (fromMaybe S.Hole . (`lookup` terms)) (fmap absurd prop), Set.unions deps)
    matchProofExpr slotTable = go Just id slotTable
      where
        unwrap = \case
          S.At _ e -> unwrap e
          S.Typed _ _ _ e -> unwrap e
          S.Dictionary _ e -> unwrap e
          S.Transport _ e _ -> unwrap e
          e -> e
        go :: forall a. (Eq a) => (a -> Maybe Int) -> (S.Expr Int -> S.Expr a) -> Map.Map S.Ref ProofSlotInfo -> S.Expr a -> S.Expr a -> Either String (Set Text)
        go toOuter liftOuter table expected0 actual0 =
          let expected = unwrap expected0
              actualExpr = unwrap actual0
              fallback = case (traverse toOuter expected, traverse toOuter actualExpr) of
                (Just e1, Just e2)
                  | Just ix1 <- expressionIndex env variables e1
                  , Just ix2 <- expressionIndex env variables e2
                  , let (n1, d1) = normalizeIndex env ix1
                        (n2, d2) = normalizeIndex env ix2
                  , n1 == n2 ->
                      Right (d1 <> d2)
                _ -> Left ("core precondition mismatch for " <> show ref)
              goScoped :: forall b. (Eq b) => Scope b S.Expr a -> Scope b S.Expr a -> Either String (Set Text)
              goScoped s1 s2 = go (\case B _ -> Nothing; F x -> toOuter x) (fmap F . liftOuter) table (fromScope s1) (fromScope s2)
           in case S.spine expected of
                (S.Global headRef, expArgs)
                  | Just info <- Map.lookup headRef table -> case info of
                      BoundSlot dictExpr arity
                        | length expArgs == arity && arity > 0 -> case S.spine dictExpr of
                            (S.Global target, []) -> case S.spine actualExpr of
                              (S.Global actHead, actArgs)
                                | actHead == target && length actArgs == arity ->
                                    Set.unions <$> sequence (zipWith (go toOuter liftOuter table) expArgs actArgs)
                              _ -> fallback
                            (S.Global (S.Ref _ fnCore), captures)
                              | g : _ <- [g | GFun g <- globals, funCore g == fnCore] ->
                                  let (prefix, suffix) = splitAt (length (funRuntime g)) captures
                                   in case S.spine actualExpr of
                                        (S.Global (S.Ref S.RefFunction actCore), actArgs)
                                          | actCore == fnCore && length actArgs == length prefix + arity + length suffix -> do
                                              let (actPrefix, rest) = splitAt (length prefix) actArgs
                                                  (actMid, actSuffix) = splitAt arity rest
                                              d1 <- sequence (zipWith (go toOuter liftOuter Map.empty) (map liftOuter prefix) actPrefix)
                                              d2 <- sequence (zipWith (go toOuter liftOuter table) expArgs actMid)
                                              d3 <- sequence (zipWith (go toOuter liftOuter Map.empty) (map liftOuter suffix) actSuffix)
                                              pure (Set.unions (d1 <> d2 <> d3))
                                        _ -> fallback
                            _ -> fallback
                        | null expArgs -> go toOuter liftOuter Map.empty (liftOuter dictExpr) actualExpr
                        | otherwise -> Left ("invalid dictionary slot arity in precondition for " <> show ref)
                      ProofOnlySlot slot _ expectedMethodTy
                        | length expArgs == slotArity slot && slotArity slot > 0 -> case S.spine actualExpr of
                            (S.Global target, actArgs)
                              | Just callerSlot <- lookup target [(r, s) | (s, r) <- places]
                              , slotMethod callerSlot == slotMethod slot
                              , length actArgs == slotArity slot -> do
                                  let dictTy = rewriteProofSlotDict env slots Nothing expectedMethodTy
                                  d0 <- validateDictionary env slots variables dictTy (S.Global target)
                                  ds <- sequence (zipWith (go toOuter liftOuter table) expArgs actArgs)
                                  pure (Set.unions (d0 : ds))
                            (S.Global (S.Ref S.RefFunction fnCore), actArgs)
                              | g : _ <- [g | GFun g <- globals, funCore g == fnCore]
                              , inst : _ <- [inst | inst <- Map.elems (envInstances env), fmap funQual (Map.lookup (slotMethod slot) (instFunctions inst)) == Just (funQual g)]
                              , let runtimeCount = length (funRuntime g)
                                    arity = funArity g
                              , arity == slotArity slot
                              , length actArgs == runtimeCount + arity + length (funSlots g) -> do
                                  let (actPrefix, rest) = splitAt runtimeCount actArgs
                                      (actMid, actSuffix) = splitAt arity rest
                                  prefixOuter <- maybe (Left "proof precondition dictionary capture escapes scope") Right (traverse (traverse toOuter) actPrefix)
                                  suffixOuter <- maybe (Left "proof precondition dictionary capture escapes scope") Right (traverse (traverse toOuter) actSuffix)
                                  let dictRef
                                        | runtimeCount > 0 = S.Ref (S.RefIndexedPartial arity runtimeCount) fnCore
                                        | not (null suffixOuter) = S.Ref (S.RefPartial arity) fnCore
                                        | otherwise = S.Ref S.RefStatic fnCore
                                      dictTy = rewriteProofSlotDict env slots (Just (inst, prefixOuter, suffixOuter)) expectedMethodTy
                                  d0 <- validateDictionary env slots variables dictTy (S.apps (S.Global dictRef) (prefixOuter <> suffixOuter))
                                  ds <- sequence (zipWith (go toOuter liftOuter table) expArgs actMid)
                                  pure (Set.unions (d0 : ds))
                            _ -> Left ("proof precondition dictionary mismatch for " <> show ref)
                        | null expArgs -> do
                            actualOuter <- maybe (Left "proof precondition dictionary escapes scope") Right (traverse toOuter actualExpr)
                            let dictTy = rewriteProofSlotDict env slots Nothing expectedMethodTy
                            validateDictionary env slots variables dictTy actualOuter
                        | otherwise -> Left ("invalid dictionary slot arity in precondition for " <> show ref)
                _ -> case (expected, actualExpr) of
                  (S.Var x, S.Var y) | x == y -> Right Set.empty
                  (S.Nat m, S.Nat n) | m == n -> Right Set.empty
                  (S.Global r1, S.Global r2) | r1 == r2 -> Right Set.empty
                  (S.App f1 x1, S.App f2 x2) -> case (go toOuter liftOuter table f1 f2, go toOuter liftOuter table x1 x2) of
                    (Right d1, Right d2) -> Right (d1 <> d2)
                    _ -> fallback
                  (S.Rel r1 a1 b1, S.Rel r2 a2 b2) | r1 == r2 -> (<>) <$> go toOuter liftOuter table a1 a2 <*> go toOuter liftOuter table b1 b2
                  (S.Conn c1 a1 b1, S.Conn c2 a2 b2) | c1 == c2 -> (<>) <$> go toOuter liftOuter table a1 a2 <*> go toOuter liftOuter table b1 b2
                  (S.Arrow a1 b1, S.Arrow a2 b2) -> (<>) <$> go toOuter liftOuter table a1 a2 <*> go toOuter liftOuter table b1 b2
                  (S.Not a1, S.Not a2) -> go toOuter liftOuter table a1 a2
                  (S.Top, S.Top) -> Right Set.empty
                  (S.Bottom, S.Bottom) -> Right Set.empty
                  (S.Universe, S.Universe) -> Right Set.empty
                  (S.Quant q1 _ bd1 ty1 b1, S.Quant q2 _ bd2 ty2 b2)
                    | q1 == q2 -> do
                        d1 <- case (bd1, bd2) of
                          (Nothing, Nothing) -> Right Set.empty
                          (Just (r1, t1), Just (r2, t2)) | r1 == r2 -> go toOuter liftOuter table t1 t2
                          _ -> Left ("core precondition quantifier bound mismatch for " <> show ref)
                        d2 <- case (ty1, ty2) of
                          (Nothing, Nothing) -> Right Set.empty
                          (Just t1, Just t2) -> go toOuter liftOuter table t1 t2
                          _ -> Left ("core precondition quantifier annotation mismatch for " <> show ref)
                        d3 <- goScoped b1 b2
                        pure (d1 <> d2 <> d3)
                  (S.If a1 b1 c1, S.If a2 b2 c2) -> do
                    d1 <- go toOuter liftOuter table a1 a2
                    d2 <- go toOuter liftOuter table b1 b2
                    d3 <- go toOuter liftOuter table c1 c2
                    pure (d1 <> d2 <> d3)
                  (S.Lam h1 b1, S.Lam h2 b2) | length h1 == length h2 -> goScoped b1 b2
                  (S.Case s1 as1, S.Case s2 as2)
                    | length as1 == length as2 && map fst as1 == map fst as2 -> do
                        d0 <- go toOuter liftOuter table s1 s2
                        ds <- sequence (zipWith (goScoped) (map snd as1) (map snd as2))
                        pure (Set.unions (d0 : ds))
                  (S.Pi _ i1 d1 b1, S.Pi _ i2 d2 b2) | i1 == i2 -> (<>) <$> go toOuter liftOuter table d1 d2 <*> goScoped b1 b2
                  (S.SchemaParameter _ r1 e1, S.SchemaParameter _ r2 e2) | r1 == r2 -> go toOuter liftOuter table e1 e2
                  (S.SchemaClosure _ e1, S.SchemaClosure _ e2) -> go toOuter liftOuter table e1 e2
                  (S.SchemaPacked h1 b1 e1, S.SchemaPacked h2 b2 e2) | length h1 == length h2 && b1 == b2 -> go toOuter liftOuter table e1 e2
                  (S.PredicatePacked h1 b1 es1, S.PredicatePacked h2 b2 es2)
                    | length h1 == length h2 && b1 == b2 && length es1 == length es2 ->
                        Set.unions <$> sequence (zipWith (go toOuter liftOuter table) es1 es2)
                  (S.ProofArg p1 _, S.ProofArg p2 _) -> go toOuter liftOuter table p1 p2
                  (S.Absurd _, S.Absurd _) -> Right Set.empty
                  _ -> fallback
    rewriteProofSlotDict _ _ _ ty = ty

-- Dictionary entries retain their runtime index captures in the current
-- value context. Check every captured value and dependent result against
-- the selected implementation before discarding its source annotations.
validateDictionary :: Env -> [Slot] -> Scoped -> Ty.Ty -> S.Expr Int -> Either String (Set Text)
validateDictionary env slots variables expected expression = case S.spine expression of
  (S.Global ref, captures)
    | Just _ <- lookup ref places -> do
        unless (null captures) $ Left "a dictionary place cannot capture arguments"
        let (ds, r) = arrows expected
        (_, _, dependencies) <- validateGlobal env slots variables ref [] [] [] ds r
        pure dependencies
    | f : _ <- [f | GFun f <- Map.elems (envGlobals env), funCore f == S.refName ref] -> do
        let scheme = funScheme f
            arity = funArity f
            runtimeCount = length (funRuntime f)
            (runtime, dictionaryCaptures) = splitAt runtimeCount captures
            n = (length (Ty.schemeParams scheme), length (Ty.schemeValues scheme))
            correctRole = case S.refKind ref of
              S.RefStatic -> arity > 0 && null captures && runtimeCount == 0
              S.RefPartial a -> a == arity && arity > 0 && runtimeCount == 0
              S.RefIndexedPartial a prefix -> a == arity && arity > 0 && prefix == runtimeCount
              S.RefFunction -> arity == 0
              _ -> False
        unless (correctRole && length captures == runtimeCount + length (funSlots f)) $ Left "a dictionary has the wrong static arity"
        when (arity > 0 && any openCapture captures) $
          Left "a static dictionary cannot capture scoped runtime values; pass a method whose runtime captures are closed"
        runtimeIndices <- traverse (maybe (Left "a dictionary runtime capture has no first-order index") Right . sourceIndex) runtime
        rawSlots <- traverse (dictionaryMethodScheme env (funSlots f)) (funSlots f)
        let freshBase = 1 + maximum (-1 : concatMap Ty.tyParams (expected : map (Ty.binderTy . snd) variables))
            shiftedRaw = [Ty.mapIx id rawTy | (_, rawTy) <- rawSlots]
        instantiated <- instantiateDictionary (funSlots f) (map sourceIndex dictionaryCaptures) (Ty.schemeType scheme : shiftedRaw)
        let normalizedType = fst . normalizeTypeIndices env
            normalizedIndex = fst . normalizeIndex env
            seed = Ty.emptyAssignment {Ty.asValues = IM.fromList (zip (funRuntime f) (map normalizedIndex runtimeIndices))}
        case instantiated of
          signature : entries -> do
            assignment <- maybe (Left "a dictionary implementation has the wrong type") Right (Ty.matchTyStrict n (normalizedType signature) (normalizedType expected) seed)
            let subFreshBase = max freshBase (1 + maximum (-1 : concatMap Ty.tyParams (IM.elems (Ty.asTypes assignment))))
            runtimeDependencies <-
              sequence
                [ do
                    body <- elaborateScoped env slots variables value
                    let required = complete (Ty.substScheme n assignment (snd (Ty.schemeValues scheme !! i)))
                    unless (null (obligations body) && normalizedType (bodyType body) == normalizedType required) $ Left "a dictionary runtime capture has the wrong type"
                    pure (indexDependencies body <> snd (normalizeTypeIndices env (bodyType body)) <> snd (normalizeTypeIndices env required))
                | (i, value) <- zip (funRuntime f) runtime
                ]
            dictionaryDependencies <-
              sequence
                [ let mapping =
                        IM.fromList
                          ( [(k, Ty.TParam (subFreshBase + k) []) | k <- [0 .. extra - 1]]
                              <> [(extra + i, Ty.substScheme n assignment (Ty.TParam i [])) | i <- [0 .. fst n - 1]]
                          )
                      subExpected = Ty.substScheme (extra + fst n, snd n) assignment {Ty.asTypes = mapping} ty
                   in validateDictionary env slots variables subExpected entry
                | ((extra, _), ty, entry) <- zip3 rawSlots entries dictionaryCaptures
                ]
            pure (Set.unions (runtimeDependencies <> dictionaryDependencies <> map (snd . normalizeIndex env) runtimeIndices <> map (snd . normalizeTypeIndices env) [signature, expected]))
          [] -> Left "a dictionary lost its implementation signature"
    | otherwise -> Left ("an unknown dictionary reference: " <> show ref)
  _ -> Left "a dictionary entry must be a resolved reference"
  where
    openCapture value =
      not (null (toList value)) || any ((== S.RefValueParam) . S.refKind) (S.globalsOf value)
    sourceIndex = expressionIndex env variables
    arrows (Ty.TArrow a b) = let (as, r) = arrows b in (a : as, r)
    arrows t = ([], t)
    places = [(r, s) | (s, r) <- placeSlots slots]

{- | Dictionary indices are tied to the actual value arguments. The typed
annotation alone never chooses a different cardinality for a dictionary.
-}
instantiateDictionary :: [Slot] -> [Maybe Ty.Ix] -> [Ty.Ty] -> Either String [Ty.Ty]
instantiateDictionary slots values types = do
  let used = concatMap (concatMap Ty.ixDicts . Ty.tyIndices) types
      positions = [position | (position, slot) <- zip [0 ..] slots, slotArity slot == 0]
      at i = listToMaybe (drop i positions) >>= (\position -> listToMaybe (drop position values)) >>= id
  replacements <- traverse (\i -> maybe (Left "a dependent dictionary value has no checked index term") (Right . (i,)) (at i)) used
  let rewrite original@(Ty.IxDict i) = fromMaybe original (lookup i replacements)
      rewrite (Ty.IxSucc x) = Ty.IxSucc (rewrite x)
      rewrite (Ty.IxCon name xs) = Ty.IxCon name (map rewrite xs)
      rewrite (Ty.IxFun name xs) = Ty.IxFun name (map rewrite xs)
      rewrite (Ty.IxPartial name arity prefix xs) = Ty.IxPartial name arity prefix (map rewrite xs)
      rewrite x = x
  pure (map (Ty.mapIx rewrite) types)

{- | The code denoted by a checked first-order source expression. An index
projection of a context variable denotes the index recorded in its checked
type; this uses the datatype's registered projection, never an annotation
placed on the expression being validated.
-}
expressionIndex :: Env -> Scoped -> S.Expr Int -> Maybe Ty.Ix
expressionIndex env variables = go
  where
    go (S.At _ value) = go value
    go (S.Typed _ _ _ value) = go value
    go (S.Dictionary _ value) = go value
    go (S.Transport _ value _) = go value
    go (S.Var position)
      | position >= 0 = fst <$> listToMaybe (drop position variables)
      | otherwise = Nothing
    go (S.Nat n) = Just (Ty.IxNat n)
    go expression
      | (S.Global (S.Ref S.RefFunction name), [child]) <- S.spine expression
      , S.Var position <- S.stripLocations child
      , position >= 0
      , Just (_, Ty.Binder _ _ (Ty.TData datatype _ indices)) <- listToMaybe (drop position variables)
      , Just projections <- indexFunctionCores env datatype
      , Just index <- lookup name (zip projections indices) =
          Just index
    go expression = case S.spine expression of
      (S.Global (S.Ref S.RefValueParam name), []) -> Ty.IxDict <$> readMaybe (T.unpack name)
      (S.Global (S.Ref S.RefStatic name), []) -> Just (Ty.IxSchema name)
      (S.Global (S.Ref (S.RefPartial arity) name), captures) -> Ty.IxPartial name arity 0 <$> traverse go captures
      (S.Global (S.Ref (S.RefIndexedPartial arity prefix) name), captures) -> Ty.IxPartial name arity prefix <$> traverse go captures
      (S.Global (S.Ref S.RefBuiltin "S"), [value]) -> Ty.IxSucc <$> go value
      (S.Global (S.Ref kind name), arguments)
        | kind `elem` [S.RefBuiltin, S.RefFunction, S.RefConstructor] ->
            (if kind == S.RefConstructor then Ty.IxCon else Ty.IxFun) name <$> traverse go arguments
      _ -> Nothing

-- | The variables of a body's positions as a context: each standing for the bound occurrence referring to it, the position its term variable.
scopedCtx :: Scoped -> Ctx Int
scopedCtx variables = [Local (Ty.writtenName b) (Ty.binderHint b) position (Ty.binderTy b) ref | (position, (ref, b)) <- zip [0 ..] variables]

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
  Apply (Signature r _ _ _ _ _) vs _ -> Tm.Call r (lowerArgs vs)
  Dictionary _ code _ -> code
  Callback _ code _ -> code
  Invoke _ callback arguments _ -> Tm.Invoke (lower callback) (lowerArgs arguments)
  Transport _ child _ _ -> lower child
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
      Invoke _ callback args _ -> evidence callback <> children args
      Transport _ child os _ -> evidence child <> os
      Absurd _ o -> [o]
      _ -> []
    children :: List (Value o ctx) ts -> [o]
    children Nil = []
    children (Cons x xs) = evidence x <> children xs

{- | Every provisional declaration used by index conversion at this explicit
boundary. Callers retain these as declaration prerequisites before erasing
source annotations, alongside the ordinary proof obligations.
-}
indexDependencies :: Body o -> Set Text
indexDependencies (EmptyBranch _) = Set.empty
indexDependencies (Body _ _ value _) = dependencies value
  where
    dependencies :: Value o ctx t -> Set Text
    dependencies = \case
      Apply (Signature _ _ _ used _ _) values _ -> used <> children values
      Dictionary _ _ used -> used
      Callback _ _ used -> used
      Invoke _ callback arguments' used -> used <> dependencies callback <> children arguments'
      Transport _ child _ used -> dependencies child <> used
      _ -> Set.empty
    children :: List (Value o ctx) ts -> Set Text
    children Nil = Set.empty
    children (Cons value' rest) = dependencies value' <> children rest

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
      Dictionary ty code dependencies -> pure (Dictionary ty code dependencies)
      Callback ty code dependencies -> pure (Callback ty code dependencies)
      Invoke ty callback values used -> (\c vs -> Invoke ty c vs used) <$> go callback <*> args values
      Transport ty child os dependencies -> (\value proofs -> Transport ty value proofs dependencies) <$> go child <*> traverse f os
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
      Apply (Signature ref ts is _ _ _) values proofs ->
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
      Callback _ _ _ -> "[fixed callback]"
      Invoke _ callback values _ -> Pretty.application p (term 11 callback) (arguments values)
      Dictionary ty code _ -> "[dict (" <> dictionary code <> " : " <> Pretty.typeText env sc 0 (forgetType ty) <> ")]"
      Transport ty child proofs _ -> Pretty.parens (p > 0) ("transport " <> term 11 child <> " [" <> T.intercalate ", " (map proofName proofs) <> "] : " <> Pretty.typeText env sc 0 (forgetType ty))
      Absurd ty proof -> Pretty.parens (p > 0) ("absurd [proof " <> proofName proof <> "] : " <> Pretty.typeText env sc 0 (forgetType ty))
    arguments :: List (Value o ctx) ts -> [Text]
    arguments Nil = []
    arguments (Cons v vs) = term 11 v : arguments vs
    dictionary = \case
      Tm.Variable i -> Pretty.nameAt "v" (Pretty.variableNames sc) i
      Tm.Literal n -> T.pack (show n)
      Tm.Call r xs -> Pretty.application 0 (Pretty.reference r) ["[dict " <> dictionary x <> "]" | x <- xs]
      Tm.Parameter _ _ -> "[fixed callback]"
      Tm.Closure _ _ -> "[callback lambda]"
      Tm.PackedClosure _ _ _ -> "[callback closure]"
      Tm.PackedPredicate _ _ _ -> "[membership predicate]"
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
