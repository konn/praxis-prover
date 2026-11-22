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
  CoreError (..),
  renderCoreError,
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
  Invoke ::
    -- | Checked return type of the callback application.
    SType t ->
    -- | Checked callback value (schema parameter or closure).
    Value o ctx u ->
    -- | Checked argument values passed to the callback.
    List (Value o ctx) args ->
    {- | Core names of projection functions unfolded by 'normalizeTypeIndices'
    when comparing callback domains/result against actual/expected types;
    collected by 'indexDependencies' as declaration prerequisites.
    -}
    Set Text ->
    Value o ctx t
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

-- | Structured errors raised when checking terms against the explicit value core boundary.
data CoreError
  = CoreReflectError !ReflectError !(Maybe Ty.Ty)
  | CoreEnvError !EnvError
  | CoreTermError !Tm.TermError
  | CoreTypeMismatch !Ty.Ty !Ty.Ty
  | CoreNatExpectedHigherKind !Ty.Kind
  | CoreArrowExpectedHigherKind !Ty.Kind
  | CoreTooManyTypeArguments !Text !Int !Int
  | CoreDataKindMismatch !Text !Ty.Kind !Ty.Kind
  | CoreIndexArityMismatch !Text !Int !Int
  | CorePartialIndexedData !Text
  | CoreOutOfScopeVariable !Int
  | CoreNegativeVariable !Int
  | CoreOutOfScopeEvidence
  | CoreEscapingMethodTypeParameter !Int
  | CoreUncheckedValue
  | CoreNonFirstOrderValue
  | CoreTransportChangesStructure !Ty.Ty !Ty.Ty
  | CoreTransportUnscopedIndex !Ty.Ix
  | CoreTransportEvidenceMismatch
  | CoreTransportInvalidProof
  | CoreCallbackNeedsFunctionSignature !Ty.Ty
  | CoreCallbackNotFirstOrder !Ty.Ty
  | CoreCallbackVariableRequiresSchema
  | CoreCallbackEnvironmentNotVariable
  | CoreCallbackWrongSignature !Ty.Ty !Ty.Ty
  | CoreCallbackUnknownParameter !S.Ref
  | CoreInternalPackedCallback
  | CoreInternalPackedPredicate
  | CoreCallbackRequiresLambda
  | CoreCallbackWrongArity !Int !Int
  | CoreCallbackLambdaHasObligations
  | CoreCallbackLambdaWrongResult !Ty.Ty !Ty.Ty
  | CoreCallbackInvocationProofs
  | CoreCallbackInvocationMismatch
  | CoreUnknownReference !S.Ref
  | CoreEvidenceArityMismatch !S.Ref !Int !Int
  | CoreApplicationArityMismatch !S.Ref !Int !Int
  | CoreApplicationTypeMismatch !S.Ref !Ty.Ty !Ty.Ty
  | CoreIndexProjectionTypeMismatch !S.Ref !Ty.Ty !Ty.Ty
  | CoreIndexProjectionArgMismatch !S.Ref
  | CoreRuntimeArgNoScopedIndex !S.Ref
  | CoreRuntimeArgIndexDisagreement !Int !Ty.Ix !Ty.Ix
  | CoreNonFirstOrderTypeParameter !S.Ref
  | CoreNonFirstOrderResult !S.Ref !Ty.Ty
  | CoreLostFunctionSignature !S.Ref
  | CorePolymorphicDictNotParametric !S.Ref
  | CorePolymorphicDictConflatesParams !S.Ref
  | CoreConstructorIndexArgMissing !S.Ref
  | CorePreconditionIndexUndetermined !S.Ref !Int
  | CorePreconditionIndexUnscoped !S.Ref !Ty.Ix
  | CorePreconditionMismatch !S.Ref
  | CorePreconditionQuantifierBoundMismatch !S.Ref
  | CorePreconditionQuantifierAnnotationMismatch !S.Ref
  | CorePreconditionInvalidSlotArity !S.Ref
  | CorePreconditionCaptureEscapes !S.Ref
  | CorePreconditionDictMismatch !S.Ref
  | CorePreconditionInvalidDepDictIndex !Int
  | CorePreconditionDepDictNoScopedIndex
  | CorePreconditionMissingCallerDepMethod
  | CorePreconditionMissingInstanceDepMethod
  | CorePreconditionMissingInstanceRuntimeCapture
  | CorePreconditionMissingInstanceDictCapture
  | CorePreconditionInstanceCaptureNoIndex
  | CoreDictPlaceCannotCapture !S.Ref
  | CoreDictWrongStaticArity !S.Ref
  | CoreDictOpenStaticCapture !S.Ref
  | CoreDictRuntimeCaptureNoIndex !S.Ref
  | CoreDictWrongType !S.Ref !Ty.Ty !Ty.Ty
  | CoreDictRuntimeCaptureWrongType !S.Ref !Ty.Ty !Ty.Ty
  | CoreDictLostSignature !S.Ref
  | CoreUnknownDictRef !S.Ref
  | CoreDictMustBeResolvedRef
  | CoreDependentDictNoIndex !Int
  deriving stock (Eq, Show)

-- | Render a 'CoreError' as a diagnostic message.
renderCoreError :: CoreError -> String
renderCoreError = \case
  CoreReflectError err Nothing -> renderReflectError err
  CoreReflectError err (Just t) -> renderReflectError err <> " in " <> show t
  CoreEnvError err -> renderEnvError err
  CoreTermError err -> Tm.renderTermError err
  CoreTypeMismatch expected actual -> "core type mismatch: expected " <> show expected <> ", got " <> show actual
  CoreNatExpectedHigherKind _ -> "Nat used where a higher-kinded type was expected in explicit core"
  CoreArrowExpectedHigherKind _ -> "function type used where a higher-kinded type was expected in explicit core"
  CoreTooManyTypeArguments dn _ _ -> "too many type arguments to " <> T.unpack dn <> " in explicit core"
  CoreDataKindMismatch dn _ _ -> "kind mismatch for " <> T.unpack dn <> " in explicit core"
  CoreIndexArityMismatch dn _ _ -> "index arity mismatch for " <> T.unpack dn <> " in explicit core"
  CorePartialIndexedData dn -> "indexed datatype " <> T.unpack dn <> " cannot be partially applied in explicit core"
  CoreOutOfScopeVariable _ -> "an out-of-scope core variable"
  CoreNegativeVariable _ -> "a negative core variable"
  CoreOutOfScopeEvidence -> "an out-of-scope variable in core evidence"
  CoreEscapingMethodTypeParameter _ -> "escaping method type parameter in explicit core"
  CoreUncheckedValue -> "a value without a checked type at the explicit core boundary"
  CoreNonFirstOrderValue -> "a non-first-order value at the explicit core boundary"
  CoreTransportChangesStructure _ _ -> "an index transport changes the type structure"
  CoreTransportUnscopedIndex _ -> "an index transport has no scoped index term"
  CoreTransportEvidenceMismatch -> "index transport evidence does not match its index equalities"
  CoreTransportInvalidProof -> "an index transport without scoped equality evidence"
  CoreCallbackNeedsFunctionSignature _ -> "a callback needs a function signature"
  CoreCallbackNotFirstOrder _ -> "callbacks take and return first-order values"
  CoreCallbackVariableRequiresSchema -> "a callback variable requires its fixed schema identity"
  CoreCallbackEnvironmentNotVariable -> "a callback parameter must keep its original environment variable"
  CoreCallbackWrongSignature _ _ -> "a callback environment has the wrong source signature"
  CoreCallbackUnknownParameter _ -> "an unknown callback parameter at the explicit core boundary"
  CoreInternalPackedCallback -> "an internal packed callback cannot be supplied as a source term"
  CoreInternalPackedPredicate -> "an internal predicate cannot be supplied as a source term"
  CoreCallbackRequiresLambda -> "a callback closure must contain a lambda"
  CoreCallbackWrongArity _ _ -> "a callback lambda has the wrong arity"
  CoreCallbackLambdaHasObligations -> "proof obligations inside a callback lambda are not supported"
  CoreCallbackLambdaWrongResult _ _ -> "a callback lambda returns the wrong type"
  CoreCallbackInvocationProofs -> "a callback application cannot take proof arguments"
  CoreCallbackInvocationMismatch -> "a callback application disagrees with its checked signature"
  CoreUnknownReference ref -> "an unknown value reference in the explicit core: " <> show ref
  CoreEvidenceArityMismatch ref _ _ -> "core evidence arity mismatch for " <> show ref
  CoreApplicationArityMismatch ref _ _ -> "core application arity mismatch for " <> show ref
  CoreApplicationTypeMismatch ref a b -> "core application type mismatch for " <> show ref <> ": " <> show a <> " against " <> show b
  CoreIndexProjectionTypeMismatch ref a b -> "core index projection type mismatch for " <> show ref <> ": " <> show a <> " against " <> show b
  CoreIndexProjectionArgMismatch ref -> "core index projection argument mismatch for " <> show ref
  CoreRuntimeArgNoScopedIndex _ -> "a runtime argument has no scoped index"
  CoreRuntimeArgIndexDisagreement {} -> "a runtime argument disagrees with its stated index"
  CoreNonFirstOrderTypeParameter _ -> "type parameters cannot contain fixed callbacks"
  CoreNonFirstOrderResult _ _ -> "a global value cannot return a fixed callback"
  CoreLostFunctionSignature _ -> "a dictionary lost its function signature"
  CorePolymorphicDictNotParametric ref -> "polymorphic dictionary method is not parametric for " <> show ref
  CorePolymorphicDictConflatesParams ref -> "polymorphic dictionary method conflates distinct type parameters for " <> show ref
  CoreConstructorIndexArgMissing _ -> "a constructor index argument has no scoped index"
  CorePreconditionIndexUndetermined ref _ -> "a precondition index is undetermined for " <> show ref
  CorePreconditionIndexUnscoped ref _ -> "a precondition index has no scoped term for " <> show ref
  CorePreconditionMismatch ref -> "core precondition mismatch for " <> show ref
  CorePreconditionQuantifierBoundMismatch ref -> "core precondition quantifier bound mismatch for " <> show ref
  CorePreconditionQuantifierAnnotationMismatch ref -> "core precondition quantifier annotation mismatch for " <> show ref
  CorePreconditionInvalidSlotArity ref -> "invalid dictionary slot arity in precondition for " <> show ref
  CorePreconditionCaptureEscapes _ -> "proof precondition dictionary capture escapes scope"
  CorePreconditionDictMismatch ref -> "proof precondition dictionary mismatch for " <> show ref
  CorePreconditionInvalidDepDictIndex _ -> "invalid dependent dictionary index in precondition"
  CorePreconditionDepDictNoScopedIndex -> "dependent dictionary argument has no scoped index"
  CorePreconditionMissingCallerDepMethod -> "proof precondition depends on a nullary class method missing from caller dictionary"
  CorePreconditionMissingInstanceDepMethod -> "proof precondition depends on a nullary class method missing from instance"
  CorePreconditionMissingInstanceRuntimeCapture -> "instance dependent method runtime capture missing from proof precondition"
  CorePreconditionMissingInstanceDictCapture -> "instance dependent method dictionary capture missing from proof precondition"
  CorePreconditionInstanceCaptureNoIndex -> "instance dependent method capture has no scoped index"
  CoreDictPlaceCannotCapture _ -> "a dictionary place cannot capture arguments"
  CoreDictWrongStaticArity _ -> "a dictionary has the wrong static arity"
  CoreDictOpenStaticCapture _ -> "a static dictionary cannot capture scoped runtime values; pass a method whose runtime captures are closed"
  CoreDictRuntimeCaptureNoIndex _ -> "a dictionary runtime capture has no first-order index"
  CoreDictWrongType {} -> "a dictionary implementation has the wrong type"
  CoreDictRuntimeCaptureWrongType {} -> "a dictionary runtime capture has the wrong type"
  CoreDictLostSignature _ -> "a dictionary lost its implementation signature"
  CoreUnknownDictRef ref -> "an unknown dictionary reference: " <> show ref
  CoreDictMustBeResolvedRef -> "a dictionary entry must be a resolved reference"
  CoreDependentDictNoIndex _ -> "a dependent dictionary value has no checked index term"

{- | A clause with a checked impossible pattern has no value term. Its result
type is retained, and PRA lowering must discharge the pattern's impossible
membership case. Zero is only the total numerical implementation of that
unreachable branch, never an inhabitant of its source result type.
-}
emptyBranch :: Ty.Ty -> Either CoreError (Body o)
emptyBranch ty = do
  SomeType result <- first (`CoreReflectError` Just ty) (reflectType (complete ty))
  pure (EmptyBranch result)

{- | Check annotations at the explicit boundary. Unconstrained, computationally
irrelevant type arguments are instantiated at Nat; value indices must be
determined. This instantiation is recorded in the core signature.
-}
elaborate :: Env -> [Slot] -> [Ty.Ty] -> S.Expr Int -> Either CoreError (Body (Tm.ProofArgument Int))
elaborate env slots tys = elaborateNamed env slots [Ty.hiddenBinder ("v" <> T.pack (show i)) ty | (i, ty) <- zip [0 :: Int ..] tys]

{- | Check a closed body over the telescope binding it: the clause's variables,
outermost first, which the indices of the types refer to by 'Ty.IxBound' —
the clause being one binder group, the k-th variable is @IxBound 0 k@ at the
top of the body.  The telescope identifies the terms denoted by source type
indices by position; its hints are for display only.
-}
elaborateNamed :: Env -> [Slot] -> Ty.Telescope -> S.Expr Int -> Either CoreError (Body (Tm.ProofArgument Int))
elaborateNamed env slots telescope = elaborateScoped env slots [(Ty.IxBound 0 k, b) | (k, b) <- zip [0 ..] telescope]

{- | A variable context as the body's positions see it: at each position, the
bound occurrence referring to the variable there from where the body is, and
its binder, the type as seen from there too.  At the top the positions are
the clause's; under a callback lambda the lambda's parameters come first, as
'S.SchemaClosure' flattens them, and the enclosing variables are one binder
group further out.
-}
type Scoped = [(Ty.Ix, Ty.Binder)]

elaborateScoped :: Env -> [Slot] -> Scoped -> S.Expr Int -> Either CoreError (Body (Tm.ProofArgument Int))
elaborateScoped env slots variables expression = do
  Context ctx <- context (map (Ty.binderTy . snd) variables)
  SomeValue ty value <- infer ctx expression
  pure (Body ctx ty value id)
  where
    reflectChecked t = do
      let completed = complete t
      validateTy env completed
      first (`CoreReflectError` Just t) (reflectType completed)
    context [] = Right (Context Nil)
    context (t : ts) = do
      SomeType ty <- reflectChecked t
      Context rest <- context ts
      pure (Context (Cons ty rest))
    infer :: List SType ctx -> S.Expr Int -> Either CoreError (SomeValue (Tm.ProofArgument Int) ctx)
    infer ctx (S.At _ e) = infer ctx e
    infer ctx (S.Typed t ts is e) = do
      SomeType ty <- reflectChecked t
      value <- check ctx ty (map complete ts) is e
      pure (SomeValue ty value)
    infer ctx (S.Transport target child proofs) = do
      SomeType ty <- reflectChecked target
      SomeValue actual value <- infer ctx child
      pairs <- maybe (Left (CoreTransportChangesStructure (forgetType actual) (forgetType ty))) Right (Ty.transportIndices (forgetType actual) (forgetType ty))
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
      unless (map fst evidence == expected) $ Left CoreTransportEvidenceMismatch
      pure (SomeValue ty (Transport ty value evidence (Set.unions dependencies)))
    infer ctx (S.SchemaParameter source ref child) = do
      SomeType ty <- reflectChecked source
      _ <- callbackSignature source
      i <- case S.stripLocations child of
        S.Var position -> Right position
        _ -> Left CoreCallbackEnvironmentNotVariable
      SomeVariable actual _ <- variable ctx i
      unless (forgetType ty == forgetType actual) $ Left (CoreCallbackWrongSignature (forgetType ty) (forgetType actual))
      let (reference, binder) = variables !! i
          depth = case reference of
            Ty.IxBound d _ -> d
            _ -> 0
          seen signature = iterate (Ty.mapIx Ty.liftIx) signature !! depth
      unless (any (\(name, known, signature) -> known == ref && Ty.writtenName binder == Just name && complete (seen signature) == forgetType ty) (envSchemas env)) $
        Left (CoreCallbackUnknownParameter ref)
      pure (SomeValue ty (Callback ty (Tm.Parameter ref (Tm.Variable i)) Set.empty))
    infer _ S.SchemaPacked {} = Left CoreInternalPackedCallback
    infer _ S.PredicatePacked {} = Left CoreInternalPackedPredicate
    infer _ (S.SchemaClosure source child) = do
      SomeType ty <- reflectChecked source
      (domains, result) <- callbackSignature source
      (hints, scope) <- case S.stripLocations child of
        S.Lam hs body -> Right (hs, body)
        _ -> Left CoreCallbackRequiresLambda
      let count = length domains
      unless (length hints == count) $ Left (CoreCallbackWrongArity count (length hints))
      let under = Ty.mapIx Ty.liftIx
          binders = [(Ty.IxBound 0 i, Ty.hiddenBinder (S.hintText hint) (under domain)) | (i, (hint, domain)) <- zip [0 ..] (zip hints domains)]
          outer = [(Ty.liftIx ref, b {Ty.binderTy = under (Ty.binderTy b)}) | (ref, b) <- variables]
          opened = fmap (\case B i -> i; F i -> count + i) (fromScope scope)
      body <- elaborateScoped env slots (binders <> outer) opened
      unless (null (obligations body)) $ Left CoreCallbackLambdaHasObligations
      unless (bodyType body == complete (under result)) $ Left (CoreCallbackLambdaWrongResult (complete (under result)) (bodyType body))
      let closed = fmap (\i -> if i < count then B i else F (i - count)) (computation body)
      pure (SomeValue ty (Callback ty (Tm.Closure count closed) (indexDependencies body)))
    infer _ (S.Nat n) = Right (SomeValue SNatural (Literal n))
    infer ctx (S.Var i) = do
      SomeVariable t v <- variable ctx i
      unless (Ty.firstOrder (forgetType t)) $ Left CoreCallbackVariableRequiresSchema
      pure (SomeValue t (Variable v))
    infer _ (S.Dictionary t e) = do
      SomeType ty <- reflectChecked t
      p <- first CoreTermError (Tm.prepareTerm e)
      code <- first CoreTermError (Tm.withoutObligations p)
      dependencies <- validateDictionary env slots variables (forgetType ty) e
      pure (SomeValue ty (Dictionary ty code dependencies))
    infer _ _ = Left CoreUncheckedValue
    callbackSignature source = case arrows source of
      ([], _) -> Left (CoreCallbackNeedsFunctionSignature source)
      (domains, result)
        | all Ty.firstOrder (result : domains) -> Right (domains, result)
        | otherwise -> Left (CoreCallbackNotFirstOrder source)
    arrows (Ty.TArrow a b) = let (rest, result) = arrows b in (a : rest, result)
    arrows t = ([], t)
    indexTerm ix = maybe (Left (CoreTransportUnscopedIndex ix)) Right (indexTermInWithDependencies env (scopedCtx variables) ix)
    transportProof e = case S.stripLocations e of
      S.ProofArg prop (S.Irrelevant raw)
        | all (\i -> i >= 0 && i < length variables) (toList prop) -> Right (prop, raw)
      _ -> Left CoreTransportInvalidProof
    check :: List SType ctx -> SType t -> [Ty.Ty] -> [(Int, Ty.Ix)] -> S.Expr Int -> Either CoreError (Value (Tm.ProofArgument Int) ctx t)
    check ctx ty _types is e = case S.spine e of
      (transport@S.Transport {}, []) -> do
        SomeValue actual value <- infer ctx transport
        equal ty actual value
      (callback@S.SchemaParameter {}, args) -> invocation ctx ty callback args
      (callback@S.SchemaClosure {}, args) -> invocation ctx ty callback args
      (S.Var i, []) -> do
        SomeVariable actual v <- variable ctx i
        unless (Ty.firstOrder (forgetType actual)) $ Left CoreCallbackVariableRequiresSchema
        equal ty actual (Variable v)
      (S.Nat n, []) -> equal ty SNatural (Literal n)
      (S.Absurd (S.Irrelevant raw), []) -> pure (Absurd ty (S.Bottom, raw))
      (S.Global ref, args) -> do
        (Arguments domains values, proofs) <- arguments ctx args
        _ <- traverse (\(_, ix) -> first (`CoreReflectError` Nothing) (reflectType (Ty.TData "#index" [] [ix]))) is
        let compArgs = [argument | argument <- args, not (proofArgument argument)]
        (types, indices, dependencies) <- validateGlobal env slots variables ref proofs is compArgs (mapTypes forgetType domains) (forgetType ty)
        pure (Apply (Signature ref types indices dependencies domains ty) values proofs)
      _ -> Left CoreNonFirstOrderValue
    proofArgument argument = case S.stripLocations argument of
      S.ProofArg {} -> True
      _ -> False
    invocation :: List SType ctx -> SType t -> S.Expr Int -> [S.Expr Int] -> Either CoreError (Value (Tm.ProofArgument Int) ctx t)
    invocation ctx expected callback [] = do
      SomeValue actual value <- infer ctx callback
      equal expected actual value
    invocation ctx expected callback args = do
      SomeValue callbackTy value <- infer ctx callback
      (domains, result) <- callbackSignature (forgetType callbackTy)
      (Arguments actual values, proofs) <- arguments ctx args
      unless (null proofs) $ Left CoreCallbackInvocationProofs
      let actualTys = mapTypes forgetType actual
          expectedTy = forgetType expected
          resultTy = complete result
          (normDomains, depsDomains) = unzip (map (normalizeTypeIndices env) domains)
          (normActual, depsActual) = unzip (map (normalizeTypeIndices env) actualTys)
          (normResult, depsResult) = normalizeTypeIndices env resultTy
          (normExpected, depsExpected) = normalizeTypeIndices env expectedTy
      unless (normDomains == normActual && normResult == normExpected) $
        Left CoreCallbackInvocationMismatch
      let deps = Set.unions (depsResult : depsExpected : depsDomains <> depsActual)
      pure (Invoke expected value values deps)
    equal :: SType t -> SType u -> Value o ctx u -> Either CoreError (Value o ctx t)
    equal expected actual v = case sameType expected actual of
      Just Refl -> Right v
      Nothing -> Left (CoreTypeMismatch (forgetType expected) (forgetType actual))
    arguments :: List SType ctx -> [S.Expr Int] -> Either CoreError (Arguments (Tm.ProofArgument Int) ctx, [Tm.ProofArgument Int])
    arguments _ [] = Right (Arguments Nil Nil, [])
    arguments ctx (a : as) = do
      (Arguments domains values, proofs) <- arguments ctx as
      case S.stripLocations a of
        S.ProofArg prop (S.Irrelevant raw)
          | all (\i -> i >= 0 && i < length (mapTypes (const ()) ctx)) (toList prop) ->
              pure (Arguments domains values, (prop, raw) : proofs)
          | otherwise -> Left CoreOutOfScopeEvidence
        _ -> do
          SomeValue ty v <- infer ctx a
          pure (Arguments (Cons ty domains) (Cons v values), proofs)
    variable :: List SType ctx -> Int -> Either CoreError (SomeVariable ctx)
    variable ctx0 i0 = go ctx0 i0
      where
        go :: List SType ctx' -> Int -> Either CoreError (SomeVariable ctx')
        go Nil _ = Left (CoreOutOfScopeVariable i0)
        go (Cons t _) 0 = Right (SomeVariable t Here)
        go (Cons _ ts) i | i > 0 = do
          SomeVariable t v <- go ts (i - 1)
          pure (SomeVariable t (There v))
        go _ i = Left (CoreNegativeVariable i)

-- Check well-kindedness and index-arity of declared datatypes in the explicit core.
validateTy :: Env -> Ty.Ty -> Either CoreError ()
validateTy env = validateTyWithKind env Ty.KType

validateTyWithKind :: Env -> Ty.Kind -> Ty.Ty -> Either CoreError ()
validateTyWithKind env expected = \case
  Ty.TNat ->
    unless (expected == Ty.KType) $ Left (CoreNatExpectedHigherKind expected)
  Ty.TArrow a b -> do
    unless (expected == Ty.KType) $ Left (CoreArrowExpectedHigherKind expected)
    validateTyWithKind env Ty.KType a
    validateTyWithKind env Ty.KType b
  Ty.TParam _ ts ->
    traverse_ (validateTyAnyKind env) ts
  Ty.TData dn ts is -> case lookupDataByName env dn of
    Just d -> do
      let paramKinds = map snd (dataParams d)
      when (length ts > length paramKinds) $
        Left (CoreTooManyTypeArguments dn (length paramKinds) (length ts))
      let (appliedKinds, remainingKinds) = splitAt (length ts) paramKinds
      sequence_ [validateTyWithKind env k t | (k, t) <- zip appliedKinds ts]
      let remaining = foldr Ty.KArrow Ty.KType remainingKinds
      unless (remaining == expected) $
        Left (CoreDataKindMismatch dn expected remaining)
      if expected == Ty.KType
        then
          unless (length is == length (dataIndices d)) $
            Left (CoreIndexArityMismatch dn (length (dataIndices d)) (length is))
        else
          unless (null is && null (dataIndices d)) $
            Left (CorePartialIndexedData dn)
    Nothing -> traverse_ (validateTyAnyKind env) ts
  Ty.THole -> Right ()

validateTyAnyKind :: Env -> Ty.Ty -> Either CoreError ()
validateTyAnyKind env = \case
  Ty.TNat -> Right ()
  Ty.TArrow a b -> validateTyWithKind env Ty.KType a *> validateTyWithKind env Ty.KType b
  Ty.TParam _ ts -> traverse_ (validateTyAnyKind env) ts
  Ty.TData dn ts is -> case lookupDataByName env dn of
    Just d -> do
      let paramKinds = map snd (dataParams d)
      when (length ts > length paramKinds) $
        Left (CoreTooManyTypeArguments dn (length paramKinds) (length ts))
      let (appliedKinds, remainingKinds) = splitAt (length ts) paramKinds
      sequence_ [validateTyWithKind env k t | (k, t) <- zip appliedKinds ts]
      if null remainingKinds
        then
          unless (length is == length (dataIndices d)) $
            Left (CoreIndexArityMismatch dn (length (dataIndices d)) (length is))
        else
          unless (null is && null (dataIndices d)) $
            Left (CorePartialIndexedData dn)
    Nothing -> traverse_ (validateTyAnyKind env) ts
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

unshiftTypeParams :: Int -> Ty.Ty -> Either CoreError Ty.Ty
unshiftTypeParams 0 t = Right t
unshiftTypeParams d t = go t
  where
    go (Ty.TParam i ts)
      | i >= d = Ty.TParam (i - d) <$> traverse go ts
      | otherwise = Left (CoreEscapingMethodTypeParameter i)
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

data ProofSlotSource
  = ProofSlotCaller Slot
  | ProofSlotInstance InstanceInfo FunInfo [S.Expr Int] [S.Expr Int]

-- Check global applications against the declaration environment before making
-- an intrinsically typed signature. In particular an annotation alone cannot
-- turn a numeral operation or an arbitrary name into a value of any type.
validateGlobal :: Env -> [Slot] -> Scoped -> S.Ref -> [Tm.ProofArgument Int] -> [(Int, Ty.Ix)] -> [S.Expr Int] -> [Ty.Ty] -> Ty.Ty -> Either CoreError ([Ty.Ty], [(Int, Ty.Ix)], Set Text)
validateGlobal env slots variables ref proofs explicitIndices compArgs actual result = case S.refKind ref of
  S.RefBuiltin | S.refName ref == "S" -> check 0 (0, 0) [] [Ty.TNat] Ty.TNat
  S.RefBuiltin | S.refName ref `elem` ["add", "sub", "mul", "pow"] -> check 0 (0, 0) [] [Ty.TNat, Ty.TNat] Ty.TNat
  S.RefFunction -> case [f | GFun f <- globals, funCore f == S.refName ref] of
    f : _ -> case lookupIndexFnOwner env (funQual f) of
      Just (d, j) -> do
        unless (null proofs) $ Left (CoreEvidenceArityMismatch ref 0 (length proofs))
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
                  Left (CoreIndexProjectionTypeMismatch ref normProj normRes)
                unless (all Ty.firstOrder ts) $ Left (CoreNonFirstOrderTypeParameter ref)
                unless (Ty.firstOrder result) $ Left (CoreNonFirstOrderResult ref result)
                pure (map complete ts, [], depsProj <> depsRes)
          _ -> Left (CoreIndexProjectionArgMismatch ref)
      Nothing -> do
        let scheme = funScheme f
            baseParams = length (Ty.schemeParams scheme)
            valCount = length (Ty.schemeValues scheme)
            runtime = [snd (Ty.schemeValues scheme !! i) | i <- funRuntime f]
            offset = length runtime + funArity f
            dictArgs = drop offset compArgs
        rawSlots <- first CoreEnvError (traverse (dictionaryMethodScheme env (funSlots f)) (funSlots f))
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
        captured <- sequence [maybe (Left (CoreRuntimeArgNoScopedIndex ref)) (Right . (i,)) value | (i, value) <- zip (funRuntime f) actualValues]
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
                          _ -> Left (CorePolymorphicDictNotParametric ref)
                      )
                      [start .. start + extra - 1]
                  unless (length params == length (nub params)) $
                    Left (CorePolymorphicDictConflatesParams ref)
              | (slot, start, extra) <- slotRanges
              , extra > 0
              ]
            proofDeps <- verifyFunctionProofs f assignment funTypes dictArgs
            pure (funTypes, indices, deps <> proofDeps)
          [] -> Left (CoreLostFunctionSignature ref)
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
                  (Left (CoreConstructorIndexArgMissing ref))
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
    missing = Left (CoreUnknownReference ref)
    places = placeSlots slots
    check required n kinds ds r = do
      (types, indices, _, deps) <- checkWithSolve [] required n kinds ds r actual result
      pure (types, indices, deps)
    checkWithSolve captured required n kinds ds r actualTys resultTy = do
      unless (length proofs == required) $ Left (CoreEvidenceArityMismatch ref required (length proofs))
      unless (length ds == length actualTys) $ Left (CoreApplicationArityMismatch ref (length ds) (length actualTys))
      let normalizedType = fst . normalizeTypeIndices env
          normalizedIndex = fst . normalizeIndex env
          dependencies = Set.unions (map (snd . normalizeTypeIndices env) (r : resultTy : ds <> actualTys) <> map (snd . normalizeIndex env . snd) (explicitIndices <> captured))
          match a b s = maybe (Left (CoreApplicationTypeMismatch ref a b)) Right (Ty.matchTyStrict n (normalizedType a) (normalizedType b) s)
      let stated = IM.fromList [(i, normalizedIndex x) | (i, x) <- explicitIndices, i >= 0, i < snd n]
      indices <-
        foldM
          ( \known (i, x) -> case IM.lookup i known of
              Nothing -> Right (IM.insert i x known)
              Just y -> maybe (Left (CoreRuntimeArgIndexDisagreement i x y)) (\value -> Right (IM.insert i value known)) (Ty.mergeIx x y)
          )
          stated
          [(i, normalizedIndex x) | (i, x) <- captured]
      let seed = Ty.emptyAssignment {Ty.asValues = indices}
      initial <- match r resultTy seed
      assignment <- foldM (\s (a, b) -> match a b s) initial (zip ds actualTys)
      unless (all Ty.firstOrder (IM.elems (Ty.asTypes assignment))) $ Left (CoreNonFirstOrderTypeParameter ref)
      unless (Ty.firstOrder resultTy) $ Left (CoreNonFirstOrderResult ref resultTy)
      let solvedTypes = [complete (Ty.substScheme n assignment (Ty.TParam i [])) | i <- [0 .. fst n - 1]]
      sequence_ [validateTyWithKind env k t | (k, t) <- zip kinds solvedTypes]
      pure (solvedTypes, IM.toList (Ty.asValues assignment), assignment, dependencies)
    arrows (Ty.TArrow a b) = let (as, r) = arrows b in (a : as, r)
    arrows t = ([], t)
    checkSlot slot = do
      (extra, ty) <- first CoreEnvError (dictionaryMethodScheme env slots slot)
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
              matchDeps <- matchProofExpr [] [] Map.empty expectedProp actualProp
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
                (extra, rawTy) <- first CoreEnvError (dictionaryMethodScheme env proofSlots slot)
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
              matchDeps <- matchProofExpr proofSlots boundMap slotTable expectedProp actualProp
              pure (idxDeps <> matchDeps)
          | ((_, prop), (actualProp, _)) <- zip (funProofs f) proofs
          ]
      pure (Set.unions deps)
    instantiateProp assignment prop = do
      pairs <-
        traverse
          ( \i -> case IM.lookup i (Ty.asValues assignment) of
              Nothing -> Left (CorePreconditionIndexUndetermined ref i)
              Just ix -> case indexTermInWithDependencies env (scopedCtx variables) ix of
                Nothing -> Left (CorePreconditionIndexUnscoped ref ix)
                Just (term, deps) -> Right ((i, term), deps)
          )
          (nub [i | B i <- toList (fromScope prop)])
      let (terms, deps) = unzip pairs
      pure (instantiate (fromMaybe S.Hole . (`lookup` terms)) (fmap absurd prop), Set.unions deps)
    matchProofExpr proofSlots boundMap slotTable = go Just id slotTable
      where
        unwrap = \case
          S.At _ e -> unwrap e
          S.Typed _ _ _ e -> unwrap e
          S.Dictionary _ e -> unwrap e
          S.Transport _ e _ -> unwrap e
          e -> e
        go :: forall a. (Eq a) => (a -> Maybe Int) -> (S.Expr Int -> S.Expr a) -> Map.Map S.Ref ProofSlotInfo -> S.Expr a -> S.Expr a -> Either CoreError (Set Text)
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
                _ -> Left (CorePreconditionMismatch ref)
              goScoped :: forall b. (Eq b) => Scope b S.Expr a -> Scope b S.Expr a -> Either CoreError (Set Text)
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
                        | otherwise -> Left (CorePreconditionInvalidSlotArity ref)
                      ProofOnlySlot slot _ expectedMethodTy
                        | length expArgs == slotArity slot && slotArity slot > 0 -> case S.spine actualExpr of
                            (S.Global target, actArgs)
                              | Just callerSlot <- lookup target [(r, s) | (s, r) <- places]
                              , slotMethod callerSlot == slotMethod slot
                              , length actArgs == slotArity slot -> do
                                  dictTy <- rewriteProofSlotDict proofSlots boundMap (ProofSlotCaller callerSlot) expectedMethodTy
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
                                  prefixOuter <- maybe (Left (CorePreconditionCaptureEscapes ref)) Right (traverse (traverse toOuter) actPrefix)
                                  suffixOuter <- maybe (Left (CorePreconditionCaptureEscapes ref)) Right (traverse (traverse toOuter) actSuffix)
                                  let dictRef
                                        | runtimeCount > 0 = S.Ref (S.RefIndexedPartial arity runtimeCount) fnCore
                                        | not (null suffixOuter) = S.Ref (S.RefPartial arity) fnCore
                                        | otherwise = S.Ref S.RefStatic fnCore
                                  dictTy <- rewriteProofSlotDict proofSlots boundMap (ProofSlotInstance inst g prefixOuter suffixOuter) expectedMethodTy
                                  d0 <- validateDictionary env slots variables dictTy (S.apps (S.Global dictRef) (prefixOuter <> suffixOuter))
                                  ds <- sequence (zipWith (go toOuter liftOuter table) expArgs actMid)
                                  pure (Set.unions (d0 : ds))
                            _ -> Left (CorePreconditionDictMismatch ref)
                        | null expArgs -> do
                            actualOuter <- maybe (Left (CorePreconditionCaptureEscapes ref)) Right (traverse toOuter actualExpr)
                            source <- case S.spine actualOuter of
                              (S.Global target, [])
                                | Just callerSlot <- lookup target [(r, s) | (s, r) <- places]
                                , slotMethod callerSlot == slotMethod slot ->
                                    Right (ProofSlotCaller callerSlot)
                              (S.Global (S.Ref _ fnCore), captures)
                                | g : _ <- [g | GFun g <- globals, funCore g == fnCore]
                                , inst : _ <- [inst | inst <- Map.elems (envInstances env), fmap funQual (Map.lookup (slotMethod slot) (instFunctions inst)) == Just (funQual g)] ->
                                    let (prefixOuter, suffixOuter) = splitAt (length (funRuntime g)) captures
                                     in Right (ProofSlotInstance inst g prefixOuter suffixOuter)
                              _ -> Left (CorePreconditionDictMismatch ref)
                            dictTy <- rewriteProofSlotDict proofSlots boundMap source expectedMethodTy
                            validateDictionary env slots variables dictTy actualOuter
                        | otherwise -> Left (CorePreconditionInvalidSlotArity ref)
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
                          _ -> Left (CorePreconditionQuantifierBoundMismatch ref)
                        d2 <- case (ty1, ty2) of
                          (Nothing, Nothing) -> Right Set.empty
                          (Just t1, Just t2) -> go toOuter liftOuter table t1 t2
                          _ -> Left (CorePreconditionQuantifierAnnotationMismatch ref)
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
                        ds <- sequence (zipWith goScoped (map snd as1) (map snd as2))
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
    rewriteProofSlotDict proofSlots boundMap source ty =
      let used = nub (concatMap Ty.ixDicts (Ty.tyIndices ty))
          nullaryProof = valueSlots proofSlots
          nullaryCaller = valueSlots slots
          resolveDict j = do
            depSlot <- maybe (Left (CorePreconditionInvalidDepDictIndex j)) Right (listToMaybe (drop j nullaryProof))
            case lookup depSlot boundMap of
              Just dictExpr ->
                maybe (Left CorePreconditionDepDictNoScopedIndex) Right (expressionIndex env variables dictExpr)
              Nothing -> case source of
                ProofSlotCaller callerSlot ->
                  case [k | (k, cs) <- zip [0 ..] nullaryCaller, slotMethod cs == slotMethod depSlot, slotParam cs == slotParam callerSlot] of
                    k : _ -> Right (Ty.IxDict k)
                    [] -> Left CorePreconditionMissingCallerDepMethod
                ProofSlotInstance inst g prefixOuter suffixOuter -> do
                  depFun <- maybe (Left CorePreconditionMissingInstanceDepMethod) Right (Map.lookup (slotMethod depSlot) (instFunctions inst))
                  depRuntime <-
                    traverse
                      ( \rIdx -> case lookup rIdx (zip (funRuntime g) prefixOuter) of
                          Just expr -> maybe (Left CorePreconditionInstanceCaptureNoIndex) Right (expressionIndex env variables expr)
                          Nothing -> Left CorePreconditionMissingInstanceRuntimeCapture
                      )
                      (funRuntime depFun)
                  depDicts <-
                    traverse
                      ( \dSlot -> case lookup dSlot (zip (funSlots g) suffixOuter) of
                          Just expr -> maybe (Left CorePreconditionInstanceCaptureNoIndex) Right (expressionIndex env variables expr)
                          Nothing -> Left CorePreconditionMissingInstanceDictCapture
                      )
                      (funSlots depFun)
                  Right (Ty.IxFun (funCore depFun) (depRuntime <> depDicts))
       in do
            replacements <- traverse (\j -> (j,) <$> resolveDict j) used
            let rewrite original@(Ty.IxDict j) = fromMaybe original (lookup j replacements)
                rewrite (Ty.IxSucc x) = Ty.IxSucc (rewrite x)
                rewrite (Ty.IxCon name xs) = Ty.IxCon name (map rewrite xs)
                rewrite (Ty.IxFun name xs) = Ty.IxFun name (map rewrite xs)
                rewrite (Ty.IxPartial name arity prefix xs) = Ty.IxPartial name arity prefix (map rewrite xs)
                rewrite x = x
            pure (Ty.mapIx rewrite ty)

-- Dictionary entries retain their runtime index captures in the current
-- value context. Check every captured value and dependent result against
-- the selected implementation before discarding its source annotations.
validateDictionary :: Env -> [Slot] -> Scoped -> Ty.Ty -> S.Expr Int -> Either CoreError (Set Text)
validateDictionary env slots variables expected expression = case S.spine expression of
  (S.Global ref, captures)
    | Just _ <- lookup ref places -> do
        unless (null captures) $ Left (CoreDictPlaceCannotCapture ref)
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
        unless (correctRole && length captures == runtimeCount + length (funSlots f)) $ Left (CoreDictWrongStaticArity ref)
        when (arity > 0 && any openCapture captures) $
          Left (CoreDictOpenStaticCapture ref)
        runtimeIndices <- traverse (maybe (Left (CoreDictRuntimeCaptureNoIndex ref)) Right . sourceIndex) runtime
        rawSlots <- first CoreEnvError (traverse (dictionaryMethodScheme env (funSlots f)) (funSlots f))
        let freshBase = 1 + maximum (-1 : concatMap Ty.tyParams (expected : map (Ty.binderTy . snd) variables))
            shiftedRaw = [Ty.mapIx id rawTy | (_, rawTy) <- rawSlots]
        instantiated <- instantiateDictionary (funSlots f) (map sourceIndex dictionaryCaptures) (Ty.schemeType scheme : shiftedRaw)
        let normalizedType = fst . normalizeTypeIndices env
            normalizedIndex = fst . normalizeIndex env
            seed = Ty.emptyAssignment {Ty.asValues = IM.fromList (zip (funRuntime f) (map normalizedIndex runtimeIndices))}
        case instantiated of
          signature : entries -> do
            assignment <- maybe (Left (CoreDictWrongType ref signature expected)) Right (Ty.matchTyStrict n (normalizedType signature) (normalizedType expected) seed)
            let subFreshBase = max freshBase (1 + maximum (-1 : concatMap Ty.tyParams (IM.elems (Ty.asTypes assignment))))
            runtimeDependencies <-
              sequence
                [ do
                    body <- elaborateScoped env slots variables value
                    let required = complete (Ty.substScheme n assignment (snd (Ty.schemeValues scheme !! i)))
                    unless (null (obligations body) && normalizedType (bodyType body) == normalizedType required) $ Left (CoreDictRuntimeCaptureWrongType ref required (bodyType body))
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
          [] -> Left (CoreDictLostSignature ref)
    | otherwise -> Left (CoreUnknownDictRef ref)
  _ -> Left CoreDictMustBeResolvedRef
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
instantiateDictionary :: [Slot] -> [Maybe Ty.Ix] -> [Ty.Ty] -> Either CoreError [Ty.Ty]
instantiateDictionary slots values types = do
  let used = concatMap (concatMap Ty.ixDicts . Ty.tyIndices) types
      positions = [position | (position, slot) <- zip [0 ..] slots, slotArity slot == 0]
      at i = listToMaybe (drop i positions) >>= (\position -> listToMaybe (drop position values)) >>= id
  replacements <- traverse (\i -> maybe (Left (CoreDependentDictNoIndex i)) (Right . (i,)) (at i)) used
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
      Transport ty child os dependencies -> (\child' proofs -> Transport ty child' proofs dependencies) <$> go child <*> traverse f os
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
