{-# LANGUAGE OverloadedStrings #-}

{- |
Checked names used by finite quantifier elaboration. A pragma associates a
role with an ordinary declaration; it supplies no axiom and does not certify
the declaration. The checker must register a binding only after its target
and the target's proof dependencies have been checked successfully.

The numeric bridge is specified by three ordinary theorems. In particular,
the types of @from-nat@ and @to-nat@ alone do not establish their inverse or
boundedness properties. Keeping those certificates explicit permits user
representations of finite ordinals without trusting constructor names.
-}
module Language.Praxis.Surface.Builtin (
  BuiltinRole (..),
  BuiltinRegistry,
  BuiltinBinding (..),
  builtinRoleName,
  parseBuiltinRole,
  rolePrerequisites,
  requiresCertificate,
  validateBuiltin,
  registerBuiltin,
) where

import Bound (Scope, instantiate)
import Control.Monad (unless)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void, absurd)
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Syntax (Expr (..), Ref (..), RefKind (..), RelOp (..), apps)
import Language.Praxis.Surface.Types (Ix (..), Kind (..), Parameter (..), Scheme (..), Ty (..))

-- | The finite protocol, including the certificates for its numeric bridge.
data BuiltinRole
  = BuiltinFin
  | BuiltinVec
  | BuiltinFinFromNat
  | BuiltinFinToNat
  | BuiltinFinToNatBound
  | BuiltinFinFromToNat
  | BuiltinFinToFromNat
  | BuiltinVecLookup
  | BuiltinFinite
  | BuiltinFiniteCard
  | BuiltinFiniteEnumeration
  | BuiltinFiniteLocate
  | BuiltinFiniteCoverage
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | Text keys allow the environment to store this without importing its validator.
type BuiltinRegistry = Map Text QualName

-- | The direct protocol dependencies, to supplement declaration dependencies.
data BuiltinBinding = BuiltinBinding
  { builtinRole :: !BuiltinRole
  , builtinTarget :: !QualName
  , builtinDependencies :: ![QualName]
  }
  deriving stock (Eq, Show)

builtinRoleName :: BuiltinRole -> Text
builtinRoleName = \case
  BuiltinFin -> "FIN"
  BuiltinVec -> "VEC"
  BuiltinFinFromNat -> "FIN_FROM_NAT"
  BuiltinFinToNat -> "FIN_TO_NAT"
  BuiltinFinToNatBound -> "FIN_TO_NAT_BOUND"
  BuiltinFinFromToNat -> "FIN_FROM_TO_NAT"
  BuiltinFinToFromNat -> "FIN_TO_FROM_NAT"
  BuiltinVecLookup -> "VEC_LOOKUP"
  BuiltinFinite -> "FINITE"
  BuiltinFiniteCard -> "FINITE_CARD"
  BuiltinFiniteEnumeration -> "FINITE_ENUMERATION"
  BuiltinFiniteLocate -> "FINITE_LOCATE"
  BuiltinFiniteCoverage -> "FINITE_COVERAGE"

parseBuiltinRole :: Text -> Either String BuiltinRole
parseBuiltinRole name = case [role | role <- [minBound .. maxBound], builtinRoleName role == name] of
  [role] -> Right role
  _ -> Left ("unknown BUILTIN role " <> T.unpack name)

-- | Required earlier registrations. These are dependencies, not new axioms.
rolePrerequisites :: BuiltinRole -> [BuiltinRole]
rolePrerequisites = \case
  BuiltinFin -> []
  BuiltinVec -> []
  BuiltinFinFromNat -> [BuiltinFin]
  BuiltinFinToNat -> [BuiltinFin]
  BuiltinFinToNatBound -> [BuiltinFin, BuiltinFinToNat]
  BuiltinFinFromToNat -> [BuiltinFin, BuiltinFinFromNat, BuiltinFinToNat]
  BuiltinFinToFromNat -> [BuiltinFin, BuiltinFinFromNat, BuiltinFinToNat]
  BuiltinVecLookup -> [BuiltinFin, BuiltinVec]
  BuiltinFinite -> []
  BuiltinFiniteCard -> [BuiltinFinite]
  BuiltinFiniteEnumeration -> [BuiltinFinite, BuiltinFiniteCard, BuiltinVec]
  BuiltinFiniteLocate -> [BuiltinFinite, BuiltinFiniteCard, BuiltinFin]
  BuiltinFiniteCoverage -> [BuiltinFinite, BuiltinFiniteCard, BuiltinFiniteEnumeration, BuiltinFiniteLocate, BuiltinVecLookup]

-- | A class law is checked at every instance; bridge theorems need a certificate now.
requiresCertificate :: BuiltinRole -> Bool
requiresCertificate role = role `elem` [BuiltinFinToNatBound, BuiltinFinFromToNat, BuiltinFinToFromNat]

registerBuiltin :: BuiltinRegistry -> Env -> Text -> QualName -> Either String (BuiltinRegistry, BuiltinBinding)
registerBuiltin registry env name target = do
  role <- parseBuiltinRole name
  binding <- validateBuiltin registry env role target
  pure (Map.insert name target registry, binding)

{- | Check the exact dependent signature or law. This does not inspect a
proof certificate or a declaration dependency graph; the module checker
must do both before storing the returned binding.
-}
validateBuiltin :: BuiltinRegistry -> Env -> BuiltinRole -> QualName -> Either String BuiltinBinding
validateBuiltin registry env role target = do
  case Map.lookup roleName registry of
    Just previous
      | previous == target -> reject "is already registered"
      | otherwise -> reject ("is already bound to " <> T.unpack (displayQualName previous) <> " and cannot be rebound")
    Nothing -> pure ()
  prerequisites <- traverse registered (rolePrerequisites role)
  declaration <- maybe (reject "names no declaration") Right (Map.lookup target (envGlobals env))
  case role of
    BuiltinFin -> do
      d <- datatype declaration
      expect "a type with exactly one Nat index and no type parameters" $
        null (dataParams d) && dataIndices d == [TNat] && map dbParameter (dataBinders d) == [IndexParameter 0]
    BuiltinVec -> do
      d <- datatype declaration
      expect "a type with a Nat index followed by one Type parameter" $
        map snd (dataParams d) == [KType]
          && dataIndices d == [TNat]
          && map dbParameter (dataBinders d) == [IndexParameter 0, TypeParameter 0]
    BuiltinFinFromNat -> do
      f <- function declaration
      fin <- typeName BuiltinFin
      expectFunction f [] [TNat, TNat] (TData fin [] [IxParam 1]) 0
      expect "exactly the precondition k < n on its two implicit Nat parameters" $
        case funProofs f of
          [(0, p)] -> open p == Rel RelLt (Var 0) (Var 1)
          _ -> False
    BuiltinFinToNat -> do
      f <- function declaration
      fin <- typeName BuiltinFin
      expectFunction f [] [TNat] (TArrow (TData fin [] [IxParam 0]) TNat) 1
      expect "no proof arguments" (null (funProofs f))
    BuiltinVecLookup -> do
      f <- function declaration
      fin <- typeName BuiltinFin
      vec <- typeName BuiltinVec
      expectFunction f [KType] [TNat] (TArrow (TData fin [] [IxParam 0]) (TArrow (TData vec [TParam 0 []] [IxParam 0]) (TParam 0 []))) 2
      expect "no proof arguments" (null (funProofs f))
    BuiltinFinToNatBound -> bridgeTheorem declaration 1 1 \fin _ toNat ->
      ( [TData fin [] [IxParam 0]]
      , Rel RelLt (call toNat [Var 0] [Var 1]) (Var 0)
      )
    BuiltinFinFromToNat -> bridgeTheorem declaration 1 1 \fin fromNat toNat ->
      ( [TData fin [] [IxParam 0]]
      , Rel RelEq (call fromNat [call toNat [Var 0] [Var 1], Var 0] []) (Var 1)
      )
    BuiltinFinToFromNat -> bridgeTheorem declaration 2 0 \_ fromNat toNat ->
      ( []
      , Arrow (Rel RelLt (Var 0) (Var 1)) (Rel RelEq (call toNat [Var 1] [call fromNat [Var 0, Var 1] []]) (Var 0))
      )
    BuiltinFinite -> case declaration of
      GClass _ -> pure ()
      _ -> expect "a class" False
    BuiltinFiniteCard -> finiteMethod declaration TNat 0
    BuiltinFiniteEnumeration -> do
      vec <- typeName BuiltinVec
      card <- registered BuiltinFiniteCard
      finiteMethod declaration (TData vec [TParam 0 []] [cardIndex card]) 0
    BuiltinFiniteLocate -> do
      fin <- typeName BuiltinFin
      card <- registered BuiltinFiniteCard
      finiteMethod declaration (TArrow (TParam 0 []) (TData fin [] [cardIndex card])) 1
    BuiltinFiniteCoverage -> do
      cls <- registered BuiltinFinite
      enum <- registered BuiltinFiniteEnumeration
      locate <- registered BuiltinFiniteLocate
      card <- registered BuiltinFiniteCard
      lookupFn <- registeredFunction BuiltinVecLookup
      l <- case declaration of
        GLaw l -> pure l
        _ -> reject "requires a class law"
      expect "a law of the registered FINITE class, over exactly one value of its parameter" $
        lawClass l == cls && map snd (lawBinders l) == [TParam 0 []]
      enumRef <- lawMethod l enum
      locateRef <- lawMethod l locate
      cardRef <- lawMethod l card
      let expected = Rel RelEq (call lookupFn [Global cardRef] [App (Global locateRef) (Var 0), Global enumRef]) (Var 0)
      expect "lookup (locate x) enumeration = x, using the registered methods of the same dictionary" (open (lawProp l) == expected)
  pure (BuiltinBinding role target prerequisites)
  where
    roleName = builtinRoleName role
    reject :: String -> Either String a
    reject message = Left ("BUILTIN " <> T.unpack roleName <> " " <> message)
    expect description ok = unless ok (reject ("requires " <> description))
    registered wanted = maybe (reject ("requires an earlier " <> T.unpack (builtinRoleName wanted) <> " registration")) Right (Map.lookup (builtinRoleName wanted) registry)
    typeName wanted = renderQualName <$> registered wanted
    datatype = \case
      GData d -> pure d
      _ -> reject "requires an inductive data type"
    function = \case
      GFun f -> pure f
      _ -> reject "requires an ordinary function"
    registeredFunction wanted = do
      q <- registered wanted
      maybe (reject "refers to an unavailable prerequisite") function (Map.lookup q (envGlobals env))
    expectFunction f kinds values ty arity = do
      let sch = funScheme f
      expect "the registered protocol's exact dependent function signature" $
        map snd (schemeParams sch) == kinds
          && map snd (schemeValues sch) == values
          && schemeType sch == ty
          && funArity f == arity
      expect "a function without a class dictionary" (null (funSlots f))
      expect "distinct, valid runtime index positions" $
        all (\i -> i >= 0 && i < length values) (funRuntime f)
          && length (Map.fromList [(i, ()) | i <- funRuntime f]) == length (funRuntime f)
    finiteMethod declaration expected arity = do
      cls <- registered BuiltinFinite
      m <- case declaration of
        GMethod m -> pure m
        _ -> reject "requires a method of the registered FINITE class"
      let sch = methodScheme m
      expect "the registered FINITE class's exact dependent method signature" $
        methodClass m == cls
          && map snd (schemeParams sch) == [KType]
          && null (schemeValues sch)
          && schemeType sch == expected
          && methodArity m == arity
    bridgeTheorem declaration valueCount binderCount expected = do
      fin <- typeName BuiltinFin
      toNat <- registeredFunction BuiltinFinToNat
      -- The bound theorem does not use from-nat; the placeholder is never called.
      fromNat <- if role == BuiltinFinToNatBound then pure toNat else registeredFunction BuiltinFinFromNat
      t <- case declaration of
        GTheorem t -> pure t
        _ -> reject "requires a theorem whose proof has been certified"
      let (membered, proposition) = expected fin fromNat toNat
      expect "the bridge theorem's exact value binders without extra hypotheses or dictionaries" $
        length (thmValues t) == valueCount
          && length (thmBinders t) == binderCount
          && thmMembered t == membered
          && null (thmSlots t)
          && null (thmPremises t)
      p <- maybe (reject "requires an explicit bridge theorem statement") Right (thmProp t)
      expect "the registered numeric bridge's exact proposition" (open p == proposition)
    lawMethod law name = case [ref | (slot, ref) <- zip (lawSlots law) (dictionaryRefs (lawSlots law)), slotMethod slot == name, slotParam slot == 0] of
      [ref] -> pure ref
      _ -> reject "requires every finite method to refer to its own class dictionary"

-- | The class elaborator uses this stable name in dependent method signatures.
cardIndex :: QualName -> Ix
cardIndex name = IxVar ("#method:" <> renderQualName name)

open :: Scope Int Expr Void -> Expr Int
open = instantiate Var . fmap absurd

-- | A function call with its actual runtime subset of implicit value parameters.
call :: FunInfo -> [Expr a] -> [Expr a] -> Expr a
call f values arguments = apps (Global (Ref RefFunction (funCore f))) ([values !! i | i <- funRuntime f] <> arguments)

-- | Keep the same separate numbering of function and value dictionary entries.
dictionaryRefs :: [Slot] -> [Ref]
dictionaryRefs = go 1 (0 :: Int)
  where
    go _ _ [] = []
    go functionIndex valueIndex (slot : rest)
      | slotArity slot > 0 = Ref RefStatic (staticName functionIndex) : go (functionIndex + 1) valueIndex rest
      | otherwise = Ref RefValueParam (T.pack (show valueIndex)) : go functionIndex (valueIndex + 1) rest
