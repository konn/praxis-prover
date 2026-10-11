{-# LANGUAGE OverloadedStrings #-}

-- | Protocol validation: matching names or result types never substitute for a certificate.
module Language.Praxis.Surface.BuiltinTest (builtinTests) where

import Bound (Scope, Var (..), toScope)
import Control.Monad (foldM, forM_)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Language.Praxis.Surface.Builtin
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Mangle (mangleGlobal)
import Language.Praxis.Surface.Syntax (Expr (..), Ref (..), RefKind (..), RelOp (..), apps)
import Language.Praxis.Surface.Syntax.Raw (Located (..), Segment (..), Span (..), segmentText)
import Language.Praxis.Surface.Syntax.Raw qualified as R
import Language.Praxis.Surface.Types (Ix (..), Kind (..), Parameter (..), Scheme (..), Ty (..))
import Test.Tasty
import Test.Tasty.HUnit

builtinTests :: TestTree
builtinTests =
  testGroup
    "builtin protocol"
    [ testCase "every documented role parses and unknown roles are rejected" $ do
        forM_ roles $ \role -> parseBuiltinRole (builtinRoleName role) @?= Right role
        rejected "unknown BUILTIN role" (parseBuiltinRole "FINITE_ENUMERATON")
    , testCase "complete, coherent signatures and bridge propositions register" $ do
        registry <- either assertFailure pure (registerAll fixture)
        Map.size registry @?= length roles
    , testCase "finite retractions do not require a vector registration" $ do
        let withoutVectors = filter (`notElem` [BuiltinVec, BuiltinVecLookup]) roles
        registry <- either assertFailure pure (foldM (\known role -> fst <$> registerBuiltin known fixture (builtinRoleName role) (target role)) Map.empty withoutVectors)
        Map.size registry @?= length withoutVectors
    , testCase "registrations retain their proof dependencies" $ do
        binding <- either assertFailure pure (validate BuiltinFiniteDecodeCode fixture)
        builtinDependencies binding @?= map target (rolePrerequisites BuiltinFiniteDecodeCode)
        assertBool "bound requires a certified theorem" (requiresCertificate BuiltinFinToNatBound)
        assertBool "inverse requires a certified theorem" (requiresCertificate BuiltinFinFromToNat)
        assertBool "coverage is a law checked at each instance" (not (requiresCertificate BuiltinFiniteDecodeCode))
    , testCase "roles cannot be duplicated or rebound" $ do
        let existing = Map.singleton "FIN" (target BuiltinFin)
        rejected "already registered" (registerBuiltin existing fixture "FIN" (target BuiltinFin))
        rejected "cannot be rebound" (registerBuiltin existing fixture "FIN" (target BuiltinVec))
    , testCase "a role cannot precede its prerequisites" $
        rejected "earlier FIN registration" (validateBuiltin Map.empty fixture BuiltinFinFromNat (target BuiltinFinFromNat))
    , testCase "finite ordinal and vector type roles have exact kinds" $ do
        rejected "exactly one Nat index" (validate BuiltinFin (changeData BuiltinFin (\d -> d {dataIndices = []}) fixture))
        rejected "Nat index followed" (validate BuiltinVec (changeData BuiltinVec (\d -> d {dataBinders = reverse (dataBinders d)}) fixture))
    , testCase "numeric conversion requires the strict bound on the right index" $ do
        rejected "precondition k < n" (validate BuiltinFinFromNat (changeFunction BuiltinFinFromNat (\f -> f {funProofs = []}) fixture))
        rejected "precondition k < n" (validate BuiltinFinFromNat (changeFunction BuiltinFinFromNat (\f -> f {funProofs = [(0, scoped (Rel RelLt (Var 1) (Var 0)))]}) fixture))
        rejected "exact dependent function signature" (validate BuiltinFinFromNat (changeFunction BuiltinFinFromNat (\f -> f {funScheme = (funScheme f) {schemeType = fin (IxParam 0)}}) fixture))
    , testCase "lookup's ordinal and vector must carry the same index" $
        rejected "exact dependent function signature" (validate BuiltinVecLookup (changeFunction BuiltinVecLookup (\f -> f {funScheme = (funScheme f) {schemeType = TArrow (fin (IxParam 0)) (TArrow (vec (IxNat 0)) parameter)}}) fixture))
    , testCase "numeric bridge propositions cannot be weakened by hypotheses" $
        rejected "exact proposition" (validate BuiltinFinToNatBound (changeTheorem BuiltinFinToNatBound (\t -> t {thmProp = Just (scoped (Arrow Top boundProp))}) fixture))
    , testCase "an inverse theorem must name the registered conversions" $
        rejected "exact proposition" (validate BuiltinFinFromToNat (changeTheorem BuiltinFinFromToNat (\t -> t {thmProp = Just (scoped (Rel RelEq (App (Global (Ref RefFunction "unrelated")) (Var 1)) (Var 1)))}) fixture))
    , testCase "a generated theorem without a surface statement is not a bridge" $
        rejected "explicit bridge theorem statement" (validate BuiltinFinToFromNat (changeTheorem BuiltinFinToFromNat (\t -> t {thmProp = Nothing}) fixture))
    , testCase "finite methods belong to the same registered class" $
        rejected "exact dependent method signature" (validate BuiltinFiniteCode (changeMethod BuiltinFiniteCode (\m -> m {methodClass = [Ident "OtherFinite"]}) fixture))
    , testCase "both directions depend on this dictionary's cardinality" $ do
        let otherCard = IxVar "#method:Other.card"
        rejected "exact dependent method signature" (validate BuiltinFiniteDecode (changeMethod BuiltinFiniteDecode (\m -> m {methodScheme = (methodScheme m) {schemeType = TArrow (fin otherCard) parameter}}) fixture))
        rejected "exact dependent method signature" (validate BuiltinFiniteCode (changeMethod BuiltinFiniteCode (\m -> m {methodScheme = (methodScheme m) {schemeType = TArrow parameter (fin otherCard)}}) fixture))
    , testCase "the retraction law uses the registered decoder and encoder" $ do
        let wrong = Rel RelEq (App (Global (Ref RefStatic "otherDecode")) (App (Global codeRef) (Var 0))) (Var 0)
        rejected "same dictionary" (validate BuiltinFiniteDecodeCode (changeLaw (\l -> l {lawProp = scoped wrong}) fixture))
        let wrongDictionary = Rel RelEq (App (Global decodeRef) (App (Global (Ref RefStatic "foreign")) (Var 0))) (Var 0)
        rejected "same dictionary" (validate BuiltinFiniteDecodeCode (changeLaw (\l -> l {lawProp = scoped wrongDictionary}) fixture))
    , testCase "coverage is unconditional and quantifies exactly one element" $ do
        rejected "same dictionary" (validate BuiltinFiniteDecodeCode (changeLaw (\l -> l {lawProp = scoped (Arrow Top coverageProp)}) fixture))
        rejected "exactly one value" (validate BuiltinFiniteDecodeCode (changeLaw (\l -> l {lawBinders = [("x", parameter), ("y", parameter)]}) fixture))
    , testCase "coverage cannot use another class's method slots" $
        rejected "own class dictionary" (validate BuiltinFiniteDecodeCode (changeLaw (\l -> l {lawSlots = [s {slotParam = 1} | s <- lawSlots l]}) fixture))
    , testCase "the retraction law's slots retain the registered method arities" $
        rejected "own class dictionary" (validate BuiltinFiniteDecodeCode (changeLaw (\l -> l {lawSlots = [if slotMethod s == target BuiltinFiniteCode then s {slotArity = 2} else s | s <- lawSlots l]}) fixture))
    ]

roles :: [BuiltinRole]
roles = [minBound .. maxBound]

registerAll :: Env -> Either String BuiltinRegistry
registerAll env = foldM (\registry role -> fst <$> registerBuiltin registry env (builtinRoleName role) (target role)) Map.empty roles

validate :: BuiltinRole -> Env -> Either String BuiltinBinding
validate role env = validateBuiltin prerequisites env role (target role)
  where
    prerequisites = Map.fromList [(builtinRoleName r, target r) | r <- roles, r /= role]

rejected :: Text -> Either String a -> Assertion
rejected message = \case
  Left err -> assertBool ("expected " <> T.unpack message <> " in: " <> err) (message `T.isInfixOf` T.pack err)
  Right _ -> assertFailure "malformed BUILTIN declaration was accepted"

target :: BuiltinRole -> QualName
target = \case
  BuiltinFin -> [Ident "Bridge", Ident "Ordinal"]
  BuiltinVec -> [Ident "Bridge", Ident "Vector"]
  BuiltinFinFromNat -> [Ident "Bridge", Ident "fromNatural"]
  BuiltinFinToNat -> [Ident "Bridge", Ident "toNatural"]
  BuiltinFinToNatBound -> [Ident "Bridge", Ident "bounded"]
  BuiltinFinFromToNat -> [Ident "Bridge", Ident "fromTo"]
  BuiltinFinToFromNat -> [Ident "Bridge", Ident "toFrom"]
  BuiltinVecLookup -> [Ident "Bridge", Ident "lookup"]
  BuiltinFinite -> [Ident "Bridge", Ident "Finite"]
  BuiltinFiniteCard -> [Ident "Bridge", Ident "Finite", Ident "card"]
  BuiltinFiniteDecode -> [Ident "Bridge", Ident "Finite", Ident "decode"]
  BuiltinFiniteCode -> [Ident "Bridge", Ident "Finite", Ident "code"]
  BuiltinFiniteDecodeCode -> [Ident "Bridge", Ident "Finite", Ident "decode-code"]

parameter :: Ty
parameter = TParam 0 []

fin :: Ix -> Ty
fin n = TData (renderQualName (target BuiltinFin)) [] [n]

vec :: Ix -> Ty
vec n = TData (renderQualName (target BuiltinVec)) [parameter] [n]

cardIndex :: Ix
cardIndex = IxVar ("#method:" <> renderQualName (target BuiltinFiniteCard))

scoped :: Expr Int -> Scope Int Expr Void
scoped = toScope . fmap B

-- These fixtures exercise declaration metadata only. The checker tests must
-- separately establish that registration follows successful certification.
fixture :: Env
fixture = withCoverage
  where
    root = emptyEnv {envModule = [Ident "Bridge"]}
    (withFin, _) = addIndexedData root (Ident "Ordinal") [] [TNat] [DataBinder "n" False (IndexParameter 0)] [] []
    (withVec, _) = addIndexedData withFin (Ident "Vector") [("a", KType)] [TNat] [DataBinder "n" False (IndexParameter 0), DataBinder "a" False (TypeParameter 0)] [] []
    (withFrom, _) = setFunProofs [(0, scoped (Rel RelLt (Var 0) (Var 1)))] (setFunRuntime [0, 1] (addFunction withVec (Ident "fromNatural") (Scheme [] [("k", TNat), ("n", TNat)] (fin (IxParam 1))) 0 []))
    (withTo, _) = addFunction withFrom (Ident "toNatural") (Scheme [] [("n", TNat)] (TArrow (fin (IxParam 0)) TNat)) 1 []
    (withLookup, _) = setFunRuntime [0] (addFunction withTo (Ident "lookup") (Scheme [("a", KType)] [("n", TNat)] (TArrow (fin (IxParam 0)) (TArrow (vec (IxParam 0)) parameter))) 2 [])
    withBound = addBridge BuiltinFinToNatBound ["n"] [fin (IxParam 0)] boundProp withLookup
    withFromTo = addBridge BuiltinFinFromToNat ["n"] [fin (IxParam 0)] fromToProp withBound
    withToFrom = addBridge BuiltinFinToFromNat ["k", "n"] [] toFromProp withFromTo
    (withClass, _) =
      addClass
        withToFrom
        (Ident "Finite")
        []
        [ (Ident "card", Scheme [("a", KType)] [] TNat, 0)
        , (Ident "code", Scheme [("a", KType)] [] (TArrow parameter (fin cardIndex)), 1)
        , (Ident "decode", Scheme [("a", KType)] [] (TArrow (fin cardIndex) parameter), 1)
        ]
    law = LawInfo (target BuiltinFiniteDecodeCode) (target BuiltinFinite) [("x", parameter)] (scoped coverageProp) slots (Located (Span (1, 1) (1, 1)) R.EWildcard)
    withCoverage = addLaws (target BuiltinFinite) [law] withClass
    slots = [Slot (target BuiltinFiniteCard) 0 0, Slot (target BuiltinFiniteCode) 0 1, Slot (target BuiltinFiniteDecode) 0 1]

addBridge :: BuiltinRole -> [Text] -> [Ty] -> Expr Int -> Env -> Env
addBridge role values types proposition env = fst (setTheoremIndices [] values (Just (scoped proposition)) (addTheorem env (target role) ["i" | not (null types)] types [] [] Nothing))

functionRef :: BuiltinRole -> Ref
functionRef role = Ref RefFunction (mangleGlobal (map segmentText (target role)))

fromCall :: Expr Int -> Expr Int -> Expr Int
fromCall k n = apps (Global (functionRef BuiltinFinFromNat)) [k, n]

toCall :: Expr Int -> Expr Int
toCall i = App (Global (functionRef BuiltinFinToNat)) i

boundProp, fromToProp, toFromProp, coverageProp :: Expr Int
boundProp = Rel RelLt (toCall (Var 1)) (Var 0)
fromToProp = Rel RelEq (fromCall (toCall (Var 1)) (Var 0)) (Var 1)
toFromProp = Arrow (Rel RelLt (Var 0) (Var 1)) (Rel RelEq (toCall (fromCall (Var 0) (Var 1))) (Var 0))
coverageProp = Rel RelEq (App (Global decodeRef) (App (Global codeRef) (Var 0))) (Var 0)

codeRef, decodeRef :: Ref
codeRef = Ref RefStatic (staticName 1)
decodeRef = Ref RefStatic (staticName 2)

changeData :: BuiltinRole -> (DataInfo -> DataInfo) -> Env -> Env
changeData role f env = env {envGlobals = Map.adjust (\case GData d -> GData (f d); other -> other) (target role) (envGlobals env)}

changeFunction :: BuiltinRole -> (FunInfo -> FunInfo) -> Env -> Env
changeFunction role f env = env {envGlobals = Map.adjust (\case GFun d -> GFun (f d); other -> other) (target role) (envGlobals env)}

changeTheorem :: BuiltinRole -> (TheoremInfo -> TheoremInfo) -> Env -> Env
changeTheorem role f env = env {envGlobals = Map.adjust (\case GTheorem d -> GTheorem (f d); other -> other) (target role) (envGlobals env)}

changeMethod :: BuiltinRole -> (MethodInfo -> MethodInfo) -> Env -> Env
changeMethod role f env = env {envGlobals = Map.adjust (\case GMethod d -> GMethod (f d); other -> other) (target role) (envGlobals env)}

changeLaw :: (LawInfo -> LawInfo) -> Env -> Env
changeLaw f env = env {envGlobals = Map.adjust (\case GLaw d -> GLaw (f d); other -> other) (target BuiltinFiniteDecodeCode) (envGlobals env)}
