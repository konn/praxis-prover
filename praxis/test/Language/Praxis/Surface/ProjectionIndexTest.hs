{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.ProjectionIndexTest (projectionIndexTests) where

import Data.Either (isLeft)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Check qualified as Check
import Language.Praxis.Surface.Core qualified as Core
import Language.Praxis.Surface.Desugar
import Language.Praxis.Surface.Elab
import Language.Praxis.Surface.Engine (Spec (..))
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Fixity
import Language.Praxis.Surface.Mangle (mangleGlobal)
import Language.Praxis.Surface.Parser
import Language.Praxis.Surface.Prelude (prelude)
import Language.Praxis.Surface.Rename
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw (Segment (..))
import Language.Praxis.Surface.Types
import Test.Tasty
import Test.Tasty.HUnit

projectionIndexTests :: TestTree
projectionIndexTests =
  testGroup
    "projection index conversion"
    [ testCase "only complete calls to direct projections are reduced" $ do
        let (initial, function) = setFunRuntime [0] (addFunction emptyEnv (Ident "card") (Scheme [] [("n", TNat)] TNat) 0 [])
            name = funCore function
            env = initial {envGlobals = Map.insert (funQual function) (GFun function {funProjection = Just 0}) (envGlobals initial)}
        normalizeIndex env (IxFun name [IxVar "n"]) @?= (IxVar "n", Set.singleton name)
        normalizeIndex env (IxFun name []) @?= (IxFun name [], Set.empty)
        normalizeIndex env (IxFun name [IxNat 1, IxNat 2]) @?= (IxFun name [IxNat 1, IxNat 2], Set.empty)
        normalizeIndex env (IxPartial name 1 1 [IxVar "n"]) @?= (IxPartial name 1 1 [IxVar "n"], Set.empty)
    , testCase "the explicit core retains conversion prerequisites and rejects a wrong index" $ do
        let (initial, card) = setFunRuntime [0] (addFunction emptyEnv (Ident "card") (Scheme [] [("n", TNat)] TNat) 0 [])
            withCard = initial {envGlobals = Map.insert (funQual card) (GFun card {funProjection = Just 0}) (envGlobals initial)}
            (withBox, _) = addIndexedData withCard (Ident "Box") [] [TNat] [DataBinder "n" False (IndexParameter 0)] [[Ident "project"]] []
            (withProjection, project) = addFunction withBox (Ident "project") (Scheme [] [("n", TNat)] (TArrow (box (IxParam 0)) TNat)) 1 []
            (env, make) = setFunRuntime [0] (addFunction withProjection (Ident "make") (Scheme [] [("n", TNat)] (box (IxParam 0))) 0 [])
            actual = box (IxFun (funCore card) [IxVar "n"])
            recovered = Typed TNat [] [] (App (Global (Ref RefFunction (funCore project))) (Typed actual [] [] (Var 0)))
            call index = Typed (box index) [] [(0, index)] (App (Global (Ref RefFunction (funCore make))) recovered)
            check = Core.elaborateNamed env [] [("value", actual)]
        body <- either assertFailure pure (check (call (IxVar "n")))
        Core.indexDependencies body @?= Set.singleton (funCore card)
        Core.indexDependencies (Core.mapComputation id (Core.mapObligations id body)) @?= Core.indexDependencies body
        assertBool "a projection authorized a different index" (isLeft (check (call (IxNat 7))))
        (_, needed) <- maybe (assertFailure "index recovery failed") pure (indexTermInWithDependencies env [("value", (0 :: Int, actual))] (IxVar "n"))
        needed @?= Set.singleton (funCore card)
        indexTermIn env [("value", (0 :: Int, actual))] (IxVar "n") @?= Nothing
    , testCase "projection metadata counts runtime prefixes and wildcards" $ do
        (env, _) <- success (T.unlines ["pick : {n : Nat} -> Nat -> Nat -> Nat", "pick {n} _ x = x", "step : Nat -> Nat", "step x = S x", "proof-id : {n : Nat} -> Nat -> n = n -> Nat", "proof-id {n} x h = x", "callback : (Nat -> Nat) -> Nat -> Nat", "callback f x = x"])
        pick <- functionNamed env "pick"
        step <- functionNamed env "step"
        proofIdentity <- functionNamed env "proof-id"
        callback <- functionNamed env "callback"
        funProjection pick @?= Just 2
        funProjection step @?= Nothing
        funProjection proofIdentity @?= Nothing
        funProjection callback @?= Nothing
        normalizeIndex env (IxFun (funCore pick) [IxNat 10, IxNat 20, IxNat 30]) @?= (IxNat 30, Set.singleton (funCore pick))
    , testCase "a symbolic indexed retraction passes both methods as fixed dictionaries" $ do
        (env, items) <- success retraction
        code <- instanceFunction env "code"
        decode <- instanceFunction env "decode"
        card <- instanceFunction env "card"
        funRuntime code @?= []
        funRuntime decode @?= []
        assertBool "pruning erased its projection prerequisite" (CertifiedDeclaration (funCore card) `elem` map requirementDependency (requirements (funRequirements decode)))
        assertBool "a generic application was not elaborated" (any (\case IFun definition -> last (funQual (fdInfo definition)) == Ident "use"; _ -> False) items)
    , testCase "a symbolic indexed retraction and its generic use pass the kernel checker" $ do
        p <- either assertFailure pure prelude
        let checked = Check.checkSource p "projection.px" checkedRetraction
        errors checked @?= []
        mapM_ (\name -> assertBool ("missing certificate " <> T.unpack name) (name `elem` Check.checkedTheorems checked)) ["Projection.Finite-Fin.code.#index", "Projection.Finite-Fin.decode.#index", "Projection.Finite-Fin.decode-code", "Projection.roundtrip-law", "Projection.use.#index", "Projection.symbolic"]
    , testCase "a failed provider cannot authorize recovery after its body was defined" $ do
        p <- either assertFailure pure prelude
        let checked = Check.checkSourceWith failedCard p "projection-failed.px" checkedRetraction
        (_, core) <- maybe (assertFailure "the module did not elaborate") pure (Check.checkedFinal checked)
        assertBool "the test did not reach the post-definition failure" (Map.member (mangleGlobal ["Projection", "Finite-Fin", "card"]) (Check.coreBodies core))
        assertBool "an unadmitted projection provider defined decode" (Map.notMember (mangleGlobal ["Projection", "Finite-Fin", "decode"]) (Check.coreBodies core))
        assertBool "a concrete use erased the failed provider requirement" (Map.notMember (mangleGlobal ["Projection", "use"]) (Check.coreBodies core))
        assertBool "a failed provider certified the final theorem" ("Projection.symbolic" `notElem` Check.checkedTheorems checked)
        assertBool "the failed provider was not reported at recovery" (any (T.isInfixOf "earlier checked declaration or certificate Projection.Finite-Fin.card") (errors checked))
    ]
  where
    box index = TData "Box" [] [index]
    errors = map Check.reportMessage . filter ((== Check.SevError) . Check.reportSeverity) . Check.checkedReports
    failedCard _ definition
      | last (funQual (fdInfo definition)) == Ident "card" =
          [Spec "#failed-contract" (const []) (\_ _ -> Bottom) (\_ _ -> []) (\_ _ -> Left "a deliberately failed post-definition contract")]
      | otherwise = []

checkedRetraction :: Text
checkedRetraction =
  "module Projection where\n"
    <> retraction
    <> T.unlines
      [ "roundtrip-law : Finite a => (x : a) -> roundtrip x = x"
      , "roundtrip-law x = calc"
      , "  roundtrip x"
      , "  = decode (code x)"
      , "  = x := Finite.decode-code x"
      , "symbolic : (i : Fin n) -> use i = i"
      , "symbolic i = rfl"
      ]

retraction :: Text
retraction =
  T.unlines
    [ "data Fin (n : Nat) where"
    , "  FZero : {n : Nat} -> Fin (S n)"
    , "  FSucc : {n : Nat} -> Fin n -> Fin (S n)"
    , "class Finite a where"
    , "  card : Nat"
    , "  code : a -> Fin card"
    , "  decode : Fin card -> a"
    , "  decode-code : (x : a) -> decode (code x) = x"
    , "instance Finite (Fin n) where"
    , "  card {n} = n"
    , "  code i = i"
    , "  decode i = i"
    , "  decode-code i = rfl"
    , "roundtrip : Finite a => a -> a"
    , "roundtrip x = decode (code x)"
    , "use : {n : Nat} -> Fin n -> Fin n"
    , "use {n} i = roundtrip i"
    ]

success :: Text -> IO (Env, [Item])
success source = do
  raw <- either (assertFailure . show) pure (parseModule "projection.px" ("module Projection where\n" <> source))
  fixities <- either (assertFailure . show) pure (moduleFixities raw)
  let (renamed, errors) = renameModule fixities emptyEnv Map.empty [Ident "Projection"] raw
  errors @?= []
  let result@(_, items) = elabModule fixities emptyEnv renamed
  [err | IFailed err <- items] @?= []
  pure result

functionNamed :: Env -> Text -> IO FunInfo
functionNamed env name = case Map.lookup [Ident "Projection", Ident name] (envGlobals env) of
  Just (GFun function) -> pure function
  _ -> assertFailure ("no function " <> T.unpack name)

instanceFunction :: Env -> Text -> IO FunInfo
instanceFunction env name = case Map.lookup [Ident "Projection", Ident "Finite-Fin", Ident name] (envGlobals env) of
  Just (GFun function) -> pure function
  _ -> assertFailure ("no instance method " <> T.unpack name)
