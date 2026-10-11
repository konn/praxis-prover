{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.InstanceContextTest (instanceContextTests) where

import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Elab (instanceClassContext)
import Language.Praxis.Surface.Engine (Knowledge (..))
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.FiniteFixtures
import Language.Praxis.Surface.Prelude (prelude)
import Language.Praxis.Surface.Syntax.Raw (Segment (..))
import Language.Praxis.Surface.Types (Ty (..))
import Test.Tasty
import Test.Tasty.HUnit

instanceContextTests :: TestTree
instanceContextTests =
  testGroup
    "instance proof contexts"
    [ testCase "a class with only laws remains a required instance context" $ do
        p <- either assertFailure pure prelude
        let checked = checkSource p "context.px" (source <> "bad : ∀ (x : Box Nat), x = x\nbad = by intro x; rfl\n")
        assertBool "the conditional retraction itself did not certify" ("FiniteQ.Finite-Box.decode-code" `elem` checkedTheorems checked)
        assertBool "a missing law-only context certified finite syntax" ("FiniteQ.bad" `notElem` checkedTheorems checked)
        assertBool "the missing context was not identified" (any (T.isInfixOf "instance of FiniteQ.Impossible for Nat") (errors checked))
        (knowledge, _) <- maybe (assertFailure "no checked environment") pure (checkedFinal checked)
        selected <- maybe (assertFailure "missing conditional instance") pure (Map.lookup ([Ident "FiniteQ", Ident "Finite"], "FiniteQ.Box") (envInstances (knowEnv knowledge)))
        instClassContext selected @?= [([Ident "FiniteQ", Ident "Impossible"], 0)]
        instanceClassContext selected (TData "FiniteQ.Box" [TNat] []) @?= Right [([Ident "FiniteQ", Ident "Impossible"], TNat)]
    , testCase "generic and inherited law-only contexts and a valid empty instance work" $ do
        p <- either assertFailure pure prelude
        let checked =
              checkSource
                p
                "context-positive.px"
                ( source
                    <> T.unlines
                      [ "generic : Impossible a => ∀ (x : Box a), x = x"
                      , "generic = by intro x; rfl"
                      , "class Impossible a => Strong a where"
                      , "  same : (x : a) -> x = x"
                      , "inherited : Strong a => ∀ (x : Box a), x = x"
                      , "inherited = by intro x; rfl"
                      ]
                    <> validVoid
                    <> "concrete : ∀ (x : Box Void), x = x\nconcrete = by intro x; rfl\n"
                )
        errors checked @?= []
        mapM_ (\name -> assertBool ("missing " <> T.unpack name) (name `elem` checkedTheorems checked)) ["FiniteQ.generic", "FiniteQ.inherited", "FiniteQ.concrete"]
    , testCase "imported conditional instances retain their canonical law context" $ do
        p <- either assertFailure pure prelude
        let (checked, build) = checkModule (\_ _ -> []) (initialBuild p) Map.empty Nothing "FiniteQ.px" (source <> validVoid)
        errors checked @?= []
        exports <- maybe (assertFailure "missing exports") pure (Map.lookup [Ident "FiniteQ"] (buildExports build))
        let imports = Map.singleton (Nothing, [Ident "FiniteQ"]) (Right exports)
            (client, _) = checkModule (\_ _ -> []) build imports Nothing "Client.px" "module Client where\nimport FiniteQ as F\ngood : ∀ (x : F.Box F.Void), x = x\ngood = by intro x; rfl\nbad : ∀ (x : F.Box Nat), x = x\nbad = by intro x; rfl\n"
        assertBool "a valid imported context did not certify" ("Client.good" `elem` checkedTheorems client)
        assertBool "an imported instance erased its context" ("Client.bad" `notElem` checkedTheorems client)
        assertBool "the imported missing context was not identified" (any (T.isInfixOf "instance of FiniteQ.Impossible for Nat") (errors client))
    ]
  where
    errors = map reportMessage . filter ((== SevError) . reportSeverity) . checkedReports

source :: Text
source =
  "module FiniteQ where\n"
    <> finiteOrdinals
    <> finiteProtocol
    <> T.unlines
      [ "class Impossible a where"
      , "  impossible : (x : a) -> 0 = 1"
      , "data Box a = Empty | Wrap a"
      , "instance Impossible a => Finite (Box a) where"
      , "  card = 1"
      , "  code x = FZero {0}"
      , "  decode i = Empty"
      , "  decode-code Empty = rfl"
      , "  decode-code (Wrap x) = by"
      , "    have no : 0 = 1 := Impossible.impossible x"
      , "    contradiction"
      ]

validVoid :: Text
validVoid = "data Void\ninstance Impossible Void where\n  impossible ()\n"
