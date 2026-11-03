{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.ConstructionTest (constructionTests) where

import Control.Monad (forM_)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.PRA.Certificate (Certificate)
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Core qualified as Core
import Language.Praxis.Surface.Eval (EvalResult (..), Value (..), evaluateEntryWithNats)
import Language.Praxis.Surface.Mangle (mangleGlobal)
import Language.Praxis.Surface.Prelude (prelude)
import Language.Praxis.Surface.Rename (Imports)
import Language.Praxis.Surface.Syntax.Raw (Segment (..))
import Test.Tasty
import Test.Tasty.HUnit

constructionTests :: TestTree
constructionTests = withResource fixtures (const (pure ())) $ \getFixtures ->
  let check source = do
        (build, imports) <- getFixtures
        pure (fst (checkModule (\_ _ -> []) build imports Nothing "construction.px" ("module Construction where\n" <> source)))
      succeeds source = do
        checked <- check source
        errors checked @?= []
        pure checked
      rejects label source = testCase label $ do
        checked <- check (opened <> source)
        assertBool "invalid construction was accepted" (not (null (errors checked)))
        forM_ (checkedFinal checked) $ \(_, core) ->
          forM_ ["contract", "closed", "index"] $ \suffix ->
            assertBool "invalid construction received a certificate" (Map.notMember (T.unpack (mangleGlobal ["Construction", "bad", "#" <> suffix])) (coreCertificates core))
   in testGroup
        "construction scripts"
        [ testCase "list constructors use expected types through nested apply goals" $ do
            checked <-
              succeeds $
                opened
                  <> T.unlines
                    [ "values : List Nat"
                    , "values = by"
                    , "  apply Cons"
                    , "  exact 1"
                    , "  apply Cons"
                    , "  exact 2"
                    , "  apply Nil"
                    , "result : Nat"
                    , "result = by exact size values"
                    ]
            evaluates checked "result" 2
        , testCase "natural successors and local fixed callbacks use the ordinary term checker" $ do
            checked <-
              succeeds $
                opened
                  <> T.unlines
                    [ "twice : (Nat -> Nat) -> Nat -> Nat"
                    , "twice f n = by"
                    , "  apply f"
                    , "  apply f"
                    , "  exact n"
                    , "result : Nat"
                    , "result = by"
                    , "  apply twice"
                    , "  { exact S }"
                    , "  { exact 0 }"
                    , "callback-result : result = 2"
                    , "callback-result = by rfl"
                    , "plain : Nat"
                    , "plain = by apply S; apply suc; exact 0"
                    ]
            core <- finalCore checked
            assertBool "constructed callback computation was not certified" (Map.member (T.unpack (mangleGlobal ["Construction", "callback-result"])) (coreCertificates core))
            evaluates checked "plain" 2
        , testCase "nested by expressions and partially supplied global applications construct values" $ do
            checked <-
              succeeds $
                opened
                  <> T.unlines
                    [ "nested : Nat"
                    , "nested = S (by apply suc; exact 3)"
                    , "result : Nat"
                    , "result = by"
                    , "  apply (plus 2)"
                    , "  exact nested"
                    ]
            evaluates checked "result" 7
        , testCase "qualified constructors respect import aliases and enclosing modules" $ do
            checked <-
              succeeds $
                T.unlines
                  [ "import ConstructionFixtures as F"
                  , "module Results where"
                  , "  values : F.List Nat"
                  , "  values = by"
                  , "    apply F.List.Cons"
                  , "    exact 4"
                  , "    exact F.List.Nil"
                  , "result : Nat"
                  , "result = by apply F.size; exact Results.values"
                  ]
            evaluates checked "result" 1
        , testCase "the same indexed proof schema has identical retained construction inside and outside internal" $ do
            let script =
                  [ "    apply Proof.MP"
                  , "    {"
                  , "      apply Proof.MP"
                  , "      { exact Proof.S {a} {Imp a a} {a} }"
                  , "      { exact Proof.K {a} {Imp a a} }"
                  , "    }"
                  , "    { exact Proof.K {a} {a} }"
                  ]
            checked <-
              succeeds $
                opened
                  <> T.unlines
                    ( [ "outside : {a : Formula} -> Proof (Imp a a)"
                      , "outside {a} = by"
                      ]
                        <> script
                        <> [ "internal Proof where"
                           , "  inside : {a : Formula} -> Imp a a"
                           , "  inside {a} = by"
                           ]
                        <> map ("  " <>) script
                    )
            core <- finalCore checked
            outside <- body core "outside"
            inside <- body core "inside"
            Core.bodyType inside @?= Core.bodyType outside
            Core.computation inside @?= Core.computation outside
            forM_ ["inside", "outside"] $ \name ->
              forM_ ["contract", "closed", "index"] $ \suffix ->
                assertBool "indexed construction lost a certificate" (Map.member (T.unpack (mangleGlobal ["Construction", name, "#" <> suffix])) (coreCertificates core))
        , testCase "native theorem tactics and retained proof preconditions keep their own checking" $ do
            checked <-
              succeeds $
                opened
                  <> T.unlines
                    [ "reflexive : (n : Nat) -> n = n"
                    , "reflexive n = by rfl"
                    , "from-hypothesis : {n : Nat} -> n = 0 -> Nat"
                    , "from-hypothesis {n} h = by apply guarded {n}; exact h"
                    , "result : Nat"
                    , "result = by apply guarded {0}; exact (by rfl)"
                    ]
            evaluates checked "result" 0
            core <- finalCore checked
            result <- body core "result"
            assertBool "native proof precondition was discarded" (not (null (Core.obligations result)))
        , rejects "wrong constructor fields are rejected" "bad : List Nat\nbad = by apply Cons; exact Nil; exact Nil\n"
        , rejects "wrong conclusion indices are rejected" "bad : Proof (Atom 0)\nbad = by apply Proof.K {Atom 0} {Bottom}\n"
        , rejects "unfinished applications are rejected" "bad : List Nat\nbad = by apply Cons; exact 0\n"
        , rejects "trailing construction tactics are rejected" "bad : Nat\nbad = by exact 0; exact 1\n"
        , rejects "unused native evidence cannot be discarded" "bad : Nat\nbad = by have unused : 0 = 1 := rfl; exact 0\n"
        , rejects "native proof tactics cannot stand for data construction" "bad : Nat\nbad = by rfl\n"
        , rejects "failed preconditions are not erased" "bad : Nat\nbad = by apply guarded {1}; exact (by rfl)\n"
        , rejects "object derivations cannot discharge native absurdity" "bad : Nat\nbad = by apply absurd; exact AnyProof.Assume {Bottom}\n"
        , rejects "native theorems do not reflect object derivations" "bad : 0 = 1\nbad = by exact AnyProof.Assume {Bottom}\n"
        , rejects "construction cannot hide unscoped proof evidence in callback lambdas" "bad : Nat\nbad = use (\\x -> (by apply guarded {0}; exact (by rfl))) 0\n"
        ]

opened :: Text
opened = "open import ConstructionFixtures\n"

errors :: Checked -> [Text]
errors checked = [message | Report _ SevError message <- checkedReports checked]

finalCore :: Checked -> IO Core
finalCore checked = snd <$> maybe (assertFailure "missing checked core") pure (checkedFinal checked)

body :: Core -> Text -> IO (Core.Body Certificate)
body core name = case Map.lookup (mangleGlobal ["Construction", name]) (coreBodies core) of
  Just [value] -> pure value
  _ -> assertFailure ("missing constructed body " <> T.unpack name)

evaluates :: Checked -> Text -> Integer -> Assertion
evaluates checked name expected = do
  result <- either assertFailure pure (evaluateEntryWithNats 1000 ("Construction." <> name) [] checked)
  evalValue result @?= NatValue (fromInteger expected)

fixtures :: IO (Build, Imports)
fixtures = do
  library <- either assertFailure pure prelude
  let source =
        T.unlines
          [ "module ConstructionFixtures where"
          , "data List a = Nil | Cons a (List a)"
          , "data Other = Cons Nat"
          , "data Formula = Atom Nat | Bottom | Imp Formula Formula"
          , "data Proof (a : Formula) where"
          , "  K : {a b : Formula} -> Proof (Imp a (Imp b a))"
          , "  S : {a b c : Formula} -> Proof (Imp (Imp a (Imp b c)) (Imp (Imp a b) (Imp a c)))"
          , "  MP : {a b : Formula} -> Proof (Imp a b) -> Proof a -> Proof b"
          , "data AnyProof (a : Formula) where"
          , "  Assume : {a : Formula} -> AnyProof a"
          , "size : List a -> Nat"
          , "size Nil = 0"
          , "size (Cons x xs) = S (size xs)"
          , "plus : Nat -> Nat -> Nat"
          , "plus x y = x + y"
          , "use : (Nat -> Nat) -> Nat -> Nat"
          , "use f n = f n"
          , "guarded : {n : Nat} -> n = 0 -> Nat"
          , "guarded {n} h = n"
          ]
      (checked, build) = checkModule (\_ _ -> []) (initialBuild library) {buildRetainGeneratedText = False} Map.empty Nothing "ConstructionFixtures.px" source
  errors checked @?= []
  exports <- maybe (assertFailure "missing construction fixture exports") pure (Map.lookup [Ident "ConstructionFixtures"] (buildExports build))
  pure (build, Map.singleton (Nothing, [Ident "ConstructionFixtures"]) (Right exports))
