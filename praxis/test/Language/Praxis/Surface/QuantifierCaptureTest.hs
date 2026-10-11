{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.QuantifierCaptureTest (quantifierCaptureTests) where

import Bound (Var (..), toScope)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Builder.Linear (runBuilder)
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.CoreText
import Language.Praxis.Surface.FiniteFixtures (finiteOrdinals)
import Language.Praxis.Surface.Prelude (prelude)
import Language.Praxis.Surface.Syntax
import Test.Tasty
import Test.Tasty.HUnit

quantifierCaptureTests :: TestTree
quantifierCaptureTests =
  testGroup
    "quantifier capture avoidance"
    [ testCase "equal binder hints preserve distinct de Bruijn variables" $ do
        let expression :: Expr Text
            expression =
              Quant Forall (Hint "x") (Just (Below, Nat 2)) Nothing $
                toScope $
                  Quant Forall (Hint "x") (Just (Below, Nat 2)) Nothing $
                    toScope (Rel RelEq (Var (F (B ()))) (Var (B ())))
        rendered expression @?= Right "(∀ q < 2. (∀ q' < 2. (q = q')))"
    , testCase "a binder cannot capture a free core variable" $ do
        let expression = Quant Exists (Hint "x") (Just (Below, Nat 2)) Nothing (toScope (Rel RelEq (Var (B ())) (Var (F "q"))))
        rendered expression @?= Right "(∃ q' < 2. (q' = q))"
    , testCase "a binder cannot capture a variable inside a generated raw term" $ do
        let expression :: Expr Text
            expression = Quant Exists (Hint "x") (Just (Below, Nat 2)) Nothing (toScope (Rel RelEq (Var (B ())) (Global (Ref RefBuiltin "(add q 1)"))))
        rendered expression @?= Right "(∃ q' < 2. (q' = (add q 1)))"
    , testCase "numeric and finite shadowing retain the outer decoder bound" $ do
        p <- either assertFailure pure prelude
        let checked = checkSource p "capture.px" ("module Capture where\n" <> finiteOrdinals <> source)
        [message | Report _ SevError message <- checkedReports checked] @?= ([] :: [Text])
        assertBool "the theorem did not certify" ("Capture.shadow" `elem` checkedTheorems checked)
    ]
  where
    rendered = fmap runBuilder . propText (const "q") CVar
    source =
      T.unlines
        [ "size : {n : Nat} -> Fin n -> Nat"
        , "size {n} i = n"
        , "shadow : ∀ (n : Nat) < 3, ∀ (n : Fin n), rank n < size n"
        , "shadow = by"
        , "  intro number"
        , "  intro ordinal"
        , "  have h := bounded ordinal"
        , "  cong"
        ]
