{-# LANGUAGE OverloadedStrings #-}

-- | Instantiating a generic predicate retains the full indexed type.
module Language.Praxis.Surface.ExactPredicateTest (exactPredicateTests) where

import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Prelude
import Test.Tasty
import Test.Tasty.HUnit

exactPredicateTests :: TestTree
exactPredicateTests =
  testGroup
    "exact indexed type predicates"
    [ testCase "a generic Finite theorem applies at symbolic Fin n" $ do
        checked <-
          check
            ( prefix
                <> T.unlines
                  [ "symbolic : (i : Fin n) -> roundtrip i = i"
                  , "symbolic i = roundtrip-law i"
                  ]
            )
        errors checked @?= []
        assertBool "the explicit generic theorem call was not certified" ("Exact.symbolic" `elem` checkedTheorems checked)
    , testCase "computed indexed values retain the instantiated predicate" $ do
        checked <-
          check
            ( prefix
                <> T.unlines
                  [ "computed : (i : Fin n) -> roundtrip (roundtrip i) = roundtrip i"
                  , "computed i = roundtrip-law (roundtrip i)"
                  ]
            )
        errors checked @?= []
        assertBool "the computed argument theorem was not certified" ("Exact.computed" `elem` checkedTheorems checked)
    , testCase "different indices cannot inhabit one instantiated parameter" $ do
        let valid =
              prefix
                <> T.unlines
                  [ "same-type : Finite a => (x : a) -> (y : a) -> x = x"
                  , "same-type x y = rfl"
                  ]
        before <- check valid
        errors before @?= []
        checked <-
          check
            ( valid
                <> T.unlines
                  [ "wrong-index : (x : Fin n) -> (y : Fin (S n)) -> x = x"
                  , "wrong-index x y = same-type x y"
                  ]
            )
        assertBool "the conflicting indices were ignored" (not (null (errors checked)))
        assertBool "the invalid application was certified" ("Exact.wrong-index" `notElem` checkedTheorems checked)
    ]
  where
    check source = do
      p <- either assertFailure pure prelude
      pure (checkSource p "exact-predicate.px" source)

errors :: Checked -> [Text]
errors checked = [reportMessage report | report <- checkedReports checked, reportSeverity report == SevError]

prefix :: Text
prefix =
  T.unlines
    [ "module Exact where"
    , "data Fin (n : Nat) where"
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
    , "roundtrip-law : Finite a => (x : a) -> roundtrip x = x"
    , "roundtrip-law x = calc"
    , "  roundtrip x"
    , "  = decode (code x)"
    , "  = x := Finite.decode-code x"
    ]
