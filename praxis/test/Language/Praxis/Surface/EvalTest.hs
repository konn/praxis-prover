{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.EvalTest (evalTests) where

import Data.Either (isLeft)
import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Eval
import Language.Praxis.Surface.Prelude (prelude)
import Test.Tasty
import Test.Tasty.HUnit

evalTests :: TestTree
evalTests =
  testGroup
    "surface evaluator"
    [ testCase "shared constructor trees avoid exponential recursion" $ do
        checked <- check treeSource
        result <- either assertFailure pure (evaluateEntry 10000 "Trees.answer" checked)
        evalValue result @?= NatValue (2 ^ (21 :: Int) - 1)
        assertBool "evaluation unfolded the exponential tree" (evalCalls result < 200 && evalNodes result < 200)
    , testCase "fuel and unsupported entry points fail explicitly" $ do
        checked <- check treeSource
        assertBool "fuel was ignored" (isLeft (evaluateEntry 1 "Trees.answer" checked))
        assertBool "a function needing an argument was evaluated" (isLeft (evaluateEntry 10000 "Trees.grow" checked))
        assertBool "an unknown entry was accepted" (isLeft (evaluateEntry 10000 "Trees.missing" checked))
    , testCase "runtime naturals are checked against the entry signature" $ do
        checked <- check treeSource
        result <- either assertFailure pure (evaluateEntryWithNats 10000 "Trees.count" [20] checked)
        evalValue result @?= NatValue (2 ^ (21 :: Int) - 1)
        assertBool "a raw number was accepted as a constructor tree" (isLeft (evaluateEntryWithNats 10000 "Trees.size" [0] checked))
    , testCase "a failed module cannot supply evaluation results" $ do
        p <- either assertFailure pure prelude
        let checked = checkSource p "failed.px" (treeSource <> "\nwrong : 0 = 1\nwrong = by rfl\n")
        assertBool "the erroneous module was evaluated" (isLeft (evaluateEntry 10000 "Trees.answer" checked))
    ]
  where
    check source = do
      p <- either assertFailure pure prelude
      let checked = checkSource p "trees.px" source
      [reportMessage r | r <- checkedReports checked, reportSeverity r == SevError] @?= []
      pure checked
    treeSource =
      T.unlines
        [ "module Trees where"
        , "data Tree = Leaf | Branch Tree Tree"
        , "grow : Nat -> Tree"
        , "grow 0 = Leaf"
        , "grow (S n) = Branch (grow n) (grow n)"
        , "size : Tree -> Nat"
        , "size Leaf = 1"
        , "size (Branch l r) = S (size l + size r)"
        , "answer : Nat"
        , "answer = size (grow 20)"
        , "count : Nat -> Nat"
        , "count n = size (grow n)"
        ]
