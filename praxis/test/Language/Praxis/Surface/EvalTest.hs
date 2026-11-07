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
    , testCase "values print operators infix and names unqualified unless they clash" $ do
        checked <- check displaySource
        let value name = evalValue <$> either assertFailure pure (evaluateEntry 1000 ("Shown." <> name) checked)
            shown depth name = renderValueWith (displayOf checked) depth <$> value name
        shown 12 "nested" >>= (@?= "(A :=> B) :=> A :=> B")
        shown 12 "lefts" >>= (@?= "A :+ B :+ A")
        shown 12 "rights" >>= (@?= "A :+ (B :+ A)")
        shown 12 "tighter" >>= (@?= "A :+ B :=> A")
        shown 12 "looser" >>= (@?= "A :+ (B :=> A)")
        shown 12 "wrapped" >>= (@?= "Wrap (A :=> B) 3")
        shown 12 "clash" >>= (@?= "Pair P.K Q.K")
        shown 12 "stored" >>= (@?= "Leaf :+: Leaf")
        shown 0 "wrapped" >>= (@?= "Wrap ...")
        shown 1 "nested" >>= (@?= "(... :=> ...) :=> ... :=> ...")
        -- Without the module's fixities every operator is the parser's default, left-associative.
        renderValue 12 <$> value "nested" >>= (@?= "A :=> B :=> (A :=> B)")
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
    displaySource =
      T.unlines
        [ "module Shown where"
        , "data F = A | B | F :=> F | F :+ F"
        , "infixr 5 :=>"
        , "infixl 6 :+"
        , "data W = Wrap F Nat"
        , "data Q = K"
        , "data P = K | Pair P Q"
        , "data T where"
        , "  Leaf : T"
        , "  (:+:) : {m : Nat} -> T -> T -> T"
        , "nested : F"
        , "nested = (A :=> B) :=> A :=> B"
        , "lefts : F"
        , "lefts = (A :+ B) :+ A"
        , "rights : F"
        , "rights = A :+ (B :+ A)"
        , "tighter : F"
        , "tighter = (A :+ B) :=> A"
        , "looser : F"
        , "looser = A :+ (B :=> A)"
        , "wrapped : W"
        , "wrapped = Wrap (A :=> B) 3"
        , "clash : P"
        , "clash = Pair P.K Q.K"
        , "stored : T"
        , "stored = (:+:) {3} Leaf Leaf"
        ]
