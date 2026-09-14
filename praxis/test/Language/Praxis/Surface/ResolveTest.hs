{-# LANGUAGE OverloadedStrings #-}

-- | The search of resolution: its policies, and its bound.
module Language.Praxis.Surface.ResolveTest (resolveTests) where

import Language.Praxis.Surface.Resolve
import Test.Tasty
import Test.Tasty.HUnit

resolveTests :: TestTree
resolveTests =
  testGroup
    "resolution"
    [ testCase "backtracking takes the next clause when one's subgoals fail" $
        solve Backtrack graph 10 3 @?= Right [3, 1]
    , testCase "coherence refuses two clauses applying, and takes the only one" $ do
        solve (Coherent overlap) graph 10 3 @?= Left "two ways on from 3"
        solve (Coherent overlap) graph 10 1 @?= Right [1]
    , testCase "a goal no clause applies to, a refusal, and a goal deeper than the bound fail as the database says" $ do
        solve Backtrack graph 10 2 @?= Left "no way on from 2"
        solve Backtrack graph 10 4 @?= Left "4 is closed"
        solve Backtrack graph 10 5 @?= Left "deeper than the bound at 5"
    , testCase "the clauses for every goal come first" $
        solve Backtrack graph {dbEvery = [\g -> if g == 3 then Just (Reduce [] (const [0])) else Nothing]} 10 3 @?= Right [0]
    ]
  where
    overlap g = "two ways on from " <> show g

{- |
A way from a number to 1, the result the numbers passed: from 3 through 2,
which leads nowhere, or through 1; 4 is refused; 5 leads to itself.
-}
graph :: Database Int Int [Int] String
graph = Database id edges [] (\g -> "no way on from " <> show g) (\g -> "deeper than the bound at " <> show g)
  where
    edges = \case
      3 -> [to 2, to 1]
      1 -> [const (Just (Reduce [] (const [1])))]
      4 -> [const (Just (Refuse "4 is closed"))]
      5 -> [to 5]
      _ -> []
    to n g = Just (Reduce [n] (\rs -> g : concat rs))
