{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.ExtractTest (extractTests) where

import Data.Either (isLeft)
import Data.Text qualified as T
import Language.Praxis.Runtime qualified as R
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Extract
import Language.Praxis.Surface.Prelude (prelude, renderPreludeError)
import Test.Tasty
import Test.Tasty.HUnit

extractTests :: TestTree
extractTests =
  testGroup
    "Surface extraction"
    [ testCase "JSON contains only value and rejects invalid natural domains" $ do
        p <- exported "API.add" source
        R.evaluateJSONText 10000 p "{\"value\":[2,3]}" @?= "{\"value\":\"5\"}"
        mapM_
          (\input -> assertBool (T.unpack input) ("error" `T.isInfixOf` R.evaluateJSONText 10000 p input))
          ["{\"value\":[-1,2]}", "{\"value\":[1.5,2]}", "{\"value\":[2]}", "{\"value\":[2,3],\"type\":\"Nat\"}", "not json"]
    , testCase "datatype membership checks every nested field and constructor" $ do
        p <- exported "API.total" source
        let list = R.DataValue "API.List.Cons" [R.NatValue 7, R.DataValue "API.List.Nil" []]
        fmap R.resultValue (R.evaluate 10000 p [list]) @?= Right (R.NatValue 7)
        assertBool "accepted wrong field type" $ isLeft (R.evaluate 10000 p [R.DataValue "API.List.Cons" [R.DataValue "API.List.Nil" [], R.DataValue "API.List.Nil" []]])
        assertBool "accepted a foreign constructor" $ isLeft (R.evaluate 10000 p [R.DataValue "API.Fin.Zero" [R.NatValue 1]])
    , testCase "GADT membership checks computed and recovered indices" $ do
        p <- exported "API.two" source
        let nil = R.DataValue "API.Vec.VNil" []
            cons n xs = R.DataValue "API.Vec.VCons" [R.NatValue n, xs]
            vec = cons 4 (cons 5 nil)
        fmap R.resultValue (R.evaluate 10000 p [vec]) @?= Right vec
        assertBool "accepted wrong vector length" $ isLeft (R.evaluate 10000 p [cons 4 nil])
        assertBool "accepted nil at length two" $ isLeft (R.evaluate 10000 p [nil])
    , testCase "erased constructor proofs are checked at the JSON boundary" $ do
        p <- exported "API.bound" source
        fmap R.resultValue (R.evaluate 10000 p [R.DataValue "API.Bounded.Mk" [R.NatValue 3]]) @?= Right (R.NatValue 3)
        assertBool "accepted a false precondition" $ isLeft (R.evaluate 10000 p [R.DataValue "API.Bounded.Mk" [R.NatValue 4]])
    , testCase "callbacks preserve their captured environment" $ do
        p <- exported "API.shift" source
        let list n = R.DataValue "API.List.Cons" [R.NatValue n, R.DataValue "API.List.Nil" []]
        fmap R.resultValue (R.evaluate 10000 p [R.NatValue 8, list 4]) @?= Right (list 12)
    , testCase "JSON output cannot unfold an exponentially shared tree without a limit" $ do
        p <-
          exported
            "Large.grow"
            ( T.unlines
                [ "module Large where"
                , "data Tree = Leaf | Fork Tree Tree"
                , "grow : Nat -> Tree"
                , "grow 0 = Tree.Leaf"
                , "grow (S n) = Tree.Fork (grow n) (grow n)"
                ]
            )
        assertBool "unbounded JSON expansion" ("JSON output limit exceeded" `T.isInfixOf` R.evaluateJSONText 1000 p "{\"value\":[20]}")
    , testCase "failed checks and proof-requiring entry points are not extracted" $ do
        p <- either (assertFailure . renderPreludeError) pure prelude
        let failed = checkSource p "bad.px" (source <> "\nwrong : 0 = 1\nwrong = by rfl\n")
        assertBool "exported an erroneous module" (isLeft (extractProgram "API.add" failed))
        let valid = checkSource p "api.px" source
        assertBool "erased an entry precondition" (isLeft (extractProgram "API.precondition" valid))
    ]
  where
    exported name src = do
      p <- either (assertFailure . renderPreludeError) pure prelude
      let checked = checkSource p "api.px" src
      [reportMessage r | r <- checkedReports checked, reportSeverity r == SevError] @?= []
      either (assertFailure . renderExtractError) pure (extractProgram name checked)
    source =
      T.unlines
        [ "module API where"
        , "data List a = Nil | Cons a (List a)"
        , "data Fin (n : Nat) where"
        , "  Zero : {n : Nat} -> Fin (S n)"
        , "data Vec (n : Nat) a where"
        , "  VNil : Vec 0 a"
        , "  VCons : {n : Nat} -> a -> Vec n a -> Vec (S n) a"
        , "data Bounded where"
        , "  Mk : {n : Nat} -> n < 4 -> Bounded"
        , "add : Nat -> Nat -> Nat"
        , "add x y = x + y"
        , "total : List Nat -> Nat"
        , "total List.Nil = 0"
        , "total (List.Cons x xs) = x + total xs"
        , "two : Vec 2 Nat -> Vec 2 Nat"
        , "two xs = xs"
        , "bound : Bounded -> Nat"
        , "bound (Bounded.Mk {n} h) = n"
        , "map : (Nat -> Nat) -> List Nat -> List Nat"
        , "map f List.Nil = List.Nil"
        , "map f (List.Cons x xs) = List.Cons (f x) (map f xs)"
        , "shift : Nat -> List Nat -> List Nat"
        , "shift n xs = map (\\x -> n + x) xs"
        , "precondition : {n : Nat} -> n < 4 -> Nat"
        , "precondition {n} h = n"
        ]
