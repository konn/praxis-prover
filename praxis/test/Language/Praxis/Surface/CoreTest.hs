{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.CoreTest (coreTests) where

import Data.Either (isLeft)
import Language.Praxis.Surface.Core qualified as Core
import Language.Praxis.Surface.Env (emptyEnv)
import Language.Praxis.Surface.Pretty qualified as Pretty
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Term qualified as Term
import Language.Praxis.Surface.Types
import Test.Tasty
import Test.Tasty.HUnit

coreTests :: TestTree
coreTests =
  testGroup
    "explicit core"
    [ testCase "variables cannot escape their typed context" $ do
        assertBool "out of scope" (isLeft (Core.elaborate emptyEnv [] [TNat] (Typed TNat [] [] (Var 1))))
        assertBool "wrong type" (isLeft (Core.elaborate emptyEnv [] [TData "Box" [] []] (Typed TNat [] [] (Var 0))))
    , testCase "global annotations cannot invent signatures" $ do
        let succAt t = Typed t [] [] (App (Global (Ref RefBuiltin "S")) (Nat 0))
        assertBool "wrong result" (isLeft (Core.elaborate emptyEnv [] [] (succAt (TData "Box" [] []))))
        assertBool "unknown name" (isLeft (Core.elaborate emptyEnv [] [] (Typed TNat [] [] (Global (Ref RefFunction "unknown")))))
        value <- either assertFailure pure (Core.elaborate emptyEnv [] [] (succAt TNat))
        Core.computation value @?= Term.Call (Ref RefBuiltin "S") [Term.Literal 0]
    , testCase "dictionary annotations cannot invent implementations" $ do
        assertBool "unknown dictionary" (isLeft (Core.elaborate emptyEnv [] [] (Dictionary TNat (Global (Ref RefStatic "missing")))))
        assertBool "a free dictionary value" (isLeft (Core.elaborate emptyEnv [] [TNat] (Dictionary TNat (Var 0))))
    , testCase "unresolved value indices cannot cross the explicit boundary" $ do
        assertBool "unknown index" (isLeft (Core.elaborate emptyEnv [] [TData "Vec" [TNat] [IxHole]] (Var 0)))
    , testCase "core printing uses surface types and preserves application precedence" $ do
        let successor x = Typed TNat [] [] (App (Global (Ref RefBuiltin "S")) x)
        value <- either assertFailure pure (Core.elaborate emptyEnv [] [TNat] (successor (successor (Var 0))))
        Core.dump value @?= "\\(v0 : Nat) -> (S (S v0) : Nat)"
        Pretty.typeText emptyEnv (Pretty.Scope ["a"] ["n"] []) 0 (TArrow (TArrow TNat TNat) (TData "Example.Vec" [TParam 0 []] [IxSucc (IxParam 0)])) @?= "(Nat -> Nat) -> Example.Vec a (S n)"
    ]
