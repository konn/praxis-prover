{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.ComputationIndexTest (computationIndexTests) where

import Data.Either (isLeft)
import Data.Text.Builder.Linear (runBuilder)
import Language.Praxis.Surface.Core qualified as Core
import Language.Praxis.Surface.Core.Types qualified as Reified
import Language.Praxis.Surface.CoreText qualified as CT
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Index (ixToExprWith)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw (Segment (..))
import Language.Praxis.Surface.Term qualified as Term
import Language.Praxis.Surface.Types
import Test.Tasty
import Test.Tasty.HUnit

computationIndexTests :: TestTree
computationIndexTests =
  testGroup
    "computation indices"
    [ testCase "schema captures survive substitution and explicit type reflection" $ do
        let index = IxFun "compute" [IxSchema "w_1", IxPartial "step" 1 1 [IxParam 0, IxVar "tail"]]
            concrete = IxFun "compute" [IxSchema "w_1", IxPartial "step" 1 1 [IxNat 3, IxVar "tail"]]
            ty = TData "Box" [] [concrete]
        instValues [IxNat 3] index @?= concrete
        ixVars concrete @?= ["tail"]
        Reified.SomeType reflected <- either assertFailure pure (Reified.reflectType ty)
        Reified.forgetType reflected @?= ty
        assertBool "negative capture prefix" (isLeft (Reified.reflectType (TData "Box" [] [IxPartial "step" 1 (-1) []])))
        assertBool "missing captures" (isLeft (Reified.reflectType (TData "Box" [] [IxPartial "step" 1 2 [IxNat 0]])))
    , testCase "partial index computations preserve prefix and suffix captures" $ do
        let index = IxFun "compute" [IxPartial "step" 1 1 [IxVar "before", IxSchema "op", IxVar "after"]]
        expression <- maybe (assertFailure "the index could not be materialized") pure (ixToExprWith (Just . Var) (const Nothing) index)
        actual <- either assertFailure pure (CT.termCT CT.CVar expression)
        actual @?= CT.CSym "compute" [CT.CIndexedPartial "step" [CT.CVar "before", CT.CStatic "op", CT.CVar "after"] 1 1]
        CT.varsCT actual @?= ["before", "after"]
        runBuilder (CT.render (CT.CIndexedPartial "step" [CT.CVar "y_1"] 1 1)) @?= "{λ y_2. (step y_1 y_2)}"
    , testCase "dictionary runtime captures determine their result index" $ do
        let scheme = Scheme [] [("n", TNat)] (TArrow TNat (box (IxParam 0)))
            (env, function) = setFunRuntime [0] (addFunction emptyEnv (Ident "indexed") scheme 1 [])
            entry index capture = Dictionary (TArrow TNat (box index)) (App (Global (Ref (RefIndexedPartial 1 1) (funCore function))) capture)
            captured = Typed TNat [] [] (Var 0)
            check = Core.elaborateNamed env [] [("n", TNat)]
        body <- either assertFailure pure (check (entry (IxNat 3) (Nat 3)))
        Core.computation body @?= Term.Call (Ref (RefIndexedPartial 1 1) (funCore function)) [Term.Literal 3]
        assertBool "an open static capture was accepted" (isLeft (check (entry (IxVar "n") captured)))
        assertBool "a forged result index" (isLeft (check (entry (IxNat 7) (Nat 3))))
        let (valueEnv, valueFunction) = setFunRuntime [0] (addFunction env (Ident "indexedValue") (Scheme [] [("n", TNat)] (box (IxParam 0))) 0 [])
            valueEntry capture = Dictionary (box (IxVar "n")) (App (Global (Ref RefFunction (funCore valueFunction))) capture)
            checkValue = Core.elaborateNamed valueEnv [] [("n", TNat)]
        _ <- either assertFailure pure (checkValue (valueEntry captured))
        assertBool "an out-of-scope capture" (isLeft (checkValue (valueEntry (Typed TNat [] [] (Var 1)))))
        assertBool "a capture with the wrong type" (isLeft (checkValue (valueEntry (Typed (box (IxVar "n")) [] [] (Var 0)))))
    , testCase "registered projections recover only their context variable's index" $ do
        let (withBox, _) = addIndexedData emptyEnv (Ident "Box") [] [TNat] [DataBinder "n" False (IndexParameter 0)] [[Ident "project"]] []
            (withProjection, projection) = addFunction withBox (Ident "project") (Scheme [] [("n", TNat)] (TArrow (box (IxParam 0)) TNat)) 1 []
            (withOther, other) = addFunction withProjection (Ident "other") (Scheme [] [("n", TNat)] (TArrow (box (IxParam 0)) TNat)) 1 []
            (env, function) = setFunRuntime [0] (addFunction withOther (Ident "indexed") (Scheme [] [("n", TNat)] (box (IxParam 0))) 0 [])
            projected f = Typed TNat [] [] (App (Global (Ref RefFunction (funCore f))) (Typed (box (IxVar "n")) [] [] (Var 0)))
            call index f = Typed (box index) [] [(0, index)] (App (Global (Ref RefFunction (funCore function))) (projected f))
            check = Core.elaborateNamed env [] [("value", box (IxVar "n"))]
        _ <- either assertFailure pure (check (call (IxVar "n") projection))
        assertBool "a different index was inferred from the projection" (isLeft (check (call (IxNat 7) projection)))
        assertBool "an ordinary function acquired a projection contract" (isLeft (check (call (IxVar "n") other)))
    , testCase "ordinary runtime calls also check the captured value index" $ do
        let scheme = Scheme [] [("n", TNat)] (box (IxParam 0))
            (env, function) = setFunRuntime [0] (addFunction emptyEnv (Ident "indexed") scheme 0 [])
            call index = Typed (box index) [] [(0, index)] (App (Global (Ref RefFunction (funCore function))) (Typed TNat [] [] (Var 0)))
            check = Core.elaborateNamed env [] [("n", TNat)]
        _ <- either assertFailure pure (check (call (IxVar "n")))
        assertBool "an annotation replaced the captured value" (isLeft (check (call (IxNat 7))))
    ]
  where
    box index = TData "Box" [] [index]
