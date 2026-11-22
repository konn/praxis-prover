{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.ComputationIndexTest (computationIndexTests) where

import Data.Either (isLeft)
import Data.Text.Builder.Linear (runBuilder)
import Language.Praxis.Surface.Core qualified as Core
import Language.Praxis.Surface.Core.Types qualified as Reified
import Language.Praxis.Surface.CoreText qualified as CT
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Index (applyIx, emptySubst, ixToExprWith, refineEqualities, renderIndexRefineError, substKeys)
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
    [ testCase "given equalities retain stuck computations while propagating substitutions" $ do
        let x = IxMeta 0 (Hint "x")
            computed = IxFun "f" [x]
            refine equations = refineEqualities noUnfold [] (const (Just 0)) equations emptySubst
        (solved, residual) <- either (assertFailure . renderIndexRefineError) pure (refine [(computed, IxNat 0), (x, IxNat 0)])
        applyIx solved computed @?= IxFun "f" [IxNat 0]
        residual @?= [(IxFun "f" [IxNat 0], IxNat 0)]
        (fields, nested) <- either (assertFailure . renderIndexRefineError) pure (refine [(IxCon "C" [x, computed], IxCon "C" [IxNat 0, IxNat 0])])
        applyIx fields x @?= IxNat 0
        nested @?= residual
        let y = IxMeta 1 (Hint "y")
        (opaque, equalCalls) <- either (assertFailure . renderIndexRefineError) pure (refine [(computed, IxFun "f" [y])])
        substKeys opaque @?= []
        equalCalls @?= [(computed, IxFun "f" [y])]
        assertBool "contradictory givens" (isLeft (refine [(x, IxNat 0), (x, IxNat 1)]))
        assertBool "a constructor cycle" (isLeft (refine [(x, IxSucc x)]))
        (_, recursive) <- either (assertFailure . renderIndexRefineError) pure (refine [(x, computed)])
        recursive @?= [(x, computed)]
    , testCase "schema captures survive substitution and explicit type reflection" $ do
        let index = IxFun "compute" [IxSchema "w_1", IxPartial "step" 1 1 [IxParam 0, IxBound 0 0]]
            concrete = IxFun "compute" [IxSchema "w_1", IxPartial "step" 1 1 [IxNat 3, IxBound 0 0]]
            ty = TData "Box" [] [concrete]
        instValues [IxNat 3] index @?= concrete
        ixBounds concrete @?= [(0, 0)]
        Reified.SomeType reflected <- either (assertFailure . Reified.renderReflectError) pure (Reified.reflectType ty)
        Reified.forgetType reflected @?= ty
        assertBool "negative capture prefix" (isLeft (Reified.reflectType (TData "Box" [] [IxPartial "step" 1 (-1) []])))
        assertBool "missing captures" (isLeft (Reified.reflectType (TData "Box" [] [IxPartial "step" 1 2 [IxNat 0]])))
    , testCase "partial index computations preserve prefix and suffix captures" $ do
        let index = IxFun "compute" [IxPartial "step" 1 1 [IxBound 0 0, IxSchema "op", IxBound 0 1]]
        expression <- maybe (assertFailure "the index could not be materialized") pure (ixToExprWith (\case IxBound 0 0 -> Just (Var "before"); IxBound 0 1 -> Just (Var "after"); _ -> Nothing) (const Nothing) index)
        actual <- either (assertFailure . CT.renderCoreTextError) pure (CT.termCT CT.CVar expression)
        actual @?= CT.CSym "compute" [CT.CIndexedPartial "step" [CT.CVar "before", CT.CStatic "op", CT.CVar "after"] 1 1]
        CT.varsCT actual @?= ["before", "after"]
        runBuilder (CT.render (CT.CIndexedPartial "step" [CT.CVar "y_1"] 1 1)) @?= "{λ y_2. (step y_1 y_2)}"
    , testCase "dictionary runtime captures determine their result index" $ do
        let scheme = Scheme [] [("n", TNat)] (TArrow TNat (box (IxParam 0)))
            (env, function) = setFunRuntime [0] (addFunction emptyEnv (Ident "indexed") scheme 1 [])
            entry index capture = Dictionary (TArrow TNat (box index)) (App (Global (Ref (RefIndexedPartial 1 1) (funCore function))) capture)
            captured = Typed TNat [] [] (Var 0)
            check = Core.elaborateNamed env [] [namedBinder "n" TNat]
        body <- either (assertFailure . Core.renderCoreError) pure (check (entry (IxNat 3) (Nat 3)))
        Core.computation body @?= Term.Call (Ref (RefIndexedPartial 1 1) (funCore function)) [Term.Literal 3]
        assertBool "an open static capture was accepted" (isLeft (check (entry (IxBound 0 0) captured)))
        assertBool "a forged result index" (isLeft (check (entry (IxNat 7) (Nat 3))))
        let (valueEnv, valueFunction) = setFunRuntime [0] (addFunction env (Ident "indexedValue") (Scheme [] [("n", TNat)] (box (IxParam 0))) 0 [])
            valueEntry capture = Dictionary (box (IxBound 0 0)) (App (Global (Ref RefFunction (funCore valueFunction))) capture)
            checkValue = Core.elaborateNamed valueEnv [] [namedBinder "n" TNat]
        _ <- either (assertFailure . Core.renderCoreError) pure (checkValue (valueEntry captured))
        assertBool "an out-of-scope capture" (isLeft (checkValue (valueEntry (Typed TNat [] [] (Var 1)))))
        assertBool "a capture with the wrong type" (isLeft (checkValue (valueEntry (Typed (box (IxFree (Named "n"))) [] [] (Var 0)))))
    , testCase "registered projections recover only their context variable's index" $ do
        let (withBox, _) = addIndexedData emptyEnv (Ident "Box") [] [TNat] [DataBinder "n" False (IndexParameter 0)] [[Ident "project"]] []
            (withProjection, projection) = addFunction withBox (Ident "project") (Scheme [] [("n", TNat)] (TArrow (box (IxParam 0)) TNat)) 1 []
            (withOther, other) = addFunction withProjection (Ident "other") (Scheme [] [("n", TNat)] (TArrow (box (IxParam 0)) TNat)) 1 []
            (env, function) = setFunRuntime [0] (addFunction withOther (Ident "indexed") (Scheme [] [("n", TNat)] (box (IxParam 0))) 0 [])
            projected f = Typed TNat [] [] (App (Global (Ref RefFunction (funCore f))) (Typed (box (IxFree (Named "n"))) [] [] (Var 0)))
            call index f = Typed (box index) [] [(0, index)] (App (Global (Ref RefFunction (funCore function))) (projected f))
            check = Core.elaborateNamed env [] [namedBinder "value" (box (IxFree (Named "n")))]
        _ <- either (assertFailure . Core.renderCoreError) pure (check (call (IxFree (Named "n")) projection))
        assertBool "a different index was inferred from the projection" (isLeft (check (call (IxNat 7) projection)))
        assertBool "an ordinary function acquired a projection contract" (isLeft (check (call (IxFree (Named "n")) other)))
    , testCase "ordinary runtime calls also check the captured value index" $ do
        let scheme = Scheme [] [("n", TNat)] (box (IxParam 0))
            (env, function) = setFunRuntime [0] (addFunction emptyEnv (Ident "indexed") scheme 0 [])
            call index = Typed (box index) [] [(0, index)] (App (Global (Ref RefFunction (funCore function))) (Typed TNat [] [] (Var 0)))
            check = Core.elaborateNamed env [] [namedBinder "n" TNat]
        _ <- either (assertFailure . Core.renderCoreError) pure (check (call (IxBound 0 0)))
        assertBool "an annotation replaced the captured value" (isLeft (check (call (IxNat 7))))
    ]
  where
    box index = TData "Box" [] [index]
