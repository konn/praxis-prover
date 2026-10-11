{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.CoreTest (coreTests) where

import Bound (Var (..), toScope)
import Data.Either (isLeft)
import Language.Praxis.Surface.Core qualified as Core
import Language.Praxis.Surface.Env (CtorInfo (..), DataInfo (..), Env (..), addData, emptyEnv)
import Language.Praxis.Surface.Pretty qualified as Pretty
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw qualified as R
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
    , testCase "index transport validates all equalities before retaining their obligations" $ do
        let vec ix = TData "Vec" [TNat] [ix]
            vars = [("n", TNat), ("m", TNat), ("xs", vec (IxVar "n"))]
            target = vec (IxVar "m")
            raw = R.Located R.noSpan (R.EProof (R.RBy []))
            proof p = ProofArg p (Irrelevant raw)
            transport ps = Transport target (Var 2) ps
            equality = Rel RelEq (Var 0) (Var 1)
            check = Core.elaborateNamed emptyEnv [] vars
        assertBool "missing equality" (isLeft (check (transport [])))
        assertBool "wrong equality" (isLeft (check (transport [proof (Rel RelEq (Var 0) (Var 0))])))
        assertBool "different type structure" (isLeft (check (Transport (TData "Other" [TNat] [IxVar "m"]) (Var 2) [proof equality])))
        body <- either assertFailure pure (check (transport [proof equality]))
        Core.bodyType body @?= target
        Core.computation body @?= Term.Variable 2
        length (Core.obligations body) @?= 1
        Core.obligations (Core.mapObligations (const ()) body) @?= [()]
        pending <- either assertFailure pure (Term.prepareTerm (transport [proof equality]))
        assertBool "term lowering erased equality evidence" (isLeft (Term.withoutObligations pending))
    , testCase "fixed callback parameters retain their schema identity and signature" $ do
        let ty = TArrow TNat TNat
            ref = Ref RefStatic "f_1"
            env = emptyEnv {envSchemas = [("f", ref, ty)]}
            parameter r i = SchemaParameter ty r (Var i)
            check = Core.elaborateNamed env [] [("f", ty), ("g", ty)]
        assertBool "a bare function variable is no runtime function code" (isLeft (check (Var 0)))
        assertBool "an annotation cannot erase static identity" (isLeft (check (Typed ty [] [] (Var 0))))
        assertBool "a natural is no callback environment" (isLeft (Core.elaborateNamed env [] [("f", TNat)] (parameter ref 0)))
        assertBool "forged static identity" (isLeft (check (parameter (Ref RefStatic "f_2") 0)))
        assertBool "swapped closure environment" (isLeft (check (parameter ref 1)))
        body <- either assertFailure pure (check (Typed TNat [] [] (App (parameter ref 0) (Nat 3))))
        Core.computation body @?= Term.Invoke (Term.Parameter ref (Term.Variable 0)) [Term.Literal 3]
    , testCase "a callback cannot be stored through a polymorphic data field" $ do
        let callbackTy = TArrow TNat TNat
            ref = Ref RefStatic "f_1"
            (declared, box) = addData emptyEnv (R.Ident "Box") [("a", KType)] [(R.Ident "Mk", [TParam 0 []])]
            env = declared {envSchemas = [("f", ref, callbackTy)]}
            ctor = Ref RefConstructor (ctorCore (head (dataCtors box)))
            callback = SchemaParameter callbackTy ref (Var 0)
            forged = Typed (TData "Box" [callbackTy] []) [] [] (App (Global ctor) callback)
        assertBool "function-valued field" (isLeft (Core.elaborateNamed env [] [("f", callbackTy)] forged))
    , testCase "internal packed callbacks cannot bypass the typed source boundary" $ do
        let packed = SchemaPacked [Hint "env", Hint "arg"] (toScope (Var (B 1))) (Nat 0)
            check = Core.elaborate emptyEnv [] []
        assertBool "an internal callback was accepted as source" (isLeft (check packed))
        assertBool "a type annotation accepted an internal callback" (isLeft (check (Typed (TArrow TNat TNat) [] [] packed)))
        assertBool "an internal callback application bypassed validation" (isLeft (check (Typed TNat [] [] (App packed (Nat 0)))))
    , testCase "callback lambdas check their bodies and retain captured values" $ do
        let ty = TArrow TNat TNat
            add x y = Typed TNat [] [] (apps (Global (Ref RefBuiltin "add")) [x, y])
            closure = SchemaClosure ty (Lam [Hint "x"] (toScope (add (Var (B 0)) (Var (F 0)))))
        body <- either assertFailure pure (Core.elaborate emptyEnv [] [TNat] closure)
        Core.computation body @?= Term.Closure 1 (Term.Call (Ref RefBuiltin "add") [Term.Variable (B 0), Term.Variable (F 0)])
        let forged = SchemaClosure (TArrow TNat (TData "Box" [] [])) (Lam [Hint "x"] (toScope (Nat 0)))
            raw = R.Located R.noSpan (R.EProof (R.RBy []))
            unproved = SchemaClosure ty (Lam [Hint "x"] (toScope (Typed TNat [] [] (Absurd (Irrelevant raw)))))
        assertBool "forged callback result" (isLeft (Core.elaborate emptyEnv [] [] forged))
        assertBool "an unused callback cannot erase a proof" (isLeft (Core.elaborate emptyEnv [] [] unproved))
    , testCase "core printing uses surface types and preserves application precedence" $ do
        let successor x = Typed TNat [] [] (App (Global (Ref RefBuiltin "S")) x)
        value <- either assertFailure pure (Core.elaborate emptyEnv [] [TNat] (successor (successor (Var 0))))
        Core.dump value @?= "\\(v0 : Nat) -> (S (S v0) : Nat)"
        Pretty.typeText emptyEnv (Pretty.Scope ["a"] ["n"] []) 0 (TArrow (TArrow TNat TNat) (TData "Example.Vec" [TParam 0 []] [IxSucc (IxParam 0)])) @?= "(Nat -> Nat) -> Example.Vec a (S n)"
    ]
