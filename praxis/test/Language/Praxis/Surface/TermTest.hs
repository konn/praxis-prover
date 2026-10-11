{-# LANGUAGE OverloadedStrings #-}

-- | Erasure must preserve both computational argument positions and proof obligations.
module Language.Praxis.Surface.TermTest (termTests) where

import Bound (Var (..), fromScope, toScope)
import Control.Monad (forM_)
import Data.Either (isLeft)
import Data.Text (Text)
import Language.Praxis.Surface.CoreText (CT (..), TermLowering (..), consSeq, fieldT, lowerTermWith, standardLowering, termCT)
import Language.Praxis.Surface.Engine (fromCT)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw qualified as R
import Language.Praxis.Surface.Term qualified as Term
import Language.Praxis.Surface.Types (Ty (..))
import Test.Tasty
import Test.Tasty.HUnit

termTests :: TestTree
termTests =
  testGroup
    "term erasure"
    [ testCase "nested obligations retain their variable scope and source order" $ do
        let first = Rel RelEq (Var "x") (Nat 0)
            second = Rel RelEq (Var "y") (Var "x")
            input = call "f" [proof first 1, call "g" [Var "x", proof second 2], Nat 3]
        prepared <- either assertFailure pure (Term.prepareTerm input)
        Term.computation prepared @?= Term.Call (Ref RefFunction "f") [Term.Call (Ref RefFunction "g") [Term.Variable "x"], Term.Literal 3]
        Term.obligations prepared @?= [(first, raw 1), (second, raw 2)]
    , testCase "bottom elimination occupies a value argument slot" $ do
        let input = call "f" [proof Top 1, Absurd (Irrelevant (raw 2)), Var "x"]
        prepared <- either assertFailure pure (Term.prepareTerm input)
        Term.computation prepared @?= Term.Call (Ref RefFunction "f") [Term.Literal 0, Term.Variable "x"]
        Term.obligations prepared @?= [(Top, raw 1), (Bottom, raw 2)]
    , testCase "ordinary statement lowering refuses pending proof obligations at every depth" $
        forM_ [proof Top 1, call "f" [proof Top 1], call "f" [call "g" [proof Top 1]], Absurd (Irrelevant (raw 1)), call "f" [Absurd (Irrelevant (raw 1))]] $ \e ->
          assertBool "an unproved argument was erased" (isLeft (termCT CVar e))
    , testCase "rewriting an unused computation does not discard its obligations" $ do
        prepared <- either assertFailure pure (Term.prepareTerm (call "f" [proof (Rel RelEq (Var "x") (Nat 0)) 1]))
        let rewritten = Term.mapComputation (const (Term.Literal 0)) prepared
        Term.obligations rewritten @?= Term.obligations prepared
        assertBool "rewriting made a pending term unconditional" (isLeft (Term.withoutObligations rewritten))
    , testCase "callback lambdas pack nullary dictionary methods into their environment" $ do
        let body = Term.Call (Ref RefValueParam "0") [] :: Term.Term (Var Int Text)
            callback = Term.Closure 1 body
            lowering = (standardLowering CVar) {lowerDictionaryValue = \_ -> Right (CVar "emptyValue")}
        lowerTermWith lowering callback
          @?= Right (CCallback (CClosure ["schema_env", "schema_x0"] (fieldT 0 (CVar "schema_env")) []) (consSeq 0 [CVar "emptyValue"]))
    , testCase "reconstructed callbacks do not capture names from their packed environment" $ do
        let callback = CCallback (CClosure ["schema_env", "schema_x0"] (CSym "add" [CVar "schema_x0", fieldT 0 (CVar "schema_env")]) []) (consSeq 0 [CVar "schema_x0"])
            restored = fromCT callback
        foldr (:) [] restored @?= ["schema_x0"]
        case restored of
          SchemaPacked _ _ environment -> foldr (:) [] environment @?= ["schema_x0"]
          _ -> assertFailure "reconstruction lost the callback's closed code"
        termCT CVar restored @?= Right callback
    , testCase "reconstructed nested callbacks retain their fixed code" $ do
        let inner = CCallback (CClosure ["schema_env", "schema_x0"] (CSym "pair" [fieldT 0 (CVar "schema_env"), CVar "schema_x0"]) []) (consSeq 0 [CVar "outer"])
            applied = CSym "map" [inner, CVar "items"]
        termCT CVar (fromCT applied) @?= Right applied
    , testCase "packed callbacks preserve opaque captures and explicit projection code" $ do
        let originalCode = CClosure ["env", "arg"] (CSym "hd" [consSeq 0 [fieldT 0 (CVar "env"), CVar "arg"]]) []
        forM_ [CVar "captured", consSeq 0 [CSym "Ctor" [CVar "x", CVar "y"]]] $ \environment -> do
          let callback = CCallback originalCode environment
          termCT CVar (fromCT callback) @?= Right callback
    , testCase "internal packed callbacks still reject malformed binders and hidden evidence" $ do
        let rawPacked code = SchemaPacked [Hint "env", Hint "arg"] (toScope code) (Nat 0) :: Expr Text
        assertBool "an out-of-scope packed binder was lowered" (isLeft (termCT CVar (rawPacked (Var (B 2)))))
        assertBool "a packed callback erased an unproved argument" (isLeft (termCT CVar (rawPacked (Absurd (Irrelevant (raw 1))))))
    , testCase "substituting a callback changes its code and preserves lambda captures" $ do
        let ty = TArrow TNat TNat
            original = SchemaParameter ty (Ref RefStatic "f_1") (Var "f")
            captured = SchemaClosure ty (Lam [Hint "x"] (toScope (callScoped "add" [Var (B 0), Var (F "x")])))
            substituted = original >>= \v -> if v == "f" then captured else Var v
        substituted @?= captured
        termCT CVar (App substituted (Nat 2)) @?= termCT CVar (App captured (Nat 2))
        let enclosing = Lam [Hint "x"] (toScope (App (fmap F original) (Var (B 0))))
            nested = enclosing >>= \v -> if v == "f" then captured else Var v
        case nested of
          Lam _ scope ->
            fromScope scope @?= App (fmap F captured) (Var (B 0))
          _ -> assertFailure "substitution lost its enclosing binder"
    , testCase "a schema's captured values retain their proof obligations" $ do
        let input = apps (Global (Ref (RefPartial 1) "f")) [Global (Ref RefStatic "g"), Absurd (Irrelevant (raw 1))] :: Expr Text
        prepared <- either assertFailure pure (Term.prepareTerm input)
        Term.obligations prepared @?= [(Bottom, raw 1)]
        termCT CVar (Term.toExpr (Term.computation prepared)) @?= Right (CPartial "f" [CStatic "g", CNum 0] 1)
    ]
  where
    callScoped name = apps (Global (Ref RefFunction name))
    call :: Text -> [Expr Text] -> Expr Text
    call f = apps (Global (Ref RefFunction f))
    proof :: Expr Text -> Int -> Expr Text
    proof p n = ProofArg p (Irrelevant (raw n))
    raw :: Int -> R.Located R.Expr
    raw n = R.Located (R.Span (n, 1) (n, 4)) (R.EName (R.QName [] (R.Ident "h")))
