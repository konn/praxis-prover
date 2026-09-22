{-# LANGUAGE OverloadedStrings #-}

-- | Erasure must preserve both computational argument positions and proof obligations.
module Language.Praxis.Surface.TermTest (termTests) where

import Control.Monad (forM_)
import Data.Either (isLeft)
import Data.Text (Text)
import Language.Praxis.Surface.CoreText (CT (..), termCT)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw qualified as R
import Language.Praxis.Surface.Term qualified as Term
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
    , testCase "a schema's captured values retain their proof obligations" $ do
        let input = apps (Global (Ref (RefPartial 1) "f")) [Global (Ref RefStatic "g"), Absurd (Irrelevant (raw 1))] :: Expr Text
        prepared <- either assertFailure pure (Term.prepareTerm input)
        Term.obligations prepared @?= [(Bottom, raw 1)]
        termCT CVar (Term.toExpr (Term.computation prepared)) @?= Right (CPartial "f" [CStatic "g", CNum 0] 1)
    ]
  where
    call :: Text -> [Expr Text] -> Expr Text
    call f = apps (Global (Ref RefFunction f))
    proof :: Expr Text -> Int -> Expr Text
    proof p n = ProofArg p (Irrelevant (raw n))
    raw :: Int -> R.Located R.Expr
    raw n = R.Located (R.Span (n, 1) (n, 4)) (R.EName (R.QName [] (R.Ident "h")))
