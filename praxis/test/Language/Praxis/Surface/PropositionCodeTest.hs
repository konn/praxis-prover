{-# LANGUAGE OverloadedStrings #-}

{- |
The code of a proposition, as the encoding writes it into a membership
predicate ('propCode'), against the core's reading of the formula the
surface writes for the same proposition ('propText'): the two are one term,
so that the core's @reify@ and @reflect@ pass between the formula and the
truth of the code, and the code reads as a formula exactly when the core
says so.
-}
module Language.Praxis.Surface.PropositionCodeTest (propositionCodeTests) where

import Bound (Var (..), toScope)
import Control.Exception (displayException)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Builder.Linear (runBuilder)
import Language.Praxis.PRA.Reflection (CodeView (..), codeView, encodeFormula)
import Language.Praxis.PRA.Syntax (canonicalise)
import Language.Praxis.PRA.Syntax.Parser (parseFormula, parseTerm, plainScope)
import Language.Praxis.PRA.Syntax.Pretty (renderTerm)
import Language.Praxis.Surface.CoreText (CT (..), codeIsFormula, propCode, propText, render)
import Language.Praxis.Surface.Prelude (Prelude (..), prelude)
import Language.Praxis.Surface.Syntax
import Test.Tasty
import Test.Tasty.HUnit

propositionCodeTests :: TestTree
propositionCodeTests =
  testGroup
    "codes of propositions"
    [testCase name (agrees prop) | (name, prop) <- samples]

-- | The encoding's code of a proposition is the core's code of the formula written for it, and reads as a formula exactly when the core reads it so.
agrees :: Expr Text -> Assertion
agrees prop = do
  p <- either assertFailure pure prelude
  let sig = preludeSignature p
      sc = plainScope sig
  text <- either assertFailure pure (propText (\h -> "b_" <> h) CVar prop)
  formula <- either (assertFailure . displayException) pure (parseFormula sc (T.unpack (runBuilder text)))
  expected <- either assertFailure pure (encodeFormula sig (const False) formula)
  code <- either assertFailure pure (propCode CVar prop)
  actual <- either (assertFailure . displayException) pure (parseTerm sc (T.unpack (runBuilder (render code))))
  assertEqual ("the code of " <> T.unpack (runBuilder text) <> ": the core reads " <> renderTerm sig id expected <> ", the encoding writes " <> renderTerm sig id actual) (canonicalise expected) (canonicalise actual)
  assertEqual ("whether the code of " <> T.unpack (runBuilder text) <> " reads as a formula") (codeView sig expected /= CodeOther) (codeIsFormula code)

-- | Propositions over the variables x, y, k and n, each relation, connective and quantifier among them.
samples :: [(String, Expr Text)]
samples =
  [ ("a comparison", Rel RelLt x y)
  , ("an equation", Rel RelEq x (s y))
  , ("a disequality", Rel RelNe x y)
  , ("the truth of a variable", Rel RelLt zero x)
  , ("the truth of a successor", Rel RelLt zero (s x))
  , ("the truth of zero", Rel RelLt zero zero)
  , ("a numeral greater than zero", Rel RelGt (Nat 3) zero)
  , ("an equation with one", Rel RelEq x (Nat 1))
  , ("the reversed orders joined", Conn And (Rel RelGt x y) (Rel RelGe x y))
  , ("the truth and the absurd disjoined", Conn Or Top Bottom)
  , ("an implication to a negation", Arrow (Rel RelLt x y) (Not (Rel RelEq x y)))
  , ("an equivalence", Conn Iff (Rel RelLe x y) (Rel RelLt x (s y)))
  , ("a bounded universal", quantified Forall Below k (Rel RelLt var (outer n)))
  , ("a bounded universal at most", quantified Forall AtMost k (Rel RelLe (plus var (Nat 1)) (outer n)))
  , ("a bounded existential", quantified Exists Below k (Rel RelEq (s var) (outer n)))
  , ("a quantifier over numerals and a repeated term", quantified Forall Below (s (s k)) (Conn Or (Conn And (Rel RelLt var (Nat 3)) (Rel RelLt (plus (outer x) (outer y)) var)) (Rel RelEq (plus (outer x) (outer y)) (Nat 2))))
  , ("nested quantifiers, the inner mentioning the outer variable", quantified Forall Below k (quantified Exists Below var (Rel RelEq (plus var (outer var)) (outer (outer n)))))
  , ("a body which is a function applied to the variable", quantified Forall Below k (Rel RelLt zero (hd var)))
  , ("a body which is the variable", quantified Forall Below k (Rel RelLt zero var))
  , ("a quantifier under a negation and over a comparison of the bound", Not (quantified Exists AtMost (plus k n) (Rel RelLt (outer k) var)))
  ]
  where
    x = Var "x"
    y = Var "y"
    k = Var "k"
    n = Var "n"
    zero = Nat 0
    s t = App (Global (Ref RefBuiltin "S")) t
    plus a b = apps (Global (Ref RefBuiltin "add")) [a, b]
    hd t = App (Global (Ref RefBuiltin "hd")) t

-- | A bounded quantifier over a body under its binder.
quantified :: Quantifier -> BoundRel -> Expr a -> Expr (Var () a) -> Expr a
quantified q rel limit body = Quant q (Hint "i") (Just (rel, limit)) Nothing (toScope body)

-- | The variable a quantifier binds.
var :: Expr (Var () a)
var = Var (B ())

-- | A term of the enclosing scope, under a binder.
outer :: Expr a -> Expr (Var () a)
outer = fmap F
