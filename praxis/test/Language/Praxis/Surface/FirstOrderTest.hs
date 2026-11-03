{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.FirstOrderTest (firstOrderTests) where

import Control.Monad (forM_)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Eval
import Language.Praxis.Surface.FirstOrderFixtures
import Language.Praxis.Surface.Mangle (mangleGlobal)
import Test.Tasty
import Test.Tasty.HUnit

firstOrderTests :: IO FirstOrderFixture -> TestTree
firstOrderTests getFixture =
  testGroup
    "syntax and presentations"
    [ testCase "syntax operations retain PR bodies and datatype closure certificates" $ do
        fixture <- getFixture
        core <- finalCore (firstOrderSyntax fixture)
        forM_ ["term-scope", "scope", "term-support", "support"] $ \name -> retained core "Syntax" name
        forM_ ["subst-term", "subst-free", "subst-two", "rename-free", "open-term", "open-at", "open-body", "close-body"] $ \name ->
          certificates core "Syntax" name ["closed"]
        forM_ ["scope-bound-example", "scope-escaping-example", "open-nested-example", "simultaneous-example", "close-nested-example", "open-close-example"] $ \name ->
          assertBool "missing native syntax equality" (("Logic.FirstOrder.Syntax." <> name) `elem` checkedTheorems (firstOrderSyntax fixture))
    , testCase "quantified derivations retain membership and conclusion certificates" $ do
        fixture <- getFixture
        core <- finalCore (firstOrderProof fixture)
        forM_ ["reflexivity-schema", "all-reflexive", "instantiate-zero", "specialized-reflexive", "nested-instantiation"] $ \name ->
          certificates core "Proof" name ["contract", "closed", "index"]
    , testCase "PA axiom witnesses include a uniform induction schema" $ do
        fixture <- getFixture
        core <- finalCore (firstOrderPeano fixture)
        forM_ ["axiom-scope", "axiom-language"] $ \name -> retained core "Peano" name
        forM_ ["axiom-formula", "induction-formula"] $ \name ->
          certificates core "Peano" name ["closed"]
        forM_ ["add-zero-schema", "induction-schema", "induction-reflexivity", "one-plus-zero", "arithmetic-reflexive"] $ \name ->
          certificates core "Peano" name ["contract", "closed", "index"]
    , testCase "opening, closing, and simultaneous substitution preserve the intended binders" $ do
        fixture <- getFixture
        let checked = check fixture computations
        errors checked @?= []
        forM_
          [ ("opened", allF (equal (free 7) (bound 0)))
          , ("closed", allF (equal (bound 1) (bound 0)))
          , ("substituted", allF (equal (free 9) (bound 0)))
          , ("simultaneous", equal (free 1) (free 0))
          , ("escaped", NatValue 1)
          , ("locally-closed", NatValue 0)
          ]
          $ \(name, expected) -> do
            result <- either assertFailure pure (evaluateEntry 100000 ("FirstOrderCase." <> name) checked)
            evalValue result @?= expected
    , rejects "instantiation cannot lie about the opened formula" $
        T.unlines
          [ "bad : Derivation (Imp (All (Equal (Bound 0) (Bound 0))) (Equal Zero (Succ Zero)))"
          , "bad = Derivation.Instantiate {Equal (Bound 0) (Bound 0)} {Equal Zero (Succ Zero)} {Zero} (by rfl) (by decide) (by rfl) (by rfl)"
          ]
    , rejects "an escaping bound index is not a closed equality proof" $
        T.unlines
          [ "bad : Derivation (Equal (Bound 0) (Bound 0))"
          , "bad = Derivation.Reflexivity {Bound 0} (by rfl)"
          ]
    , rejects "generalization checks the actual closed body" $
        T.unlines
          [ "bad : Derivation (All Bottom)"
          , "bad = Derivation.Generalize {Equal Zero Zero} {Bottom} {0} (by rfl) (by rfl) (by rfl) zero-reflexive"
          ]
    , rejects "a PA witness cannot certify an unrelated conclusion" $
        T.unlines
          [ "bad : PA Bottom"
          , "bad = PA.Arithmetic {Bottom} (AddZero Zero) (by rfl) (by rfl) (by rfl) (by rfl)"
          ]
    , rejects "PA induction does not silently include extra relation symbols" $
        T.unlines
          [ "bad : PA (induction-formula (Rel 0 (Bound 0) Zero))"
          , "bad = induction-schema {Rel 0 (Bound 0) Zero} (by decide) (by rfl) (by decide)"
          ]
    , rejects "PA logical embedding also checks the arithmetic language" $
        T.unlines
          [ "bad : PA (Imp (Rel 0 Zero Zero) (Imp Bottom (Rel 0 Zero Zero)))"
          , "bad = PA.Logic {Imp (Rel 0 Zero Zero) (Imp Bottom (Rel 0 Zero Zero))} (by rfl) (Derivation.K {Rel 0 Zero Zero} {Bottom} (by rfl) (by rfl))"
          ]
    ]
  where
    rejects label source = testCase label $ do
      fixture <- getFixture
      let checked = check fixture source
      assertBool "invalid object proof was accepted" (not (null (errors checked)))
      assertBool "invalid object proof received a contract" ("FirstOrderCase.bad.#contract" `notElem` checkedTheorems checked)

check :: FirstOrderFixture -> Text -> Checked
check fixture source = fst (checkModule (\_ _ -> []) (firstOrderBuild fixture) (firstOrderImports fixture) Nothing "first-order-case.px" (prefix <> source))

prefix :: Text
prefix =
  T.unlines
    [ "module FirstOrderCase where"
    , "open import Logic.FirstOrder.Syntax"
    , "open import Logic.FirstOrder.Proof"
    , "open import Logic.FirstOrder.Peano"
    ]

computations :: Text
computations =
  T.unlines
    [ "opened : Formula"
    , "opened = open-body (Free 7) (All (Equal (Bound 1) (Bound 0)))"
    , "closed : Formula"
    , "closed = close-body 7 (All (Equal (Free 7) (Bound 0)))"
    , "substituted : Formula"
    , "substituted = subst-free 0 (Free 9) (All (Equal (Free 0) (Bound 0)))"
    , "simultaneous : Formula"
    , "simultaneous = subst-two (Free 1) (Free 0) (Equal (Free 0) (Free 1))"
    , "escaped : Nat"
    , "escaped = scope (All (Equal (Bound 1) Zero))"
    , "locally-closed : Nat"
    , "locally-closed = scope (All (Equal (Bound 0) Zero))"
    ]

errors :: Checked -> [Text]
errors checked = [message | Report _ SevError message <- checkedReports checked]

finalCore :: Checked -> IO Core
finalCore checked = snd <$> maybe (assertFailure "missing checked core") pure (checkedFinal checked)

certificates :: Core -> Text -> Text -> [Text] -> Assertion
certificates core namespace name = mapM_ $ \suffix ->
  assertBool
    (T.unpack (namespace <> "." <> name <> " has no " <> suffix <> " certificate"))
    (Map.member (T.unpack (mangleGlobal ["Logic", "FirstOrder", namespace, name, "#" <> suffix])) (coreCertificates core))

retained :: Core -> Text -> Text -> Assertion
retained core namespace name =
  assertBool
    (T.unpack (namespace <> "." <> name <> " has no retained checked body"))
    (Map.member (mangleGlobal ["Logic", "FirstOrder", namespace, name]) (coreBodies core))

free, bound :: Integer -> Value
free x = DataValue "Logic.FirstOrder.Syntax.Term.Free" [NatValue (fromInteger x)]
bound x = DataValue "Logic.FirstOrder.Syntax.Term.Bound" [NatValue (fromInteger x)]

equal :: Value -> Value -> Value
equal x y = DataValue "Logic.FirstOrder.Syntax.Formula.Equal" [x, y]

allF :: Value -> Value
allF a = DataValue "Logic.FirstOrder.Syntax.Formula.All" [a]
