{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.GlivenkoTest (glivenkoTests) where

import Control.Monad (forM_, unless)
import Data.Either (isLeft)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Eval
import Language.Praxis.Surface.Prelude (prelude)
import Test.Tasty
import Test.Tasty.HUnit

glivenkoTests :: TestTree
glivenkoTests = withResource load (const (pure ())) $ \getChecked ->
  testGroup
    "Glivenko"
    [ testCase "uniform transformation and contradiction contracts certify" $ do
        checked <- getChecked
        (_, core) <- maybe (assertFailure "no checked Glivenko module") pure (checkedFinal checked)
        forM_ ["glivenko", "contradiction", "embed", "recover"] $ \name ->
          forM_ ["contract", "closed", "index"] $ \suffix ->
            assertBool
              (name <> " has no " <> suffix <> " certificate")
              (Map.member ("u_Logic_sGlivenko_s" <> name <> "_s_x23_" <> suffix) (coreCertificates core))
    , testCase "evaluated Peirce proof and Glivenko output pass independent Hilbert checking" $ do
        checked <- getChecked
        result <- run checked "demo-proofs"
        (input, output) <- case evalValue result of
          DataValue "Logic.Glivenko.Translation.Translated" [input, output] -> pure (input, output)
          other -> assertFailure ("unexpected translation package: " <> T.unpack (renderValue 2 other))
        let a = formula "Atom" [NatValue 0]
            b = formula "Atom" [NatValue 1]
            peirce = imp (imp (imp a b) a) a
        proofConclusion "Classical" input @?= Right peirce
        proofConclusion "Intuitionistic" output @?= Right (nn peirce)
        assertBool "the classical proof was accepted intuitionistically" (isLeft (proofConclusion "Intuitionistic" input))
        assertBool "unexpectedly large evaluator allocation" (evalNodes result < 100000)
    , testCase "malformed MP and classical-to-intuitionistic casts are rejected" $ do
        p <- either assertFailure pure prelude
        source <- TIO.readFile sourcePath
        let declarations = fst (T.breakOn "identity :" source)
            badMP = "bad : Intuitionistic (Atom 0)\nbad = Intuitionistic.MP {Bottom} {Atom 0} (Intuitionistic.Explosion {Atom 0}) (Intuitionistic.K {Atom 0} {Bottom})\n"
            badDNE = "bad : Intuitionistic (Imp (Imp (Imp (Atom 0) Bottom) Bottom) (Atom 0))\nbad = Classical.DNE {Atom 0}\n"
        forM_ [badMP, badDNE] $ \bad -> do
          let checked = checkSource p "invalid-glivenko.px" (declarations <> bad)
          assertBool "an invalid object proof was certified" (any ((== SevError) . reportSeverity) (checkedReports checked))
    ]
  where
    sourcePath = "data/libraries/logic/src/Logic/Glivenko.px"
    load = do
      p <- either assertFailure pure prelude
      source <- TIO.readFile sourcePath
      let checked = fst (checkModule (\_ _ -> []) (initialBuild p) {buildRetainGeneratedText = False} Map.empty Nothing sourcePath source)
      [reportMessage r | r <- checkedReports checked, reportSeverity r == SevError] @?= []
      pure checked
    run checked name = either assertFailure pure (evaluateEntryWithNats 1000000 ("Logic.Glivenko." <> name) [0, 1] checked)

formula :: Text -> [Value] -> Value
formula name = DataValue ("Logic.Glivenko.Formula." <> name)

imp :: Value -> Value -> Value
imp a b = formula "Imp" [a, b]

bottom :: Value
bottom = formula "Bottom" []

nn :: Value -> Value
nn a = imp (imp a bottom) bottom

-- An object-level checker independent of Praxis's GADT index/membership
-- generation and of the evaluator. Every premise of MP is checked afresh.
proofConclusion :: Text -> Value -> Either String Value
proofConclusion system = go
  where
    go (DataValue name fields) = case T.stripPrefix ("Logic.Glivenko." <> system <> ".") name of
      Just "K" | [a, b] <- fields -> valid [a, b] *> pure (imp a (imp b a))
      Just "S" | [a, b, c] <- fields -> valid [a, b, c] *> pure (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
      Just "Explosion" | [a] <- fields -> valid [a] *> pure (imp bottom a)
      Just "DNE" | system == "Classical", [a] <- fields -> valid [a] *> pure (imp (nn a) a)
      Just "MP" | [b, f, x] <- fields -> do
        valid [b]
        function <- go f
        argument <- go x
        unless (function == imp argument b) (Left "invalid modus ponens")
        pure b
      _ -> Left "not a proof constructor of this calculus"
    go _ = Left "not an object proof"
    valid = mapM_ checkFormula
    checkFormula (DataValue "Logic.Glivenko.Formula.Atom" [NatValue _]) = Right ()
    checkFormula (DataValue "Logic.Glivenko.Formula.Bottom" []) = Right ()
    checkFormula (DataValue "Logic.Glivenko.Formula.Imp" [a, b]) = valid [a, b]
    checkFormula _ = Left "invalid formula"
