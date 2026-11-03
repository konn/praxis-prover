{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.DefinitionsTest (definitionsTests) where

import Control.Monad (forM_)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Eval (EvalResult (..), Value (..), evaluateEntryWithNats)
import Language.Praxis.Surface.FirstOrderFixtures (FirstOrderFixture (..))
import Language.Praxis.Surface.Mangle (mangleGlobal)
import Language.Praxis.Surface.Rename (Imports)
import Test.Tasty
import Test.Tasty.HUnit

definitionsTests :: IO FirstOrderFixture -> TestTree
definitionsTests getFirstOrder = withResource (fixtures getFirstOrder) (const (pure ())) $ \getFixtures ->
  let check source = do
        (_, build) <- getFixtures
        pure (fst (checkModule (\_ _ -> []) build (importsOf build) Nothing "definition-test.px" (header <> source)))
      succeeds source = do
        checked <- check source
        errors checked @?= []
        pure checked
      rejects label source = testCase label $ do
        checked <- check source
        assertBool "invalid definition proof was accepted" (not (null (errors checked)))
        forM_ (checkedFinal checked) $ \(_, core) ->
          assertBool
            "an invalid proof received a contract"
            (Map.notMember (T.unpack (mangleGlobal ["DefinitionTests", "bad", "#contract"])) (coreCertificates core))
   in testGroup
        "first-order relation definitions"
        [ testCase "expansion and proof elimination have uniform PRA contracts" $ do
            (checked, _) <- getFixtures
            (_, core) <- maybe (assertFailure "no checked definition module") pure (checkedFinal checked)
            forM_ ["instantiate-term", "instantiate-body", "expand", "expand-goal"] $ \name ->
              assertBool
                (T.unpack (name <> " lacks its closure certificate"))
                (Map.member (certificate name "closed") (coreCertificates core))
            forM_ ["erase", "same-reflexive", "all-same-reflexive", "base-reflexive", "base-all-reflexive"] $ \name ->
              assertBool
                (T.unpack (name <> " lacks its contract"))
                (Map.member (certificate name "contract") (coreCertificates core))
            forM_ ["closed", "index"] $ \suffix ->
              assertBool
                (T.unpack ("erase lacks its " <> suffix <> " certificate"))
                (Map.member (certificate "erase" suffix) (coreCertificates core))
        , testCase "proofs retain their definition and source syntax and erase to base derivations" $ do
            checked <-
              succeeds $
                T.unlines
                  [ "retained : DefinitionProof (Goal same (Defined Zero Zero))"
                  , "retained = same-reflexive {Zero} (by rfl)"
                  , "erased : Derivation (Equal Zero Zero)"
                  , "erased = erase retained"
                  ]
            retained <- run checked "retained"
            erased <- run checked "erased"
            let zero = syntax "Term.Zero" []
                proof = DataValue "Logic.FirstOrder.Proof.Derivation.Reflexivity" [zero]
                body = definition "RelationBody.Equation" [definition "TemplateTerm.First" [], definition "TemplateTerm.Second" []]
                formula = definition "ExtendedFormula.Defined" [zero, zero]
            evalValue retained @?= definition "DefinitionProof.Expanded" [body, formula, proof]
            evalValue erased @?= proof
        , testCase "parameter insertion is simultaneous and preserves surrounding binders" $ do
            _ <-
              succeeds $
                T.unlines
                  [ "swap : expand same (Defined (Free 1) (Free 0)) = Equal (Free 1) (Free 0)"
                  , "swap = by decide"
                  , "bound : expand same (Universal (Defined (Bound 0) (Bound 0))) = All (Equal (Bound 0) (Bound 0))"
                  , "bound = by decide"
                  , "fixed : (d : RelationBody) -> (a : Formula) -> expand d (Base a) = a"
                  , "fixed d a = base-fixed d a"
                  ]
            pure ()
        , rejects "an unused relation argument cannot hide an escaping bound variable" $
            T.unlines
              [ "ignore-second : RelationBody"
              , "ignore-second = Equation First First"
              , "bad : DefinitionProof (Goal ignore-second (Defined Zero (Bound 0)))"
              , "bad = Expanded {ignore-second} {Defined Zero (Bound 0)} (by rfl) zero-reflexive"
              ]
        , rejects "a quantifier does not hide an index escaping that binder" $
            T.unlines
              [ "ignore-first : RelationBody"
              , "ignore-first = Equation Second Second"
              , "bad : DefinitionProof (Goal ignore-first (Universal (Defined (Bound 1) (Bound 0))))"
              , "bad = Expanded {ignore-first} {Universal (Defined (Bound 1) (Bound 0))} (by decide) all-reflexive"
              ]
        , rejects "the retained base derivation must prove the actual expansion" $
            T.unlines
              [ "bad : DefinitionProof (Goal same (Defined Zero (Succ Zero)))"
              , "bad = Expanded {same} {Defined Zero (Succ Zero)} (by rfl) zero-reflexive"
              ]
        , rejects "changing the definition requires new evidence" $
            T.unlines
              [ "different : RelationBody"
              , "different = Equation (Successor First) Second"
              , "bad : DefinitionProof (Goal different (Defined Zero Zero))"
              , "bad = same-reflexive {Zero} (by rfl)"
              ]
        ]
  where
    certificate name suffix = T.unpack (mangleGlobal ["Logic", "FirstOrder", "Definitions", name, "#" <> suffix])
    syntax name = DataValue ("Logic.FirstOrder.Syntax." <> name)
    definition name = DataValue ("Logic.FirstOrder.Definitions." <> name)
    run checked name = either assertFailure pure (evaluateEntryWithNats 100000 ("DefinitionTests." <> name) [] checked)

header :: Text
header =
  T.unlines
    [ "module DefinitionTests where"
    , "open import Logic.FirstOrder.Syntax"
    , "open import Logic.FirstOrder.Proof"
    , "open import Logic.FirstOrder.Definitions"
    ]

errors :: Checked -> [Text]
errors checked = [reportMessage report | report <- checkedReports checked, reportSeverity report == SevError]

importsOf :: Build -> Imports
importsOf build = Map.fromList [((Nothing, name), Right exports) | (name, exports) <- Map.toList (buildExports build)]

fixtures :: IO FirstOrderFixture -> IO (Checked, Build)
fixtures getFirstOrder = do
  fixture <- getFirstOrder
  let path = "data/libraries/logic/src/Logic/FirstOrder/Definitions.px"
  source <- TIO.readFile path
  let (checked, next) = checkModule (\_ _ -> []) (firstOrderBuild fixture) (firstOrderImports fixture) Nothing path source
  errors checked @?= []
  pure (checked, next)
