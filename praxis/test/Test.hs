module Main (main) where

import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Language.Praxis.Package.PackageTest (packageTests)
import Language.Praxis.Surface.AdequacyTest (adequacyTests)
import Language.Praxis.Surface.BuiltinCheckTest (builtinCheckTests)
import Language.Praxis.Surface.BuiltinTest (builtinTests)
import Language.Praxis.Surface.CheckTest (checkTests)
import Language.Praxis.Surface.ClassAdmissionTest (classAdmissionTests)
import Language.Praxis.Surface.ComputationIndexTest (computationIndexTests)
import Language.Praxis.Surface.ConstructionTest (constructionTests)
import Language.Praxis.Surface.CoreTest (coreTests)
import Language.Praxis.Surface.DefinitionsTest (definitionsTests)
import Language.Praxis.Surface.DependentClassTest (dependentClassTests)
import Language.Praxis.Surface.Encode (natInductionLemma)
import Language.Praxis.Surface.EvalTest (evalTests)
import Language.Praxis.Surface.EvidenceTest (evidenceTests)
import Language.Praxis.Surface.ExactPredicateTest (exactPredicateTests)
import Language.Praxis.Surface.FiniteElaborationTest (finiteElaborationTests)
import Language.Praxis.Surface.FiniteQuantifierTest (finiteQuantifierTests)
import Language.Praxis.Surface.FiniteTacticTest (finiteTacticTests)
import Language.Praxis.Surface.FirstOrderFixtures (loadFirstOrderFixture)
import Language.Praxis.Surface.FirstOrderTest (firstOrderTests)
import Language.Praxis.Surface.GlivenkoTest (glivenkoTests)
import Language.Praxis.Surface.IndexedInstanceTest (indexedInstanceTests)
import Language.Praxis.Surface.InstanceContextTest (instanceContextTests)
import Language.Praxis.Surface.InternalTest (internalTests)
import Language.Praxis.Surface.LogicalPreconditionTest (logicalPreconditionTests)
import Language.Praxis.Surface.MethodContractTest (methodContractTests)
import Language.Praxis.Surface.ParserTest (parserTests)
import Language.Praxis.Surface.Prelude
import Language.Praxis.Surface.ProjectionIndexTest (projectionIndexTests)
import Language.Praxis.Surface.PropositionCodeTest (propositionCodeTests)
import Language.Praxis.Surface.QuantifierCaptureTest (quantifierCaptureTests)
import Language.Praxis.Surface.ResolveTest (resolveTests)
import Language.Praxis.Surface.TermTest (termTests)
import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main =
  defaultMain $
    testGroup
      "praxis"
      [ testCase "the prelude certifies, and states the lemmas generated proofs appeal to" $ do
          p <- either assertFailure pure prelude
          mapM_ (\n -> assertBool n (Map.member n (preludeLemmas p))) ["hdCons", "tlCons", "dropConsSucc", "cvrecUnfold", "histAt", "cvInduction", "belowElim", T.unpack natInductionLemma]
      , parserTests
      , resolveTests
      , projectionIndexTests
      , quantifierCaptureTests
      , termTests
      , propositionCodeTests
      , coreTests
      , dependentClassTests
      , computationIndexTests
      , constructionTests
      , indexedInstanceTests
      , finiteQuantifierTests
      , finiteTacticTests
      , finiteElaborationTests
      , exactPredicateTests
      , evidenceTests
      , evalTests
      , glivenkoTests
      , internalTests
      , withResource loadFirstOrderFixture (const (pure ())) $ \get ->
          testGroup "first-order" [firstOrderTests get, definitionsTests get]
      , instanceContextTests
      , logicalPreconditionTests
      , methodContractTests
      , builtinTests
      , builtinCheckTests
      , classAdmissionTests
      , checkTests
      , adequacyTests
      , packageTests
      ]
