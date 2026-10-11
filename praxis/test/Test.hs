module Main (main) where

import Data.Map.Strict qualified as Map
import Language.Praxis.Package.PackageTest (packageTests)
import Language.Praxis.Surface.AdequacyTest (adequacyTests)
import Language.Praxis.Surface.BuiltinCheckTest (builtinCheckTests)
import Language.Praxis.Surface.BuiltinTest (builtinTests)
import Language.Praxis.Surface.CheckTest (checkTests)
import Language.Praxis.Surface.ClassAdmissionTest (classAdmissionTests)
import Language.Praxis.Surface.ComputationIndexTest (computationIndexTests)
import Language.Praxis.Surface.CoreTest (coreTests)
import Language.Praxis.Surface.DependentClassTest (dependentClassTests)
import Language.Praxis.Surface.EvidenceTest (evidenceTests)
import Language.Praxis.Surface.FiniteElaborationTest (finiteElaborationTests)
import Language.Praxis.Surface.FiniteQuantifierTest (finiteQuantifierTests)
import Language.Praxis.Surface.FiniteTacticTest (finiteTacticTests)
import Language.Praxis.Surface.IndexedInstanceTest (indexedInstanceTests)
import Language.Praxis.Surface.InstanceContextTest (instanceContextTests)
import Language.Praxis.Surface.LogicalPreconditionTest (logicalPreconditionTests)
import Language.Praxis.Surface.MethodContractTest (methodContractTests)
import Language.Praxis.Surface.ParserTest (parserTests)
import Language.Praxis.Surface.Prelude
import Language.Praxis.Surface.ProjectionIndexTest (projectionIndexTests)
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
          mapM_ (\n -> assertBool n (Map.member n (preludeLemmas p))) ["hdCons", "tlCons", "dropConsSucc", "cvrecUnfold", "histAt", "cvInduction", "belowElim"]
      , parserTests
      , resolveTests
      , projectionIndexTests
      , quantifierCaptureTests
      , termTests
      , coreTests
      , dependentClassTests
      , computationIndexTests
      , indexedInstanceTests
      , finiteQuantifierTests
      , finiteTacticTests
      , finiteElaborationTests
      , evidenceTests
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
