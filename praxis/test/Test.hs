module Main (main) where

import Data.Map.Strict qualified as Map
import Language.Praxis.Package.PackageTest (packageTests)
import Language.Praxis.Surface.AdequacyTest (adequacyTests)
import Language.Praxis.Surface.CheckTest (checkTests)
import Language.Praxis.Surface.ParserTest (parserTests)
import Language.Praxis.Surface.Prelude
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
      , termTests
      , checkTests
      , adequacyTests
      , packageTests
      ]
