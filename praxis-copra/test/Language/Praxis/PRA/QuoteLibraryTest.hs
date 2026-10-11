{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Coverage for lemmas across modules: the quasiquoter of
"Language.Praxis.PRA.QuoteLibrary" appeals to the lemmas
"Language.Praxis.PRA.QuoteTest" declared under its @library@ header, and
declarations spliced from files do the same.
-}
module Language.Praxis.PRA.QuoteLibraryTest (libraryTests) where

import Control.Exception (displayException)
import Data.Map.Strict qualified as Map
import Data.Multiset (Multiset)
import Data.Multiset qualified as MS
import Data.Sized qualified as SV
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.PrimitiveRecursion.Quote (prfFile)
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.QuoteLibrary (libraryPra)
import Language.Praxis.PRA.QuoteSignature (testSignature)
import Language.Praxis.PRA.Signature qualified as Sig
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Syntax.Parser
import Language.Praxis.PRA.Tactic.Quote (Library (..), quoteFile)
import Test.Tasty
import Test.Tasty.HUnit

[libraryPra|
library moreLemmas

theorem plusTwoZeroElsewhere : |- plus 2 0 = 2
by exact plusZeroRight

rule symmElsewhere (a b : term) (Δ : ctx) : a = b, Δ |- b = a
by exact symm

theorem calcElsewhere : |- plus (plus y 0) 0 = y
by calc plus (plus y 0) 0 = plus y 0 by exact plusZeroRight = y by exact plusZeroRight
|]

$(quoteFile libraryPra "test/data/library.pra")

$(prfFile "test/data/definitions.prf")

libraryTests :: TestTree
libraryTests =
  testGroup
    "libraries"
    [ testCase "a quoter over a library appeals to the lemmas of another module" $ do
        inferConclusion plusTwoZeroElsewhere @?= Right (sequent "|- plus 2 0 = 2")
        inferConclusion (symmElsewhere (Var "a") (Lit 3) (ctx ["b = 0"]))
          @?= Right (sequent "a = 3, b = 0 |- 3 = a")
        inferConclusion calcElsewhere @?= Right (sequent "|- plus (plus y 0) 0 = y")
    , testCase "a library extends the one the quoter was built over" $ do
        let names = Map.keys (libraryLemmas moreLemmas)
        assertBool "the base lemmas" (all (`elem` names) ["plusZeroRight", "symm", "conjSwap"])
        assertBool "the new lemmas" (all (`elem` names) ["plusTwoZeroElsewhere", "symmElsewhere", "calcElsewhere"])
        map Sig.symbolName (Sig.symbols (librarySignature moreLemmas)) @?= map Sig.symbolName (Sig.symbols testSignature)
    , testCase "a file of declarations is spliced like a quote" $ do
        inferConclusion plusThreeZeroFromFile @?= Right (sequent "|- plus 3 0 = 3")
        map Sig.symbolName (Sig.symbols fileDefinitions) @?= ["double"]
        env <- either (assertFailure . displayException) pure (Sig.signatureKernelEnv fileDefinitions)
        F.evalFunction env double (3 SV.:< SV.Nil) @?= Right 6
    ]
  where
    sc = plainScope testSignature
    sequent = either (error . displayException) id . parseSequent sc
    atom = either (error . displayException) id . parseFormula sc
    ctx :: [String] -> Multiset (Formula String)
    ctx = foldr (MS.insertOne . atom) MS.empty
