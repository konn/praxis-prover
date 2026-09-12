module Main (main) where

import Data.Text (Text)
import Data.Text qualified as T
import Language.LSP.Protocol.Types (DiagnosticSeverity (..))
import Language.Praxis.LSP
import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "praxis-lsp"
    [ testCase "the language is told by the extension" $ do
        languageOf "Lemmas.pra" @?= Just Pra
        languageOf "Definitions.prf" @?= Just Prf
        languageOf "Main.hs" @?= Nothing
    , testCase "a file which certifies reports nothing" $
        analyse Pra proofs @?= []
    , testCase "a sorry is reported as information, with the goal" $
        analyse Pra (proofs <> "\ntheorem open : a = 0 |- a = 0 /\\ a = 0\nby ConjR { Id } { sorry }\n")
          @?= [Report 8 19 DiagnosticSeverity_Information "sorry: the proof stops here\n  H1 : a = 0\n  |- a = 0"]
    , testCase "a failing tactic is reported at its position" $ do
        let reports = analyse Pra "theorem wrong : |- 2 = 3\nby refl\n"
        map reportLine reports @?= [2]
        map reportSeverity reports @?= [DiagnosticSeverity_Error]
    , testCase "a syntax error is reported where it is" $ do
        let reports = analyse Pra "theorem broken : |- 2 = 2\nby refl {\n"
        map reportSeverity reports @?= [DiagnosticSeverity_Error]
        map reportLine reports @?= [3]
    , testCase "a declaration is a lemma for those after it, and hover shows the goal" $ do
        hoverAt (proofs <> "\ntheorem again : b = 0 |- b + 0 = b\nby Cut (b = 0) { exact H1 } { exact plusZero }\n") 8 20
          @?= Just "H1 : b = 0\n|- b = 0"
        hoverAt (proofs <> "\ntheorem again : b = 0 |- b + 0 = b\nby Cut (b = 0) { exact H1 } { exact plusZero }\n") 8 33
          @?= Just "H1 : b = 0\nH2 : b = 0\n|- b + 0 = b"
    , testCase "a declaration whose proof fails is still a lemma for those after it" $
        map reportSeverity (analyse Pra "theorem later : |- 3 = 3\nby sorry\n\ntheorem uses : b = 0 |- 3 = 3\nby exact later\n")
          @?= [DiagnosticSeverity_Information]
    , testCase "a file of definitions is checked" $ do
        analyse Prf "double 0 = 0\ndouble (S n) = S (S (double n))\n" @?= []
        map reportSeverity (analyse Prf "double 0 = 0\ndouble (S n) = S (S (doubled n))\n") @?= [DiagnosticSeverity_Error]
    ]
  where
    proofs :: Text
    proofs =
      T.unlines
        [ "theorem plusZero : |- y + 0 = y"
        , "by induction y as n { refl } { Defeq (S n + 0) (S (n + 0)); rewrite H1 in (S n + 0 = _); Id }"
        , ""
        , "theorem two : |- 2 = 2"
        , "by refl"
        ]
