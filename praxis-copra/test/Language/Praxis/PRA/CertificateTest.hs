{-# LANGUAGE QuasiQuotes #-}

module Language.Praxis.PRA.CertificateTest (certificateTests) where

import Control.Monad (foldM)
import Data.Map.Strict qualified as Map
import Data.Multiset qualified as MS
import Language.Praxis.PRA.Certificate
import Language.Praxis.PRA.PrimitiveRecursion (builtin)
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Tactic
import Language.Praxis.PRA.Tactic.Parser
import Language.Praxis.PRA.Tactic.Quote
import Test.Tasty
import Test.Tasty.HUnit

[pra|
rule atLocal (t : term) (D ∀ x : |- x = x) : |- t = t
by exact D

theorem localExport : |- S x = S x
by exact atLocal { refl }
|]

certificateTests :: TestTree
certificateTests =
  testGroup
    "certificate replay"
    [ testCase "quantified premises export as proof functions" $ do
        let t = suc (Var "x")
        inferConclusion (atLocal t (\u -> Defeq u u (Id (u :=== u) MS.empty))) @?= Right (MS.empty :|- Atm (t :=== t))
        inferConclusion (localExport :: Proof String) @?= Right (MS.empty :|- Atm (t :=== t))
    , testCase "runtime replay expands a quantified premise and its caller" $ do
        known <- checked "rule at (t : term) (D ∀ x : |- x = x) : |- t = t by exact D\ntheorem use : |- S x = S x by exact at { refl }"
        replayed known "use" [] []
    , testCase "runtime replay checks supplied premises" $ do
        known <- checked "rule at (t : term) (D ∀ x : |- x = x) : |- t = t by exact D"
        let cert = known Map.! "at"
            call = Appeal "at" [ArgTerm (Var (Obj "x"))] [] MS.empty
        (expected, _) <- right (instantiateLemma builtin (certificateLemma cert) call)
        case expected of
          [_ :|- Atm (u :=== v)] -> replayed known "at" (appealArgs call) [Defeq u v (Id (u :=== v) MS.empty)]
          _ -> assertFailure "unexpected local premise"
        case replayCertificate environment cert call [Id (Lit 0 :=== Lit 0) MS.empty] of
          Left WrongPremise {} -> pure ()
          other -> assertFailure ("expected a wrong-premise error, got " <> show other)
    , testCase "incremental stores preserve schematic calls and lexical dependencies" $ do
        initial <- checked "rule at (t : term) : |- t = t by refl"
        ds <- right (parseDeclsIn (storedMetas (certificateStore initial)) (schemaScope builtin) "theorem use : |- S x = S x by exact at (S x)\nrule at (t : term) : |- 0 = 0 by refl")
        store <- foldM (\known d -> snd <$> right (checkAndInsertCertificate environment known d)) (certificateStore initial) ds
        replayed (storedCertificates store) "use" [] []
        storedLemmas store @?= fmap certificateLemma (storedCertificates store)
        storedMetas store @?= fmap (map snd . lemmaMetas) (storedLemmas store)
    , testCase "term sharing preserves distinct variable names and hypotheses" $ do
        ds <- right (parseDecls (schemaScope builtin) "theorem first : |- S x = S x by refl\ntheorem second : S y = S z |- S y = S z by assumption")
        store <- foldM (\known d -> snd <$> right (checkAndInsertCertificate environment known d)) (certificateStore Map.empty) ds
        replayed (storedCertificates store) "first" [] []
        replayed (storedCertificates store) "second" [] []
        let statement = lemmaGoal (certificateLemma (storedCertificates store Map.! "second"))
            equation = suc (Var (Obj "y")) :=== suc (Var (Obj "z"))
        statement @?= (MS.insertOne (Atm equation) MS.empty :|- Atm equation)
    , testCase "incremental stores reject unchecked declarations" $ do
        ds <- right (parseDecls (schemaScope builtin) "theorem unproved : |- 0 = S 0 by refl")
        case ds of
          [d] -> case checkAndInsertCertificate environment (certificateStore Map.empty) d of
            Left _ -> pure ()
            Right _ -> assertFailure "an invalid declaration entered the certificate store"
          _ -> assertFailure "expected one declaration"
    , testCase "captured dependencies survive later name shadowing" $ do
        known <- checked "theorem original : |- x = x by refl\ntheorem use : |- x = x by exact original\ntheorem original : |- 0 = 0 by refl"
        replayed known "use" [] []
    ]
  where
    environment = either (error . show) id (signatureEnv builtin)
    right result = either (assertFailure . show) pure result
    checked source = do
      ds <- right (parseDeclsIn Map.empty (schemaScope builtin) source)
      foldM (\known d -> do c <- right (checkCertificate environment known d); pure (Map.insert (declName d) c known)) Map.empty ds
    replayed known name args premises = do
      let cert = known Map.! name
          call = Appeal name args [] MS.empty
      (_, expected) <- right (instantiateLemma builtin (certificateLemma cert) call)
      proof <- right (replayCertificate environment cert call premises)
      inferConclusionIn (envKernel environment) proof @?= Right expected
