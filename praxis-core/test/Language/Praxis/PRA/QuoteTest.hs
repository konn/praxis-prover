{-# LANGUAGE QuasiQuotes #-}

{- |
Coverage for the quasiquoter.  The declarations below are certified when this
module is compiled; the tests then instantiate the derived rules and hand the
results to the checker, which is what the certification promises will succeed.
-}
module Language.Praxis.PRA.QuoteTest (quoteTests) where

import Control.Exception (displayException)
import Control.Monad (forM_)
import Data.Multiset (Multiset)
import Data.Multiset qualified as MS
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.QuoteSignature (arithWithMu, muPra, pra, testSignature)
import Language.Praxis.PRA.Signature qualified as Sig
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Syntax.Parser
import Test.Tasty
import Test.Tasty.HUnit

[pra|
-- The left identity is definitional.
theorem plusZeroLeft : |- plus(0, y) = y
by refl

theorem plusZeroRight : |- plus(y, 0) = y
by induction y as n
   { refl }
   { Defeq plus(S(n), 0) S(plus(n, 0))
   ; rewrite (plus(n, 0) = n) in (plus(S(n), 0) = _)
   ; Id }

rule symm (t s : term) (Γ : ctx) : t = s, Γ |- s = t
by Defeq t t; Subst x t s (x = t); Id

rule symmFixed (t s : term) : x = x, t = s |- s = t
by Defeq t t; Subst x t s (x = t); Id

rule symmPremise (t s : term) (D : x = x, t = s, t = t, s = t |- s = t)
  : x = x, t = s |- s = t
by Defeq t t; Subst x t s (x = t); exact D

rule identityAtom (P : atom) : P |- P
by Id (P)

rule substAtom (P : atom) (t s : term) : x = x, t = s, P |- P
by Subst x t s (P); Id (P)

rule trans (t s u : term) (Γ : ctx) : t = s, s = u, Γ |- t = u
by Subst x s u (t = x); Id

rule congS (t s : term) (Γ : ctx) : t = s, Γ |- S(t) = S(s)
by Defeq S(t) S(t); Subst x t s (S(t) = S(x)); Id

rule conjSwap (A B : formula) (Γ : ctx) (D1 : A, B, Γ |- B) (D2 : A, B, Γ |- A)
  : A /\ B, Γ |- B /\ A
by ConjL; ConjR { exact D1 } { exact D2 }

rule swapAtoms (P Q : atom) (Γ : ctx) : P /\ Q, Γ |- Q /\ P
by ConjL; ConjR { Id } { Id }

rule plusZeroRightAt (t : term) (Γ : ctx) : Γ |- plus(t, 0) = t
by Ind n (plus(n, 0) = n) t
   { refl }
   { Defeq plus(S(n), 0) S(plus(n, 0)); rewrite (plus(n, 0) = n) in (plus(S(n), 0) = _); Id }
|]

[muPra|
theorem desugaredAddMul : |- 2 + 3 * 4 = 14
by refl

theorem desugaredIfTrue : |- (if 0 < 1 then 10 else 20) = 10
by refl

theorem desugaredIfFalse : |- (if 1 < 0 then 10 else 20) = 20
by refl

theorem muSchemaApp1 : |- mu(lt, 3, 2) = 0
by refl

theorem muSchemaApp2 : |- mu {lt} (3, 0) = 3
by refl

theorem muUnaryApp : |- mu(sgn, 5) = 1
by refl
|]

quoteTests :: TestTree
quoteTests =
  testGroup
    "quasiquoter"
    [ testCase "a theorem is the proof of its sequent" $
        inferConclusion plusZeroLeft @?= Right (sequent "|- plus(0, y) = y")
    , testCase "typed quotation witnesses do not specialize generated proofs" $ do
        inferConclusion (plusZeroLeft :: Proof Text)
          @?= Right (asText (sequent "|- plus(0, y) = y"))
        inferConclusion (identityAtom (Var (T.pack "a") :=== Lit 0))
          @?= Right (asText (sequent "a = 0 |- a = 0"))
    , testCase "a theorem by induction" $
        inferConclusion plusZeroRight @?= Right (sequent "|- plus(y, 0) = y")
    , testCase "an expression quote is a proof" $
        inferConclusion [pra| a = 0 |- a = 0 /\ 2 = 2 by ConjR { Id } { refl } |]
          @?= Right (sequent "a = 0 |- a = 0 /\\ 2 = 2")
    , testCase "a rule instantiates at terms and a context" $
        inferConclusion (symm (Var "a") (Lit 3) (ctx ["b = 0"]))
          @?= Right (sequent "a = 3, b = 0 |- 3 = a")
    , testCase "the internal variable of a rule avoids the arguments" $
        inferConclusion (symm (Var "x") (Var "x'") (ctx ["x = x'"]))
          @?= Right (sequent "x = x', x = x' |- x' = x")
    , testCase "a substitution placeholder is fresh even when its name is in the statement" $
        forM_ [Var "a", Var "x", Var "x'", suc (Var "x"), Lit 0] $ \t ->
          forM_ [Var "x", Var "x'", Lit 0] $ \s ->
            inferConclusion (symmFixed t s)
              @?= Right (MS.insertOne (t === s) (ctx ["x = x"]) :|- s === t)
    , testCase "freshening a substitution preserves free variables in a premise" $
        inferConclusion
          (symmPremise (Var "x") (Lit 0) (Id (Lit 0 :=== Var "x") (ctx ["x = x", "x = 0", "x = x"])))
          @?= Right (sequent "x = x, x = 0 |- 0 = x")
    , testCase "an explicit atom metavariable instantiates under Id" $
        inferConclusion (identityAtom (Var "x" :=== Lit 0))
          @?= Right (sequent "x = 0 |- x = 0")
    , testCase "Subst does not capture names inside an explicit atom metavariable" $
        inferConclusion (substAtom (Var "x" :=== Lit 0) (Var "a") (Var "b"))
          @?= Right (sequent "x = x, a = b, x = 0 |- x = 0")
    , testCase "transitivity" $
        inferConclusion (trans (Var "a") (Var "b") (Lit 1) MS.empty)
          @?= Right (sequent "a = b, b = 1 |- a = 1")
    , testCase "congruence canonicalises the successor of a numeral" $
        inferConclusion (congS (Var "a") (Lit 2) MS.empty)
          @?= Right (sequent "a = 2 |- S(a) = 3")
    , testCase "a rule with formula metavariables and premises" $
        inferConclusion
          ( conjSwap
              (atom "a = 0")
              (atom "b = 0")
              (ctx ["c = 0"])
              (Id (Var "b" :=== Lit 0) (ctx ["a = 0", "c = 0"]))
              (Id (Var "a" :=== Lit 0) (ctx ["b = 0", "c = 0"]))
          )
          @?= Right (sequent "a = 0 /\\ b = 0, c = 0 |- b = 0 /\\ a = 0")
    , testCase "a rule with atom metavariables under Id" $
        inferConclusion (swapAtoms (Var "a" :=== Lit 0) (Var "b" :=== Lit 0) MS.empty)
          @?= Right (sequent "a = 0 /\\ b = 0 |- b = 0 /\\ a = 0")
    , testCase "the eigenvariable of a rule avoids the arguments" $
        inferConclusion (plusZeroRightAt (Var "n") (ctx ["n = 0"]))
          @?= Right (sequent "n = 0 |- plus(n, 0) = n")
    , testCase "desugared operators, ifte, and schema application in pra quotes" $ do
        kenv <- either (assertFailure . show) pure (Sig.signatureKernelEnv arithWithMu)
        inferConclusionIn kenv desugaredAddMul @?= Right (sequentMu "|- 2 + 3 * 4 = 14")
        inferConclusionIn kenv desugaredIfTrue @?= Right (sequentMu "|- (if 0 < 1 then 10 else 20) = 10")
        inferConclusionIn kenv desugaredIfFalse @?= Right (sequentMu "|- (if 1 < 0 then 10 else 20) = 20")
        inferConclusionIn kenv muSchemaApp1 @?= Right (sequentMu "|- mu(lt, 3, 2) = 0")
        inferConclusionIn kenv muSchemaApp2 @?= Right (sequentMu "|- mu {lt} (3, 0) = 3")
        inferConclusionIn kenv muUnaryApp @?= Right (sequentMu "|- mu(sgn, 5) = 1")
    ]
  where
    sc = plainScope testSignature
    sequent = either (error . displayException) id . parseSequent sc
    scMu = plainScope arithWithMu
    sequentMu = either (error . displayException) id . parseSequent scMu
    atom = either (error . displayException) id . parseFormula sc
    ctx :: [String] -> Multiset (Formula String)
    ctx = foldr (MS.insertOne . atom) MS.empty
    asText :: Sequent String -> Sequent Text
    asText (g :|- f) = foldr (MS.insertOne . fmap T.pack) MS.empty g :|- fmap T.pack f
