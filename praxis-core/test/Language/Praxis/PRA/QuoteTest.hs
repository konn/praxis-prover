{-# LANGUAGE QuasiQuotes #-}

{- |
Coverage for the quasiquoter.  The declarations below are certified when this
module is compiled; the tests then instantiate the derived rules and hand the
results to the checker, which is what the certification promises will succeed.
-}
module Language.Praxis.PRA.QuoteTest (quoteTests) where

import Data.Multiset (Multiset)
import Data.Multiset qualified as MS
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.QuoteSignature (pra, testSignature)
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

quoteTests :: TestTree
quoteTests =
  testGroup
    "quasiquoter"
    [ testCase "a theorem is the proof of its sequent" $
        inferConclusion plusZeroLeft @?= Right (sequent "|- plus(0, y) = y")
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
    ]
  where
    sc = plainScope testSignature
    sequent = either error id . parseSequent sc
    atom = either error id . parseFormula sc
    ctx :: [String] -> Multiset (Formula String)
    ctx = foldr (MS.insertOne . atom) MS.empty
