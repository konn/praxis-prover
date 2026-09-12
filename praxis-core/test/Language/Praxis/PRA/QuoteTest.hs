{-# LANGUAGE QuasiQuotes #-}

{- |
Coverage for the quasiquoter.  The declarations below are certified when this
module is compiled; the tests then instantiate the derived rules and hand the
results to the checker, which is what the certification promises will succeed.
-}
module Language.Praxis.PRA.QuoteTest (
  quoteTests,

  -- * The library of this module, for "Language.Praxis.PRA.QuoteLibrary"
  testLemmas,
  plusZeroRight,
  symm,
) where

import Control.Exception (displayException)
import Control.Monad (forM_)
import Data.Foldable (toList)
import Data.Multiset (Multiset)
import Data.Multiset qualified as MS
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.PRA.PrimitiveRecursion (builtin)
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.QuoteSignature (testPra, testSignature)
import Language.Praxis.PRA.Signature qualified as Sig
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Syntax.Parser
import Language.Praxis.PRA.Tactic.Quote (pra)
import Test.Tasty
import Test.Tasty.HUnit

[testPra|
library testLemmas

-- The left identity is definitional.
theorem plusZeroLeft : |- plus 0 y = y
by refl

theorem plusZeroRight : |- plus y 0 = y
by induction y as n
   { refl }
   { Defeq (plus (S n) 0) (S (plus n 0))
   ; rewrite (plus n 0 = n) in (plus (S n) 0 = _)
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

rule congS (t s : term) (Γ : ctx) : t = s, Γ |- S t = S s
by Defeq (S t) (S t); Subst x t s (S t = S x); Id

rule conjSwap (A B : formula) (Γ : ctx) (D1 : A, B, Γ |- B) (D2 : A, B, Γ |- A)
  : A /\ B, Γ |- B /\ A
by ConjL; ConjR { exact D1 } { exact D2 }

rule swapAtoms (P Q : atom) (Γ : ctx) : P /\ Q, Γ |- Q /\ P
by ConjL; ConjR { Id } { Id }

rule plusZeroRightAt (t : term) (Γ : ctx) : Γ |- plus t 0 = t
by Ind n (plus n 0 = n) t
   { refl }
   { Defeq (plus (S n) 0) (S (plus n 0)); rewrite (plus n 0 = n) in (plus (S n) 0 = _); Id }

-- Appeals to the lemmas above: a theorem at an instance of its free variable,
-- under hypotheses, and rules with their metavariables inferred or given.
theorem plusZeroRightAtS : |- plus (S x) 0 = S x
by exact plusZeroRight

rule plusZeroRightUnder (Γ : ctx) : Γ |- plus y 0 = y
by exact plusZeroRight

rule transP (t s u : term) (Γ : ctx) (D1 : Γ |- t = s) (D2 : t = s, Γ |- s = u) : Γ |- t = u
by Cut (t = s) { exact D1 } { Cut (s = u) { exact D2 } { Subst x s u (t = x); Id } }

theorem plusZeroRightTwice : |- plus (plus y 0) 0 = y
by exact transP _ (plus y 0) { exact plusZeroRight } { exact plusZeroRight }

rule symmUse (a b : term) (Δ : ctx) : a = b, Δ |- b = a
by exact symm

rule symmGiven (a b : term) (Δ : ctx) : a = b, Δ |- b = a
by exact symm a b

theorem transAt : a = b, b = c |- a = c
by exact trans

theorem conjSwapAt : a = 0 /\ b = 0, c = 0 |- b = 0 /\ a = 0
by exact conjSwap { Id } { Id }

rule conjSwapMeta (A B : formula) (Γ : ctx) (D1 : A, B, Γ |- B) (D2 : A, B, Γ |- A)
  : A /\ B, Γ |- B /\ A
by exact conjSwap { exact D1 } { exact D2 }

-- A calculation, each step by a lemma.
theorem calcPlus : |- plus (plus y 0) 0 = y
by calc plus (plus y 0) 0 = plus y 0 by exact plusZeroRight = y by exact plusZeroRight
|]

-- A quote later in the module sees the lemmas of the quotes before it.
[testPra|
theorem plusTwoZero : |- plus 2 0 = 2
by exact plusZeroRight
|]

[pra|
theorem desugaredAddMul : |- 2 + 3 * 4 = 14
by refl

theorem desugaredIfTrue : |- (if 0 < 1 then 10 else 20) = 10
by refl

theorem desugaredIfFalse : |- (if 1 < 0 then 10 else 20) = 20
by refl

theorem muSchemaApp1 : |- mu lt 3 2 = 0
by refl

theorem muSchemaApp2 : |- mu {lt} 3 0 = 3
by refl

theorem muUnaryApp : |- mu sgn 5 = 1
by refl

theorem muLambda : |- mu {λ i. 3 < i} 10 = 4
by refl

theorem muSugar : |- (μ i < 10. 3 < i) = 4
by refl

theorem succSubSucc : |- S n - S m = n - m
by induction m
   { Defeq (S n - 1) (n - 0); Id }
   { Defeq (S n - S (S m')) (prd (S n - S m'))
   ; rewrite (S n - S m' = n - m') in (S n - S (S m') = prd (S n - S m'))
   ; Defeq (prd (n - m')) (n - S m')
   ; rewrite (prd (n - m') = n - S m') in (S n - S (S m') = prd (n - m'))
   ; Id }

-- The theorem at other terms, under a hypothesis, and with its own eigenvariable in the instance.
theorem succSubSuccAt : x = 0 |- S 3 - S x = 3 - x
by exact succSubSucc

theorem succSubSuccEigen : |- S m' - S (S m') = m' - S m'
by exact succSubSucc

-- A lemma cut in, then a calculation with a congruence on it.
theorem ltSucc : |- (t < S t) = 1
by induction t as n
   { refl }
   { Cut (S (S n) - S n = S n - n)
     { exact succSubSucc }
     { calc (S n < S (S n))
         = sgn (S (S n) - S n)
         = sgn (S n - n) by cong H2
         = (n < S n)
         = 1 by exact H1 }
   }

-- A formula metavariable closed by assumption: the identity is expanded at the instance.
rule assumeAny (A : formula) (Γ : ctx) : A, Γ |- A
by assumption

-- Generalized induction on a term metavariable, discharging a formula metavariable.
rule ltZero (t : term) (Γ : ctx) (A : formula) : (t < 0) = 1, Γ |- A
by induction t as n
   { Defeq (0 < 0) 0; Subst x (0 < 0) 0 (x = 1); symmetry (0 = 1); SuccNonZero }
   { Defeq (S n < 0) (sgn (prd (0 - n)))
   ; Subst x (S n < 0) (sgn (prd (0 - n))) (x = 1)
   ; Defeq (n < 0) (sgn (0 - n))
   ; ImplL ((n < 0) = 1) (A)
     { induction (0 - n) as y
       { Defeq (sgn (prd 0)) 0; Subst x (sgn (prd 0)) 0 (x = 1); symmetry (0 = 1); SuccNonZero }
       { Defeq (sgn (S y)) 1; Subst x (sgn (S y)) 1 ((n < 0) = x); Id }
     }
     { assumption }
   }
|]

quoteTests :: TestTree
quoteTests =
  testGroup
    "quasiquoter"
    [ testCase "a theorem is the proof of its sequent" $
        inferConclusion plusZeroLeft @?= Right (sequent "|- plus 0 y = y")
    , testCase "typed quotation witnesses do not specialize generated proofs" $ do
        inferConclusion (plusZeroLeft :: Proof Text)
          @?= Right (asText (sequent "|- plus 0 y = y"))
        inferConclusion (identityAtom (Var (T.pack "a") :=== Lit 0))
          @?= Right (asText (sequent "a = 0 |- a = 0"))
    , testCase "a theorem by induction" $
        inferConclusion plusZeroRight @?= Right (sequent "|- plus y 0 = y")
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
          @?= Right (sequent "a = 2 |- S a = 3")
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
          @?= Right (sequent "n = 0 |- plus n 0 = n")
    , testCase "an appeal to a theorem instantiates its free variables" $ do
        inferConclusion plusZeroRightAtS @?= Right (sequent "|- plus (S x) 0 = S x")
        inferConclusion plusTwoZero @?= Right (sequent "|- plus 2 0 = 2")
    , testCase "an appeal to a theorem is weakened, renaming its eigenvariable apart from the hypotheses" $
        inferConclusion (plusZeroRightUnder (ctx ["n = 0", "y = 1"]))
          @?= Right (sequent "n = 0, y = 1 |- plus y 0 = y")
    , testCase "an appeal to a rule instantiates its metavariables" $ do
        inferConclusion (symmUse (Var "a") (Lit 3) (ctx ["b = 0"]))
          @?= Right (sequent "a = 3, b = 0 |- 3 = a")
        inferConclusion (symmGiven (Var "x") (Var "x'") (ctx ["x = x'"]))
          @?= Right (sequent "x = x', x = x' |- x' = x")
        inferConclusion transAt @?= Right (sequent "a = b, b = c |- a = c")
    , testCase "a calculation appeals to lemmas at each step" $
        inferConclusion calcPlus @?= Right (sequent "|- plus (plus y 0) 0 = y")
    , testCase "the premises of an appeal are proved by the blocks" $ do
        inferConclusion plusZeroRightTwice @?= Right (sequent "|- plus (plus y 0) 0 = y")
        inferConclusion conjSwapAt @?= Right (sequent "a = 0 /\\ b = 0, c = 0 |- b = 0 /\\ a = 0")
        inferConclusion
          ( conjSwapMeta
              (atom "a = 0")
              (atom "b = 0")
              (ctx ["c = 0"])
              (Id (Var "b" :=== Lit 0) (ctx ["a = 0", "c = 0"]))
              (Id (Var "a" :=== Lit 0) (ctx ["b = 0", "c = 0"]))
          )
          @?= Right (sequent "a = 0 /\\ b = 0, c = 0 |- b = 0 /\\ a = 0")
    , testCase "desugared operators, ifte, and schema application in pra quotes" $ do
        kenv <- either (assertFailure . show) pure (Sig.signatureKernelEnv builtin)
        inferConclusionIn kenv desugaredAddMul @?= Right (sequentMu "|- 2 + 3 * 4 = 14")
        inferConclusionIn kenv desugaredIfTrue @?= Right (sequentMu "|- (if 0 < 1 then 10 else 20) = 10")
        inferConclusionIn kenv desugaredIfFalse @?= Right (sequentMu "|- (if 1 < 0 then 10 else 20) = 20")
        inferConclusionIn kenv muSchemaApp1 @?= Right (sequentMu "|- mu lt 3 2 = 0")
        inferConclusionIn kenv muSchemaApp2 @?= Right (sequentMu "|- mu {lt} 3 0 = 3")
        inferConclusionIn kenv muUnaryApp @?= Right (sequentMu "|- mu sgn 5 = 1")
        inferConclusionIn kenv muLambda @?= Right (sequentMu "|- mu {λ i. 3 < i} 10 = 4")
        inferConclusionIn kenv muSugar @?= Right (sequentMu "|- mu {λ i. 3 < i} 10 = 4")
        inferConclusionIn kenv succSubSuccAt @?= Right (sequentMu "x = 0 |- S 3 - S x = 3 - x")
        inferConclusionIn kenv succSubSuccEigen @?= Right (sequentMu "|- S m' - S (S m') = m' - S m'")
        inferConclusionIn kenv ltSucc @?= Right (sequentMu "|- (t < S t) = 1")
    , testCase "a formula metavariable under Id is the identity expanded at the instance" $ do
        kenv <- either (assertFailure . show) pure (Sig.signatureKernelEnv builtin)
        let compound = atomMu "a = 0 /\\ (b = 0 ==> c = 0 \\/ _|_)"
        inferConclusionIn kenv (assumeAny compound (ctxMu ["d = 0"]))
          @?= Right (sequentMu "a = 0 /\\ (b = 0 ==> c = 0 \\/ _|_), d = 0 |- a = 0 /\\ (b = 0 ==> c = 0 \\/ _|_)")
        inferConclusionIn kenv (ltZero (Lit 5) (ctxMu ["n = 0", "x = 1"]) compound)
          @?= Right (sequentMu "(5 < 0) = 1, n = 0, x = 1 |- a = 0 /\\ (b = 0 ==> c = 0 \\/ _|_)")
        case parseTerm scMu "μ i < 10. y < i" of
          Right (App _ args) -> toList args @?= [Lit 10, Var "y"]
          other -> assertFailure ("a bounded search over a variable: " <> show other)
    ]
  where
    sc = plainScope testSignature
    sequent = either (error . displayException) id . parseSequent sc
    scMu = plainScope builtin
    sequentMu = either (error . displayException) id . parseSequent scMu
    atomMu = either (error . displayException) id . parseFormula scMu
    ctxMu :: [String] -> Multiset (Formula String)
    ctxMu = foldr (MS.insertOne . atomMu) MS.empty
    atom = either (error . displayException) id . parseFormula sc
    ctx :: [String] -> Multiset (Formula String)
    ctx = foldr (MS.insertOne . atom) MS.empty
    asText :: Sequent String -> Sequent Text
    asText (g :|- f) = foldr (MS.insertOne . fmap T.pack) MS.empty g :|- fmap T.pack f
