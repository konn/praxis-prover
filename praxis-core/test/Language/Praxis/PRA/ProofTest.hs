{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

{- |
Coverage for 'inferConclusion'.

Every rule is exercised in both directions: the sequent it must infer from a
well-formed premise, and the reason it must report when its side condition
fails.  The inferred sequent is compared in full, so a rule which forgets to
discharge a premise — or discharges one too many — is caught by the context of
the result rather than by an explicit assertion.
-}
module Language.Praxis.PRA.ProofTest (proofTests) where

import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Multiset (Multiset)
import Data.Multiset qualified as MS
import Data.Sized (pattern Nil, pattern (:<))
import Data.Type.Ordinal (od)
import Language.Praxis.PRA.PrimitiveRecursion hiding (suc)
import Language.Praxis.PRA.PrimitiveRecursion.Examples (mult, plus)
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.Syntax
import Test.Tasty
import Test.Tasty.HUnit

proofTests :: TestTree
proofTests =
  testGroup
    "inferConclusion"
    [ idTests
    , exFalsoTests
    , conjLTests
    , conjRTests
    , disjLTests
    , disjRTests
    , implLTests
    , implRTests
    , defeqTests
    , defeqUnfoldingTests
    , substTests
    , errorContextTests
    , isProofOfTests
    ]

-- * A small stock of formulae to build proofs out of

pA, pB, pC :: Atomic String
pA = Var "a" :=== Lit 0
pB = Var "b" :=== Lit 0
pC = Var "c" :=== Lit 0

-- | Three pairwise distinct atomic formulae.
a, b, c :: Formula String
a = Atm pA
b = Atm pB
c = Atm pC

-- | A context, written in the order the rules display it.
ctx :: [Formula String] -> Multiset (Formula String)
ctx = foldr MS.insertOne MS.empty

-- | The reasons reported by a rejected proof; empty if it was accepted.
reasons :: Proof String -> [ProofErrorReason String]
reasons = either (map reason . NE.toList) (const []) . inferConclusion

-- | The rule stack each reported error was raised under, innermost first.
errorContexts :: Proof String -> [NonEmpty ProofContext]
errorContexts = either (map context . NE.toList) (const []) . inferConclusion

idTests :: TestTree
idTests =
  testGroup
    "Id"
    [ testCase "concludes its own atom against the extended context" $
        inferConclusion (Id pA (ctx [b])) @?= Right (ctx [a, b] |- a)
    , testCase "the principal formula is added, not merged" $
        inferConclusion (Id pA (ctx [a])) @?= Right (ctx [a, a] |- a)
    ]

exFalsoTests :: TestTree
exFalsoTests =
  testGroup
    "ExFalso"
    [ testCase "concludes anything from an absurd context" $
        inferConclusion (ExFalso (ctx [a]) b) @?= Right (ctx [Bot, a] |- b)
    , testCase "the context may already contain an absurdity" $
        inferConclusion (ExFalso (ctx [Bot]) a) @?= Right (ctx [Bot, Bot] |- a)
    ]

conjLTests :: TestTree
conjLTests =
  testGroup
    "ConjL"
    [ testCase "discharges both conjuncts" $
        inferConclusion (ConjL a b (Id pA (ctx [b]))) @?= Right (ctx [a /\ b] |- a)
    , testCase "leaves the rest of the context alone" $
        inferConclusion (ConjL a b (Id pC (ctx [a, b]))) @?= Right (ctx [a /\ b, c] |- c)
    , testCase "discharges each conjunct once when they coincide" $
        inferConclusion (ConjL a a (Id pA (ctx [a]))) @?= Right (ctx [a /\ a] |- a)
    , testCase "rejects a premise lacking a conjunct" $
        reasons (ConjL a c (Id pA (ctx [b]))) @?= [MissingAssumption c (ctx [b])]
    ]

conjRTests :: TestTree
conjRTests =
  testGroup
    "ConjR"
    [ testCase "accepts branches sharing a context" $
        inferConclusion (ConjR (Id pA MS.empty) (DisjR1 b (Id pA MS.empty)))
          @?= Right (ctx [a] |- a /\ (b \/ a))
    , testCase "rejects branches whose contexts differ" $
        reasons (ConjR (Id pA MS.empty) (Id pB MS.empty))
          @?= [AssumptionMismatch (ctx [a]) (ctx [b])]
    ]

disjLTests :: TestTree
disjLTests =
  testGroup
    "DisjL"
    [ testCase "discharges one disjunct from each branch" $
        inferConclusion (DisjL a b (Id pC (ctx [a])) (Id pC (ctx [b])))
          @?= Right (ctx [a \/ b, c] |- c)
    , testCase "rejects branches proving different conclusions" $
        reasons (DisjL a b (Id pC (ctx [a])) (DisjR1 a (Id pC (ctx [b]))))
          @?= [ConsequentMismatch c (a \/ c)]
    , testCase "rejects branches whose remaining contexts differ" $
        reasons (DisjL a b (Id pC (ctx [a])) (Id pC (ctx [b, a])))
          @?= [AssumptionMismatch (ctx [c]) (ctx [c, a])]
    , testCase "rejects a branch lacking its disjunct" $
        reasons (DisjL a b (Id pC (ctx [a])) (Id pC (ctx [a])))
          @?= [MissingAssumption b (ctx [c, a])]
    ]

disjRTests :: TestTree
disjRTests =
  testGroup
    "DisjR"
    [ testCase "DisjR1 introduces the new disjunct on the left" $
        inferConclusion (DisjR1 b (Id pA MS.empty)) @?= Right (ctx [a] |- b \/ a)
    , testCase "DisjR2 introduces the new disjunct on the right" $
        inferConclusion (DisjR2 b (Id pA MS.empty)) @?= Right (ctx [a] |- a \/ b)
    ]

implLTests :: TestTree
implLTests =
  testGroup
    "ImplL"
    [ testCase "keeps the implication and discharges its consequent" $
        inferConclusion (ImplL a b (Id pA (ctx [a ==> b])) (Id pB (ctx [a])))
          @?= Right (ctx [a ==> b, a] |- b)
    , testCase "rejects a left branch proving the wrong antecedent" $
        reasons (ImplL a b (Id pC (ctx [a ==> b])) (Id pB (ctx [c])))
          @?= [ConsequentMismatch a c]
    , testCase "rejects a left branch lacking the implication" $
        reasons (ImplL a b (Id pA MS.empty) (Id pB MS.empty))
          @?= [MissingAssumption (a ==> b) (ctx [a])]
    , testCase "rejects branches whose remaining contexts differ" $
        reasons (ImplL a b (Id pA (ctx [a ==> b])) (Id pB MS.empty))
          @?= [AssumptionMismatch (ctx [a]) MS.empty]
    ]

implRTests :: TestTree
implRTests =
  testGroup
    "ImplR"
    [ testCase "discharges the antecedent" $
        inferConclusion (ImplR a (Id pA MS.empty)) @?= Right (MS.empty |- a ==> a)
    , testCase "discharges only the antecedent" $
        inferConclusion (ImplR a (Id pB (ctx [a]))) @?= Right (ctx [b] |- a ==> b)
    , testCase "rejects a premise lacking the antecedent" $
        reasons (ImplR b (Id pA MS.empty)) @?= [MissingAssumption b (ctx [a])]
    ]

-- | @'Succ' 4@, definitionally but not syntactically the numeral @5@.
sucFour :: Term String
sucFour = Succ :$ (Lit 4 :< Nil)

{- |
The canonical use of 'Defeq': 'Id' supplies the equation and 'Defeq' discharges
it, so @|- s = t@ is derivable from no assumptions exactly when the trusted
evaluator identifies @s@ and @t@.
-}
unfoldsTo :: Term String -> Term String -> Assertion
unfoldsTo s t =
  inferConclusion (Defeq s t (Id (s :=== t) MS.empty)) @?= Right (MS.empty |- s === t)

-- | The same proof, rejected: reduction finds no common form for @s@ and @t@.
doesNotUnfoldTo :: Term String -> Term String -> Assertion
doesNotUnfoldTo s t =
  reasons (Defeq s t (Id (s :=== t) MS.empty)) @?= [EqualityCheckFailed s t]

defeqTests :: TestTree
defeqTests =
  testGroup
    "Defeq"
    [ testCase "proves a definitional equation from no assumptions" $
        sucFour `unfoldsTo` Lit 5
    , testCase "discharges the equation from a larger context" $
        inferConclusion (Defeq (Lit 5) (Lit 5) (Id pA (ctx [Lit 5 === Lit 5])))
          @?= Right (ctx [a] |- a)
    , testCase "rejects an equation reduction does not decide" $
        reasons (Defeq (Lit 5) (Lit 4) (Id (Lit 5 :=== Lit 4) MS.empty))
          @?= [EqualityCheckFailed (Lit 5) (Lit 4)]
    , testCase "rejects a premise lacking the equation" $
        reasons (Defeq (Lit 5) (Lit 5) (Id pA MS.empty))
          @?= [MissingAssumption (Lit 5 === Lit 5) (ctx [a])]
    ]

-- | Open arguments, so that a rule can only fire by its defining equation.
x, y :: Term String
x = Var "x"
y = Var "y"

{- |
Each equation below is the defining equation of one 'PRFCode' constructor, read
left to right as a single unfolding step.  The arguments are variables: nothing
here can be decided by evaluating both sides down to a numeral, so 'Defeq' must
genuinely take the step under an open term.  The sole numeral is the @0@ which
selects the base clause of 'Rec'.
-}
defeqUnfoldingTests :: TestTree
defeqUnfoldingTests =
  testGroup
    "Defeq unfolds a PRFCode by its defining equation"
    [ testCase "Zero(x) = 0" $
        (Zero :$ (x :< Nil)) `unfoldsTo` Lit 0
    , testCase "Succ(t) = S(t), for t itself a redex" $
        (Succ :$ ((plus :$ ((Succ :$ (y :< Nil)) :< x :< Nil)) :< Nil))
          `unfoldsTo` suc (suc (plus :$ (y :< x :< Nil)))
    , testCase "Proj_1(x, y) = y" $
        (Proj [od|1|] :$ (x :< y :< Nil)) `unfoldsTo` y
    , testCase "Comp f (g_0, g_1) (x, y) = f(g_0(x, y), g_1(x, y))" $
        (Comp plus (Proj [od|1|] :< Proj [od|0|] :< Nil) :$ (x :< y :< Nil))
          `unfoldsTo` (plus :$ (y :< x :< Nil))
    , testCase "Rec g h (0, x) = g(x)" $
        (plus :$ (Lit 0 :< x :< Nil)) `unfoldsTo` x
    , testCase "Rec g h (S y, x) = h(y, Rec g h (y, x), x)" $
        (plus :$ ((Succ :$ (y :< Nil)) :< x :< Nil))
          `unfoldsTo` (Succ :$ ((plus :$ (y :< x :< Nil)) :< Nil))
    , testCase "the recursive call may be left residual inside the step code" $
        (mult :$ ((Succ :$ (y :< Nil)) :< x :< Nil))
          `unfoldsTo` (plus :$ ((mult :$ (y :< x :< Nil)) :< x :< Nil))
    , testCase "rejects a step which loses the successor" $
        (plus :$ ((Succ :$ (y :< Nil)) :< x :< Nil))
          `doesNotUnfoldTo` (plus :$ (y :< x :< Nil))
    , testCase "rejects a step code applied to the wrong argument" $
        (mult :$ ((Succ :$ (y :< Nil)) :< x :< Nil))
          `doesNotUnfoldTo` (plus :$ ((mult :$ (y :< x :< Nil)) :< y :< Nil))
    ]

-- | @P@, @P[n := 1]@, @P[n := 2]@ and the equation relating the two witnesses.
substP :: Atomic String
substP = Var "n" :=== Lit 0

eq12, one0, two0 :: Formula String
eq12 = Lit 1 === Lit 2
one0 = Lit 1 === Lit 0
two0 = Lit 2 === Lit 0

substTests :: TestTree
substTests =
  testGroup
    "Subst"
    [ testCase "keeps the equation and the witness it was substituted into" $
        inferConclusion
          (Subst "n" (Lit 1) (Lit 2) substP (Id (Lit 2 :=== Lit 0) (ctx [eq12, one0])))
          @?= Right (ctx [eq12, one0] |- two0)
    , testCase "discharges both instances when they coincide" $
        inferConclusion
          ( Subst "n" (Lit 1) (Lit 1) substP $
              Id (Lit 1 :=== Lit 1) (ctx [one0, one0])
          )
          @?= Right (ctx [Lit 1 === Lit 1, one0] |- Lit 1 === Lit 1)
    , testCase "rejects a premise lacking the substituted instance" $
        reasons (Subst "n" (Lit 1) (Lit 2) substP (Id (Lit 1 :=== Lit 0) (ctx [eq12])))
          @?= [MissingAssumption two0 MS.empty]
    ]

errorContextTests :: TestTree
errorContextTests =
  testGroup
    "error contexts"
    [ testCase "an error names the rule which raised it" $
        errorContexts (ConjR (Id pA MS.empty) (Id pB MS.empty))
          @?= [CheckingRule ConjRRule :| []]
    , testCase "an error inside a subproof names the enclosing rule" $
        errorContexts (ConjL a b (ConjR (Id pA MS.empty) (Id pB MS.empty)))
          @?= [CheckingRule ConjRRule :| [Subproof 0, CheckingRule ConjLRule]]
    , testCase "a side condition is reported under the branch it constrains" $
        errorContexts (ImplL a b (Id pA MS.empty) (Id pB MS.empty))
          @?= [Subproof 0 :| [CheckingRule ImplLRule]]
    ]

isProofOfTests :: TestTree
isProofOfTests =
  testGroup
    "isProofOf"
    [ testCase "accepts the sequent the proof infers" $
        isProofOf (ImplR a (Id pA MS.empty)) (MS.empty |- a ==> a) @?= True
    , testCase "rejects a sequent carrying an undischarged premise" $
        isProofOf (ImplR a (Id pA MS.empty)) (ctx [a] |- a ==> a) @?= False
    , testCase "rejects a proof which does not typecheck at all" $
        isProofOf (ImplR b (Id pA MS.empty)) (MS.empty |- b ==> a) @?= False
    ]
