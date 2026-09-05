{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

{- |
Coverage for the tactic engine and the textual syntax.

Every script below is run through the parser and the engine, and the proof
the engine builds is handed to the checker: a tactic which produced the wrong
proof fails here as a rejected proof rather than a wrong theorem.
-}
module Language.Praxis.PRA.TacticTest (tacticTests) where

import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Data.Sized (pattern Nil, pattern (:<))
import Language.Praxis.PRA.Pattern (Hole (..))
import Language.Praxis.PRA.PrimitiveRecursion (PRFCode (..))
import Language.Praxis.PRA.PrimitiveRecursion.Examples (mult, plus)
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.Rule (Sort (..))
import Language.Praxis.PRA.Signature
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Syntax.Parser
import Language.Praxis.PRA.Syntax.Pretty
import Language.Praxis.PRA.Tactic
import Language.Praxis.PRA.Tactic.Parser
import Test.Tasty
import Test.Tasty.HUnit

tacticTests :: TestTree
tacticTests =
  testGroup
    "tactics"
    [ syntaxTests
    , tacticParserTests
    , provingTests
    , derivedTests
    , combinatorTests
    , failureTests
    , declarationTests
    ]

sig :: Signature
sig = signature [symbol "plus" plus, symbol "mult" mult]

sc :: Scope String
sc = plainScope sig

-- | Parse, or fail the test.
parsed :: Either String x -> IO x
parsed = either assertFailure pure

-- | A sequent from its concrete syntax.
sequent :: String -> Sequent String
sequent = either error id . parseSequent sc

-- | Prove the script @sequent by tactic@ and check the proof.
proves :: String -> Assertion
proves src = do
  (goal, tac) <- parsed (parseGoal sc src)
  case prove goal tac of
    Left err -> assertFailure (renderTacticError sig id err)
    Right p -> inferConclusion p @?= Right goal

-- | The script must fail, for the given reason.
failsWith :: String -> (Failure String -> Bool) -> Assertion
failsWith src ok = do
  (goal, tac) <- parsed (parseGoal sc src)
  case prove goal tac of
    Right _ -> assertFailure "the script was not expected to succeed"
    Left err -> assertBool (renderTacticError sig id err) (ok (errorFailure err))

-- | Forget the positions the parser attaches.
stripLoc :: Tactic a -> Tactic a
stripLoc = \case
  At _ t -> stripLoc t
  Then t u -> Then (stripLoc t) (stripLoc u)
  OrElse t u -> OrElse (stripLoc t) (stripLoc u)
  Try t -> Try (stripLoc t)
  Repeat t -> Repeat (stripLoc t)
  Dispatch t us -> Dispatch (stripLoc t) (map stripLoc us)
  t -> t

parsesTo :: String -> Tactic String -> Assertion
parsesTo src expected = do
  t <- parsed (parseTactic sc src)
  stripLoc t @?= expected

syntaxTests :: TestTree
syntaxTests =
  testGroup
    "concrete syntax"
    [ testCase "renders what it parsed" $
        roundTrip "a = 0 /\\ (b = 0 \\/ c = 0) ==> ~plus(x, S(y)) = 2"
    , testCase "the connectives associate to the right" $
        roundTrip "a = 0 ==> b = 0 ==> c = 0"
    , testCase "left-nested connectives are parenthesised" $
        roundTrip "(a = 0 ==> b = 0) ==> c = 0"
    , testCase "negation binds tighter than the connectives" $
        roundTrip "~a = 0 /\\ b = 0"
    , testCase "Unicode spellings are accepted" $ do
        f <- parsed (parseFormula sc "a = 0 ∧ b = 0 ∨ ¬c = 0 → ⊥")
        f @?= either error id (parseFormula sc "a = 0 /\\ b = 0 \\/ ~c = 0 ==> _|_")
    , testCase "a successor of a numeral is the next numeral" $ do
        t <- parsed (parseTerm sc "S(S(3))")
        t @?= Lit 5
    , testCase "a 0-ary symbol is written bare" $ do
        t <- parsed (parseTerm (plainScope (signature [symbol "c" (Zero :: PRFCode 0)])) "c")
        t @?= Lit 0
    , testCase "an application is arity-checked" $
        either (const (pure ())) (const (assertFailure "accepted")) (parseTerm sc "plus(x)")
    , testCase "the antecedent is a multiset" $
        sequent "a = 0, a = 0 |- a = 0" @?= sequent "a = 0, a = 0 |- a = 0"
    , testCase "a wildcard is refused in a sequent" $
        either (const (pure ())) (const (assertFailure "accepted")) (parseSequent sc "_ = 0 |- a = 0")
    , testCase "comments are skipped" $ do
        s <- parsed (parseSequent sc "a = 0 -- the hypothesis\n |- a = 0")
        s @?= sequent "a = 0 |- a = 0"
    ]
  where
    roundTrip src = do
      f <- parsed (parseFormula sc src)
      renderFormula sig id f @?= src

tacticParserTests :: TestTree
tacticParserTests =
  testGroup
    "tactic syntax"
    [ testCase "; binds looser than |" $
        "Id | refl; Id" `parsesTo` Then (OrElse (applyWith IdRule []) Refl) (applyWith IdRule [])
    , testCase "; associates to the left" $
        "Id; refl; skip" `parsesTo` Then (Then (applyWith IdRule []) Refl) Skip
    , testCase "blocks attach to the tactic before them" $
        "ConjR { refl } { Id }"
          `parsesTo` Dispatch (applyWith ConjRRule []) [Refl, applyWith IdRule []]
    , testCase "blocks under ; apply to every goal" $
        "ConjR; ConjR { refl } { refl }"
          `parsesTo` Then (applyWith ConjRRule []) (Dispatch (applyWith ConjRRule []) [Refl, Refl])
    , testCase "arguments follow the parameters, and _ leaves one open" $ do
        a <- parsed (parseFormulaPattern sc "a = 0")
        "ConjL _ (a = 0)" `parsesTo` Apply ConjLRule [Nothing, Just (ArgForm a)]
    , testCase "trailing arguments may be omitted" $
        "ConjL" `parsesTo` Apply ConjLRule [Nothing, Nothing]
    , testCase "context parameters are skipped" $ do
        t <- parsed (parseTermPattern sc "x")
        a <- parsed (parseFormulaPattern sc "a = 0")
        "SuccNonZero x (a = 0)" `parsesTo` Apply SuccNonZeroRule [Just (ArgTerm t), Nothing, Just (ArgForm a)]
    , testCase "a term argument may contain wildcards" $ do
        t <- parsed (parseTermPattern sc "plus(_, 0)")
        t @?= plus :$ (Var Wild :< Lit 0 :< Nil)
    , testCase "a reserved word is not a variable" $
        either (const (pure ())) (const (assertFailure "accepted")) (parseTactic sc "Subst Id t s (x = t)")
    , testCase "juxtaposed tactics are a syntax error" $
        either (const (pure ())) (const (assertFailure "accepted")) (parseTactic sc "ConjR refl")
    , testCase "try and repeat take a basic tactic" $
        "try repeat ConjL" `parsesTo` Try (Repeat (applyWith ConjLRule []))
    , testCase "the atomic pattern of rewrite may be parenthesised" $ do
        e <- parsed (parseAtomicPattern sc "t = s")
        h <- parsed (parseAtomicPattern sc "plus(t, 0) = _")
        "rewrite (t = s) in plus(t, 0) = _" `parsesTo` Rewrite e h
    , testCase "induction takes an optional eigenvariable" $
        "induction y as n" `parsesTo` Induction "y" (Just "n")
    , testCase "errors carry the position of the tactic" $ do
        (goal, tac) <- parsed (parseGoal sc "|- 2 = 3 by skip; refl")
        either errorLoc (const Nothing) (prove goal tac) @?= Just (Loc 1 19)
    ]

provingTests :: TestTree
provingTests =
  testGroup
    "primitive tactics"
    [ testCase "Id" $ proves "a = 0, b = 0 |- a = 0 by Id"
    , testCase "ExFalso" $ proves "_|_ |- a = 0 by ExFalso"
    , testCase "ConjL infers the unique conjunction" $
        proves "a = 0 /\\ b = 0 |- b = 0 /\\ a = 0 by ConjL; ConjR { Id } { Id }"
    , testCase "DisjL, DisjR1 and DisjR2" $
        proves "a = 0 \\/ b = 0 |- b = 0 \\/ a = 0 by DisjL { DisjR1; Id } { DisjR2; Id }"
    , testCase "ImplL with a partial argument" $
        proves
          "a = 0 ==> b = 0, b = 0 ==> c = 0 |- a = 0 ==> c = 0 by ImplR; ImplL (a = 0) _ { Id } { ImplL (b = 0) _ { Id } { Id } }"
    , testCase "Defeq and Subst prove symmetry" $
        proves "t = s |- s = t by Defeq t t; Subst x t s (x = t); Id"
    , testCase "Subst proves transitivity" $
        proves "t = s, s = u |- t = u by Subst x s u (t = x); Id"
    , testCase "Subst infers the equation from the substituted formula" $
        proves "t = s, s = u |- t = u by Subst x _ _ (t = x); Id"
    , testCase "SuccNonZero" $ proves "S(x) = 0 |- _|_ by SuccNonZero"
    , testCase "SuccInj" $ proves "S(x) = S(y) |- x = y by SuccInj; Id"
    , testCase "Ind with the motive given and the term inferred" $
        proves
          "|- plus(y, 0) = y by Ind n (plus(n, 0) = n) { refl } { Defeq plus(S(n), 0) S(plus(n, 0)); rewrite (plus(n, 0) = n) in (plus(S(n), 0) = _); Id }"
    , testCase "an argument pattern constrains the inference" $
        proves "a = 0 ==> b = 0, c = 0 ==> b = 0, c = 0 |- b = 0 by ImplL (c = 0) _ { Id } { Id }"
    , testCase "a closed argument is checked against the goal" $
        proves "|- a = 0 ==> a = 0 by ImplR (a = 0); Id"
    ]

derivedTests :: TestTree
derivedTests =
  testGroup
    "derived tactics"
    [ testCase "refl closes a definitional equation" $ proves "|- plus(0, y) = y by refl"
    , testCase "refl evaluates closed terms" $ proves "|- mult(3, 4) = 12 by refl"
    , testCase "symmetry" $ proves "t = s |- s = t by symmetry (t = s); Id"
    , testCase "symmetry selects by pattern" $ proves "t = s, u = 0 |- s = t by symmetry (_ = s); Id"
    , testCase "rewrite" $
        proves "t = s, plus(t, 0) = 3 |- plus(s, 0) = 3 by rewrite (t = s) in (plus(t, 0) = 3); Id"
    , testCase "rewrite replaces every occurrence" $
        proves "t = s, plus(t, t) = t |- plus(s, s) = s by rewrite (t = s) in (plus(t, t) = _); Id"
    , testCase "induction with a fresh eigenvariable" $
        proves
          "|- plus(y, 0) = y by induction y { refl } { Defeq plus(S(y'), 0) S(plus(y', 0)); rewrite (plus(y', 0) = y') in (plus(S(y'), 0) = _); Id }"
    , testCase "induction with a named eigenvariable" $
        proves
          "|- plus(y, 0) = y by induction y as n { refl } { Defeq plus(S(n), 0) S(plus(n, 0)); rewrite (plus(n, 0) = n) in (plus(S(n), 0) = _); Id }"
    , testCase "induction leaves the context alone" $
        proves "z = 0 |- plus(y, 0) = y by induction y as n { refl } { Defeq plus(S(n), 0) S(plus(n, 0)); rewrite (plus(n, 0) = n) in (plus(S(n), 0) = _); Id }"
    , testCase "assumption on an atom" $ proves "a = 0 |- a = 0 by assumption"
    , testCase "assumption on absurdity" $ proves "_|_ |- _|_ by assumption"
    , testCase "assumption expands the identity through the connectives" $
        proves "a = 0 /\\ (b = 0 ==> c = 0 \\/ _|_) |- a = 0 /\\ (b = 0 ==> c = 0 \\/ _|_) by assumption"
    , testCase "assumption keeps the rest of the context" $
        proves "a = 0 \\/ b = 0, c = 0 |- a = 0 \\/ b = 0 by assumption"
    ]

combinatorTests :: TestTree
combinatorTests =
  testGroup
    "combinators"
    [ testCase "| takes the first alternative which succeeds" $ proves "|- 2 = 2 by Id | refl"
    , testCase "try never fails" $ proves "|- 2 = 2 by try ConjL; refl"
    , testCase "repeat stops when the tactic fails" $
        proves "a = 0 /\\ b = 0 /\\ c = 0 |- c = 0 by repeat ConjL; Id"
    , testCase "; runs on every goal" $ proves "|- 2 = 2 /\\ 3 = 3 by ConjR; refl"
    , testCase "skip leaves a goal open, which is reported" $
        "|- 2 = 2 by skip" `failsWith` \case
          Unsolved [g] -> g == sequent "|- 2 = 2"
          _ -> False
    , testCase "repeat is bounded" $
        "|- 2 = 2 by repeat skip" `failsWith` \case
          RepeatLimit -> True
          _ -> False
    ]

failureTests :: TestTree
failureTests =
  testGroup
    "failures"
    [ testCase "a rule whose principal formula is absent" $
        "|- 2 = 2 by ConjL" `failsWith` \case
          NoHypothesis ConjLRule _ _ -> True
          _ -> False
    , testCase "a rule whose conclusion does not fit" $
        "|- 2 = 2 by ConjR" `failsWith` \case
          WrongSuccedent ConjRRule _ -> True
          _ -> False
    , testCase "an ambiguous principal formula" $
        "a = 0 ==> b = 0, c = 0 ==> b = 0 |- b = 0 by ImplL" `failsWith` \case
          AmbiguousHypothesis ImplLRule _ _ [_, _] -> True
          _ -> False
    , testCase "a parameter the goal does not determine" $
        "|- 2 = 2 by Defeq" `failsWith` \case
          CannotInfer DefeqRule _ -> True
          _ -> False
    , testCase "a failed side condition" $
        "|- 2 = 3 by refl" `failsWith` \case
          SideCondition DefeqRule (EqualityCheckFailed (Lit 2) (Lit 3)) -> True
          _ -> False
    , testCase "an eigenvariable in the induction term" $
        "|- plus(y, 0) = y by Ind y (plus(y, 0) = y) y" `failsWith` \case
          SideCondition IndRule (TermEigenVariableViolation "y" (Var "y")) -> True
          _ -> False
    , testCase "an eigenvariable in the context" $
        "n = 0 |- plus(y, 0) = y by Ind n (plus(n, 0) = n) y" `failsWith` \case
          SideCondition IndRule (AssumptionEigenVariableViolation "n" _) -> True
          _ -> False
    , testCase "an eigenvariable which is not fresh" $
        "|- plus(y, 0) = y by induction y as y" `failsWith` \case
          NotFresh "y" -> True
          _ -> False
    , testCase "the wrong number of blocks" $
        "|- 2 = 2 /\\ 3 = 3 by ConjR { refl }" `failsWith` \case
          WrongGoalCount 1 2 -> True
          _ -> False
    , testCase "refl on a connective" $
        "|- 2 = 2 /\\ 3 = 3 by refl" `failsWith` \case
          NotAnEquation _ -> True
          _ -> False
    , testCase "rewrite with a term which does not occur" $
        "t = s, u = 0 |- u = 0 by rewrite (t = s) in (u = 0)" `failsWith` \case
          NothingToRewrite _ _ -> True
          _ -> False
    , testCase "assumption on a succedent which is not in the context" $
        "a = 0 |- b = 0 by assumption" `failsWith` \case
          NotInContext _ -> True
          _ -> False
    , testCase "every alternative failing is reported with each failure" $
        "|- 2 = 3 by Id | refl" `failsWith` \case
          Alternatives [_, _] -> True
          _ -> False
    , testCase "an unknown premise" $
        "|- 2 = 2 by exact D" `failsWith` \case
          UnknownPremise "D" -> True
          _ -> False
    , testCase "the rendering names the rule and the goal" $ do
        (goal, tac) <- parsed (parseGoal sc "|- 2 = 2 by ConjL")
        case prove goal tac of
          Right _ -> assertFailure "proved"
          Left err ->
            renderTacticError sig id err
              @?= "1:13: ConjL: no hypothesis of the form A /\\ B\n  goal: |- 2 = 2"
    ]

declarationTests :: TestTree
declarationTests =
  testGroup
    "declarations"
    [ testCase "theorems and rules parse, with their binders" $ do
        decls <- parsed (parseDecls (plainMetaScope sig) source)
        map declName decls @?= ["plus_zero_left", "swap"]
        map declBinders decls
          @?= [ []
              ,
                [ MetaBinder ["a", "b"] TermS
                , PremiseBinder "D1" (sequent "a = 0, b = 0 |- b = 0")
                , PremiseBinder "D2" (sequent "a = 0, b = 0 |- a = 0")
                ]
              ]
    , testCase "a theorem is proved" $ do
        decls <- parsed (parseDecls (plainMetaScope sig) source)
        case decls of
          d : _ -> either (assertFailure . renderTacticError sig id) (const (pure ())) (prove (declGoal d) (declTactic d))
          [] -> assertFailure "no declarations"
    , testCase "a rule is proved from its premises, which become the leaves" $ do
        decls <- parsed (parseDecls (plainMetaScope sig) source)
        case decls of
          [_, d] -> do
            let prems = Map.fromList [(n, s) | PremiseBinder n s <- declBinders d]
            case proveOpen prems (declGoal d) (declTactic d) of
              Left err -> assertFailure (renderTacticError sig id err)
              Right p -> toList p @?= ["D1", "D2"]
          _ -> assertFailure "expected two declarations"
    , testCase "exact checks the premise against the goal" $ do
        (goal, tac) <- parsed (parseGoal sc "|- 2 = 2 by exact D")
        case proveOpen (Map.fromList [("D", sequent "|- 3 = 3")]) goal tac of
          Left (TacticError _ _ (PremiseMismatch "D" _)) -> pure ()
          Left err -> assertFailure (renderTacticError sig id err)
          Right _ -> assertFailure "proved"
    , testCase "a formula metavariable needs the quasiquoter" $
        either
          (const (pure ()))
          (const (assertFailure "accepted"))
          (parseDecls (plainMetaScope sig) "rule r (A : formula) : A |- A by assumption")
    ]
  where
    source =
      unlines
        [ "-- The left identity is definitional."
        , "theorem plus_zero_left : |- plus(0, y) = y"
        , "by refl"
        , ""
        , "rule swap (a b : term) (D1 : a = 0, b = 0 |- b = 0) (D2 : a = 0, b = 0 |- a = 0)"
        , "  : a = 0 /\\ b = 0 |- b = 0 /\\ a = 0"
        , "by ConjL; ConjR { exact D1 } { exact D2 }"
        ]
