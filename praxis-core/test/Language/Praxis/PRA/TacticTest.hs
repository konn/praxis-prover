{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

{- |
Coverage for the tactic engine and the textual syntax.

Every script below is run through the parser and the engine, and the proof
the engine builds is handed to the checker: a tactic which produced the wrong
proof fails here as a rejected proof rather than a wrong theorem.
-}
module Language.Praxis.PRA.TacticTest (tacticTests) where

import Control.Exception (displayException)
import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Data.Sized (pattern Nil, pattern (:<))
import Language.Praxis.PRA.Pattern (Hole (..))
import Language.Praxis.PRA.PrimitiveRecursion (PRFCode (..), builtin)
import Language.Praxis.PRA.PrimitiveRecursion.Examples (mult, plus)
import Language.Praxis.PRA.PrimitiveRecursion.Function (emptyKernelEnv)
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.Rule (Sort (..))
import Language.Praxis.PRA.Signature
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Syntax.Parser
import Language.Praxis.PRA.Syntax.Pretty
import Language.Praxis.PRA.Tactic
import Language.Praxis.PRA.Tactic.Parser
import Language.Praxis.PRA.Tactic.Quote (SchemaName (..), renderSchemaTacticError, schemaScope)
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
    , prettyTests
    , sorryTests
    , inductionTests
    , lemmaTests
    , namingTests
    , calcTests
    , congTests
    , haveTests
    , equationTests
    ]

sig :: Signature
sig = signature [symbol "plus" plus, symbol "mult" mult]

sc :: Scope String
sc = plainScope sig

-- | Parse, or fail the test.
parsed :: Either SyntaxError x -> IO x
parsed = either (assertFailure . displayException) pure

-- | A sequent from its concrete syntax.
sequent :: String -> Sequent String
sequent = either (error . displayException) id . parseSequent sc

-- | Prove the script @sequent by tactic@ and check the proof.
proves :: String -> Assertion
proves src = do
  (goal, tac) <- parsed (parseGoal sc src)
  case prove goal tac of
    Left err -> assertFailure (renderTacticError sig id err)
    Right p -> inferConclusion p @?= Right (goalSequent goal)

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
  On ns t -> On ns (stripLoc t)
  As ns t -> As ns (stripLoc t)
  Calc t steps -> Calc t (map (fmap stripLoc) steps)
  Have n f t -> Have n f (stripLoc t)
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
        roundTrip "a = 0 /\\ (b = 0 \\/ c = 0) ==> ~x + S y = 2"
    , testCase "the connectives associate to the right" $
        roundTrip "a = 0 ==> b = 0 ==> c = 0"
    , testCase "left-nested connectives are parenthesised" $
        roundTrip "(a = 0 ==> b = 0) ==> c = 0"
    , testCase "negation binds tighter than the connectives" $
        roundTrip "~a = 0 /\\ b = 0"
    , testCase "Unicode spellings are accepted" $ do
        f <- parsed (parseFormula sc "a = 0 ∧ b = 0 ∨ ¬c = 0 → ⊥")
        f @?= either (error . displayException) id (parseFormula sc "a = 0 /\\ b = 0 \\/ ~c = 0 ==> _|_")
    , testCase "a successor of a numeral is the next numeral" $ do
        t <- parsed (parseTerm sc "S (S 3)")
        t @?= Lit 5
    , testCase "a 0-ary symbol is written bare" $ do
        t <- parsed (parseTerm (plainScope (signature [symbol "c" (Zero :: PRFCode 0)])) "c")
        t @?= Lit 0
    , testCase "an application is arity-checked" $
        either (const (pure ())) (const (assertFailure "accepted")) (parseTerm sc "plus x")
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
    , testCase "term arguments are atoms, so applications are parenthesized" $ do
        t <- parsed (parseTermPattern sc "S t")
        "Defeq (S t) (S t)" `parsesTo` Apply DefeqRule [Just (ArgTerm t), Just (ArgTerm t)]
        either (const (pure ())) (const (assertFailure "accepted")) (parseTactic sc "Defeq S t S t")
    , testCase "context parameters are skipped" $ do
        t <- parsed (parseTermPattern sc "x")
        a <- parsed (parseFormulaPattern sc "a = 0")
        "SuccNonZero x (a = 0)" `parsesTo` Apply SuccNonZeroRule [Just (ArgTerm t), Nothing, Just (ArgForm a)]
    , testCase "a term argument may contain wildcards" $ do
        t <- parsed (parseTermPattern sc "plus _ 0")
        t @?= plus :$ (Var Wild :< Lit 0 :< Nil)
    , testCase "a reserved word is not a variable" $
        either (const (pure ())) (const (assertFailure "accepted")) (parseTactic sc "Subst Id t s (x = t)")
    , testCase "juxtaposed tactics are a syntax error" $
        either (const (pure ())) (const (assertFailure "accepted")) (parseTactic sc "ConjR refl")
    , testCase "try and repeat take a basic tactic" $
        "try repeat ConjL" `parsesTo` Try (Repeat (applyWith ConjLRule []))
    , testCase "the atomic pattern of rewrite may be parenthesised" $ do
        e <- parsed (parseAtomicPattern sc "t = s")
        h <- parsed (parseAtomicPattern sc "plus t 0 = _")
        "rewrite (t = s) in (plus t 0 = _)" `parsesTo` Rewrite (ByPattern e) (ByPattern h)
    , testCase "induction takes an optional eigenvariable" $
        "induction y as n" `parsesTo` Induction (Var "y") (Just "n")
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
    , testCase "SuccNonZero" $ proves "S x = 0 |- _|_ by SuccNonZero"
    , testCase "SuccInj" $ proves "S x = S y |- x = y by SuccInj; Id"
    , testCase "Ind with the motive given and the term inferred" $
        proves
          "|- plus y 0 = y by Ind n (plus n 0 = n) { refl } { Defeq (plus (S n) 0) (S (plus n 0)); rewrite (plus n 0 = n) in (plus (S n) 0 = _); Id }"
    , testCase "an argument pattern constrains the inference" $
        proves "a = 0 ==> b = 0, c = 0 ==> b = 0, c = 0 |- b = 0 by ImplL (c = 0) _ { Id } { Id }"
    , testCase "a closed argument is checked against the goal" $
        proves "|- a = 0 ==> a = 0 by ImplR (a = 0); Id"
    ]

derivedTests :: TestTree
derivedTests =
  testGroup
    "derived tactics"
    [ testCase "refl closes a definitional equation" $ proves "|- plus 0 y = y by refl"
    , testCase "refl evaluates closed terms" $ proves "|- mult 3 4 = 12 by refl"
    , testCase "symmetry" $ proves "t = s |- s = t by symmetry (t = s); Id"
    , testCase "symmetry selects by pattern" $ proves "t = s, u = 0 |- s = t by symmetry (_ = s); Id"
    , testCase "rewrite" $
        proves "t = s, plus t 0 = 3 |- plus s 0 = 3 by rewrite (t = s) in (plus t 0 = 3); Id"
    , testCase "rewrite replaces every occurrence" $
        proves "t = s, plus t t = t |- plus s s = s by rewrite (t = s) in (plus t t = _); Id"
    , testCase "induction with a fresh eigenvariable" $
        proves
          "|- plus y 0 = y by induction y { refl } { Defeq (plus (S y') 0) (S (plus y' 0)); rewrite (plus y' 0 = y') in (plus (S y') 0 = _); Id }"
    , testCase "induction with a named eigenvariable" $
        proves
          "|- plus y 0 = y by induction y as n { refl } { Defeq (plus (S n) 0) (S (plus n 0)); rewrite (plus n 0 = n) in (plus (S n) 0 = _); Id }"
    , testCase "induction leaves the context alone" $
        proves "z = 0 |- plus y 0 = y by induction y as n { refl } { Defeq (plus (S n) 0) (S (plus n 0)); rewrite (plus n 0 = n) in (plus (S n) 0 = _); Id }"
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
          Unsolved [g] -> goalSequent g == sequent "|- 2 = 2"
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
        "|- plus y 0 = y by Ind y (plus y 0 = y) y" `failsWith` \case
          SideCondition IndRule (TermEigenVariableViolation "y" (Var "y")) -> True
          _ -> False
    , testCase "an eigenvariable in the context" $
        "n = 0 |- plus y 0 = y by Ind n (plus n 0 = n) y" `failsWith` \case
          SideCondition IndRule (AssumptionEigenVariableViolation "n" _) -> True
          _ -> False
    , testCase "an eigenvariable which is not fresh" $
        "|- plus y 0 = y by induction y as y" `failsWith` \case
          NotFresh "y" -> True
          _ -> False
    , testCase "the wrong number of blocks" $
        "|- 2 = 2 /\\ 3 = 3 by ConjR { refl }" `failsWith` \case
          WrongGoalCount 1 2 -> True
          _ -> False
    , testCase "refl on a connective" $
        "|- 2 = 2 /\\ 3 = 3 by refl" `failsWith` \case
          NotAnEquation "refl" _ -> True
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
    , testCase "atomic metavariables parse in primitive and derived tactic arguments" $ do
        let scope = schemaScope sig [("P", AtomS), ("Q", AtomS)]
        mapM_
          (parsed . parseTactic scope)
          ["Id (P)", "Subst x t s (P)", "symmetry (P)", "rewrite P in (Q)"]
    , testCase "formula and context metavariables are refused in atomic positions" $ do
        let scope = schemaScope sig [("A", FormS), ("G", CtxS)]
        mapM_
          (\src -> either (const (pure ())) (const (assertFailure ("accepted " <> src))) (parseTactic scope src))
          ["Id (A)", "Subst x t s (A)", "rewrite A in (A)", "Id (G)"]
    ]
  where
    source =
      unlines
        [ "-- The left identity is definitional."
        , "theorem plus_zero_left : |- plus 0 y = y"
        , "by refl"
        , ""
        , "rule swap (a b : term) (D1 : a = 0, b = 0 |- b = 0) (D2 : a = 0, b = 0 |- a = 0)"
        , "  : a = 0 /\\ b = 0 |- b = 0 /\\ a = 0"
        , "by ConjL; ConjR { exact D1 } { exact D2 }"
        ]

prettyTests :: TestTree
prettyTests =
  testGroup
    "rendering"
    [ testCase "operators, conditionals and bounded searches round-trip over the builtin signature" $
        mapM_
          (\src -> (renderSequent builtin id <$> parseSequent (plainScope builtin) src) @?= Right src)
          [ "|- 2 + 3 * 4 = 14"
          , "|- (2 + 3) * 4 = 20"
          , "|- 2 ^ 3 ^ 2 = 512"
          , "|- (2 ^ 3) ^ 2 = 64"
          , "|- x - (y - z) = x - y - z"
          , "|- x < y"
          , "|- (x < y) = 0"
          , "|- (x < y) + 1 = 2"
          , "|- x < y /\\ x <= y"
          , "|- ~x < y"
          , "|- S (x + 1) = y"
          , "|- (if 0 < 1 then 10 else 20) = 10"
          , "|- x + (if x < y then 1 else 2) = z"
          , "|- x = if x < y then 1 else 2"
          , "|- mu {lt} 3 0 = 3"
          , "|- (μ i < 10. 3 < i) = 4"
          , "|- (μ i < 10. y < i) + 1 = 4"
          , "|- (μ i < 10. (μ j < i. 3 < j) < i) = 5"
          , "a + 1 = 2 |- a = 1"
          ]
    , testCase "a comparison standing alone is its equation with 1" $ do
        let sc' = plainScope builtin
        parseSequent sc' "|- t < S t" @?= parseSequent sc' "|- (t < S t) = 1"
        parseSequent sc' "x <= y, ~x < y |- _|_" @?= parseSequent sc' "(x <= y) = 1, ~(x < y) = 1 |- _|_"
        (renderSequent builtin id <$> parseSequent sc' "|- (t < S t) = 1") @?= Right "|- t < S t"
        (renderSequent builtin id <$> parseSequent sc' "|- 1 = (t < S t)") @?= Right "|- 1 = t < S t"
    , testCase "an operator is shown only for the symbol it reads as" $ do
        renderTerm sig id (plus :$ (Var "x" :< Var "y" :< Nil)) @?= "x + y"
        renderTerm sig id (mult :$ (Var "x" :< Var "y" :< Nil)) @?= "mult x y"
        let shadowed = signature [symbol "plus" plus, symbol "add" mult]
        renderTerm shadowed id (plus :$ (Var "x" :< Var "y" :< Nil)) @?= "plus x y"
        renderTerm shadowed id (mult :$ (Var "x" :< Var "y" :< Nil)) @?= "x + y"
    ]

sorryTests :: TestTree
sorryTests =
  testGroup
    "sorry"
    [ testCase "sorry parses" $ "sorry" `parsesTo` Sorry
    , testCase "sorry abandons the proof at its goal" $
        "|- 2 = 2 by sorry" `failsWith` \case
          Unfinished -> True
          _ -> False
    , testCase "neither |, try nor repeat catches sorry" $
        mapM_
          ( \src ->
              src `failsWith` \case
                Unfinished -> True
                _ -> False
          )
          ["|- 2 = 2 by sorry | refl", "|- 2 = 2 by try sorry; refl", "|- 2 = 2 by repeat sorry"]
    , testCase "the report shows the goal of the branch" $ do
        (goal, tac) <- parsed (parseGoal sc "|- 2 = 2 /\\ 3 = 3 by ConjR { sorry } { refl }")
        case prove goal tac of
          Right _ -> assertFailure "proved"
          Left err -> renderTacticError sig id err @?= "1:30: sorry: the proof stops here\n  |- 2 = 2"
    , testCase "the report lists the assumptions of the branch, one per line" $ do
        (goal, tac) <- parsed (parseGoal sc "a = 0, b = 0 /\\ c = 0 |- c = 0 by ConjL; sorry")
        case prove goal tac of
          Right _ -> assertFailure "proved"
          Left err -> renderTacticError sig id err @?= "1:42: sorry: the proof stops here\n  H1 : a = 0\n  H3 : b = 0\n  H4 : c = 0\n  |- c = 0"
    ]

inductionTests :: TestTree
inductionTests =
  testGroup
    "induction on a term"
    [ testCase "a compound term is abstracted into the eigenvariable" $
        proves "|- plus (S x) 0 = S x by induction (S x) as n { refl } { Defeq (plus (S n) 0) (S (plus n 0)); rewrite (plus n 0 = n) in (plus (S n) 0 = _); Id }"
    , testCase "a term metavariable of a rule, whose branches sorry reports by name" $ do
        let source =
              unlines
                [ "rule ltZero (t: term) (G: ctx) (A : formula) : t < 0 = 1, G |- A"
                , "by"
                , "  induction t"
                , "  { "
                , "    sorry "
                , "  }"
                , "  { "
                , "    sorry"
                , "  }"
                ]
        decls <- parsed (parseDecls (schemaScope builtin) source)
        env <- either (assertFailure . displayException) pure (signatureKernelEnv builtin)
        case decls of
          [d] -> case proveOpenIn env Map.empty (declGoal d) (declTactic d) of
            Left err -> renderSchemaTacticError builtin err @?= "5:5: sorry: the proof stops here\n  H1 : t < 0\n  G\n  H2 : 0 < 0\n  |- A"
            Right _ -> assertFailure "proved"
          _ -> assertFailure "expected one declaration"
    , testCase "hypotheses mentioning the term are generalized, through Cut" $
        proves "y + 0 = 0 |- y = 0 by induction y as n { refl } { Defeq (S n + 0) (S (n + 0)); rewrite (S n + 0 = S (n + 0)) in (S n + 0 = 0); SuccNonZero }"
    , testCase "each case carries the generalized hypotheses and the induction hypothesis" $ do
        (base, baseTactic) <- parsed (parseGoal sc "y + 0 = z |- y = z by induction y as n { sorry } { skip }")
        case prove base baseTactic of
          Left err -> renderTacticError sig id err @?= "1:42: sorry: the proof stops here\n  H1 : y + 0 = z\n  H2 : 0 + 0 = z\n  |- 0 = z"
          Right _ -> assertFailure "proved"
        (step, stepTactic) <- parsed (parseGoal sc "y + 0 = z |- y = z by induction y as n { skip } { sorry }")
        case prove step stepTactic of
          Left err -> renderTacticError sig id err @?= "1:51: sorry: the proof stops here\n  H1 : y + 0 = z\n  H2 : n + 0 = z ==> n = z\n  H3 : S n + 0 = z\n  |- S n = z"
          Right _ -> assertFailure "proved"
    ]

lemmaTests :: TestTree
lemmaTests =
  testGroup
    "lemmas"
    [ testCase "exact takes arguments for the metavariables of a lemma" $ do
        t <- parsed (parseTermPattern sc "S x")
        f <- parsed (parseFormulaPattern sc "a = 0")
        let lemmas = Map.fromList [("foo", [TermS, CtxS, FormS])]
        tac <- parsed (parseTacticIn lemmas sc "exact foo (S x) (a = 0)")
        stripLoc tac @?= Exact "foo" [Just (ArgTerm t), Nothing, Just (ArgForm f)]
        bare <- parsed (parseTacticIn lemmas sc "exact foo")
        stripLoc bare @?= Exact "foo" [Nothing, Nothing, Nothing]
    , testCase "a premise takes no arguments" $ "exact D" `parsesTo` Exact "D" []
    , testCase "a declaration is a lemma for those after it" $ do
        decls <- parsed (parseDecls (plainMetaScope sig) "theorem two : |- 2 = 2 by refl\ntheorem again : |- 2 = 2 by exact two")
        map (stripLoc . declTactic) decls @?= [Refl, Exact "two" []]
    , testCase "a theorem is appealed to at an instance of its free variables" $ do
        lemmas <- plusZero
        provesWith lemmas "|- plus (S x) 0 = S x by exact plusZero"
        provesWith lemmas "|- plus 3 0 = 3 by exact plusZero"
    , testCase "a theorem is weakened to the hypotheses of the goal" $ do
        lemmas <- plusZero
        provesWith lemmas "z = 0, plus x 0 = 3 |- plus x 0 = x by exact plusZero"
    , testCase "the eigenvariable of the lemma is renamed apart from the goal" $ do
        lemmas <- plusZero
        provesWith lemmas "n = 0 |- plus n 0 = n by exact plusZero"
        provesWith lemmas "|- plus (S n) 0 = S n by exact plusZero"
    , testCase "a goal which is not an instance" $ do
        lemmas <- plusZero
        failsWithIn lemmas "|- plus 0 y = y by exact plusZero" \case
          NotAnInstance "plusZero" _ -> True
          _ -> False
    , testCase "the premises of a lemma are left as goals" $
        provesWith both "2 = 2 |- 2 = 2 /\\ 2 = 2 by exact both { Id }"
    , testCase "a lemma with premises but no context metavariable is not weakened" $
        failsWithIn both "2 = 2, c = 0 |- 2 = 2 /\\ 2 = 2 by exact both { Id }" \case
          CannotWeaken "both" _ -> True
          _ -> False
    , testCase "a lemma with premises must be closed but for its metavariables" $
        failsWithIn bothOpen "a = 0 |- a = 0 /\\ a = 0 by exact bothOpen { Id }" \case
          NotClosed "bothOpen" ["a"] -> True
          _ -> False
    , testCase "an unknown lemma" $
        "|- 2 = 2 by exact nothing" `failsWith` \case
          UnknownPremise "nothing" -> True
          _ -> False
    , testCase "a bound variable metavariable must be instantiated apart from the goal" $ do
        let scope = schemaScope builtin [("x", VarS), ("t", TermS), ("Γ", CtxS)]
        statement <- parsed (parseSequent scope "Γ |- t + 0 = t")
        let indAt = Lemma [("x", VarS), ("t", TermS), ("Γ", CtxS)] [] statement ["x"]
            lemmas = Map.fromList [("indAt", indAt)]
            run src = do
              (goal, tac) <- parsed (parseGoalIn (Map.map (map snd . lemmaMetas) lemmas) (schemaScope builtin []) src)
              pure (proveOpenWith emptyKernelEnv lemmas Map.empty goal tac)
        either (assertFailure . renderSchemaTacticError builtin) (const (pure ())) =<< run "m = 0 |- n + 0 = n by exact indAt k"
        run "m = 0 |- n + 0 = n by exact indAt n" >>= \case
          Left (TacticError _ _ (NotEigen "indAt" "x" (Obj "n"))) -> pure ()
          Left err -> assertFailure (renderSchemaTacticError builtin err)
          Right _ -> assertFailure "proved"
        run "m = 0 |- n + 0 = n by exact indAt" >>= \case
          Left (TacticError _ _ (CannotInstantiate "indAt" _)) -> pure ()
          Left err -> assertFailure (renderSchemaTacticError builtin err)
          Right _ -> assertFailure "proved"
    ]
  where
    plusZero = do
      thm <- certified "|- plus y 0 = y by induction y as n { refl } { Defeq (plus (S n) 0) (S (plus n 0)); rewrite (plus n 0 = n) in (plus (S n) 0 = _); Id }"
      pure (Map.fromList [("plusZero", thm)])
    -- A rule with a premise and no context metavariable: from the premise, the conjunction.
    both = conjoining "both" "2 = 2"
    bothOpen = conjoining "bothOpen" "a = 0"
    conjoining name p =
      Map.fromList
        [
          ( name
          , Certified
              (Lemma [] [("D", sequent (p <> " |- " <> p))] (sequent (p <> " |- " <> p <> " /\\ " <> p)) [])
              (\_ ds -> case ds of [d] -> ConjR d d; _ -> error (name <> " takes one premise"))
          )
        ]

-- | A theorem proved by a script, as a lemma for others.
certified :: String -> IO (Certified String)
certified src = do
  (goal, tac) <- parsed (parseGoal sc src)
  either (assertFailure . renderTacticError sig id) (pure . theorem (goalSequent goal)) (prove goal tac)

lemmaSortsOf :: Map.Map String (Certified String) -> Lemmas
lemmaSortsOf = Map.map (map snd . lemmaMetas . certifiedLemma)

-- | Prove the script with lemmas to appeal to, and check the proof.
provesWith :: Map.Map String (Certified String) -> String -> Assertion
provesWith lemmas src = do
  (goal, tac) <- parsed (parseGoalIn (lemmaSortsOf lemmas) sc src)
  case proveWith emptyKernelEnv lemmas goal tac of
    Left err -> assertFailure (renderTacticError sig id err)
    Right p -> inferConclusion p @?= Right (goalSequent goal)

failsWithIn :: Map.Map String (Certified String) -> String -> (Failure String -> Bool) -> Assertion
failsWithIn lemmas src ok = do
  (goal, tac) <- parsed (parseGoalIn (lemmaSortsOf lemmas) sc src)
  case proveWith emptyKernelEnv lemmas goal tac of
    Right _ -> assertFailure "the script was not expected to succeed"
    Left err -> assertBool (renderTacticError sig id err) (ok (errorFailure err))

namingTests :: TestTree
namingTests =
  testGroup
    "named hypotheses"
    [ testCase "on and as follow a step" $ do
        "ConjL on H2 as H5 H6" `parsesTo` As ["H5", "H6"] (On ["H2"] (Apply ConjLRule [Nothing, Nothing]))
        "symmetry H1" `parsesTo` Symmetry (ByName "H1")
        h <- parsed (parseAtomicPattern sc "plus t 0 = _")
        "rewrite H1 in (plus t 0 = _) as H3" `parsesTo` As ["H3"] (Rewrite (ByName "H1") (ByPattern h))
        "induction y as n IH H" `parsesTo` As ["IH", "H"] (Induction (Var "y") (Just "n"))
    , testCase "the hypotheses are numbered in the order written" $ do
        (goal, _) <- parsed (parseGoal sc "a = 0, b = 0 |- c = 0 by skip")
        map hypothesisName (goalHypotheses goal) @?= ["H1", "H2"]
    , testCase "symmetry and rewrite select by name" $ do
        proves "t = s |- s = t by symmetry H1; Id"
        proves "t = s, plus t 0 = 3 |- plus s 0 = 3 by rewrite H1 in H2; Id"
    , testCase "a name given to symmetry is not taken by its Defeq step" $ do
        proves "t = s |- s = t by symmetry H1 as H2; exact H2"
        (goal, tac) <- parsed (parseGoal sc "t = s |- s = t by symmetry H1 as H2; sorry")
        case prove goal tac of
          Right _ -> assertFailure "proved"
          Left err -> renderTacticError sig id err @?= "1:38: sorry: the proof stops here\n  H1 : t = s\n  H3 : t = t\n  H2 : s = t\n  |- s = t"
    , testCase "on picks the principal formula" $
        proves "a = 0 ==> b = 0, c = 0 ==> b = 0, c = 0 |- b = 0 by ImplL on H2 { Id } { Id }"
    , testCase "as names what a step introduces, and exact closes by a hypothesis" $ do
        proves "a = 0 /\\ b = 0 |- b = 0 by ConjL as HA HB; exact HB"
        proves "a = 0, b = 0 |- b = 0 by exact H2"
        proves "a = 0, b = 0 |- b = 0 by Cut (a = 0) { Id } { exact H2 }"
    , testCase "a hypothesis stated again keeps its name and place" $ do
        (goal, tac) <- parsed (parseGoal sc "t = s, plus t 0 = 3 |- plus s 0 = 3 by rewrite H1 in H2 as H5; sorry")
        case prove goal tac of
          Right _ -> assertFailure "proved"
          Left err -> renderTacticError sig id err @?= "1:64: sorry: the proof stops here\n  H1 : t = s\n  H2 : t + 0 = 3\n  H5 : s + 0 = 3\n  |- s + 0 = 3"
    , testCase "a name given moves the numbering past it" $ do
        (goal, tac) <- parsed (parseGoal sc "|- 2 = 2 /\\ 3 = 3 by Cut (1 = 1) as H7 { refl } { Cut (0 = 0) { refl } { sorry } }")
        case prove goal tac of
          Right _ -> assertFailure "proved"
          Left err -> renderTacticError sig id err @?= "1:74: sorry: the proof stops here\n  H7 : 1 = 1\n  H8 : 0 = 0\n  |- 2 = 2 /\\ 3 = 3"
    , testCase "induction names the induction hypothesis and the ones reintroduced" $ do
        (goal, tac) <- parsed (parseGoal sc "y + 0 = z |- y = z by induction y as n IH H { skip } { sorry }")
        case prove goal tac of
          Right _ -> assertFailure "proved"
          Left err -> renderTacticError sig id err @?= "1:56: sorry: the proof stops here\n  H1 : y + 0 = z\n  IH : n + 0 = z ==> n = z\n  H : S n + 0 = z\n  |- S n = z"
    , testCase "an unknown name" $
        "a = 0 |- a = 0 by symmetry H5" `failsWith` \case
          UnknownHypothesis "H5" -> True
          _ -> False
    , testCase "on with a hypothesis of the wrong shape" $
        "a = 0, b = 0 ==> c = 0 |- c = 0 by ImplL on H1 { Id } { Id }" `failsWith` \case
          NotPrincipal ImplLRule "H1" _ -> True
          _ -> False
    , testCase "exact on a hypothesis which is not the succedent" $
        "a = 0 |- b = 0 by exact H1" `failsWith` \case
          HypothesisMismatch "H1" _ -> True
          _ -> False
    , testCase "names left over, a name in use, and a step which names nothing" $ do
        "a = 0 /\\ b = 0 |- b = 0 by ConjL as H1 H2 H3; Id" `failsWith` \case
          NamesUnused ["H3"] -> True
          _ -> False
        "a = 0, b = 0 /\\ c = 0 |- c = 0 by ConjL as H1 H9; Id" `failsWith` \case
          NameInUse "H1" -> True
          _ -> False
        "|- 2 = 2 by refl as H" `failsWith` \case
          NothingToName -> True
          _ -> False
    ]

calcTests :: TestTree
calcTests =
  testGroup
    "calc"
    [ testCase "a chain of equations, each with its tactic or refl" $ do
        "calc a = b by Id = c" `parsesTo` Calc (Var "a") [(Var "b", applyWith IdRule []), (Var "c", Refl)]
        "calc plus 0 y = y" `parsesTo` Calc (plus :$ (Lit 0 :< Var "y" :< Nil)) [(Var "y", Refl)]
    , testCase "the steps are proved under the hypotheses and chained" $ do
        proves "a = b, b = c |- a = c by calc a = b by Id = c by Id"
        proves "a = b, b = c, c = d |- a = d by calc a = b by Id = c by Id = d by Id"
        proves "|- plus 0 y = y by calc plus 0 y = y"
        proves "|- mult 2 3 = 6 by calc mult 2 3 = plus 3 3 = 6"
        proves "t = s |- plus 0 t = s by calc plus 0 t = t = s by Id"
    , testCase "a step may use blocks, and every step sees the goal's hypotheses" $ do
        (goal, tac) <- parsed (parseGoal sc "a = b, b = c |- a = c by calc a = b by Id = c by sorry")
        case prove goal tac of
          Right _ -> assertFailure "proved"
          Left err -> renderTacticError sig id err @?= "1:50: sorry: the proof stops here\n  H1 : a = b\n  H2 : b = c\n  |- b = c"
    , testCase "the chain must run between the sides of the goal" $
        "|- a = c by calc a = b = d" `failsWith` \case
          CalcMismatch (Var "a") (Var "d") -> True
          _ -> False
    ]

congTests :: TestTree
congTests =
  testGroup
    "cong"
    [ testCase "cong takes a hypothesis, or finds one" $ do
        "cong H2" `parsesTo` Cong (Just (ByName "H2"))
        "cong" `parsesTo` Cong Nothing
        e <- parsed (parseAtomicPattern sc "t = s")
        "cong (t = s)" `parsesTo` Cong (Just (ByPattern e))
    , testCase "an equation rewritten under function symbols" $ do
        proves "t = s |- plus t 0 = plus s 0 by cong H1"
        proves "t = s |- plus t t = plus s s by cong H1"
        proves "t = s |- plus t t = plus s t by cong H1"
        proves "t = s |- S (mult t 2) = S (mult s 2) by cong (t = s)"
        proves "t = s |- t = s by cong H1"
    , testCase "the hypothesis may state the equation either way round" $
        proves "s = t |- plus t 0 = plus s 0 by cong H1"
    , testCase "without a selector, the first hypothesis which fits is used" $
        proves "a = 0, t = s, u = 0 |- mult t 2 = mult s 2 by cong"
    , testCase "a numeral is a successor" $
        proves "n = 2 |- S n = 3 by cong"
    , testCase "cong in a calculation" $
        proves "t = s, plus s 0 = s |- plus t 0 = s by calc plus t 0 = plus s 0 by cong H1 = s by Id"
    , testCase "no hypothesis fits" $ do
        "t = s |- plus t 0 = plus 0 s by cong" `failsWith` \case
          NoCongruence _ [_] -> True
          _ -> False
        "t = s, u = 0 |- plus t 0 = plus u 0 by cong H1" `failsWith` \case
          NoCongruence _ [_] -> True
          _ -> False
        "t = s, u = 0 |- plus t 0 = plus u 0 by cong" `failsWith` \case
          NoCongruence _ [_, _] -> True
          _ -> False
    , testCase "cong on a goal which is not an equation" $
        "t = s |- 2 = 2 /\\ 3 = 3 by cong" `failsWith` \case
          NotAnEquation "cong" _ -> True
          _ -> False
    , testCase "cong names nothing" $
        "t = s |- plus t 0 = plus s 0 by cong H1 as H" `failsWith` \case
          NothingToName -> True
          _ -> False
    ]

haveTests :: TestTree
haveTests =
  testGroup
    "have"
    [ testCase "have takes a name, or none" $ do
        f <- parsed (parseFormula sc "a = 0")
        "have H: (a = 0) { Id }" `parsesTo` Have (Just "H") f (applyWith IdRule [])
        "have (a = 0) { Id }" `parsesTo` Have Nothing f (applyWith IdRule [])
        "have : (a = 0) { Id }" `parsesTo` Have Nothing f (applyWith IdRule [])
    , testCase "the lemma is proved in the block and is a hypothesis after" $ do
        proves "a = 0 |- a = 0 /\\ a = 0 by have H: (a = 0) { Id }; ConjR { exact H } { exact H }"
        proves "t = s |- plus s 0 = plus t 0 by have (s = t) { symmetry H1; Id }; cong H"
    , testCase "the hypothesis is H, or the next number when H is taken" $ do
        (goal, tac) <- parsed (parseGoal sc "a = 0 |- b = 0 by have (a = 0) { Id }; have (a = 0) { Id }; sorry")
        case prove goal tac of
          Right _ -> assertFailure "proved"
          Left err -> renderTacticError sig id err @?= "1:61: sorry: the proof stops here\n  H1 : a = 0\n  H : a = 0\n  H2 : a = 0\n  |- b = 0"
    , testCase "a name in use" $
        "a = 0 |- b = 0 by have H1: (a = 0) { Id }; sorry" `failsWith` \case
          NameInUse "H1" -> True
          _ -> False
    , testCase "blocks after have are for the goal it leaves" $
        proves "a = 0 |- a = 0 by have H: (a = 0) { Id } { exact H }"
    ]

equationTests :: TestTree
equationTests =
  testGroup
    "a lemma as an equation"
    [ testCase "cong finds the instance of a theorem where the sides differ" $ do
        lemmas <- zeroPlus
        provesWith lemmas "|- mult (plus 0 y) 2 = mult y 2 by cong zeroPlus"
        provesWith lemmas "|- S (plus 0 (S z)) = S (S z) by cong zeroPlus"
        provesWith lemmas "|- S y = S (plus 0 y) by cong zeroPlus"
        provesWith lemmas "a = 0 |- plus (plus 0 y) (plus 0 y) = plus y y by cong zeroPlus"
        provesWith lemmas "|- plus 0 y = plus 0 y by cong zeroPlus"
    , testCase "rewrite finds the instance of a theorem in the hypothesis" $ do
        lemmas <- zeroPlus
        provesWith lemmas "plus 0 z = 3 |- z = 3 by rewrite zeroPlus in H1; Id"
        provesWith lemmas "plus 0 z = 3 |- z = 3 by rewrite zeroPlus in H1 as H; exact H"
        provesWith lemmas "plus 0 z = 3 |- z = 3 by rewrite zeroPlus in H1 as H2; exact H2"
    , testCase "symmetry takes a closed equation" $ do
        lemmas <- twoTwo
        provesWith lemmas "|- 4 = plus 2 2 by symmetry twoTwo; Id"
    , testCase "a lemma which is not an equation, or whose instance is not determined" $ do
        conj <- Map.singleton "conj" <$> certified "|- 2 = 2 /\\ 3 = 3 by ConjR { refl } { refl }"
        failsWithIn conj "|- 2 = 2 by cong conj" \case
          LemmaNotEquation "conj" _ -> True
          _ -> False
        lemmas <- zeroPlus
        failsWithIn lemmas "|- plus 1 y = y by cong zeroPlus" \case
          NoCongruence _ [_] -> True
          _ -> False
        failsWithIn lemmas "|- 2 = 2 by symmetry zeroPlus; Id" \case
          Undetermined "zeroPlus" ["y"] -> True
          _ -> False
        zeroMult <- Map.singleton "zeroMult" <$> certified "|- 0 = mult 0 y by refl"
        failsWithIn zeroMult "0 = 5 |- 0 = 5 by rewrite zeroMult in H1; Id" \case
          Undetermined "zeroMult" ["y"] -> True
          _ -> False
        failsWithIn lemmas "3 = 3 |- 3 = 3 by rewrite zeroPlus in H1; Id" \case
          NothingToRewrite _ _ -> True
          _ -> False
    ]
  where
    zeroPlus = Map.singleton "zeroPlus" <$> certified "|- plus 0 y = y by refl"
    twoTwo = Map.singleton "twoTwo" <$> certified "|- plus 2 2 = 4 by refl"
