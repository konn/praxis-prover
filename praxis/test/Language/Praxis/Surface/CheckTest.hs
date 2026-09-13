{-# LANGUAGE OverloadedStrings #-}

-- | The checker, end to end: what certifies, and what must not.
module Language.Praxis.Surface.CheckTest (checkTests) where

import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Elab (Item (..), TheoremDef (..), elabModule)
import Language.Praxis.Surface.Engine (theoremStatement)
import Language.Praxis.Surface.Fixity (moduleFixities)
import Language.Praxis.Surface.Parser (parseModule)
import Language.Praxis.Surface.Prelude (Prelude, prelude)
import Language.Praxis.Surface.Syntax.Raw (Span (..))
import Test.Tasty
import Test.Tasty.HUnit

checkTests :: TestTree
checkTests =
  testGroup
    "checker"
    [ testCase "the List example certifies, in the functional and the tactic style" $ do
        c <- checkFile "test/data/list.px"
        errors c @?= []
        checkedTheorems c @?= ["Data.List.append-nil", "Data.List.append-nil-tactically"]
    , testCase "the FOL example's data types are encoded, and their lemmas certify" $ do
        c <- checkFile "test/data/fol.px"
        errors c @?= []
    , testCase "a method is the function of the instance of its class for the type it is used at" $ do
        c <- checkFile "test/data/classes.px"
        errors c @?= []
        checkedTheorems c @?= ["Classes.nat-unit", "Classes.list-unit", "Classes.list-cons", "Classes.both"]
    , testCase "an instance follows its superclasses', is its type's only one, defines methods only; a method is at a known type, no variable" $ do
        c <- checkFile "test/data/classes-bad.px"
        checkedTheorems c @?= ["ClassesBad.fine"]
        let lines' = [l | Report (Span (l, _) _) SevError _ <- checkedReports c]
        mapM_ (\(n, l) -> assertBool ("an error for " <> n) (l `elem` lines')) [("superclass", 12 :: Int), ("second", 19), ("other", 25), ("generic", 28), ("ambiguous", 32), ("pair", 38)]
    , testCase "a function under a constraint is a schema over the methods it uses, at the instances of known types" $ do
        c <- checkFile "test/data/constrained.px"
        errors c @?= []
        checkedTheorems c @?= ["Constrained.sum-three", "Constrained.flatten", "Constrained.triple-two", "Constrained.twice-sum"]
    , testCase "a theorem under a constraint is a rule over the methods its statement uses, proved once, and appealed to at an instance" $ do
        c <- checkFile "test/data/generic.px"
        errors c @?= []
        checkedTheorems c @?= ["Generic.mconcat-single", "Generic.mconcat-copy", "Generic.single-five"]
    , testCase "a class's laws are proved by each instance, and are premises of a theorem under the class, discharged where it is appealed to" $ do
        c <- checkFile "test/data/laws.px"
        errors c @?= []
        checkedTheorems c @?= ["Laws.Pointed-Nat.plus-zero", "Laws.Pointed-List.plus-zero", "Laws.plus-zero-twice", "Laws.plus-zero-thrice", "Laws.twice-nat", "Laws.twice-list", "Laws.list-law"]
    , testCase "an instance under a context takes the context's dictionary, passed at the instances of known types" $ do
        c <- checkFile "test/data/contexts.px"
        errors c @?= []
        checkedTheorems c @?= ["Contexts.pair-sum", "Contexts.pair-mconcat", "Contexts.nested-sum", "Contexts.Pointed-Nat.plus-zero", "Contexts.Pointed-Option.plus-zero"]
    , testCase "an instance proves every law of its class, and its proofs are checked" $ do
        c <- checkFile "test/data/laws-bad.px"
        checkedTheorems c @?= ["LawsBad.fine"]
        let lines' = [l | Report (Span (l, _) _) SevError _ <- checkedReports c]
        mapM_ (\(n, ls) -> assertBool ("an error for " <> n) (any (`elem` lines') ls)) [("the missing proof", [13 :: Int]), ("the wrong proof", [22 .. 25])]
    , testCase "a function's closure lemma gives the membership of its results, and a lemma applies at them" $ do
        c <- checkFile "test/data/closure.px"
        errors c @?= []
        checkedTheorems c @?= ["Closure.app-nil", "Closure.rev-app-nil", "Closure.cons-app-nil", "Closure.twice-rev"]
        mapM_ (\f -> assertBool ("the closure of " <> f) (any (("theorem u_Closure_s" <> T.pack f <> "_s_x23_closed :") `T.isPrefixOf`) (checkedCore c))) ["app", "rev"]
    , testCase "a false theorem, a non-structural recursion, a sorry and an appeal to a failed theorem are refused" $ do
        c <- checkFile "test/data/bad.px"
        checkedTheorems c @?= []
        let lines' = [l | Report (Span (l, _) _) SevError _ <- checkedReports c]
        mapM_ (\(n, ls) -> assertBool ("an error for " <> n) (any (`elem` lines') ls)) [("wrong", [13 .. 19]), ("loop", [22 .. 24]), ("unfinished", [27, 28]), ("uses", [31, 32])]
        assertBool "the non-structural call is named" (any ("recursive call" `T.isInfixOf`) (map reportMessage (checkedReports c)))
        assertBool "sorry shows its goal" (any ("sorry" `T.isInfixOf`) (map reportMessage (checkedReports c)))
    , testCase "values are first-order: a field, an argument or a variable of function type, and a partial application, are refused" $ do
        c <- checkFile "test/data/higher-order.px"
        checkedTheorems c @?= ["HigherOrder.fine"]
        let errs = [(l, m) | Report (Span (l, _) _) SevError m <- checkedReports c]
        mapM_ (\(n, l) -> assertBool ("an error for " <> n) (any ((== l) . fst) errs)) [("Box", 9 :: Int), ("apply", 12), ("fun-refl", 16), ("partly", 20)]
        assertBool "the partial application is named" (any (("applied to 1 of its 2 arguments" `T.isInfixOf`) . snd) errs)
    , testCase "duplicate theorem binders cannot merge independent membership hypotheses" $ do
        c <- checkFile "test/data/duplicate-binders.px"
        checkedTheorems c @?= ["DuplicateBinders.only-a", "DuplicateBinders.only-b", "DuplicateBinders.fine"]
        let messages = [m | Report _ SevError m <- checkedReports c]
        length messages @?= 3
        assertBool "the duplicate binder is diagnosed" (any ("the variable x is bound twice" `T.isInfixOf`) messages)
        assertBool "distinct binders do not prove the false equation" (any ("DuplicateBinders.distinct" `T.isInfixOf`) messages)
        assertBool "a rejected theorem is unavailable" (any ("not a hypothesis or a lemma: bad" `T.isInfixOf`) messages)
    , testCase "grouped and forall theorem binders must also be distinct" $ do
        p <- either assertFailure pure prelude
        mapM_
          ( \signature -> do
              let src = T.unlines ["module Duplicate where", signature, "bad a b = by rfl"]
                  c = checkSource p "duplicate.px" src
              checkedTheorems c @?= []
              assertBool "the duplicate value binder is diagnosed" (any ("the variable x is bound twice" `T.isInfixOf`) (map reportMessage (checkedReports c)))
          )
          [ "bad : (x x : Nat) -> x ≡ x"
          , "bad : (x : Nat) -> ∀ (x : Nat), x ≡ x"
          ]
    , testCase "statement translation refuses colliding binders even in an already elaborated declaration" $ do
        src <- TIO.readFile "test/data/duplicate-binders.px"
        m <- either (assertFailure . show) pure (parseModule "duplicate-binders.px" src)
        fx <- either (assertFailure . show) pure (moduleFixities m)
        let (_, items) = elabModule fx m
        case reverse [td | ITheorem td <- items] of
          td : _ -> do
            let colliding = td {tdBinders = [("x", ty) | (_, ty) <- tdBinders td]}
            theoremStatement Map.empty colliding @?= Left "a theorem's value binders must have distinct names"
          [] -> assertFailure "expected the ordinary theorem at the end of the fixture"
    , testCase "induction eigenvariables stay apart from surface binders" $ do
        c <- checkFile "test/data/induction-names.px"
        errors c @?= []
        checkedTheorems c @?= ["InductionNames.only", "InductionNames.other", "InductionNames.nested"]
    ]

checkFile :: FilePath -> IO Checked
checkFile path = do
  p <- either assertFailure pure prelude
  src <- TIO.readFile path
  pure (check p path src)
  where
    check :: Prelude -> FilePath -> Text -> Checked
    check = checkSource

-- | The errors, rendered with their lines, for a readable failure.
errors :: Checked -> [String]
errors c = [show l <> ": " <> T.unpack m | Report (Span (l, _) _) SevError m <- checkedReports c]
