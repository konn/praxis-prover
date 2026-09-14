{-# LANGUAGE OverloadedStrings #-}

-- | The checker, end to end: what certifies, and what must not.
module Language.Praxis.Surface.CheckTest (checkTests) where

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Builder.Linear (runBuilder)
import Data.Text.IO qualified as TIO
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.CoreText (CT (..), Pred (..), membershipText, predicateOver, predicateParam)
import Language.Praxis.Surface.Elab (FunDef (..), Item (..), TheoremDef (..), elabModule)
import Language.Praxis.Surface.Engine (Goal (..), Hyp (..), Knowledge (..), Spec (..), equationCase, membershipProof, theoremStatement)
import Language.Praxis.Surface.Env (CtorInfo (..), Env, FunInfo (..), Global (..), constructorsNamed, resolve)
import Language.Praxis.Surface.Fixity (moduleFixities)
import Language.Praxis.Surface.Parser (parseModule)
import Language.Praxis.Surface.Prelude (Prelude, prelude)
import Language.Praxis.Surface.Syntax (Expr (..), Ref (..), RefKind (..), RelOp (..))
import Language.Praxis.Surface.Syntax.Raw (QName (..), Segment (..), Span (..), segmentText)
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
        mapM_ (\(n, l) -> assertBool ("an error for " <> n) (l `elem` lines')) [("superclass", 12 :: Int), ("second", 19), ("other", 25), ("generic", 28), ("ambiguous", 32), ("pair", 38), ("ambiguous function", 49)]
    , testCase "an application's type comes from the type expected and from its arguments, and an argument undetermined is checked again" $ do
        c <- checkFile "test/data/bidirectional.px"
        errors c @?= []
        checkedTheorems c @?= ["Bidirectional.unit-left", "Bidirectional.unit-right", "Bidirectional.empty-sum", "Bidirectional.put-off", "Bidirectional.length-nil", "Bidirectional.nil-left"]
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
        checkedTheorems c @?= ["Contexts.pair-sum", "Contexts.pair-mconcat", "Contexts.nested-sum", "Contexts.Pointed-Nat.plus-zero", "Contexts.Pointed-Option.plus-zero", "Contexts.Pointed-Pair.plus-zero", "Contexts.plus-zero-twice", "Contexts.twice-pair", "Contexts.twice-pair-generic"]
    , testCase "an instance proves every law of its class, and its proofs are checked" $ do
        c <- checkFile "test/data/laws-bad.px"
        checkedTheorems c @?= ["LawsBad.fine"]
        let lines' = [l | Report (Span (l, _) _) SevError _ <- checkedReports c]
        mapM_ (\(n, ls) -> assertBool ("an error for " <> n) (any (`elem` lines') ls)) [("the missing proof", [13 :: Int]), ("the wrong proof", [22 .. 25])]
    , testCase "a function's closure lemma gives the membership of its results, and a lemma applies at them" $ do
        c <- checkFile "test/data/closure.px"
        errors c @?= []
        checkedTheorems c @?= ["Closure.app-nil", "Closure.rev-app-nil", "Closure.cons-app-nil", "Closure.twice-rev"]
        -- A rule over the predicate of the type parameter of its list.
        mapM_ (\f -> assertBool ("the closure of " <> f) (any (("rule u_Closure_s" <> T.pack f <> "_s_x23_closed ") `T.isPrefixOf`) (checkedCore c))) ["app", "rev"]
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
    , testCase "a data type in the GADT style: a function omits a constructor impossible at its indices, and what it says of indices certifies" $ do
        c <- checkFile "test/data/gadt.px"
        errors c @?= []
        mapM_ (\n -> assertBool ("certified: " <> T.unpack n) (n `elem` checkedTheorems c)) ["Gadt.tail.#index", "Gadt.tail-two.#index", "Gadt.zero-of.#index"]
        -- Theorems over its values: the index a bare value, a case its indices exclude, an appeal needing an index;
        -- and over a data type whose head has implicit parameters, its indices lists.
        mapM_ (\n -> assertBool ("certified: " <> T.unpack n) (n `elem` checkedTheorems c)) ["Gadt.length-index", "Gadt.head-tail", "Gadt.head-tail-two", "Gadt.same-eq"]
        -- The membership of its results, under the indices of its argument: a rule over its type parameter's predicate.
        mapM_ (\f -> assertBool ("the closure of " <> T.unpack f) (any (("rule u_Gadt_s" <> f <> "_s_x23_closed ") `T.isPrefixOf`) (checkedCore c))) ["tail", "tail_dtwo", "head", "first"]
    , testCase "an index which cannot be, a clause missing or never matching, and a kind which disagrees, are refused" $ do
        c <- checkFile "test/data/gadt-bad.px"
        let lines' = [l | Report (Span (l, _) _) SevError _ <- checkedReports c]
        mapM_
          (\(n, ls) -> assertBool ("an error for " <> n) (any (`elem` lines') ls))
          [("impossible", [13, 14]), ("tail-zero", [17, 18]), ("nil-any", [21, 22]), ("head-any", [25, 26]), ("never", [29, 30, 31]), ("Box", [34, 35, 36]), ("Expr", [39, 40]), ("bad-type", [43, 44]), ("length-any", [55, 56]), ("Lost", [59, 60]), ("bad-kind", [63, 64])]
        assertBool "fine is certified" ("GadtBad.fine.#index" `elem` checkedTheorems c)
        assertBool "nothing refused is certified" (not (any (`elem` checkedTheorems c) ["GadtBad.impossible.#index", "GadtBad.tail-zero.#index", "GadtBad.nil-any.#index", "GadtBad.length-any"]))
    , testCase "theorems over Nat, by its induction: clauses on 0 and S n, the tactic, a comparison by unfolding, and a value not named" $ do
        c <- checkFile "test/data/nat.px"
        errors c @?= []
        mapM_ (\n -> assertBool ("certified: " <> T.unpack n) (n `elem` checkedTheorems c)) ["NatTheorems.zero-add", "NatTheorems.zero-add-by", "NatTheorems.zero-lt-succ", "NatTheorems.zero-lt-succ-by-cases", "NatTheorems.plt-zero"]
    , testCase "a clause on a numeral other than 0, and a proposition where a type is expected, are refused" $ do
        c <- checkFile "test/data/nat-bad.px"
        let lines' = [l | Report (Span (l, _) _) SevError _ <- checkedReports c]
        mapM_ (\(n, ls) -> assertBool ("an error for " <> n) (any (`elem` lines') ls)) [("one-lt", [4, 5, 6]), ("prop-arg", [9, 10])]
    , testCase "a function's specifications are proved by the skeleton of its lemmas, each case by the specification's prover" $ do
        p <- either assertFailure pure prelude
        src <- TIO.readFile "test/data/specs.px"
        let c = checkSourceWith specs p "test/data/specs.px" src
            messages = [m | Report _ SevError m <- checkedReports c]
        checkedTheorems c @?= ["Specs.copy.#spec", "Specs.app.#spec"]
        assertBool "the false specification is refused, and nothing else" (length messages == 1 && any ("Specs.copy.#wrong" `T.isInfixOf`) messages)
    , testCase "a membership predicate of one parameter is variadic: at a closure capturing a variable, the type's lemmas and a function's closure lemma apply" $ do
        p <- either assertFailure pure prelude
        src <- TIO.readFile "test/data/specs.px"
        (k, core) <- maybe (assertFailure "the module did not elaborate") pure (checkedFinal (checkSource p "test/data/specs.px" src))
        let env = knowEnv k
        (listIs, _) <- maybe (assertFailure "no membership predicate for List") pure (Map.lookup "Specs.List" (knowMembership k))
        assertBool "List's predicate is variadic" (listIs `Set.member` knowVariadic k)
        cons <- case constructorsNamed env (Op ":") of
          c : _ -> pure (ctorCore c)
          [] -> assertFailure "no constructor (:)"
        copy <- case [f | GFun f <- resolve env (QName [] (Ident "copy"))] of
          f : _ -> pure (funCore f)
          [] -> assertFailure "no function copy"
        -- The elements below b, a closure capturing b; and the lists of them.
        let below = predicateOver "x" (CSym "lt" [CVar "x", CVar "b"])
            lists = Pred listIs [predicateParam below]
            g = Goal [("H1", HMember below "a"), ("H2", HMember lists "xs")] Top [] [] [] [] []
            hyps = membershipText below (CVar "a") <> ", " <> membershipText lists (CVar "xs")
            prove name t = do
              tactic <- either assertFailure pure (membershipProof k g lists t)
              either assertFailure pure (certifyDecl (runBuilder ("theorem " <> name <> " : " <> hyps <> " |- " <> membershipText lists t <> "\nby " <> tactic)) core)
        -- Through the introduction of (:), and through the closure lemma of copy.
        mapM_ (uncurry prove) [("consBelow", CSym cons [CVar "a", CVar "xs"]), ("copyBelow", CSym copy [CVar "xs"])]
    ]

{- |
Of @copy@, that it is the identity, and, falsely, that it is @Nil@; of
@app@, that it is the identity where its second argument is @Nil@, a
precondition.
-}
specs :: Env -> FunDef -> [Spec]
specs env fd = case map segmentText (funQual (fdInfo fd)) of
  [_, "copy"] ->
    [ equational "#spec" (const []) (\xs applied -> Rel RelEq applied (Var (xs !! 0)))
    , equational "#wrong" (const []) (\_ applied -> Rel RelEq applied nil)
    ]
  [_, "app"] -> [equational "#spec" (\xs -> [Rel RelEq (Var (xs !! 1)) nil]) (\xs applied -> Rel RelEq applied (Var (xs !! 0)))]
  _ -> []
  where
    equational name pre post = Spec name pre post (\_ _ -> []) equationCase
    nil = case constructorsNamed env (Ident "Nil") of
      c : _ -> Global (Ref RefConstructor (ctorCore c))
      [] -> error "no constructor Nil"

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
