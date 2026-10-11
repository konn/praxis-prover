{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.FiniteTacticTest (finiteTacticTests) where

import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.FiniteQuantifierTest (finitePrelude)
import Language.Praxis.Surface.Prelude (prelude)
import Language.Praxis.Surface.Syntax.Raw (Segment (..))
import Test.Tasty
import Test.Tasty.HUnit

finiteTacticTests :: TestTree
finiteTacticTests =
  testGroup
    "source finite quantifier tactics"
    [ succeeds
        "intro exposes a data value usable by induction"
        [ "all : ∀ (x : Bool), x = x"
        , "all = by"
        , "  intro value"
        , "  induction value"
        , "  · rfl"
        , "  · rfl"
        ]
    , succeeds
        "exists accepts an element rather than its enumeration index"
        [ "some : ∃ (x : Bool), x = True"
        , "some = by exists True; rfl"
        ]
    , succeeds
        "universal elimination transports through coverage"
        [ "use : (∀ (x : Bool), x = x) -> True = True"
        , "use h = by exact h True"
        ]
    , succeeds
        "obtain exposes the element and its source proposition"
        [ "use : (∃ (x : Bool), x = True) -> ∃ (y : Bool), y = True"
        , "use h = by"
        , "  obtain ⟨element, fact⟩ := h"
        , "  exists element"
        , "  exact fact"
        ]
    , succeeds
        "nested finite domains retain renamed numeric binders"
        [ "nested : ∀ (n : Nat) < 3, ∀ (i : Fin n), i = i"
        , "nested = by intro bound; intro element; rfl"
        ]
    , succeeds
        "grouped domain annotations precede all names in their group"
        [ "grouped : (n : Nat) -> ∀ (n m : Fin n), m = m"
        , "grouped n = by intro first; intro second; rfl"
        ]
    , succeeds
        "finite quantifiers under conjunctions keep separate origins"
        [ "nested : (∀ (x : Bool), x = x) ∧ (∃ (y : Bool), y = True)"
        , "nested = by"
        , "  constructor"
        , "  · intro value; rfl"
        , "  · exists True; rfl"
        ]
    , succeeds
        "have preserves nested source bindings after an application"
        [ "use : (∀ (n : Nat) < 3, ∀ (i : Fin n), i = i) -> ∀ (j : Fin 1), j = j"
        , "use h = by"
        , "  have bound : 1 < 3 := by rfl"
        , "  have specialized := h 1"
        , "  intro element"
        , "  exact specialized element"
        ]
    , succeeds
        "nested source values follow data induction substitutions"
        [ "nested : ∀ (x : Bool), ∀ (y : Bool), x = x"
        , "nested = by"
        , "  intro value"
        , "  induction value"
        , "  · intro other; rfl"
        , "  · intro other; rfl"
        ]
    , succeeds
        "numeric exists keeps its bound in the body proof context"
        [ "numeric : (m n : Nat) -> m < n -> ∃ (i : Nat) < n, i < n"
        , "numeric m n h = by exists m; assumption; assumption"
        ]
    , succeeds
        "reused theorem domains use the original explicit binder"
        [ "all : (n : Nat) -> ∀ (i : Fin n), i = i"
        , "all n = by intro element; rfl"
        , "use : ∀ (m : Nat) < 3, ∀ (i : Fin m), i = i"
        , "use = by intro bound; intro value; exact all bound value"
        ]
    , succeeds
        "two applications of one source theorem keep independent domains"
        [ "all : (n : Nat) -> ∀ (i : Fin n), i = i"
        , "all n = by intro element; rfl"
        , "use : (∀ (i : Fin 1), i = i) ∧ (∀ (i : Fin 2), i = i)"
        , "use = by"
        , "  have first := all 1"
        , "  have second := all 2"
        , "  constructor"
        , "  · intro value; exact first value"
        , "  · intro value; exact second value"
        ]
    , succeeds
        "a generic quantified theorem specializes its source type and dictionary"
        [ "all : Finite a => (x : a) -> ∀ (y : a), y = y"
        , "all x = by intro value; rfl"
        , "use : (x : Bool) -> x = x"
        , "use x = by exact all x x"
        ]
    , succeeds
        "identical applications at one source span retain equivalent views"
        [ "all : (n : Nat) -> ∀ (i : Fin n), i = i"
        , "all n = by intro element; rfl"
        , "use : ∀ (i : Fin 1), i = i"
        , "use = by"
        , "  have first := all 1"
        , "  have second := all 1"
        , "  intro value"
        , "  exact first value"
        ]
    , succeeds
        "finite quantifiers remain usable below implication and negation"
        [ "identity-negation : (¬ (∀ (x : Bool), x = x)) -> ¬ (∀ (x : Bool), x = x)"
        , "identity-negation h = by exact h"
        , "implication : (∀ (x : Bool), x = x) -> ∃ (y : Bool), y = True"
        , "implication h = by exists True; exact h True"
        ]
    , succeeds
        "explicit proof antecedents precede quantified element arguments"
        [ "all : 0 = 0 -> ∀ (x : Bool), x = x"
        , "all h = by intro value; rfl"
        , "use : 0 = 0 -> True = True"
        , "use h = by exact all h True"
        ]
    , succeeds
        "a finite universal argument determines an implicit ordinal bound"
        [ "all : ∀ (i : Fin n), i = i"
        , "all = by intro i; rfl"
        , "use : (i : Fin n) -> i = i"
        , "use i = all i"
        ]
    , succeeds
        "a finite universal argument determines its generic dictionary"
        [ "all : Finite a => ∀ (x : a), x = x"
        , "all = by intro x; rfl"
        , "use : (b : Bool) -> b = b"
        , "use b = all b"
        ]
    , succeeds
        "two finite arguments consistently specialize one generic domain"
        [ "all : Finite a => ∀ (x y : a), x = x ∧ y = y"
        , "all = by intro x y; constructor; rfl; rfl"
        , "use : (b c : Bool) -> b = b ∧ c = c"
        , "use b c = all b c"
        ]
    , succeeds
        "finite inference preserves explicit proof antecedent routing"
        [ "all : Finite a => 0 = 0 -> ∀ (x : a), x = x"
        , "all h = by intro x; rfl"
        , "use : (b : Bool) -> 0 = 0 -> b = b"
        , "use b h = all h b"
        ]
    , succeeds
        "grouped finite inference freezes the shared annotation before shadowing"
        [ "all : ∀ (n i : Fin n), n = n ∧ i = i"
        , "all = by intro x y; constructor; rfl; rfl"
        , "use : (x y : Fin n) -> x = x ∧ y = y"
        , "use x y = all x y"
        ]
    , succeeds
        "later finite arguments infer independent index parameters"
        [ "all : ∀ (b : Bool) (i : Fin n) (j : Fin m), j = j"
        , "all = by intro b i j; rfl"
        , "use : (b : Bool) -> (i : Fin n) -> (j : Fin m) -> j = j"
        , "use b i j = all b i j"
        ]
    , succeeds
        "a later finite domain can depend on an earlier element"
        [ "all : ∀ (i : Fin n) (j : Fin (rank i)), j = j"
        , "all = by intro i j; rfl"
        , "use : ∀ (i : Fin n) (j : Fin (rank i)), j = j"
        , "use = by intro i j; exact all i j"
        ]
    , succeeds
        "finite inference distinguishes callee and caller type parameters"
        [ "all : Finite a => ∀ (x : a), x = x"
        , "all = by intro x; rfl"
        , "use : (Finite a, Finite b) => (seed : a) -> (value : b) -> value = value"
        , "use seed value = all value"
        ]
    , succeeds
        "finite inference distinguishes callee and caller index parameters"
        [ "all : ∀ (i : Fin n), i = i"
        , "all = by intro i; rfl"
        , "use : (seed : Fin n) -> (value : Fin m) -> value = value"
        , "use seed value = all value"
        ]
    , succeeds
        "finite inference preserves explicit transport to a fixed domain"
        [ "all : ∀ (i : Fin 1), i = i"
        , "all = by intro i; rfl"
        , "use : (i : Fin n) -> n = 1 -> i = i"
        , "use i h = all i"
        ]
    , succeeds
        "finite inference retains expected types for constructor arguments"
        [ "all : ∀ (i : Fin 2), i = i"
        , "all = by intro i; rfl"
        , "use : FZero {1} = FZero {1}"
        , "use = all FZero"
        ]
    , rejects
        "an unresolved finite argument cannot be silently discarded"
        [ "all : ∀ (i : Fin n), i = i"
        , "all = by intro i; rfl"
        , "bad : ∀ (i : Fin 1), i = i"
        , "bad = all True"
        ]
    , rejects
        "finite arguments cannot infer inconsistent ordinal bounds"
        [ "all : ∀ (i j : Fin n), i = i ∧ j = j"
        , "all = by intro i j; constructor; rfl; rfl"
        , "bad : (i : Fin 1) -> (j : Fin 2) -> i = i ∧ j = j"
        , "bad i j = all i j"
        ]
    , rejects
        "finite inference does not accept an unrelated explicit antecedent"
        [ "all : Finite a => 0 = 0 -> ∀ (x : a), x = x"
        , "all h = by intro x; rfl"
        , "bad : (b : Bool) -> 1 = 1 -> b = b"
        , "bad b h = all h b"
        ]
    , rejects
        "finite inference leaves numeric universal bound checking intact"
        [ "all : ∀ (i : Nat) < 2, i = i"
        , "all = by intro i; rfl"
        , "bad : 3 = 3"
        , "bad = all 3"
        ]
    , testCase "identical spans in imported theorems keep their source scopes" $ do
        library <- either assertFailure pure prelude
        let check build imports file source = checkModule (\_ _ -> []) build imports Nothing file source
            errors checked = [message | Report _ SevError message <- checkedReports checked]
            (domain, firstBuild) = check (initialBuild library) Map.empty "Domain.px" ("module Domain where\n" <> finitePrelude)
        errors domain @?= []
        domainExports <- maybe (assertFailure "missing Domain exports") pure (Map.lookup [Ident "Domain"] (buildExports firstBuild))
        let imports = Map.singleton (Nothing, [Ident "Domain"]) (Right domainExports)
            declaration name = "module " <> name <> " where\nimport Domain\nall : (n : Nat) -> ∀ (i : Domain.Fin n), i = i\nall n = by intro element; rfl\n"
            (first, secondBuild) = check firstBuild imports "A.px" (declaration "A")
            (second, thirdBuild) = check secondBuild imports "B.px" (declaration "B")
        errors first @?= []
        errors second @?= []
        aExports <- maybe (assertFailure "missing A exports") pure (Map.lookup [Ident "A"] (buildExports thirdBuild))
        bExports <- maybe (assertFailure "missing B exports") pure (Map.lookup [Ident "B"] (buildExports thirdBuild))
        let clientImports = imports <> Map.fromList [((Nothing, [Ident "A"]), Right aExports), ((Nothing, [Ident "B"]), Right bExports)]
            (client, _) =
              check
                thirdBuild
                clientImports
                "Client.px"
                ( T.unlines
                    [ "module Client where"
                    , "import Domain"
                    , "import A"
                    , "import B"
                    , "use : (∀ (i : Domain.Fin 1), i = i) ∧ (∀ (i : Domain.Fin 2), i = i)"
                    , "use = by"
                    , "  have first := A.all 1"
                    , "  have second := B.all 2"
                    , "  constructor"
                    , "  · intro value; exact first value"
                    , "  · intro value; exact second value"
                    ]
                )
        errors client @?= []
    ]
  where
    succeeds label declarations = testCase label $ do
      library <- either assertFailure pure prelude
      let checked = checkSource library "finite-tactics.px" ("module FiniteQ where\n" <> finitePrelude <> T.unlines declarations)
      [message | Report _ SevError message <- checkedReports checked] @?= ([] :: [Text])

    rejects label declarations = testCase label $ do
      library <- either assertFailure pure prelude
      let checked = checkSource library "finite-tactics.px" ("module FiniteQ where\n" <> finitePrelude <> T.unlines declarations)
      assertBool "the source theorem failed" ("FiniteQ.all" `elem` checkedTheorems checked)
      assertBool "the invalid application was certified" ("FiniteQ.bad" `notElem` checkedTheorems checked)
      assertBool "the invalid application had no diagnostic" (any ((== SevError) . reportSeverity) (checkedReports checked))
