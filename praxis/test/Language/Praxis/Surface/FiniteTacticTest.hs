{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.FiniteTacticTest (finiteTacticTests) where

import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.FiniteQuantifierTest (finitePrelude)
import Language.Praxis.Surface.Prelude (prelude)
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
    ]
  where
    succeeds label declarations = testCase label $ do
      library <- either assertFailure pure prelude
      let checked = checkSource library "finite-tactics.px" ("module FiniteQ where\n" <> finitePrelude <> T.unlines declarations)
      [message | Report _ SevError message <- checkedReports checked] @?= ([] :: [Text])
