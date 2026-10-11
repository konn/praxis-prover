{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.LogicalPreconditionTest (logicalPreconditionTests) where

import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.FiniteFixtures
import Language.Praxis.Surface.Prelude (prelude)
import Test.Tasty
import Test.Tasty.HUnit

logicalPreconditionTests :: TestTree
logicalPreconditionTests =
  testGroup
    "logical finite preconditions"
    [ testCase "generic result closure retains and discharges quantified preconditions" $ do
        library <- either assertFailure pure prelude
        let source =
              "module Logical where\n"
                <> finitePrelude
                <> T.unlines
                  [ "keep : Finite a => a -> (∀ (y : a), y = y) -> a"
                  , "keep x h = x"
                  , "forward : Finite a => a -> (∀ (y : a), y = y) -> a"
                  , "forward x h = keep x h"
                  , "test : (x : Bool) -> ∃ (y : Bool), y = x"
                  , "test x = by exists (forward x (by intro y; rfl)); rfl"
                  ]
            checked = checkSource library "logical.px" source
        [message | Report _ SevError message <- checkedReports checked] @?= []
        assertBool "result closure absent" (any ("u_Logical_sforward_s_x23_closed" `T.isInfixOf`) (checkedCore checked))
    , testCase "a quantified bound variable cannot escape into a free argument" $ do
        library <- either assertFailure pure prelude
        let prefix =
              "module Escape where\n"
                <> T.unlines
                  [ "need : {x : Nat} -> (∀ (i : Nat) < 2, x = i) -> Nat"
                  , "need {x} h = 0"
                  ]
            source =
              prefix
                <> T.unlines
                  [ "bad : {x : Nat} -> (∀ (i : Nat) < 2, i = i) -> Nat"
                  , "bad {x} h = need {x} h"
                  ]
            valid = checkSource library "escape-prefix.px" prefix
            checked = checkSource library "escape.px" source
        [message | Report _ SevError message <- checkedReports valid] @?= []
        assertBool "an invalid quantified precondition was accepted" (any isError (checkedReports checked))
    ]
  where
    isError (Report _ SevError _) = True
    isError _ = False
