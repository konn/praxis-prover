{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.IndexedInstanceTest (indexedInstanceTests) where

import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Prelude (prelude)
import Language.Praxis.Surface.Syntax.Raw (Span (..))
import Test.Tasty
import Test.Tasty.HUnit

indexedInstanceTests :: TestTree
indexedInstanceTests =
  testGroup
    "indexed instances"
    [ testCase "an indexed instance captures its head value in dependent methods" $ do
        checked <- check (source <> "witness-for : {n : Nat} -> Cell n -> Cell n\nwitness-for {n} x = witness {Cell n}\n")
        errors checked @?= []
    , testCase "computed runtime indices retain their checked subexpressions" $ do
        checked <- check (source <> "witness-next : {n : Nat} -> Cell n -> Cell (S (S n))\nwitness-next {n} x = witness {Cell (S (S n))}\nnext : Nat -> Nat\nnext n = S n\nwitness-function : {n : Nat} -> Cell n -> Cell (next (next n))\nwitness-function {n} x = witness {Cell (next (next n))}\n")
        errors checked @?= []
    , testCase "an indexed method remains fixed when passed as a dictionary" $ do
        checked <- check (source <> "twice : Indexed a => a -> a\ntwice x = identity (identity x)\nuse-twice : {n : Nat} -> Cell n -> Cell n\nuse-twice {n} x = twice x\n")
        errors checked @?= []
    , testCase "proof-only runtime indices are recovered from method arguments" $ do
        checked <- check (source <> "index : Cell n -> Nat\nindex (Mk n) = n\nuse : Indexed a => a -> Nat\nuse x = index (witness-of x)\nprobe : {n : Nat} -> Cell n -> Nat\nprobe {n} x = use x\n")
        errors checked @?= []
    , testCase "explicit class types select one of two available dictionaries" $ do
        checked <- check (source <> "choose : Indexed a => Indexed b => a -> b -> Nat\nchoose x y = amount {a}\n")
        errors checked @?= []
    , testCase "an explicit class type cannot contradict a method argument" $ do
        checked <- check (source <> "wrong : Cell 0 -> Cell 0\nwrong x = identity {Cell 1} x\n")
        assertBool "an incompatible class type was accepted" (not (null (errors checked)))
    , testCase "a static dictionary with a required open runtime capture is rejected" $ do
        checked <- check "module Indexed where\ndata Cell (n : Nat) where\n  Mk : (n : Nat) -> Cell n\nclass Make a where\n  make : Nat -> a\ninstance Make (Cell n) where\n  make x = Mk n\nuse : Make a => Nat -> a\nuse x = make x\nwrong : {n : Nat} -> Nat -> Cell n\nwrong {n} x = use x\n"
        assertBool "an open static capture was accepted" (any ("scoped runtime values" `T.isInfixOf`) [message | Report _ SevError message <- checkedReports checked])
    , testCase "an indexed instance head must cover every index uniformly" $ do
        checked <- check "module Indexed where\ndata Cell (n : Nat) where\n  Mk : (n : Nat) -> Cell n\nclass Identity a where\n  identity : a -> a\ninstance Identity (Cell 0) where\n  identity x = x\n"
        assertBool "a constant-index head silently became universal" (not (null (errors checked)))
    ]
  where
    source =
      T.unlines
        [ "module Indexed where"
        , "data Cell (n : Nat) where"
        , "  Mk : (n : Nat) -> Cell n"
        , "class Indexed a where"
        , "  amount : Nat"
        , "  witness : Cell amount"
        , "  identity : a -> a"
        , "  witness-of : a -> Cell amount"
        , "  identity-law : (x : a) -> identity x = x"
        , "instance Indexed (Cell n) where"
        , "  amount = n"
        , "  witness = Mk n"
        , "  identity x = x"
        , "  witness-of x = x"
        , "  identity-law x = rfl"
        ]
    check input = do
      p <- either assertFailure pure prelude
      pure (checkSource p "indexed.px" input)

errors :: Checked -> [String]
errors checked = [show line <> ": " <> T.unpack message | Report (Span (line, _) _) SevError message <- checkedReports checked]
