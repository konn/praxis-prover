{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.FiniteQuantifierTest (
  finiteQuantifierTests,
  finitePrelude,
  finiteOrdinals,
  finiteProtocol,
  boolInstance,
) where

import Bound (fromScope)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Engine (Knowledge (..))
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.FiniteFixtures
import Language.Praxis.Surface.Prelude (prelude)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw (Segment (..))
import Test.Tasty
import Test.Tasty.HUnit

finiteQuantifierTests :: TestTree
finiteQuantifierTests =
  testGroup
    "finite quantifier lowering"
    [ testCase "Fin quantification needs no Finite class" $ do
        checked <- check (finiteOrdinals <> "all : ∀ (i : Fin n), i = i\nall = by intro i; rfl\n")
        errors checked @?= []
        assertCertified "all" checked
    , testCase "empty finite domains have the correct universal and existential behavior" $ do
        valid <- check (finiteOrdinals <> "empty : ∀ (i : Fin 0), ⊥\nempty = by\n  intro i\n  induction i\n  · contradiction\n  · contradiction\n")
        errors valid @?= []
        invalid <- check (finiteOrdinals <> "inhabited : ∃ (i : Fin 0), i = i\ninhabited = rfl\n")
        assertRejected invalid
    , testCase "an empty retraction has no decoded inhabitants" $ do
        let source = finiteOrdinals <> finiteProtocol <> emptyInstance
        valid <- check (source <> "empty-all : ∀ (x : Empty), ⊥\nempty-all = by intro x; induction x\n")
        errors valid @?= []
        assertCertified "empty-all" valid
        invalid <- check (source <> "empty-some : ∃ (x : Empty), x = x\nempty-some = rfl\n")
        assertRejected invalid
        assertBool "the empty retraction acquired an inhabitant" ("FiniteQ.empty-some" `notElem` checkedTheorems invalid)
    , testCase "finite quantifiers nest under propositional connectives" $ do
        checked <- check (finitePrelude <> "nested : (∀ (x : Bool), x = x) -> ∀ (y : Bool), y = y\nnested h = by intro y; rfl\n")
        errors checked @?= []
        (_, info) <- theorem "nested" checked
        let statements = catMaybes [thmStatement info, thmProp info]
        assertBool "the theorem lost its statement" (not (null statements))
        assertBool "surface finite syntax reached Praxis Core" (all (numericOnly . fromScope) statements)
    , testCase "generic finite evidence survives a tautological statement" $ do
        checked <- check (finitePrelude <> "generic : Finite a => ∀ (x : a), x = x\ngeneric = by intro x; rfl\n")
        errors checked @?= []
        (_, info) <- theorem "generic" checked
        assertBool "coverage was pruned" (any isCoverage (thmPremises info))
        assertBool "code was pruned" (any ((== [Ident "FiniteQ", Ident "Finite", Ident "code"]) . slotMethod) (thmSlots info))
    , testCase "a finite retraction permits unused ordinal representations" $ do
        checked <-
          check
            ( finiteOrdinals
                <> finiteProtocol
                <> boolRetractionWithSpareOrdinal
                <> T.unlines
                  [ "spare-decodes : bool-from-nat 2 = bool-from-nat 1"
                  , "spare-decodes = rfl"
                  , "all-bools : ∀ (b : Bool), b = b"
                  , "all-bools = by intro b; rfl"
                  , "some-bool : ∃ (b : Bool), b = True"
                  , "some-bool = by exists True; rfl"
                  ]
            )
        errors checked @?= []
        mapM_ (`assertCertified` checked) ["spare-decodes", "all-bools", "some-bool"]
    , testCase "a numerically bounded binder cannot silently discard its type" $ do
        checked <- check (finitePrelude <> "bad : ∀ (b : Bool) < 2, b = b\nbad = rfl\n")
        assertRejected checked
    , testCase "an unregistered numeric bridge cannot desugar even a tautology" $ do
        checked <- check (T.replace "{-# BUILTIN FIN_FROM_TO_NAT from-to #-}" "" finiteOrdinals <> "bad : ∀ (i : Fin 1), i = i\nbad = rfl\n")
        assertRejected checked
        assertBool "a missing bridge was certified" ("FiniteQ.bad" `notElem` checkedTheorems checked)
    , testCase "later pragmas do not retroactively authorize local proof syntax" $ do
        let (before, pragmas) = T.breakOn "{-# BUILTIN FIN Fin #-}" finiteOrdinals
        checked <- check (before <> "early : 0 = 0\nearly = by\n  have unused : ∀ (i : Fin 0), i = i := by rfl\n  rfl\n" <> pragmas)
        assertRejected checked
        assertBool "late registration changed the earlier proof scope" ("FiniteQ.early" `notElem` checkedTheorems checked)
    , testCase "failed instance roundtrip prevents desugaring a tautology" $ do
        checked <- check (finiteOrdinals <> finiteProtocol <> T.replace "decode-code True = rfl" "decode-code True = by sorry" boolInstance <> "bad : ∀ (b : Bool), b = b\nbad = by intro b; rfl\n")
        assertRejected checked
        assertBool "an incomplete finite instance was accepted" ("FiniteQ.bad" `notElem` checkedTheorems checked)
    , testCase "failed roundtrip remains required for an unused local fact" $ do
        checked <- check (finiteOrdinals <> finiteProtocol <> T.replace "decode-code True = rfl" "decode-code True = by sorry" boolInstance <> "bad : 0 = 0\nbad = by\n  have unused : ∀ (b : Bool), b = b := by intro b; rfl\n  rfl\n")
        assertRejected checked
        assertBool "erasure lost the local fact's dependency" ("FiniteQ.bad" `notElem` checkedTheorems checked)
    , testCase "a builtin implementation cannot bootstrap through finite syntax" $ do
        let before = T.replace "{-# BUILTIN FIN_TO_NAT_BOUND bounded #-}" "" finiteOrdinals
        checked <-
          check
            ( before
                <> T.unlines
                  [ "new-bound : (i : Fin n) -> rank i < n"
                  , "new-bound i = by"
                  , "  have unused : ∀ (j : Fin n), j = j := by intro j; rfl"
                  , "  exact bounded i"
                  , "{-# BUILTIN FIN_TO_NAT_BOUND new-bound #-}"
                  ]
            )
        assertRejected checked
        assertBool "a bridge certified itself through its own desugaring role" ("FiniteQ.new-bound" `notElem` checkedTheorems checked)
    , testCase "proof-only finite dictionaries do not become phantom runtime schemas" $ do
        checked <-
          check
            ( finitePrelude
                <> T.unlines
                  [ "ignore : Finite a => a -> (∀ (y : a), y = y) -> Nat"
                  , "ignore x h = 0"
                  , "again : Finite a => a -> (∀ (y : a), y = y) -> Nat"
                  , "again x h = ignore x h"
                  , "applied : again True (by intro y; rfl) = 0"
                  , "applied = rfl"
                  ]
            )
        errors checked @?= []
        assertCertified "applied" checked
    ]
  where
    isCoverage (PLaw name 0) = name == [Ident "FiniteQ", Ident "Finite", Ident "decode-code"]
    isCoverage _ = False

check :: Text -> IO Checked
check source = do
  p <- either assertFailure pure prelude
  pure (checkSource p "finite-quantifier.px" ("module FiniteQ where\n" <> source))

errors :: Checked -> [Text]
errors checked = [message | Report _ SevError message <- checkedReports checked]

assertRejected :: Checked -> Assertion
assertRejected checked = assertBool "an invalid finite quantifier was accepted" (not (null (errors checked)))

assertCertified :: Text -> Checked -> Assertion
assertCertified name checked = assertBool (T.unpack name <> " was not certified") (("FiniteQ." <> name) `elem` checkedTheorems checked)

theorem :: Text -> Checked -> IO (Knowledge, TheoremInfo)
theorem name checked = do
  (knowledge, _) <- maybe (assertFailure "no checked module") pure (checkedFinal checked)
  case Map.lookup [Ident "FiniteQ", Ident name] (envGlobals (knowEnv knowledge)) of
    Just (GTheorem info) -> pure (knowledge, info)
    _ -> assertFailure ("missing theorem " <> T.unpack name)

numericOnly :: Expr a -> Bool
numericOnly = \case
  Quant _ _ (Just (_, bound)) Nothing body -> numericOnly bound && numericOnly (fromScope body)
  Quant {} -> False
  At _ expression -> numericOnly expression
  Arrow left right -> numericOnly left && numericOnly right
  Conn _ left right -> numericOnly left && numericOnly right
  Not expression -> numericOnly expression
  _ -> True

-- The third ordinal also decodes to True. The only law is decode-code;
-- a converse code-decode equation would be false at that ordinal.
boolRetractionWithSpareOrdinal :: Text
boolRetractionWithSpareOrdinal =
  T.replace "card = 2" "card = 3"
    . T.replace "code False = FZero {1}" "code False = FZero {2}"
    . T.replace "code True = FSucc (FZero {0})" "code True = FSucc (FZero {1})"
    $ boolInstance

-- The cardinal is a class method, so its zero value is converted through
-- an ordinary function contract before the absurd decoder clause is used.
emptyInstance :: Text
emptyInstance =
  T.unlines
    [ "data Empty"
    , "empty-fin : Fin 0 -> Empty"
    , "empty-fin ()"
    , "instance Finite Empty where"
    , "  card = 0"
    , "  code ()"
    , "  decode i = empty-fin i"
    , "  decode-code ()"
    ]
