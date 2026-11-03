{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.InternalTest (internalTests) where

import Control.Monad (forM_)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Core qualified as Core
import Language.Praxis.Surface.Eval (EvalResult (..), Value (..), evaluateEntryWithNats)
import Language.Praxis.Surface.Mangle (mangleGlobal)
import Language.Praxis.Surface.Prelude (prelude)
import Language.Praxis.Surface.Rename (Imports, ModuleExports (..), RDecl (..), Renamed (..))
import Language.Praxis.Surface.Syntax.Raw
import Language.Praxis.Surface.Types (Ty (..))
import Test.Tasty
import Test.Tasty.HUnit

internalTests :: TestTree
internalTests = withResource fixtures (const (pure ())) $ \getFixtures ->
  let check source = do
        (build, imports) <- getFixtures
        pure (checkModule (\_ _ -> []) build imports Nothing "internal.px" (header <> source))
      succeeds source = do
        (checked, build) <- check source
        errors checked @?= []
        pure (checked, build)
      rejects label source = testCase label $ do
        (checked, _) <- check source
        assertBool "invalid internal proof was accepted" (not (null (errors checked)))
        assertNoCertificates checked "bad"
   in testGroup
        "internal mode"
        [ testCase "proof data retains certificates and feeds an ordinary proof consumer" $ do
            (checked, _) <-
              succeeds $
                T.unlines
                  [ "open import InternalFixtures"
                  , "internal Intuitionistic where"
                  , "  identity : {a : Formula} -> Imp a a"
                  , "  identity {a} = by exact MP (MP (S {a} {Imp a a} {a}) (K {a} {Imp a a})) (K {a} {a})"
                  , "keep : Intuitionistic a -> Intuitionistic a"
                  , "keep p = p"
                  , "outside : {a : Formula} -> Intuitionistic (Imp a a)"
                  , "outside {a} = keep (identity {a})"
                  ]
            core <- finalCore checked
            forM_ ["identity", "outside"] $ \name -> do
              assertCertificates core name
              assertFamily core name "Intuitionistic"
        , testCase "apply constructs both premises and focus closes each selected goal" $ do
            (checked, _) <-
              succeeds $
                T.unlines
                  [ "open import InternalFixtures"
                  , "internal Intuitionistic where"
                  , "  applied : {a : Formula} -> Imp a a"
                  , "  applied {a} = by"
                  , "    apply MP"
                  , "    {"
                  , "      apply MP"
                  , "      { exact S {a} {Imp a a} {a} }"
                  , "      { exact K {a} {Imp a a} }"
                  , "    }"
                  , "    { exact K {a} {a} }"
                  ]
            finalCore checked >>= \core -> assertCertificates core "applied"
        , testCase "proof premises retain their ordinary family types" $ do
            (checked, _) <-
              succeeds $
                T.unlines
                  [ "open import InternalFixtures"
                  , "internal Third where"
                  , "  keep : {a : Formula} -> Third a -> a"
                  , "  keep {a} p = by exact p"
                  ]
            core <- finalCore checked
            assertCertificates core "keep"
            assertFamily core "keep" "Third"
        , testCase "nested theories restore constructors and leave arithmetic successor outside" $ do
            (checked, _) <-
              succeeds $
                T.unlines
                  [ "open import InternalFixtures"
                  , "internal Intuitionistic where"
                  , "  before : {a b : Formula} -> Imp a (Imp b a)"
                  , "  before {a} {b} = K {a} {b}"
                  , "  internal Classical where"
                  , "    classical : {a : Formula} -> Imp (Imp (Imp a Bottom) Bottom) a"
                  , "    classical {a} = by DNE {a}"
                  , "  after : {a b c : Formula} -> Imp (Imp a (Imp b c)) (Imp (Imp a b) (Imp a c))"
                  , "  after {a} {b} {c} = by S {a} {b} {c}"
                  , "successor : Nat -> Nat"
                  , "successor n = S n"
                  ]
            core <- finalCore checked
            assertFamily core "before" "Intuitionistic"
            assertFamily core "after" "Intuitionistic"
            assertFamily core "classical" "Classical"
            evaluated <- either assertFailure pure (evaluateEntryWithNats 100 "Internal.successor" [2] checked)
            evalValue evaluated @?= NatValue 3
        , testCase "qualified family aliases keep declarations in their enclosing namespaces" $ do
            (checked, build) <-
              succeeds $
                T.unlines
                  [ "import InternalFixtures as F"
                  , "module Results where"
                  , "  internal F.Third where"
                  , "    witness : F.Formula.Atom 0"
                  , "    witness = by Axiom"
                  , "internal F.Third where"
                  , "  module Nested where"
                  , "    witness : F.Formula.Atom 0"
                  , "    witness = Axiom"
                  , "use-result : F.Third (F.Formula.Atom 0)"
                  , "use-result = Results.witness"
                  , "use-nested : F.Third (F.Formula.Atom 0)"
                  , "use-nested = Nested.witness"
                  ]
            core <- finalCore checked
            assertBool "internal block invented a family namespace" (Map.notMember "u_Internal_sThird_switness" (coreBodies core))
            forM_ (map mangleGlobal [["Internal", "Results", "witness"], ["Internal", "Nested", "witness"], ["Internal", "use-result"], ["Internal", "use-nested"]]) $ \name ->
              assertBool (T.unpack name <> " was not lowered") (Map.member name (coreBodies core))
            exported <- exportOf build "Internal"
            assertBool "enclosing modules were not exported" (all (`Map.member` meMembers exported) [Ident "Results", Ident "Nested"])
            (_, imports) <- getFixtures
            let client =
                  T.unlines
                    [ "module Client where"
                    , "import Internal as I"
                    , "import InternalFixtures as F"
                    , "from-result : F.Third (F.Formula.Atom 0)"
                    , "from-result = I.Results.witness"
                    , "from-nested : F.Third (F.Formula.Atom 0)"
                    , "from-nested = I.Nested.witness"
                    ]
                (clientChecked, _) = checkModule (\_ _ -> []) build (Map.insert (Nothing, [Ident "Internal"]) (Right exported) imports) Nothing "client.px" client
            errors clientChecked @?= []
        , testCase "private internal declarations are usable locally but are not exported" $ do
            (checked, build) <-
              succeeds $
                T.unlines
                  [ "open import InternalFixtures"
                  , "internal Third where"
                  , "  private"
                  , "    hidden : Atom 0"
                  , "    hidden = Axiom"
                  , "  visible : Atom 0"
                  , "  visible = hidden"
                  ]
            finalCore checked >>= \core -> assertCertificates core "visible"
            exported <- exportOf build "Internal"
            assertBool "private proof escaped the module" (Map.notMember (Ident "hidden") (meMembers exported))
            assertBool "public proof was lost" (Map.member (Ident "visible") (meMembers exported))
        , testCase "imports inside an internal block have lexical alias scope" $ do
            let block =
                  T.unlines
                    [ "open import InternalFixtures using (Third, Formula)"
                    , "internal Third where"
                    , "  import InternalFixtures as Local"
                    , "  witness : Local.Formula.Atom 0"
                    , "  witness = Axiom"
                    ]
            (checked, _) <- succeeds (block <> "outside : Third (Formula.Atom 0)\noutside = witness\n")
            finalCore checked >>= \core -> assertCertificates core "outside"
            (leaked, _) <- check (block <> "bad : Local.Third (Formula.Atom 0)\nbad = witness\n")
            assertBool "an internal import alias leaked into the next declaration" (not (null (errors leaked)))
        , testCase "open directives inside an internal block do not leak" $ do
            (checked, _) <-
              succeeds $
                T.unlines
                  [ "import InternalFixtures as F"
                  , "internal F.Third where"
                  , "  open F using (Formula)"
                  , "  open F.Formula using (Atom)"
                  , "  witness : Atom 0"
                  , "  witness = Axiom"
                  , "outside : F.Formula"
                  , "outside = F.Formula.Atom 0"
                  ]
            renamed <- maybe (assertFailure "missing renamed module") pure (checkedRenamed checked)
            let signatures = [(unLocated name, ty) | RDecl _ (Located _ (DSignature name ty)) <- rnDecls renamed]
            assertBool "outside signature was accidentally wrapped" (case lookup (Ident "outside") signatures of Just (Located _ (EName (QName [Ident "InternalFixtures"] (Ident "Formula")))) -> True; _ -> False)
            (leaked, _) <-
              check $
                T.unlines
                  [ "import InternalFixtures as F"
                  , "internal F.Third where"
                  , "  open F using (Formula)"
                  , "  open F.Formula using (Atom)"
                  , "  witness : Atom 0"
                  , "  witness = Axiom"
                  , "bad : Formula"
                  , "bad = F.Formula.Atom 0"
                  ]
            assertBool "an internal open leaked into the next declaration" (not (null (errors leaked)))
        , testCase "an inconsistent object calculus supplies proof data without reflection" $ do
            (checked, _) <-
              succeeds $
                T.unlines
                  [ "open import InternalFixtures"
                  , "internal AnyFormula where"
                  , "  object-bottom : Bottom"
                  , "  object-bottom = Assume {Bottom}"
                  , "retain : AnyFormula Bottom"
                  , "retain = object-bottom"
                  ]
            finalCore checked >>= \core -> assertFamily core "retain" "AnyFormula"
        , testCase "internal admission checks the membership predicates actually generated" $ do
            let declarations =
                  opened
                    <> T.unlines
                      [ "data Deferred (a : Formula) where"
                      , "  DeferredRule : Later -> Deferred (Atom 0)"
                      , "data Later = LaterValue"
                      ]
            _ <- succeeds declarations
            (checked, _) <- check (declarations <> "internal Deferred where {}\n")
            assertBool "an omitted field membership was accepted" (any (T.isInfixOf "complete field membership") (errors checked))
            (used, _) <- check (declarations <> "internal Deferred where\n  bad : Atom 0\n  bad = DeferredRule LaterValue\n")
            assertNoCertificates used "bad"
        , testCase "internal admission checks field membership dependencies transitively" $ do
            let declarations =
                  opened
                    <> T.unlines
                      [ "data Wrapper = Wrap Later"
                      , "data Later = LaterValue"
                      , "data Indirect (a : Formula) where"
                      , "  IndirectRule : Wrapper -> Indirect (Atom 0)"
                      ]
            _ <- succeeds declarations
            (checked, _) <- check (declarations <> "internal Indirect where {}\n")
            assertBool "an incomplete dependency membership was accepted" (any (T.isInfixOf "complete field membership") (errors checked))
        , testCase "parameterized stored fields are outside the initial admission contract" $ do
            let declarations =
                  opened
                    <> T.unlines
                      [ "data List a = Nil | Cons a (List a)"
                      , "data WithList (a : Formula) where"
                      , "  ListRule : List Nat -> WithList (Atom 0)"
                      ]
            _ <- succeeds declarations
            (checked, _) <- check (declarations <> "internal WithList where {}\n")
            assertBool "a parameterized field encoding was accepted" (any (T.isInfixOf "closed first-order fields") (errors checked))
        , rejects "the conclusion index is checked" (opened <> "internal Third where\n  bad : Atom 1\n  bad = Axiom\n")
        , rejects "proofs of different calculi are not interchangeable" (opened <> "internal Intuitionistic where\n  bad : Imp (Imp (Imp (Atom 0) Bottom) Bottom) (Atom 0)\n  bad = Classical.DNE {Atom 0}\n")
        , rejects "native theorem tactics do not prove object goals" (opened <> "internal Third where\n  bad : Atom 0\n  bad = by rfl\n")
        , rejects "sorry never certifies an internal proof" (opened <> "internal Third where\n  bad : Atom 0\n  bad = by sorry\n")
        , rejects "apply cannot leave a premise unfinished" (opened <> "internal Intuitionistic where\n  bad : {a : Formula} -> Imp a a\n  bad {a} = by apply MP {Imp a (Imp a a)} {Imp a a}\n")
        , rejects "a completed proof cannot discard trailing tactics" (opened <> "internal Third where\n  bad : Atom 0\n  bad = by\n    exact Axiom\n    exact Axiom\n")
        , rejects "failed unused have evidence is not discarded" (opened <> "internal Third where\n  bad : Atom 0\n  bad = by\n    have unused : 0 = 1 := rfl\n    exact Axiom\n")
        , rejects "unsupported unused have evidence is not discarded" (opened <> "internal Third where\n  bad : Atom 0\n  bad = by\n    have unused : 0 = 0 := rfl\n    exact Axiom\n")
        , rejects "a nonindexed datatype is not a proof family" (opened <> "internal Formula where\n  bad : Atom 0\n  bad = Atom 0\n")
        , rejects "an empty block still checks its selected family" (opened <> "internal Formula where {}\n")
        , rejects "a family with multiple conclusion indices is rejected" (opened <> "internal Double where\n  bad : Atom 0\n  bad = Both {Atom 0} {Atom 0}\n")
        , rejects "a family with type parameters is rejected" (opened <> "internal Parameterized where\n  bad : Atom 0\n  bad = ParamProof {Atom 0} 0\n")
        , rejects "an unknown family is rejected" (opened <> "internal Unknown where\n  bad : Atom 0\n  bad = Third.Axiom\n")
        , rejects "a signature cannot acquire a clause from another internal block" (opened <> "internal Third where\n  bad : Atom 0\ninternal Third where\n  bad = Axiom\n")
        , rejects "an internal signature cannot acquire a clause outside its block" (opened <> "internal Third where\n  bad : Atom 0\nbad = Third.Axiom\n")
        , rejects "object bottom does not prove a native arithmetic contradiction" (opened <> "internal AnyFormula where\n  object-bottom : Bottom\n  object-bottom = Assume {Bottom}\nbad : 0 = 1\nbad = by exact object-bottom\n")
        , rejects "object bottom is not native absurdity evidence" (opened <> "internal AnyFormula where\n  object-bottom : Bottom\n  object-bottom = Assume {Bottom}\nbad : Nat\nbad = absurd object-bottom\n")
        ]

header :: Text
header = "module Internal where\n"

opened :: Text
opened = "open import InternalFixtures\n"

errors :: Checked -> [Text]
errors checked = [message | Report _ SevError message <- checkedReports checked]

finalCore :: Checked -> IO Core
finalCore checked = snd <$> maybe (assertFailure "missing checked core") pure (checkedFinal checked)

assertCertificates :: Core -> Text -> Assertion
assertCertificates core name = forM_ ["contract", "closed", "index"] $ \suffix ->
  assertBool
    (T.unpack name <> " has no " <> T.unpack suffix <> " certificate")
    (Map.member (T.unpack (mangleGlobal ["Internal", name, "#" <> suffix])) (coreCertificates core))

assertNoCertificates :: Checked -> Text -> Assertion
assertNoCertificates checked name = forM_ (checkedFinal checked) $ \(_, core) ->
  forM_ ["contract", "closed", "index"] $ \suffix ->
    assertBool
      (T.unpack name <> " unexpectedly received a " <> T.unpack suffix <> " certificate")
      (Map.notMember (T.unpack (mangleGlobal ["Internal", name, "#" <> suffix])) (coreCertificates core))

assertFamily :: Core -> Text -> Text -> Assertion
assertFamily core name family = case Map.lookup (mangleGlobal ["Internal", name]) (coreBodies core) of
  Just [body] -> case Core.bodyType body of
    TData actual [] [_] -> actual @?= "InternalFixtures." <> family
    other -> assertFailure ("internal proof lost its indexed result: " <> show other)
  _ -> assertFailure ("missing body for " <> T.unpack name)

exportOf :: Build -> Text -> IO ModuleExports
exportOf build name = maybe (assertFailure "missing module exports") pure (Map.lookup [Ident name] (buildExports build))

fixtures :: IO (Build, Imports)
fixtures = do
  p <- either assertFailure pure prelude
  let source =
        T.unlines
          [ "module InternalFixtures where"
          , "data Formula = Atom Nat | Bottom | Imp Formula Formula"
          , "data Intuitionistic (a : Formula) where"
          , "  K : {a b : Formula} -> Intuitionistic (Imp a (Imp b a))"
          , "  S : {a b c : Formula} -> Intuitionistic (Imp (Imp a (Imp b c)) (Imp (Imp a b) (Imp a c)))"
          , "  MP : {a b : Formula} -> Intuitionistic (Imp a b) -> Intuitionistic a -> Intuitionistic b"
          , "data Classical (a : Formula) where"
          , "  DNE : {a : Formula} -> Classical (Imp (Imp (Imp a Bottom) Bottom) a)"
          , "data Third (a : Formula) where"
          , "  Axiom : Third (Atom 0)"
          , "data AnyFormula (a : Formula) where"
          , "  Assume : {a : Formula} -> AnyFormula a"
          , "data Double (a : Formula) (b : Formula) where"
          , "  Both : {a b : Formula} -> Double a b"
          , "data Parameterized t (a : Formula) where"
          , "  ParamProof : {a : Formula} -> t -> Parameterized t a"
          ]
      (checked, build) = checkModule (\_ _ -> []) (initialBuild p) {buildRetainGeneratedText = False} Map.empty Nothing "InternalFixtures.px" source
  errors checked @?= []
  exports <- exportOf build "InternalFixtures"
  pure (build, Map.singleton (Nothing, [Ident "InternalFixtures"]) (Right exports))
