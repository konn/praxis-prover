{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.ClassAdmissionTest (classAdmissionTests) where

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Desugar
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Evidence
import Language.Praxis.Surface.FiniteFixtures
import Language.Praxis.Surface.Prelude (prelude)
import Language.Praxis.Surface.Syntax.Raw (QName (..), Segment (..), Span (..))
import Test.Tasty
import Test.Tasty.HUnit

classAdmissionTests :: TestTree
classAdmissionTests =
  testGroup
    "class admission"
    [ testCase "class admission is distinct from a dictionary or a named certificate" $ do
        let name = QName [Ident "A"] (Ident "Trusted")
            needed = requirement (Span (1, 1) (1, 2)) (AdmittedClass name)
            evidence = Evidence Map.empty (Set.singleton "A.Trusted") [membershipSlot 0] []
        assertBool "an ordinary certificate admitted a class" (either (const True) (const False) (validateRequirements evidence needed))
        validateRequirements evidence {evidenceDeclarations = Set.singleton (classEvidenceName [Ident "A", Ident "Trusted"])} needed @?= Right ()
    , testCase "failed classes cannot justify erased constraints or instance contexts" $ do
        p <- either assertFailure pure prelude
        let declarations =
              T.unlines
                [ "use : Trusted a => a -> 0 = 0"
                , "use x = rfl"
                , "discard : Trusted a => a -> Nat"
                , "discard x = 0"
                , "instantiated : Bool -> Nat"
                , "instantiated x = discard x"
                , "data Box a = MkBox a"
                , "class Safe a where"
                , "  out : a -> Nat"
                , "instance Trusted a => Safe (Box a) where"
                , "  out b = 0"
                , "class Trusted a => Child a where"
                , "  child : a -> Nat"
                ]
            (checked, build) = checkModule (\_ _ -> []) (initialBuild p) Map.empty Nothing "A.px" (source False <> declarations)
        assertBool "the failed class had no admission diagnostic" (any (T.isInfixOf "successfully checked class A.Trusted") (errors checked))
        assertBool "a zero-method failed class certified a theorem" ("A.use" `notElem` checkedTheorems checked)
        mapM_ (notAdmitted build) [[Ident "A", Ident "discard"], [Ident "A", Ident "instantiated"], [Ident "A", Ident "Safe-Box", Ident "out"], [Ident "A", Ident "Child"]]
    , testCase "failed class admission survives qualified imports and renaming" $ do
        p <- either assertFailure pure prelude
        let (_, build) = checkModule (\_ _ -> []) (initialBuild p) Map.empty Nothing "A.px" (source False)
        exports <- maybe (assertFailure "missing exports") pure (Map.lookup [Ident "A"] (buildExports build))
        let imports = Map.singleton (Nothing, [Ident "A"]) (Right exports)
            (checked, _) = checkModule (\_ _ -> []) build imports Nothing "B.px" "module B where\nimport A as V\nopen V using (Trusted) renaming (Trusted to Imported)\nuse : Imported a => a -> 0 = 0\nuse x = rfl\n"
        assertBool "an imported failed class was accepted" ("B.use" `notElem` checkedTheorems checked)
        assertBool "canonical class name was lost at import" (any (T.isInfixOf "successfully checked class A.Trusted") (errors checked))
    , testCase "admitted class laws work generically, concretely, and through imports" $ do
        p <- either assertFailure pure prelude
        let declarations =
              T.unlines
                [ "instance Trusted Bool where"
                , "  law x = by intro b; rfl"
                , "generic : Trusted a => (x : a) -> ∀ (b : Bool), b = b"
                , "generic x = Trusted.law x"
                , "concrete : (x : Bool) -> ∀ (b : Bool), b = b"
                , "concrete x = Trusted.law x"
                ]
            (checked, build) = checkModule (\_ _ -> []) (initialBuild p) Map.empty Nothing "A.px" (source True <> declarations)
        errors checked @?= []
        assertBool "generic class law was not certified" ("A.generic" `elem` checkedTheorems checked)
        assertBool "concrete class law was not certified" ("A.concrete" `elem` checkedTheorems checked)
        exports <- maybe (assertFailure "missing exports") pure (Map.lookup [Ident "A"] (buildExports build))
        let imports = Map.singleton (Nothing, [Ident "A"]) (Right exports)
            (imported, _) = checkModule (\_ _ -> []) build imports Nothing "B.px" "module B where\nimport A as V\nuse : V.Trusted a => a -> 0 = 0\nuse x = rfl\n"
        errors imported @?= []
        assertBool "imported class admission was lost" ("B.use" `elem` checkedTheorems imported)
    ]
  where
    errors = map reportMessage . filter ((== SevError) . reportSeverity) . checkedReports
    notAdmitted build name = assertBool ("failed class admitted " <> show name) (name `Set.notMember` buildCheckedDeclarations build)
    source valid = "module A where\n" <> finiteOrdinals <> finiteProtocol <> (if valid then boolInstance else T.replace "decode-code True = rfl" "decode-code True = by sorry" boolInstance) <> "class Trusted a where\n  law : (x : a) -> ∀ (b : Bool), b = b\n"
