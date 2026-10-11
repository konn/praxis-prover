{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.EvidenceTest (evidenceTests) where

import Data.Either (isLeft)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Language.Praxis.Surface.Desugar
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Evidence
import Language.Praxis.Surface.Syntax (Ref (..), RefKind (..))
import Language.Praxis.Surface.Syntax.Raw (QName (..), Segment (..), Span (..))
import Language.Praxis.Surface.Types
import Test.Tasty
import Test.Tasty.HUnit

evidenceTests :: TestTree
evidenceTests =
  testGroup
    "finite desugaring evidence"
    [ testCase "source scopes cannot gain a later or rebound registration" $ do
        builtinScope (Map.singleton "FIN" fin) (Map.fromList [("FIN", other), ("VEC", vec)]) @?= Map.empty
        builtinScope (Map.singleton "FIN" fin) (Map.fromList [("FIN", fin), ("VEC", vec)]) @?= Map.singleton "FIN" fin
    , testCase "every dependency is required even for an erased tautology" $ do
        let needed = requirement sp (RegisteredBuiltin "FIN" finName) <> requirement sp (CertifiedDeclaration "coverage")
            available = empty {evidenceBuiltins = Map.singleton "FIN" fin, evidenceDeclarations = Set.singleton "coverage"}
        validateRequirements available needed @?= Right ()
        assertBool "missing coverage accepted" (isLeft (validateRequirements available {evidenceDeclarations = Set.empty} needed))
        assertBool "missing registration accepted" (isLeft (validateRequirements available {evidenceBuiltins = Map.empty} needed))
    , testCase "dictionary evidence must come from the same type parameter" $ do
        let needed = requirement sp (DictionaryEntry methodName 0 1) <> requirement sp (MethodPremise methodName 0) <> requirement sp (MembershipEntry 0)
            available = empty {evidenceSlots = [Slot method 0 1, membershipSlot 0], evidencePremises = [PMethod method 0 (TArrow (TParam 0 []) TNat) (Ref RefStatic "w_1")]}
        validateRequirements available needed @?= Right ()
        assertBool "membership-only evidence accepted for an indexed method" (isLeft (validateRequirements available {evidencePremises = [PClosure method 0]} needed))
        validateRequirements available {evidencePremises = [PClosure method 0]} (requirement sp (ClosurePremise methodName 0)) @?= Right ()
        assertBool "another dictionary's contract accepted" (isLeft (validateRequirements available {evidencePremises = [PClosure method 1]} needed))
        assertBool "missing membership predicate accepted" (isLeft (validateRequirements available {evidenceSlots = [Slot method 0 1]} needed))
    , testCase "method closure evidence cannot substitute for coverage" $ do
        let available = empty {evidencePremises = [PClosure method 0]}
        assertBool "closure substituted for a law" (isLeft (validateRequirements available (requirement sp (LawPremise methodName 0))))
    ]
  where
    empty = Evidence Map.empty Set.empty [] []
    sp = Span (1, 1) (1, 5)
    fin = [Ident "Finite", Ident "Fin"]
    other = [Ident "Other", Ident "Fin"]
    vec = [Ident "Finite", Ident "Vec"]
    finName = QName [Ident "Finite"] (Ident "Fin")
    method = [Ident "Finite", Ident "code"]
    methodName = QName [Ident "Finite"] (Ident "code")
