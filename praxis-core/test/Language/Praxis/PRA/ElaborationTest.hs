{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Praxis.PRA.ElaborationTest (elaborationTests) where

import Data.Either (isLeft)
import Data.Foldable (toList)
import Data.Hashable (hash)
import Data.Map.Strict qualified as Map
import Data.Type.Ordinal (Ordinal, ordToNatural)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration
import Language.Praxis.PRA.PrimitiveRecursion.Examples (plus)
import Language.Praxis.PRA.Signature qualified as Sig
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit

elaborationTests :: TestTree
elaborationTests =
  testGroup
    "equation elaboration"
    [ testCase "application associates left, parentheses nest" $
        parseEqTerm "f x (g y)" @?= Right ((NameET "f" :@ NameET "x") :@ (NameET "g" :@ NameET "y"))
    , testCase "parenthesized application heads are flattened" $ do
        term <- expectRight (parseEqTerm "(plus 1) 2")
        result <- expectRight (renameTerm @0 (signatureEnv (Sig.signature [Sig.symbol "plus" plus])) Map.empty term)
        case result of
          AppFT (Primitive _) xs -> case toList xs of
            [LitFT 1, LitFT 2] -> pure ()
            _ -> assertFailure (show xs)
          _ -> assertFailure (show result)
    , testCase "identifiers and constructor prefixes" $
        parseEquation "f x' Suffix = x'" @?= Right (Equation "f" [VarP "x'", VarP "Suffix"] (NameET "x'"))
    , testCase "successor patterns and nested comments" $
        parseEquation " {- a {- b -} -} f (Succ (S x)) 0 = S x -- end"
          @?= Right (Equation "f" [SuccP (SuccP (VarP "x")), ZeroP] (NameET "S" :@ NameET "x"))
    , testCase "reject trailing input and malformed numerals" $
        map (isLeft . parseEqTerm) ["x )", "12x", "(f x", ""] @?= replicate 4 True
    , testCase "resolve self and forward references with fixed vectors" $ do
        equations <- expectRight (parseEquations "f 0 y = g y; f (S x) y = f x (S y); g z = z;")
        renamed <- expectRight (renameEquations (signatureEnv mempty) equations)
        case renamed of
          [ RenamedEquation "f" (toList -> [ZeroP, VarP "y"]) (AppFT (Defined "g") xs)
            , RenamedEquation "f" (toList -> [SuccP (VarP "x"), VarP "y"]) (AppFT (Defined "f") ys)
            , RenamedEquation "g" (toList -> [VarP "z"]) (VarFT (ordToNatural -> 0))
            ] -> do
              case toList xs of
                [VarFT (ordToNatural -> 1)] -> pure ()
                _ -> assertFailure (show xs)
              case toList ys of
                [VarFT (ordToNatural -> 0), AppFT (Primitive _) zs] -> case toList zs of
                  [VarFT (ordToNatural -> 1)] -> pure ()
                  _ -> assertFailure (show zs)
                _ -> assertFailure (show ys)
          _ -> assertFailure (show renamed)
    , testCase "resolve an existing signature and nullary definitions" $ do
        equations <- expectRight (parseEquations "two = 2; f x = plus x two")
        renamed <- expectRight (renameEquations (signatureEnv (Sig.signature [Sig.symbol "plus" plus])) equations)
        case renamed of
          [RenamedEquation "two" (toList -> []) (LitFT 2), RenamedEquation "f" (toList -> [VarP "x"]) (AppFT (Primitive _) xs)] ->
            case toList xs of
              [VarFT (ordToNatural -> 0), AppFT (Defined "two") ys] -> length ys @?= 0
              _ -> assertFailure (show xs)
          _ -> assertFailure (show renamed)
    , testCase "indices follow argument slots through zeros and nested successors" $ do
        equations <- expectRight (parseEquations "f z 0 (S (S a)) = f a 0 z")
        renamed <- expectRight (renameEquations (signatureEnv mempty) equations)
        case renamed of
          [RenamedEquation "f" pats body] -> do
            length pats @?= 3
            map (fmap rawName) (toList pats) @?= [VarP "z", ZeroP, SuccP (SuccP (VarP "a"))]
            variableIndices body @?= [2, 0]
          _ -> assertFailure (show renamed)
    , testCase "alpha-renaming preserves indices and irrelevant patterns" $ do
        equations <- expectRight (parseEquations "f 0 (S z) a = f 0 a z; f 0 (S x) y = f 0 y x")
        renamed <- expectRight (renameEquations (signatureEnv mempty) equations)
        case renamed of
          [RenamedEquation _ ps body, RenamedEquation _ qs body'] -> do
            toList ps @?= toList qs
            hash (toList ps) @?= hash (toList qs)
            variableIndices body @?= [2, 1]
            variableIndices body' @?= variableIndices body
          _ -> assertFailure (show renamed)
    , testCase "zero patterns introduce no variables" $ do
        equations <- expectRight (parseEquations "f 0 (S 0) = 7")
        renamed <- expectRight (renameEquations (signatureEnv mempty) equations)
        case renamed of
          [RenamedEquation _ pats (LitFT 7)] -> length pats @?= 2
          _ -> assertFailure (show renamed)
        bad <- expectRight (parseEquations "f 0 = x")
        assertBool "zero must not bind a name" (isLeft (renameEquations (signatureEnv mempty) bad))
    , testCase "reject scope, arity, and binder errors" $
        map
          (isLeft . (parseEquations >=> renameEquations (signatureEnv mempty)))
          [ "f x = missing"
          , "f x = S"
          , "f x = S x x"
          , "f x = x x"
          , "f x = 1 x"
          , "f x x = x"
          , "f x = x; f x y = x"
          , "S x = x"
          , "f x = (S x) x"
          ]
          @?= replicate 9 True
    , testCase "nonlinear patterns report the repeated variable" $
        map
          (fmap (const ()) . (parseEquations >=> renameEquations (signatureEnv mempty)))
          [ "f x x = x"
          , "f (S x) x = x"
          , "f x (Succ x) = x"
          , "f (S (Succ x)) (S x) = x"
          ]
          @?= replicate 4 (Left "Nonlinear pattern: repeated variable x")
    , testCase "linearity is per clause and permits repeated body variables" $ do
        equations <- expectRight (parseEquations "f 0 x = plus x x; f (S n) x = plus x x")
        renamed <- expectRight (renameEquations (signatureEnv (Sig.signature [Sig.symbol "plus" plus])) equations)
        case renamed of
          [RenamedEquation _ _ body, RenamedEquation _ _ body'] -> do
            variableIndices body @?= [1, 1]
            variableIndices body' @?= [1, 1]
          _ -> assertFailure (show renamed)
    , testCase "local names shadow functions" $ do
        result <- expectRight (renameTerm (signatureEnv mempty) (Map.singleton "S" (0 :: Ordinal 1)) (NameET "S"))
        case result of
          VarFT (ordToNatural -> 0) -> pure ()
          _ -> assertFailure (show result)
    ]
  where
    (>=>) f g x = f x >>= g

expectRight :: (Show e) => Either e a -> IO a
expectRight = either (\err -> assertFailure (show err) >> fail "unexpected Left") pure

variableIndices :: FunctionalTerm n -> [Natural]
variableIndices (LitFT _) = []
variableIndices (VarFT index) = [ordToNatural index]
variableIndices (AppFT _ terms) = foldMap variableIndices terms
