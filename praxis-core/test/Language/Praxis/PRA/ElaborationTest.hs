{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.PRA.ElaborationTest (elaborationTests) where

import Data.Either (isLeft)
import Data.Foldable (toList)
import Data.Set qualified as Set
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration
import Language.Praxis.PRA.PrimitiveRecursion.Examples (plus)
import Language.Praxis.PRA.Signature qualified as Sig
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
        result <- expectRight (renameTerm (signatureEnv (Sig.signature [Sig.symbol "plus" plus])) Set.empty term)
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
          [ RenamedEquation "f" [ZeroP, VarP "y"] (AppFT (Defined "g") xs)
            , RenamedEquation "f" [SuccP (VarP "x"), VarP "y"] (AppFT (Defined "f") ys)
            , RenamedEquation "g" [VarP "z"] (VarFT "z")
            ] -> do
              case toList xs of
                [VarFT "y"] -> pure ()
                _ -> assertFailure (show xs)
              case toList ys of
                [VarFT "x", AppFT (Primitive _) zs] -> case toList zs of
                  [VarFT "y"] -> pure ()
                  _ -> assertFailure (show zs)
                _ -> assertFailure (show ys)
          _ -> assertFailure (show renamed)
    , testCase "resolve an existing signature and nullary definitions" $ do
        equations <- expectRight (parseEquations "two = 2; f x = plus x two")
        renamed <- expectRight (renameEquations (signatureEnv (Sig.signature [Sig.symbol "plus" plus])) equations)
        case renamed of
          [RenamedEquation "two" [] (LitFT 2), RenamedEquation "f" [VarP "x"] (AppFT (Primitive _) xs)] ->
            case toList xs of
              [VarFT "x", AppFT (Defined "two") ys] -> length ys @?= 0
              _ -> assertFailure (show xs)
          _ -> assertFailure (show renamed)
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
        length renamed @?= 2
    , testCase "local names shadow functions" $ do
        result <- expectRight (renameTerm (signatureEnv mempty) (Set.singleton "S") (NameET "S"))
        case result of
          VarFT "S" -> pure ()
          _ -> assertFailure (show result)
    ]
  where
    (>=>) f g x = f x >>= g

expectRight :: (Show e) => Either e a -> IO a
expectRight = either (\err -> assertFailure (show err) >> fail "unexpected Left") pure
