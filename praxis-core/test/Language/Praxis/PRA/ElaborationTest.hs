{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Praxis.PRA.ElaborationTest (elaborationTests) where

import Data.Either (isLeft)
import Data.Foldable (toList)
import Data.Hashable (hash)
import Data.List (isInfixOf)
import Data.Map.Strict qualified as Map
import Data.Sized qualified as SV
import Data.Text qualified as T
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Type.Natural (sNat)
import Data.Type.Ordinal (Ordinal, ordToNatural)
import Language.Praxis.PRA.PrimitiveRecursion qualified as PR
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration
import Language.Praxis.PRA.PrimitiveRecursion.Examples (plus)
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.Signature qualified as Sig
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit

elaborationTests :: TestTree
elaborationTests =
  testGroup
    "equation elaboration"
    [ compilerTests
    , testCase "application associates left, parentheses nest" $
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
        parseEquation "f x' Suffix = x'" @?= Right (Equation "f" [] [VarP "x'", VarP "Suffix"] Nothing (NameET "x'"))
    , testCase "successor patterns and nested comments" $
        parseEquation " {- a {- b -} -} f (Succ (S x)) 0 = S x -- end"
          @?= Right (Equation "f" [] [SuccP (SuccP (VarP "x")), ZeroP] Nothing (NameET "S" :@ NameET "x"))
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

compilerTests :: TestTree
compilerTests =
  testGroup
    "PRF elaboration"
    [ testCase "coverage and overlap agree with a finite pattern model" $ do
        let patterns = [VarP "_", ZeroP, SuccP (VarP "_"), SuccP ZeroP, SuccP (SuccP (VarP "_"))]
            rows = [p SV.:< q SV.:< SV.Nil | p <- patterns, q <- patterns]
            matrices = [] : [[r] | r <- rows] <> [[r, s] | r <- rows, s <- rows]
            matches (VarP _) _ = True
            matches ZeroP x = x == 0
            matches (SuccP p) x = x > 0 && matches p (x - 1)
            -- All patterns have depth at most two, so larger inputs have the
            -- same matching behavior as 3. This checks the whole domain.
            totalDisjoint ps =
              all
                (\xs -> length (filter (and . zipWith (flip matches) xs . toList) ps) == 1)
                [[x, y] | x <- [0 .. 3 :: Natural], y <- [0 .. 3]]
        mapM_
          ( \ps -> do
              let actual = buildCaseTree (zipWith (\i pats -> EquationRow i pats (LitFT 0)) [0 ..] ps)
              assertEqual (show ps) (totalDisjoint ps) (either (const False) (const True) actual)
          )
          matrices
    , testCase "nullary and composed environmental calls" $ do
        defs <- compileProgram "two = 2; double x = plus x x; answer = double two"
        checkValues defs "answer" [([], 4)]
        checkValues defs "double" [([x], 2 * x) | x <- range]
    , testCase "nested successor patterns bind the correct predecessor" $ do
        defs <- compileProgram "f 0 = 7; f (S 0) = 8; f (S (S x)) = x"
        checkValues defs "f" [([x], if x < 2 then x + 7 else x - 2) | x <- range]
    , testCase "wildcard bodies retain the whole scrutinee after splitting" $ do
        defs <- compileProgram "f x 0 = x; f 0 (S y) = y; f (S x) (S y) = plus (S x) (S y)"
        checkValues defs "f" [([x, y], if y == 0 then x else if x == 0 then y - 1 else x + y) | x <- range, y <- range]
    , testCase "second-argument recursion restores public argument order" $ do
        defs <- compileProgram "add x 0 = x; add x (S y) = S (add x y)"
        checkValues defs "add" [([x, y], x + y) | x <- range, y <- range]
        chosenArgument defs "add" @?= Just 1
    , testCase "multiple constructor columns choose the valid recursion argument" $ do
        defs <- compileProgram "mul 0 0 = 0; mul 0 (S y) = 0; mul (S x) 0 = 0; mul (S x) (S y) = plus (S x) (mul (S x) y)"
        checkValues defs "mul" [([x, y], x * y) | x <- range, y <- range]
        chosenArgument defs "mul" @?= Just 1
    , testCase "parameter splits preserve the outer recursive result" $ do
        defs <- compileProgram "f 0 b = b; f (S n) 0 = S (f n 0); f (S n) (S x) = plus (f n (S x)) (S x)"
        checkValues defs "f" [([n, b], if b == 0 then n else (n + 1) * b) | n <- range, b <- range]
        chosenArgument defs "f" @?= Just 0
    , testCase "nested parameter patterns and repeated recursive results" $ do
        defs <- compileProgram "f 0 b = b; f (S n) 0 = f n 0; f (S n) (S 0) = plus (f n 1) (f n 1); f (S n) (S (S x)) = S (f n (S (S x)))"
        checkValues defs "f" [([n, b], if b == 0 then 0 else if b == 1 then 2 ^ n else b + n) | n <- range, b <- range]
    , testCase "unary recursion needs no fixed parameters" $ do
        defs <- compileProgram "f 0 = 3; f (S n) = S (f n)"
        checkValues defs "f" [([x], x + 3) | x <- range]
    , testCase "three arguments and a middle recursion column" $ do
        defs <- compileProgram "f a 0 b = plus a b; f a (S n) b = plus a (f a n b)"
        checkValues defs "f" [([a, n, b], (n + 1) * a + b) | a <- range, n <- range, b <- range]
        chosenArgument defs "f" @?= Just 1
    , testCase "forward dependencies are compiled before their callers" $ do
        defs <- compileProgram "a x = z x; z 0 = 0; z (S n) = S (z n)"
        checkValues defs "a" [([x], x) | x <- range]
    , testCase "reject holes, overlaps, changed parameters, and cycles" $
        mapM_
          (uncurry rejectProgram)
          [ ("f 0 = 0", "Non-exhaustive")
          , ("f 0 x = 0; f (S x) 0 = 0", "Non-exhaustive")
          , ("f (S (S x)) = x; f 0 = 0", "Non-exhaustive")
          , ("f 0 = 0; f x = 1", "Overlapping")
          , ("f 0 y = 0; f x 0 = 0; f (S x) (S y) = 0", "Overlapping")
          , ("f = 0; f = 1", "Overlapping")
          , ("f 0 x = x; f (S n) x = f n (S x)", "No primitive recursion argument")
          , ("f 0 = 0; f (S n) = f (S n)", "No primitive recursion argument")
          , ("f 0 = f 0; f (S n) = f n", "No primitive recursion argument")
          , ("f 0 = 0; f (S 0) = 1; f (S (S n)) = f n", "No primitive recursion argument")
          , ("f x = g x; g x = f x", "Mutual recursion")
          , ("f = f", "No primitive recursion argument")
          ]
    , testCase "compiled dependency arities are checked" $ do
        eqs <- expectRight (parseEquations "f x = plus x x")
        renamed <- expectRight (renameEquations (Map.insert "plus" (SomeFunction (Defined "plus" :: Function 2)) compilerEnv) eqs)
        case elaborateRenamedEquations (Map.singleton "plus" (SomeProgram (F.Base PR.Succ))) renamed of
          Left err -> assertBool err ("arity mismatch" `isInfixOf` err)
          Right _ -> assertFailure "accepted an environmental code of the wrong arity"
    , testCase "empty programs are allowed, empty individual definitions are rejected" $ do
        defs <- compileProgram ""
        Map.size defs @?= 0
        assertBool "empty definition" (isLeft (elaborateDefinition Map.empty []))
    , testCase "infix operators and conditionals parse and respect precedence" $ do
        parseEqTerm "x + y * z" @?= Right (InfixET (NameET "x") "+" (InfixET (NameET "y") "*" (NameET "z")))
        parseEqTerm "x * y + z" @?= Right (InfixET (InfixET (NameET "x") "*" (NameET "y")) "+" (NameET "z"))
        parseEqTerm "x < y + 1" @?= Right (InfixET (NameET "x") "<" (InfixET (NameET "y") "+" (LitET 1)))
        parseEqTerm "if x < y then x else y"
          @?= Right (IfThenElseET (InfixET (NameET "x") "<" (NameET "y")) (NameET "x") (NameET "y"))
    , testCase "scope-based desugaring of operators and ifte" $ do
        let arithEnv = signatureEnv PR.arithmetic
            locals = Map.fromList [("x", 0 :: Ordinal 2), ("y", 1 :: Ordinal 2)]
        term1 <- expectRight (parseEqTerm "if x < y then x + y else x * y")
        renamed1 <- expectRight (renameTerm @2 arithEnv locals term1)
        case renamed1 of
          AppFT (Bound _) _ -> pure ()
          _ -> assertFailure ("unexpected renamed term: " <> show renamed1)
        let noIfteEnv = Map.delete "ifte" arithEnv
        assertBool "missing ifte rejected" (isLeft (renameTerm @2 noIfteEnv locals term1))
        term2 <- expectRight (parseEqTerm "x + y")
        let noAddEnv = Map.delete "plus" (Map.delete "add" arithEnv)
        assertBool "missing add rejected" (isLeft (renameTerm @2 noAddEnv locals term2))
    , testCase "function schema parsing, elaboration, and instantiation" $ do
        eqs <-
          expectRight
            ( parseEquations
                "myMu {P} 0 x = 0; myMu {P} (S n) x = if myMu P n x < n then myMu P n x else if P n x then n else S n"
            )
        fam <- expectRight (elaborateFamilyWith id (signatureEnv PR.arithmetic) eqs)
        case Map.lookup "myMu" (familySchemas fam) of
          Nothing -> assertFailure "schema 'myMu' not found in familySchemas"
          Just muSchema -> do
            inst <- expectRight (instantiateSchemaFunction muSchema (F.SomeFunction PR.lt))
            case inst of
              F.SomeFunction (muLt :: F.Function n) -> case testEquality (sNat @n) (sNat @2) of
                Just Refl -> do
                  kernel <- expectRight (Sig.signatureKernelEnv PR.arithmetic)
                  case SV.fromList' [3, 2] of
                    Nothing -> assertFailure "bad vector"
                    Just vec -> F.evalFunction kernel muLt vec @?= Right 0
                  case SV.fromList' [3, 0] of
                    Nothing -> assertFailure "bad vector"
                    Just vec -> F.evalFunction kernel muLt vec @?= Right 3
                Nothing -> assertFailure "unexpected instantiated function arity"
    ]
  where
    range = [0 .. 4] :: [Natural]

compilerEnv :: Env
compilerEnv = signatureEnv (Sig.signature [Sig.symbol "plus" plus])

compileProgram :: T.Text -> IO (Map.Map T.Text ElaboratedDefinition)
compileProgram source = expectRight (parseEquations source >>= elaborateEquations compilerEnv)

checkValues :: Map.Map T.Text ElaboratedDefinition -> T.Text -> [([Natural], Natural)] -> Assertion
checkValues defs ident examples = case Map.lookup ident defs of
  Nothing -> assertFailure ("missing definition " <> T.unpack ident)
  Just def -> case definitionCode def of
    SomeProgram code ->
      mapM_
        ( \(inputs, expected) -> case SV.fromList' inputs of
            Nothing -> assertFailure "test input arity mismatch"
            Just xs -> F.evalFunction kernel (F.Inline code) xs @?= Right expected
        )
        examples
  where
    kernel =
      either error id $
        F.extendKernelEnv
          F.emptyKernelEnv
          [F.Definition (F.DefId name) code | (name, ElaboratedDefinition _ code _ _ _) <- Map.toList defs]

chosenArgument :: Map.Map T.Text ElaboratedDefinition -> T.Text -> Maybe Natural
chosenArgument defs ident = case Map.lookup ident defs of
  Just (ElaboratedDefinition _ _ _ _ index) -> fmap ordToNatural index
  Nothing -> Nothing

rejectProgram :: T.Text -> String -> Assertion
rejectProgram source message = case parseEquations source >>= elaborateEquations compilerEnv of
  Left err -> assertBool err (message `isInfixOf` err)
  Right _ -> assertFailure ("accepted invalid definition: " <> T.unpack source)
