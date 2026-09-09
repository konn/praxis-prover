{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Variadic schemas, lambda parameters and the bounded-search sugar.
module Language.Praxis.PRA.VariadicTest (variadicTests) where

import Control.Monad (forM_, unless)
import Data.Either (isLeft)
import Data.List (find)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Sized qualified as SV
import Data.Text qualified as T
import Language.Haskell.TH (recover)
import Language.Haskell.TH.Quote (quoteDec)
import Language.Praxis.PRA.PRFQuoteSupport (arithPRF)
import Language.Praxis.PRA.PrimitiveRecursion (mu)
import Language.Praxis.PRA.PrimitiveRecursion qualified as PR
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration
import Language.Praxis.PRA.PrimitiveRecursion.Environment
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.PrimitiveRecursion.Quote (prf)
import Language.Praxis.PRA.Signature qualified as Sig
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit

-- A variadic schema of its own, lambda parameters, and the sugar, all in a
-- quote extending the arithmetic library.
[arithPRF|
  environment searchEnv

  count {P} 0 $[xs] = 0
  count {P} (S n) $[xs] = count {P} n $[xs] + sgn (P n $[xs])

  above3 = count {λ i. 3 < i} 10
  belowArg a = count {λ i a. i < a} 10 a
  rootSugar z = μ i < S z. z < triangle (i + 1)
  nestedSugar x = μ i < x. x < i + (μ j < x. 2 < j)
|]

[arithPRF|
  environment searchUse extends searchEnv
  countUse = count {λ i. 3 < i} 10
  muUse a b = mu {λ i a b. a + b < i} 10 a b
|]

-- Compile-time rejections: each source must fail inside quoteDec.
$( do
     forM_
       [ "f {P} n $[xs] = P n"
       , "f {P} n $[xs] = P $[xs] $[xs]"
       , "f n $[xs] = n"
       , "f {P} n $[xs] = f {P} n 0 $[xs] + P n $[xs]"
       , "f x = $[xs]"
       , "g x = x; f x = g (λ i. i)"
       ]
       ( \source -> do
           rejected <- recover (pure True) (quoteDec prf source >> pure False)
           unless rejected (fail ("prf accepted an invalid variadic declaration: " <> source))
       )
     pure []
 )

variadicTests :: TestTree
variadicTests =
  testGroup
    "variadic schemas and binders"
    [ parserTests
    , elaborationTests
    , quoteTests
    ]

parserTests :: TestTree
parserTests =
  testGroup
    "parsing"
    [ testCase "lambda and bounded-search binders are locally nameless" $ do
        parseEqTerm "λ i z. z < triangle (i + 1)"
          @?= Right (LamET ["i", "z"] (InfixET (BoundET 0 1) "<" (NameET "triangle" :@ InfixET (BoundET 0 0) "+" (LitET 1))))
        parseEqTerm "\\i z -> z" @?= parseEqTerm "λ a b. b"
        parseEqTerm "μ i < z. z < triangle (i + 1)"
          @?= Right (MuET "i" (NameET "z") (InfixET (NameET "z") "<" (NameET "triangle" :@ InfixET (BoundET 0 0) "+" (LitET 1))))
        parseEqTerm "λ x. μ i < x. x" @?= Right (LamET ["x"] (MuET "i" (BoundET 0 0) (BoundET 1 0)))
        parseEqTerm "mu {λ i. i} n" @?= Right (NameET "mu" :@ LamET ["i"] (BoundET 0 0) :@ NameET "n")
    , testCase "variadic groups are parsed at the ends of a head and as arguments" $ do
        parseEquation "muN {P} 0 $[xs] = 0" @?= Right (Equation "muN" ["P"] [ZeroP] (Just (Splat "xs" SplatLast)) (LitET 0))
        parseEquation "f {P} $[xs] n = P n $[xs]"
          @?= Right (Equation "f" ["P"] [VarP "n"] (Just (Splat "xs" SplatFirst)) (NameET "P" :@ NameET "n" :@ SplatET "xs"))
        assertBool "a group in the middle" (isLeft (parseEquation "f {P} a $[xs] b = 0"))
        assertBool "two groups" (isLeft (parseEquation "f {P} $[xs] $[ys] = 0"))
    ]

elaborationTests :: TestTree
elaborationTests =
  testGroup
    "elaboration"
    [ testCase "a variadic schema is instantiated at each applied number of arguments" $ do
        eqs <- expectRight (parseEquations muNSource)
        fam <- expectRight (elaborateFamilyWith id (signatureEnv PR.arithmetic) eqs)
        Map.keys (familyVariadics fam) @?= ["muN"]
        Map.keys (familySchemas fam) @?= []
        let defs = familyDefinitions fam
        checkValues defs "root0" [([], 4)]
        checkValues defs "root2" [([a, b], a + b + 1) | a <- range, b <- range]
        checkValues defs "sameAsMu" [([z], search z (\i -> z < triangle (i + 1))) | z <- range]
    , testCase "the imported variadic mu is instantiated at any arity" $ do
        eqs <-
          expectRight
            ( parseEquations
                "w z = mu {λ i z. z < triangle (i + 1)} z z; u = mu {λ i. 3 < i} 10; v a b = mu {λ i a b. a + b < i} 10 a b"
            )
        defs <- expectRight (elaborateEquations (signatureEnv PR.arithmetic) eqs)
        checkValues defs "w" [([z], search z (\i -> z < triangle (i + 1))) | z <- range]
        checkValues defs "u" [([], 4)]
        checkValues defs "v" [([a, b], a + b + 1) | a <- range, b <- range]
    , testCase "a bounded search captures pattern variables and enclosing binders" $ do
        eqs <-
          expectRight
            ( parseEquations
                "w z = μ i < z. z < triangle (i + 1); u = μ i < 10. 3 < i; v a b = μ i < 10. a + b < i; t x = μ i < x. x < i + (μ j < x. 2 < j)"
            )
        defs <- expectRight (elaborateEquations (signatureEnv PR.arithmetic) eqs)
        checkValues defs "w" [([z], search z (\i -> z < triangle (i + 1))) | z <- range]
        checkValues defs "u" [([], 4)]
        checkValues defs "v" [([a, b], a + b + 1) | a <- range, b <- range]
        checkValues defs "t" [([x], nested x) | x <- [0 .. 12]]
    , testCase "lambdas must be closed, non-recursive, and schema parameters of the right arity" $
        mapM_
          (uncurry rejectProgram)
          [ ("w z = mu {λ i y. z < i} z z", LambdaCapturesVariable "z")
          , ("w z = mu {λ i y. mu {λ j x. i < x} y y} z z", LambdaCapturesBinder)
          , ("f 0 = 0; f (S n) = mu {λ i. f 0 < i} n", NoRecursionArgument "f" [(0, RecursiveCallInLambda "f")])
          , ("g x = add (λ i. i) x", LambdaOutsideSchemaParameter)
          , ("h x = mu {λ i. i} x x", LambdaArityMismatch "mu@1" 2 1)
          , ("k x = (λ i. i) x", InvalidApplicationHead (LamET ["i"] (BoundET 0 0)))
          ]
    , testCase "variadic templates are checked at every number of arguments" $ do
        mapM_
          (uncurry rejectProgram)
          [ ("bad {P} n $[xs] = P n $[xs] + add $[xs]", ArityMismatch "add" 2 0)
          , ("grow {P} n $[xs] = grow {P} n 0 $[xs] + P n $[xs]", VariadicRecursionChangesArity "grow" 0 1)
          , ("noP {P} n $[xs] = P n", VariadicParameterGroupMismatch "noP" "P" "xs" 0)
          , ("unused {P} n $[xs] = n", VariadicParameterUnapplied "unused" "P" "xs")
          , ("twice {P} n $[xs] = P $[xs] $[xs]", VariadicParameterGroupMismatch "twice" "P" "xs" 2)
          , ("plain n $[xs] = n", VariadicWithoutParameter "plain")
          , ("f x = $[xs]", SplatOutsideArgument "xs")
          , ("f x = add x $[xs]", SplatOutsideVariadicSchema "xs")
          , ("few {P} a b $[xs] = P a b $[xs]; use = few {sgn} 1", TooFewVariadicArguments "few" 2 2)
          ]
        muless <- expectRight (parseEquations "u = μ i < 10. i")
        noMu <- expectLeft (elaborateEquations (signatureEnv mempty) muless)
        noMu @?= BoundedSearchOutOfScope
    , testCase "compiled variadic symbols instantiate at run time like the inlined instances" $ do
        eqs <- expectRight (parseEquations muNSource)
        let initial = compiledEnvironment PR.arithmetic
        block <- expectRight (compileDefinitions initial eqs)
        env <- expectRight (extendEnvironment initial block)
        kernel <- expectRight (Sig.signatureKernelEnv (environmentSignature env))
        sym <- maybe (assertFailure "muN is not a variadic symbol") pure (Sig.lookupVariadicSchema "muN" (environmentSignature env))
        Sig.variadicSchemaFixedArity sym @?= 1
        Sig.variadicSchemaParamArity sym @?= 1
        inst <- expectRight (Sig.instantiateVariadicSchemaSymbol sym 2)
        Sig.schemaSymbolParamArity inst @?= 3
        Sig.schemaSymbolArity inst @?= 3
        p2 <- maybe (assertFailure "p2") pure (Sig.lookupSymbol "p2" (environmentSignature env))
        p0 <- maybe (assertFailure "p0") pure (Sig.lookupSymbol "p0" (environmentSignature env))
        applied2 <- expectRight (Sig.applyVariadicSchemaSymbol sym (Sig.symbolFunction p2))
        applied0 <- expectRight (Sig.applyVariadicSchemaSymbol sym (Sig.symbolFunction p0))
        evalSome kernel applied2 [10, 2, 3] >>= (@?= Right 6)
        evalSome kernel applied0 [10] >>= (@?= Right 4)
        Sig.applyVariadicSchemaSymbol sym (F.SomeFunction (F.Primitive (PR.Zero :: PR.PRFCode 0)))
          @?= Left (VariadicParameterTooSmall "muN" 1 0)
    ]
  where
    muNSource =
      T.unlines
        [ "muN {P} 0 $[xs] = 0"
        , "muN {P} (S n) $[xs] ="
        , "  if muN {P} n $[xs] < n then muN {P} n $[xs] else if P n $[xs] then n else S n"
        , "p0 i = 3 < i"
        , "p2 i a b = a + b < i"
        , "root0 = muN {p0} 10"
        , "root2 a b = muN {p2} 10 a b"
        , "sameAsMu z = muN {λ i z. z < triangle (i + 1)} z z"
        ]
    nested x =
      let inner = search x (\j -> 2 < j)
       in search x (\i -> x < i + inner)

quoteTests :: TestTree
quoteTests =
  testGroup
    "quotes"
    [ testCase "a quoted variadic schema is a function polymorphic in its parameter's arity" $ do
        env <- expectRight (Sig.signatureKernelEnv searchEnv)
        F.evalFunction env (count PR.lt) (10 SV.:< 4 SV.:< SV.Nil) @?= Right 4
        F.evalFunction env (count PR.sgn) (10 SV.:< SV.Nil) @?= Right 9
        F.evalFunction env above3 SV.Nil @?= Right 6
        forM_ range $ \a -> F.evalFunction env belowArg (a SV.:< SV.Nil) @?= Right a
    , testCase "the library's mu is usable from Haskell at any arity" $ do
        env <- expectRight (Sig.signatureKernelEnv PR.arithmetic)
        F.evalFunction env (mu PR.lt) (3 SV.:< 2 SV.:< SV.Nil) @?= Right 0
        F.evalFunction env (mu PR.sgn) (5 SV.:< SV.Nil) @?= Right 1
        F.evalFunction env (mu PR.sgn) (0 SV.:< SV.Nil) @?= Right 0
    , testCase "the bounded-search sugar agrees with the explicit definition" $ do
        env <- expectRight (Sig.signatureKernelEnv searchEnv)
        forM_ [0 .. 12] $ \z -> do
          F.evalFunction env rootSugar (z SV.:< SV.Nil) @?= F.evalFunction env PR.projW (z SV.:< SV.Nil)
          F.evalFunction env nestedSugar (z SV.:< SV.Nil) @?= Right (let inner = search z (\j -> 2 < j) in search z (\i -> z < i + inner))
    , testCase "a child environment instantiates an inherited variadic schema" $ do
        env <- expectRight (Sig.signatureKernelEnv searchUse)
        F.evalFunction env countUse SV.Nil @?= Right 6
        forM_ range $ \a -> forM_ range $ \b -> F.evalFunction env muUse (a SV.:< b SV.:< SV.Nil) @?= Right (a + b + 1)
        assertBool "the signature records the schema" (Sig.lookupVariadicSchema "count" searchUse /= Nothing)
    , testCase "instances are elaborated from the lifted template" $ do
        sym <- maybe (assertFailure "count") pure (Sig.lookupVariadicSchema "count" searchEnv)
        inst <- expectRight (Sig.instantiateVariadicSchemaSymbol sym 3)
        Sig.schemaSymbolArity inst @?= 4
        env <- expectRight (Sig.signatureKernelEnv searchEnv)
        applied <- expectRight (Sig.applyVariadicSchemaSymbol sym (F.SomeFunction PR.lt))
        evalSome env applied [10, 4] >>= (@?= Right 4)
    ]

range :: [Natural]
range = [0 .. 4]

triangle :: Natural -> Natural
triangle n = n * (n + 1) `div` 2

-- | The least @i < b@ satisfying the predicate, or @b@.
search :: Natural -> (Natural -> Bool) -> Natural
search b p = fromMaybe b (find p (takeWhile (< b) [0 ..]))

evalSome :: F.KernelEnv -> F.SomeFunction -> [Natural] -> IO (Either F.KernelError Natural)
evalSome env (F.SomeFunction f) inputs = case SV.fromList' inputs of
  Just xs -> pure (F.evalFunction env f xs)
  Nothing -> assertFailure "input arity mismatch"

checkValues :: Map.Map T.Text ElaboratedDefinition -> T.Text -> [([Natural], Natural)] -> Assertion
checkValues defs ident examples = do
  arithmeticKernel <- expectRight (Sig.signatureKernelEnv PR.arithmetic)
  kernel <- expectRight (F.extendKernelEnv arithmeticKernel [F.Definition (F.DefId name) code | (name, ElaboratedDefinition _ code _ _ _) <- Map.toList defs])
  case Map.lookup ident defs of
    Nothing -> assertFailure ("missing definition " <> T.unpack ident)
    Just def -> case definitionCode def of
      SomeProgram code ->
        mapM_
          ( \(inputs, expected) -> case SV.fromList' inputs of
              Nothing -> assertFailure "test input arity mismatch"
              Just xs -> F.evalFunction kernel (F.Inline code) xs @?= Right expected
          )
          examples

rejectProgram :: T.Text -> ElaborationError -> Assertion
rejectProgram source expected = do
  equations <- expectRight (parseEquations source)
  case elaborateEquations (signatureEnv PR.arithmetic) equations of
    Left err -> assertEqual (T.unpack source) expected err
    Right _ -> assertFailure ("accepted invalid definition: " <> T.unpack source)

expectRight :: (Show e) => Either e a -> IO a
expectRight = either (\err -> assertFailure (show err) >> fail "unexpected Left") pure

expectLeft :: (Show a) => Either e a -> IO e
expectLeft = either pure (\value -> assertFailure ("unexpected Right: " <> show value) >> fail "unexpected Right")
