{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.Praxis.PRA.PRFQuoteTest (prfQuoteTests) where

import Control.Monad (forM_, unless)
import Data.Either (isLeft)
import Data.Hashable (hash)
import Data.List (sort)
import Data.Sized qualified as SV
import Data.Text qualified as T
import Data.Type.Ordinal (Ordinal)
import Language.Haskell.TH (recover)
import Language.Haskell.TH.Quote (quoteDec, quoteExp, quotePat, quoteType)
import Language.Haskell.TH.Syntax (lift, liftTyped)
import Language.Praxis.PRA.Equality
import Language.Praxis.PRA.PRFQuoteSupport
import Language.Praxis.PRA.PrimitiveRecursion (mu)
import Language.Praxis.PRA.PrimitiveRecursion qualified as PR
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration
import Language.Praxis.PRA.PrimitiveRecursion.Environment
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.PrimitiveRecursion.Quote (prf)
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.Signature qualified as Sig
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Syntax.Parser (parseTerm, plainScope)
import Language.Praxis.PRA.Syntax.Pretty (renderTerm)
import Language.Praxis.PRA.Tactic.Quote (pra)
import Test.Tasty
import Test.Tasty.HUnit

-- Consecutive declaration quotes, with no intervening declaration splice.
[prf|
  environment basic
  plus n 0 = n
  plus n (S m) = S (plus n m)
|]

[prf|
  environment extended extends basic
  times n 0 = 0
  times n (S m) =
    plus n
         (times n m)
|]

[prf|
  environment branch extends basic
  doubled n = plus n n
|]

[prf|
  answer = later 6
  later n = n
|]

[builtinPRF|
  environment imported
  cube n = pow n 3
|]

[builtinPRF|
  environment schemaEnv

  opExpr a b c = a + b * c
  condExpr a b = if a < b then a else b
|]

[rawPRF|
  environment lifted
  liftedPower n m = rawPower n m
  liftedZero = rawZero
  liftedIdentity n = rawIdentity n
|]

[pra|
  theorem productExample : |- mul 3 4 = 12
  by refl

  theorem additionZero : |- add n 0 = n
  by refl
|]

-- These are real compiler-stage failures, rather than runtime parser tests.
-- A cycle accepted by quoteDec makes this test module fail to compile.
$( do
     forM_
       [ "f x = g x; g x = f x"
       , "f x = g x; g x = h x; h x = f x"
       , "f 0 = 0; f (S n) = g n; g n = f n"
       , "f 0 = 0; f (S n) = f (S n)"
       , "f x = missing x"
       , "f x = S x x"
       , "f 0 = 0"
       , "f x = 0; f 0 = 1"
       , "f x x = x"
       , "f x = x; f x y = x"
       , "environment child extends missing; f x = x"
       , "environment duplicate extends basic; plus x y = x"
       , "environment basic; f x = x"
       ]
       ( \source -> do
           rejected <- recover (pure True) (quoteDec prf source >> pure False)
           unless rejected (fail ("prf accepted invalid declarations: " <> source))
       )
     forM_ [quoteExp prf "f x = x" >> pure (), quotePat prf "f x = x" >> pure (), quoteType prf "f x = x" >> pure ()] $ \action -> do
       rejected <- recover (pure True) (action >> pure False)
       unless rejected (fail "prf accepted an unsupported quote context")
     pure []
 )

prfQuoteTests :: TestTree
prfQuoteTests =
  testGroup
    "PRF quotes and shared definitions"
    [ testCase "derived Lift preserves bare codes in typed and untyped splices" $ do
        $(lift rawLiftFixture) @?= rawLiftFixture
        $$(liftTyped rawLiftFixture) @?= rawLiftFixture
    , testCase "derived Lift preserves shared calls and residual programs" $ do
        $(lift sharedLiftFixture) @?= sharedLiftFixture
        $$(liftTyped sharedLiftFixture) @?= sharedLiftFixture
        $$(liftTyped (F.Inline sharedLiftFixture)) @?= F.Inline sharedLiftFixture
        $$(liftTyped PR.pow) @?= PR.pow
    , testCase "derived Lift retains nullary and hidden composition arities" $ do
        $$(liftTyped (PR.Comp (PR.Zero :: PR.PRFCode 0) SV.Nil :: PR.PRFCode 3))
          @?= (PR.Comp (PR.Zero :: PR.PRFCode 0) SV.Nil :: PR.PRFCode 3)
    , testCase "typed Lift preserves ordinal bounds and sized vector lengths" $ do
        show $(lift (6 :: Ordinal 7)) @?= show (6 :: Ordinal 7)
        $(lift (6 :: Ordinal 7)) @?= (6 :: Ordinal 7)
        $$(liftTyped (6 :: Ordinal 7)) @?= (6 :: Ordinal 7)
        $(lift (SV.Nil :: PR.V 0 Int)) @?= (SV.Nil :: PR.V 0 Int)
        $$(liftTyped (SV.Nil :: PR.V 0 Int)) @?= (SV.Nil :: PR.V 0 Int)
        $$(liftTyped (3 SV.:< SV.Nil :: PR.V 1 Int)) @?= (3 SV.:< SV.Nil :: PR.V 1 Int)
    , testCase "quoted signatures preserve named raw codes and unnamed arities" $ do
        env <- expectRight (Sig.signatureKernelEnv lifted)
        F.evalFunction env liftedPower (3 SV.:< 4 SV.:< SV.Nil) @?= Right 81
        F.evalFunction env liftedZero SV.Nil @?= Right 0
        F.evalFunction env liftedIdentity (7 SV.:< SV.Nil) @?= Right 7
    , testCase "incremental environments evaluate arithmetic" $ do
        env <- expectRight (Sig.signatureKernelEnv extended)
        forM_ [0 .. 4] $ \n -> forM_ [0 .. 4] $ \m -> do
          F.evalFunction env plus (n SV.:< m SV.:< SV.Nil) @?= Right (n + m)
          F.evalFunction env times (n SV.:< m SV.:< SV.Nil) @?= Right (n * m)
    , testCase "parent and sibling snapshots are independent" $ do
        Sig.lookupSymbol "times" basic @?= Nothing
        Sig.lookupSymbol "times" branch @?= Nothing
        env <- expectRight (Sig.signatureKernelEnv branch)
        F.evalFunction env doubled (7 SV.:< SV.Nil) @?= Right 14
    , testCase "headerless forward references expose a signature" $ do
        env <- expectRight (Sig.signatureKernelEnv answerSignature)
        F.evalFunction env answer SV.Nil @?= Right 6
        Sig.symbols answerSignature @?= Sig.symbols laterSignature
    , testCase "imported definitions and qualified Haskell names survive staging" $ do
        env <- expectRight (Sig.signatureKernelEnv imported)
        F.evalFunction env cube (4 SV.:< SV.Nil) @?= Right 64
        F.evalFunction env PR.mul (4 SV.:< 5 SV.:< SV.Nil) @?= Right 20
    , testCase "function schema and operator desugaring in prf quasiquotes" $ do
        env <- expectRight (Sig.signatureKernelEnv schemaEnv)
        F.evalFunction env opExpr (2 SV.:< 3 SV.:< 4 SV.:< SV.Nil) @?= Right 14
        F.evalFunction env condExpr (2 SV.:< 5 SV.:< SV.Nil) @?= Right 2
        F.evalFunction env condExpr (5 SV.:< 2 SV.:< SV.Nil) @?= Right 2
        let muLt = mu PR.lt
        F.evalFunction env muLt (3 SV.:< 2 SV.:< SV.Nil) @?= Right 0
        F.evalFunction env muLt (3 SV.:< 0 SV.:< SV.Nil) @?= Right 3
        builtinKernel <- expectRight (Sig.signatureKernelEnv PR.builtin)
        F.evalFunction builtinKernel PR.projW (0 SV.:< SV.Nil) @?= Right 0
        F.evalFunction builtinKernel PR.projW (1 SV.:< SV.Nil) @?= Right 1
        F.evalFunction builtinKernel PR.projW (2 SV.:< SV.Nil) @?= Right 1
        F.evalFunction builtinKernel PR.projW (3 SV.:< SV.Nil) @?= Right 2
        F.evalFunction builtinKernel PR.projW (4 SV.:< SV.Nil) @?= Right 2
        F.evalFunction builtinKernel PR.projW (5 SV.:< SV.Nil) @?= Right 2
        F.evalFunction builtinKernel PR.projW (6 SV.:< SV.Nil) @?= Right 3
    , testCase "term parsing stores a name, not expanded code" $ do
        t <- expectRight (parseTerm (plainScope extended) "times 3 4")
        t @?= App times (Lit 3 SV.:< Lit 4 SV.:< SV.Nil)
        renderTerm extended id t @?= "times 3 4"
        env <- expectRight (Sig.signatureKernelEnv extended)
        evalTermIn env (const 0) t @?= Right 12
        normalizeIn env (Limited 0) t @?= Right t
        forM_ [0 .. 30] $ \fuel -> do
          normalized <- expectRight (normalizeIn env (Limited fuel) t)
          evalTermIn env (const 0) normalized @?= Right 12
        case evalTermIn F.emptyKernelEnv (const 0) t of
          Left (F.UnknownDefinition _) -> pure ()
          other -> assertFailure ("missing environment: " <> show other)
    , testCase "compiled dependency calls remain references" $ do
        env <- expectRight (Sig.signatureKernelEnv extended)
        case times of
          F.Defined ident -> do
            body <- expectRight (F.lookupDefinition env ident)
            assertBool "times refers to plus" (case plus of F.Defined callee -> F.definitionName callee `elem` calls body; _ -> False)
            assertBool "source self recursion became Rec" (F.definitionName ident `notElem` calls body)
          _ -> assertFailure "quote generated an expanded function"
    , testCase "explicit erasure agrees with shared evaluation" $ do
        env <- expectRight (Sig.signatureKernelEnv PR.builtin)
        bare <- expectRight (F.eraseFunction env PR.pow)
        forM_ [0 .. 3] $ \n -> forM_ [0 .. 3] $ \m ->
          F.evalFunction env PR.pow (n SV.:< m SV.:< SV.Nil) @?= Right (PR.evalPRFCode bare (n SV.:< m SV.:< SV.Nil))
    , testCase "named proof conversion uses the supplied PRA environment" $ do
        env <- expectRight (Sig.signatureKernelEnv PR.builtin)
        inferConclusionIn env productExample @?= Right (mempty :|- (App PR.mul (Lit 3 SV.:< Lit 4 SV.:< SV.Nil) === Lit 12) :: Sequent String)
        inferConclusionIn env (additionZero :: Proof String) @?= Right (mempty :|- (App PR.add (Var "n" SV.:< Lit 0 SV.:< SV.Nil) === Var "n"))
        assertBool "the default checker cannot resolve named arithmetic" (isLeft (inferConclusion (productExample :: Proof String)))
    , testCase "distinct identities are not equal merely because their bodies agree" $ do
        let a = App (F.Defined (F.DefId "one" :: F.DefId 0)) SV.Nil :: Term String
            b = App (F.Defined (F.DefId "two" :: F.DefId 0)) SV.Nil :: Term String
        assertBool "name identity" (a /= b)
        let f = F.Defined (F.DefId "unary" :: F.DefId 1)
            x = App f (Lit 1 SV.:< SV.Nil) :: Term String
            y = App f ((PR.Succ :$ (Lit 0 SV.:< SV.Nil)) SV.:< SV.Nil) :: Term String
        x @?= y
        hash x @?= hash y
    , environmentTests
    , layoutTests
    ]

calls :: F.Program n -> [T.Text]
calls (F.Base _) = []
calls (F.Call ident) = [F.definitionName ident]
calls (F.Comp f xs) = calls f <> foldMap calls xs
calls (F.Rec b s) = calls b <> calls s

environmentTests :: TestTree
environmentTests =
  testGroup
    "checked environment"
    [ testCase "reject self, mutual, and longer call cycles without expansion" $
        forM_ [[("a", "a")], [("a", "b"), ("b", "a")], [("a", "b"), ("b", "c"), ("c", "a")]] $ \edges ->
          case F.extendKernelEnv F.emptyKernelEnv [F.Definition (F.DefId x :: F.DefId 1) (F.Call (F.DefId y)) | (x, y) <- edges] of
            Left (F.CyclicDefinitions names) -> sort names @?= sort (map fst edges)
            other -> assertFailure ("cyclic environment: " <> show other)
    , testCase "reject missing references and inconsistent arities" $ do
        F.extendKernelEnv F.emptyKernelEnv [F.Definition (F.DefId "f" :: F.DefId 1) (F.Call (F.DefId "missing"))]
          @?= Left (F.UnknownDefinition "missing")
        F.extendKernelEnv F.emptyKernelEnv [F.Definition (F.DefId "f" :: F.DefId 1) (F.Call (F.DefId "g")), F.Definition (F.DefId "g" :: F.DefId 0) (F.Base PR.Zero)]
          @?= Left (F.DefinitionArityMismatch "g" 1 0)
    , testCase "conflicting signatures cannot change definition meanings" $ do
        a <- expectRight (F.extendKernelEnv F.emptyKernelEnv [F.Definition (F.DefId "f" :: F.DefId 1) (F.Base PR.Zero)])
        b <- expectRight (F.extendKernelEnv F.emptyKernelEnv [F.Definition (F.DefId "f" :: F.DefId 1) (F.Base PR.Succ)])
        Sig.signatureKernelEnv (Sig.withKernelEnv a mempty <> Sig.withKernelEnv b mempty) @?= Left (F.ConflictingDefinitions ["f"])
    , testCase "pure incremental compilation agrees with one family" $ do
        first <- expectRight (parseEquations "add n 0 = n; add n (S m) = S (add n m)")
        second <- expectRight (parseEquations "mul n 0 = 0; mul n (S m) = add n (mul n m)")
        let initial = compiledEnvironment mempty
        a <- expectRight (compileDefinitions initial first >>= extendEnvironment initial)
        b <- expectRight (compileDefinitions a second >>= extendEnvironment a)
        both <- expectRight (compileDefinitions initial (first <> second) >>= extendEnvironment initial)
        environmentSignature b @?= environmentSignature both
        redefinition <- expectLeft (compileDefinitions a first)
        redefinition @?= ElaborationFailure (FunctionAlreadyDefined "add")
    , testCase "repeated calls do not expand the dependency tree" $ do
        let source = T.unlines ("d0 n = n" : ["d" <> T.pack (show i) <> " n = d" <> T.pack (show (i - 1)) <> " (d" <> T.pack (show (i - 1)) <> " n)" | i <- [1 .. 12 :: Int]])
        equations <- expectRight (parseEquations source)
        block <- expectRight (compileDefinitions (compiledEnvironment mempty) equations)
        env <- expectRight (Sig.signatureKernelEnv (blockSignature block))
        assertBool "code size should grow with the source, not the expanded call tree" (sum [programSize code | F.Definition _ code <- F.definitions env] < 200)
    ]

programSize :: F.Program n -> Int
programSize (F.Base _) = 1
programSize (F.Call _) = 1
programSize (F.Comp f xs) = 1 + programSize f + sum (fmap programSize xs)
programSize (F.Rec b s) = 1 + programSize b + programSize s

layoutTests :: TestTree
layoutTests =
  testGroup
    "equation layout"
    [ testCase "the requested Haskell-like example is the semicolon program" $
        parseEquations (T.unlines ["  add n 0 = n", "  add n (S m) = S (add n m)", "", "  mul n 0 = 0", "  mul n (S m) =", "    add n", "        (mul n m)"])
          @?= parseEquations "add n 0 = n; add n (S m) = S (add n m); mul n 0 = 0; mul n (S m) = add n (mul n m)"
    , testCase "blank lines, nested comments, and CRLF preserve layout" $
        parseEquations "  f x = x -- comment\r\n\r\n{- nested {- comment -} -}\r\n  g x =\r\n    f x\r\n"
          @?= parseEquations "f x = x; g x = f x"
    , testCase "parentheses suspend layout and braces require separators" $ do
        parseEquations "  f x = (S\nx)\n  g y = y" @?= parseEquations "f x = S x; g y = y"
        parseEquations "{ f x = x;\n g y =\n y; }" @?= parseEquations "f x = x; g y = y"
        assertBool "explicit separator required" (isLeft (parseEquations "{ f x = x\ng y = y }"))
    , testCase "misindented continuations and declarations are rejected" $
        forM_ ["  f x =\n  x", "  f x = x\n g y = y", "  f x = x\n    g y = y", "f x = x g y = y"] $ \source ->
          assertBool (T.unpack source) (isLeft (parseEquations source))
    ]

expectRight :: (Show e) => Either e a -> IO a
expectRight = either (\err -> assertFailure (show err) >> fail "unexpected Left") pure

expectLeft :: Either e a -> IO e
expectLeft = either pure (const (assertFailure "unexpected Right"))
