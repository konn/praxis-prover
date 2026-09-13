{-# LANGUAGE OverloadedStrings #-}

{- |
Coverage for schemas of several parameters, each of an arity of its own:
their elaboration and instances, the refusal of a recursion changing a
parameter, their symbols in a compiled signature, and derived rules over
abstract functions standing as their parameters.
-}
module Language.Praxis.PRA.SchemaTest (schemaTests) where

import Control.Exception (displayException)
import Data.Map.Strict qualified as Map
import Data.Sized qualified as SV
import Data.Text qualified as T
import Language.Praxis.PRA.Library (libraryScope)
import Language.Praxis.PRA.PrimitiveRecursion qualified as PR
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration qualified as E
import Language.Praxis.PRA.PrimitiveRecursion.Environment (CompiledEnv, compileDefinitions, compiledEnvironment, environmentSignature, extendEnvironment)
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.Signature qualified as Sig
import Language.Praxis.PRA.Syntax.Parser (parseFormula, plainScope)
import Language.Praxis.PRA.Syntax.Pretty (renderFormula)
import Language.Praxis.PRA.Tactic (Lemma (..), signatureEnv)
import Language.Praxis.PRA.Tactic.Parser (Decl (..), parseDeclsIn)
import Language.Praxis.PRA.Tactic.Quote (checkDecl, renderSchemaTacticError, schemaScope)
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit

-- | A schema whose first parameter is binary and whose second is unary.
mixSource :: T.Text
mixSource = "mix {F, G} 0 x = G x; mix {F, G} (S n) x = F n (mix {F} {G} n x)"

schemaTests :: TestTree
schemaTests =
  testGroup
    "schemas of several parameters"
    [ testCase "each parameter has the arity of its first application, and is substituted at it" $ do
        eqs <- expectRight (E.parseEquations mixSource)
        fam <- expectRight (E.elaborateFamilyWith id (E.signatureEnv PR.builtin) eqs)
        sch <- maybe (assertFailure "no schema mix") pure (Map.lookup "mix" (E.familySchemas fam))
        E.compiledSchemaParams sch @?= ["F", "G"]
        E.compiledSchemaParamArities sch @?= [2, 1]
        add <- builtinFunction "add"
        mixed <- expectRight (E.instantiateSchemaFunction sch [add, successor])
        kernel <- expectRight (Sig.signatureKernelEnv PR.builtin)
        -- mix {add} {S} n x: x + 1, and then n - 1, …, 0 added to it.
        evalSome kernel mixed [3, 0] >>= (@?= Right 4)
        evalSome kernel mixed [3, 5] >>= (@?= Right 9)
        swapped <- expectLeft (E.instantiateSchemaFunction sch [successor, add])
        swapped @?= E.SchemaParameterArityMismatch "mix" 2 1
    , testCase "a schema recurs at its own parameters, unchanged and in order, and uses each" $ do
        rejects "swap {F, G} 0 x = F x (G x); swap {F, G} (S n) x = swap {G} {F} n x" (E.SchemaRecursionChangesParameters "swap" ["F", "G"])
        rejects "less {F, G} 0 x = F x (G x); less {F, G} (S n) x = less {F} n x" (E.SchemaAppliedWithoutParameter "less" ["F", "G"])
        rejects "konst {F, G} x = F x" (E.SchemaParameterUnused "konst" "G")
    , testCase "a compiled schema is a symbol of the signature, applied in a later block" $ do
        env <- mixEnvironment
        let sig = environmentSignature env
        sym <- maybe (assertFailure "no schema symbol mix") pure (Sig.lookupSchema "mix" sig)
        Sig.schemaSymbolParamArities sym @?= [2, 1]
        Sig.schemaSymbolArity sym @?= 2
        add <- builtinFunction "add"
        kernel <- expectRight (Sig.signatureKernelEnv sig)
        mixed <- expectRight (Sig.applySchemaSymbol sym [add, successor])
        evalSome kernel mixed [3, 5] >>= (@?= Right 9)
        few <- expectLeft (Sig.applySchemaSymbol sym [add])
        few @?= Sig.SchemaParameterCountMismatch "mix" 2 1
        swapped <- expectLeft (Sig.applySchemaSymbol sym [successor, add])
        swapped @?= Sig.SchemaParameterArityMismatch "mix" 2 1
        later <- expectRight (E.parseEquations "useMix n = mix {add} {S} n 0")
        block <- expectRight (compileDefinitions env later)
        env' <- expectRight (extendEnvironment env block)
        use <- maybe (assertFailure "no symbol useMix") pure (Sig.lookupSymbol "useMix" (environmentSignature env'))
        kernel' <- expectRight (Sig.signatureKernelEnv (environmentSignature env'))
        evalSome kernel' (Sig.symbolFunction use) [3] >>= (@?= Right 4)
    , testCase "an instance reads back as it is written" $ do
        sig <- environmentSignature <$> mixEnvironment
        f <- either (assertFailure . displayException) pure (parseFormula (plainScope sig) "mix {add} {S} n x = 0")
        renderFormula sig id f @?= "mix {add} {S} n x = 0"
    , testCase "rules over abstract functions of two arities, the parameters of one schema, are appealed to at functions of the signature" $ do
        sig <- environmentSignature <$> mixEnvironment
        certifiesIn
          sig
          [ "rule mixZero (a b : var) (x : term) (Γ : ctx) (f(a, b) : term) (g(a) : term) : Γ |- mix {f} {g} 0 x = g(x) by refl"
          , "rule mixStep (a b : var) (n x : term) (Γ : ctx) (f(a, b) : term) (g(a) : term) : Γ |- mix {f} {g} (S n) x = f n (mix {f} {g} n x) by refl"
          , "theorem mixAddZero : |- mix {add} {S} 0 y = S y by exact mixZero"
          , "theorem mixAddStep : |- mix {add} {S} (S m) y = add m (mix {add} {S} m y) by exact mixStep"
          , -- Backwards: the side applying an abstract function is matched after the schema instance binds it.
            "theorem mixAddBack : |- add m (mix {add} {S} m y) = mix {add} {S} (S m) y by cong mixStep"
          ]
    ]

-- | 'builtin' extended by 'mixSource'.
mixEnvironment :: IO CompiledEnv
mixEnvironment = do
  eqs <- expectRight (E.parseEquations mixSource)
  let initial = compiledEnvironment PR.builtin
  block <- expectRight (compileDefinitions initial eqs)
  expectRight (extendEnvironment initial block)

-- | Every declaration certified in turn over the library, each a lemma for those after it.
certifiesIn :: Sig.Signature -> [String] -> Assertion
certifiesIn sig srcs = do
  env <- either (assertFailure . displayException) pure (signatureEnv sig)
  scope <- either assertFailure pure libraryScope
  decls <- either (assertFailure . displayException) pure (parseDeclsIn (Map.map (map snd . lemmaMetas) scope) (schemaScope sig) (unlines srcs))
  let go _ [] = pure ()
      go known (d : ds) = case checkDecl env known d of
        Right (_, lemma) -> go (Map.insert (declName d) lemma known) ds
        Left err -> assertFailure (declName d <> ": " <> renderSchemaTacticError sig err)
  go scope decls

rejects :: T.Text -> E.ElaborationError -> Assertion
rejects source expected = do
  eqs <- expectRight (E.parseEquations source)
  err <- expectLeft (E.elaborateEquations (E.signatureEnv PR.builtin) eqs)
  err @?= expected

builtinFunction :: String -> IO F.SomeFunction
builtinFunction n = maybe (assertFailure ("no symbol " <> n)) (pure . Sig.symbolFunction) (Sig.lookupSymbol n PR.builtin)

successor :: F.SomeFunction
successor = F.SomeFunction (F.Primitive PR.Succ)

evalSome :: F.KernelEnv -> F.SomeFunction -> [Natural] -> IO (Either F.KernelError Natural)
evalSome env (F.SomeFunction f) inputs = case SV.fromList' inputs of
  Just xs -> pure (F.evalFunction env f xs)
  Nothing -> assertFailure "input arity mismatch"

expectRight :: (Show e) => Either e a -> IO a
expectRight = either (assertFailure . show) pure

expectLeft :: Either e a -> IO e
expectLeft = either pure (const (assertFailure "unexpectedly accepted"))
