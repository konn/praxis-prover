{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.FiniteElaborationTest (finiteElaborationTests) where

import Bound (fromScope, instantiate, instantiate1)
import Control.Monad (forM_)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (absurd)
import Language.Praxis.Surface.Desugar
import Language.Praxis.Surface.Elab
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.FiniteFixtures
import Language.Praxis.Surface.Fixity
import Language.Praxis.Surface.Mangle (mangleGlobal)
import Language.Praxis.Surface.Parser
import Language.Praxis.Surface.Rename
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw (Segment (..))
import Test.Tasty
import Test.Tasty.HUnit

finiteElaborationTests :: TestTree
finiteElaborationTests =
  testGroup
    "finite proposition elaboration"
    [ testCase "direct Fin infers its implicit bound" $ do
        (_, items) <- success (finiteOrdinals <> "q : ∀ (i : Fin n), i = i\nq = rfl\n")
        theorem <- findTheorem "q" items
        thmValues (tdInfo theorem) @?= ["n"]
        numericCount (proposition theorem) @?= Just 1
        assertBool "the numeric bridge was not retained" (any bridge (requirements (tdRequirements theorem)))
    , testCase "finite quantifiers remain nested under connectives and negation" $ do
        (_, items) <- success (finiteOrdinals <> "q : ¬ (∃ (i : Fin 3), i = i) -> ∀ (j : Fin 2), j = j\nq = rfl\n")
        theorem <- findTheorem "q" items
        numericCount (proposition theorem) @?= Just 2
        case stripLocations (proposition theorem) of
          Arrow left right -> do
            numericCount left @?= Just 1
            numericCount right @?= Just 1
          other -> assertFailure ("connective structure changed: " <> show other)
    , testCase "a finite bound can depend on an outer numeric binder" $ do
        (_, items) <- success (finiteOrdinals <> "q : ∀ n < 3, ∀ (i : Fin n), i = i\nq = rfl\n")
        theorem <- findTheorem "q" items
        case stripLocations (proposition theorem) of
          Quant _ _ (Just (Below, limit)) Nothing body -> do
            stripLocations limit @?= Nat 3
            case stripLocations (instantiate1 (Var 42) body) of
              Quant _ _ (Just (Below, innerLimit)) Nothing _ -> stripLocations innerLimit @?= Var 42
              other -> assertFailure (show other)
          other -> assertFailure (show other)
    , testCase "grouped binders freeze their type before shadowing an outer value" $ do
        (_, items) <- success (finiteOrdinals <> "q : (n : Nat) -> ∀ (n m : Fin n), m = m\nq n = rfl\n")
        theorem <- findTheorem "q" items
        case stripLocations (proposition theorem) of
          Quant _ _ (Just (Below, limit)) Nothing body -> do
            stripLocations limit @?= Var 0
            case stripLocations (instantiate1 (Var 42) body) of
              Quant _ _ (Just (Below, innerLimit)) Nothing _ -> stripLocations innerLimit @?= Var 0
              other -> assertFailure (show other)
          other -> assertFailure (show other)
    , testCase "a concrete finite instance lowers to ordinary numeric syntax" $ do
        (_, items) <- success (finitePrelude <> "q : ∃ (x : Bool), x = x\nq = rfl\n")
        theorem <- findTheorem "q" items
        numericCount (proposition theorem) @?= Just 1
        assertBool "instance coverage was not retained" (any coverage (requirements (tdRequirements theorem)))
    , testCase "generic evidence includes proof-only code and membership slots" $ do
        (_, items) <- success (finitePrelude <> "q : Finite a => ∀ (x : a), x = x\nq = rfl\n")
        theorem <- findTheorem "q" items
        numericCount (proposition theorem) @?= Just 1
        assertBool "code was pruned" (any ((== [Ident "FiniteQ", Ident "Finite", Ident "code"]) . slotMethod) (tdSlots theorem))
        assertBool "membership was pruned" (any isMembershipSlot (tdSlots theorem))
    , testCase "numeric quantification rejects a non-Nat written binder type" $ do
        (_, items) <- elaborate (finiteOrdinals <> "q : ∀ (i : Fin 3) < 3, i = i\nq = rfl\n")
        assertBool "the written type was silently ignored" (any failed items)
    , testCase "proof-only dictionaries stay out of the runtime schema" $ do
        (env, _) <- success (finitePrelude <> T.unlines ["ignore : Finite a => a -> (∀ (x : a), x = x) -> Nat", "ignore x h = 0", "again : Finite a => a -> (∀ (x : a), x = x) -> Nat", "again x h = ignore x h"])
        forM_ ["ignore", "again"] $ \name -> case Map.lookup [Ident "FiniteQ", Ident name] (envGlobals env) of
          Just (GFun function) -> do
            funSlots function @?= []
            assertBool "logical evidence was erased" (not (null (funProofSlots function)))
            assertBool "reusable dependencies were erased" (not (null (requirements (funRequirements function))))
          _ -> assertFailure "the function was not elaborated"
    ]
  where
    bridge required = case requirementDependency required of
      CertifiedDeclaration name -> name == mangleGlobal ["FiniteQ", "from-to"]
      _ -> False
    coverage required = case requirementDependency required of
      CertifiedDeclaration name -> name == mangleGlobal ["FiniteQ", "Finite-Bool", "decode-code"]
      _ -> False
    failed IFailed {} = True
    failed _ = False

elaborate :: Text -> IO (Env, [Item])
elaborate source = do
  raw <- either (assertFailure . show) pure (parseModule "finite-elaboration.px" ("module FiniteQ where\n" <> source))
  fixities <- either (assertFailure . show) pure (moduleFixities raw)
  let (renamed, errors) = renameModule fixities emptyEnv Map.empty [Ident "FiniteQ"] raw
  errors @?= []
  pure (elabModule fixities emptyEnv renamed)

success :: Text -> IO (Env, [Item])
success source = do
  result@(_, items) <- elaborate source
  [err | IFailed err <- items] @?= []
  pure result

findTheorem :: Text -> [Item] -> IO TheoremDef
findTheorem name items = case [theorem | ITheorem theorem <- items, thmQual (tdInfo theorem) == [Ident "FiniteQ", Ident name]] of
  [theorem] -> pure theorem
  _ -> assertFailure ("missing theorem " <> T.unpack name)

proposition :: TheoremDef -> Expr Int
proposition = instantiate Var . fmap absurd . tdProp

-- Inspect every expression field, including scopes, types and proof arguments.
-- Nothing means a surviving unbounded or typed surface quantifier.
numericCount :: Expr a -> Maybe Int
numericCount = \case
  Quant _ _ (Just (_, bound)) Nothing body -> (1 +) <$> ((+) <$> numericCount bound <*> numericCount (fromScope body))
  Quant {} -> Nothing
  App f x -> both f x
  At _ value -> numericCount value
  Typed _ _ _ value -> numericCount value
  Dictionary _ value -> numericCount value
  Transport _ value proofs -> sum <$> traverse numericCount (value : proofs)
  SchemaParameter _ _ value -> numericCount value
  SchemaClosure _ value -> numericCount value
  SchemaPacked _ body value -> (+) <$> numericCount (fromScope body) <*> numericCount value
  Lam _ body -> numericCount (fromScope body)
  Case value alternatives -> (+) <$> numericCount value <*> (sum <$> traverse (numericCount . fromScope . snd) alternatives)
  If condition yes no -> sum <$> traverse numericCount [condition, yes, no]
  Pi _ _ domain body -> (+) <$> numericCount domain <*> numericCount (fromScope body)
  Arrow left right -> both left right
  Rel _ left right -> both left right
  Conn _ left right -> both left right
  Not value -> numericCount value
  ProofArg value _ -> numericCount value
  Var _ -> pure 0
  Global _ -> pure 0
  Nat _ -> pure 0
  Top -> pure 0
  Bottom -> pure 0
  Universe -> pure 0
  Hole -> pure 0
  Absurd _ -> pure 0
  where
    both left right = (+) <$> numericCount left <*> numericCount right
