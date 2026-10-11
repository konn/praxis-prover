{-# LANGUAGE OverloadedStrings #-}

-- | Dependent method telescopes keep the value and index from one dictionary.
module Language.Praxis.Surface.DependentClassTest (dependentClassTests) where

import Data.Either (isLeft)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Core qualified as Core
import Language.Praxis.Surface.Elab (ElabError (..), Item (..), elabModule)
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Fixity (moduleFixities)
import Language.Praxis.Surface.Parser (parseModule)
import Language.Praxis.Surface.Prelude (prelude)
import Language.Praxis.Surface.Rename (renameModule)
import Language.Praxis.Surface.Syntax (Expr (..), Ref (..), RefKind (..))
import Language.Praxis.Surface.Syntax.Raw (Segment (..), Span (..))
import Language.Praxis.Surface.Types
import Test.Tasty
import Test.Tasty.HUnit

dependentClassTests :: TestTree
dependentClassTests =
  testGroup
    "dependent class dictionaries"
    [ testCase "method types depend on preceding nullary members" $ do
        (env, items) <- elaborate declaration
        failures items @?= []
        case Map.lookup sized (envGlobals env) of
          Just (GClass cls) -> case classMethods cls of
            [card, enumeration] -> do
              methodDependencies card @?= []
              methodDependencies enumeration @?= [(cardName, TNat)]
              schemeType (methodScheme enumeration) @?= vector (methodIndex cardName)
            _ -> assertFailure "the class did not retain its ordered method telescope"
          _ -> assertFailure "the dependent class was not declared"
    , testCase "a dependent method cannot refer to a later member" $ do
        (_, items) <- elaborate (types <> "class Sized a where\n  enumeration : Vec card a\n  card : Nat\n")
        assertBool "the forward dependency was accepted" (not (null (failures items)))
    , testCase "nullary methods use a determining class dictionary" $ do
        p <- either assertFailure pure prelude
        let checked = checkSource p "dependent.px" (declaration <> "count : Sized a => a -> Nat\ncount x = card\n")
        errors checked @?= []
    , testCase "a nullary method cannot choose between two dictionaries" $ do
        (_, items) <- elaborate (declaration <> "ambiguous : Sized a => Sized b => a -> b -> Nat\nambiguous x y = card\n")
        assertBool "an ambiguous class dictionary was selected" (any ("ambiguous" `T.isInfixOf`) (map T.pack (failures items)))
    , testCase "dictionary result indices refer to the same cardinality value" $ do
        (env, _) <- elaborate declaration
        let slots = [Slot cardName 0 0, Slot enumerationName 0 0]
            value ty = Typed ty [] [] (Global (Ref RefValueParam "1"))
            check = Core.elaborate env slots []
        _ <- either assertFailure pure (check (value (vector (dictionaryIndex 0))))
        assertBool "a forged cardinality was accepted" (isLeft (check (value (vector (IxNat 99)))))
        assertBool "another dictionary value was accepted as cardinality" (isLeft (check (value (vector (dictionaryIndex 1)))))
        assertBool "an absent dependency was silently erased" (isLeft (dictionaryMethodType env [Slot enumerationName 0 0] (Slot enumerationName 0 0)))
    , testCase "dictionary dependencies survive function pruning" $ do
        (env, items) <- elaborate (declaration <> "copy : Sized a => Vec card a\ncopy = enumeration\n")
        failures items @?= []
        case Map.lookup [Ident "Dependent", Ident "copy"] (envGlobals env) of
          Just (GFun function) -> funSlots function @?= [Slot cardName 0 0, Slot enumerationName 0 0]
          _ -> assertFailure "the dependent function was not elaborated"
    , testCase "unfolding supplies a dependent index without local hypotheses" $ do
        p <- either assertFailure pure prelude
        let source bound = declaration <> "data Unit = Mk\ninstance Sized Unit where\n  card = " <> bound <> "\n  enumeration = Nil\n"
        errors (checkSource p "dependent-valid.px" (source "0")) @?= []
        (_, items) <- elaborate (source "0" <> "copy : Sized a => Vec card a\ncopy = enumeration\nunit-copy : Vec 0 Unit\nunit-copy = copy\n")
        failures items @?= []
        assertBool "a false dependent index was accepted" (not (null (errors (checkSource p "dependent-invalid.px" (source "1")))))
    ]
  where
    sized = [Ident "Dependent", Ident "Sized"]
    cardName = sized <> [Ident "card"]
    enumerationName = sized <> [Ident "enumeration"]
    vector index = TData "Dependent.Vec" [TParam 0 []] [index]
    types = "module Dependent where\ndata Vec (n : Nat) a where\n  Nil : Vec 0 a\n  Cons : {n : Nat} -> a -> Vec n a -> Vec (S n) a\n"
    declaration = types <> "class Sized a where\n  card : Nat\n  enumeration : Vec card a\n"

elaborate :: Text -> IO (Env, [Item])
elaborate source = do
  parsed <- either (assertFailure . show) pure (parseModule "dependent.px" source)
  fixities <- either (assertFailure . show) pure (moduleFixities parsed)
  let (renamed, scopeErrors) = renameModule fixities emptyEnv Map.empty [Ident "Dependent"] parsed
  assertBool (show scopeErrors) (null scopeErrors)
  pure (elabModule fixities emptyEnv renamed)

failures :: [Item] -> [String]
failures items = [message | IFailed (ElabError _ message) <- items]

errors :: Checked -> [String]
errors checked = [show line <> ": " <> T.unpack message | Report (Span (line, _) _) SevError message <- checkedReports checked]
