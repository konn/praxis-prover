{-# LANGUAGE OverloadedStrings #-}

-- | Dictionary contracts retain both result membership and dependent indices.
module Language.Praxis.Surface.MethodContractTest (methodContractTests) where

import Data.Either (isLeft)
import Data.List (find)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Elab (Item (..), TheoremDef (..), elabModule)
import Language.Praxis.Surface.Engine (Knowledge (..), proveTheorem, theoremStatement)
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Fixity (moduleFixities)
import Language.Praxis.Surface.Mangle (demangle)
import Language.Praxis.Surface.Parser (parseModule)
import Language.Praxis.Surface.Prelude (prelude)
import Language.Praxis.Surface.Rename (renameModule)
import Language.Praxis.Surface.Syntax.Raw (Segment (..))
import Test.Tasty
import Test.Tasty.HUnit

methodContractTests :: TestTree
methodContractTests =
  testGroup
    "dictionary method contracts"
    [ testCase "generic and concrete applications discharge complete method contracts" $ do
        checked <- check
        errors checked @?= []
        let names = checkedTheorems checked
        mapM_
          (\name -> assertBool (T.unpack name <> " was not certified") (name `elem` names))
          ["Methods.generic-again", "Methods.nullary-again", "Methods.concrete", "Methods.decoded-again", "Methods.decoded-law"]
    , testCase "a nullary method's contract states its exact selected cardinality" $ do
        checked <- check
        errors checked @?= []
        (knowledge, _) <- maybe (assertFailure "no checked module") pure (checkedFinal checked)
        theorem <- definition "nullary"
        statement <- either assertFailure pure (theoremStatement (knowMembership knowledge) theorem)
        let text = demangle (T.unlines (checkedCore checked))
        assertBool "no method contract was emitted" ("method_closed_" `T.isInfixOf` text)
        assertBool "the method contract lost its exact vector index" ("Methods.Vec.#idx" `T.isInfixOf` text)
        assertBool "the theorem did not retain its dictionary value" ("v__x23_d" `T.isInfixOf` statement)
    , testCase "class laws retain the exact indices of dependent binders" $ do
        checked <- check
        errors checked @?= []
        (knowledge, _) <- maybe (assertFailure "no checked module") pure (checkedFinal checked)
        theorem <- definition "generic-sized"
        declarations <- either (assertFailure . show) pure (proveTheorem knowledge theorem)
        let generated = demangle (T.unlines (map snd declarations))
        assertBool "the indexed class law was not retained" (PLaw [Ident "Methods", Ident "Sized", Ident "sized-self"] 0 `elem` thmPremises (tdInfo theorem))
        assertBool "the law premise lost its exact binder index" ("Methods.Vec.#idx schema_arg_0" `T.isInfixOf` generated)
        assertBool "the selected dictionary cardinality was lost" ("#d" `T.isInfixOf` generated)
    , testCase "concrete method contracts require a certified membership provider" $ do
        (knowledge, theorem, implementation) <- concrete
        let incomplete = knowledge {knowClosures = Map.delete (funCore implementation) (knowClosures knowledge)}
        assertBool "the implementation's absent membership certificate was ignored" (isLeft (proveTheorem incomplete theorem))
    , testCase "concrete method contracts require certified exact indices" $ do
        (knowledge, theorem, implementation) <- concrete
        let incomplete = knowledge {knowIndexSpecs = Map.delete (funCore implementation) (knowIndexSpecs knowledge)}
        assertBool "the implementation's absent index certificate was ignored" (isLeft (proveTheorem incomplete theorem))
    ]
  where
    check = do
      p <- either assertFailure pure prelude
      pure (checkSource p "method-contracts.px" source)
    concrete = do
      checked <- check
      errors checked @?= []
      (knowledge, _) <- maybe (assertFailure "no checked module") pure (checkedFinal checked)
      theorem <- definition "concrete"
      instanceInfo <- maybe (assertFailure "no Sized Unit instance") pure (Map.lookup ([Ident "Methods", Ident "Sized"], "Methods.Unit") (envInstances (knowEnv knowledge)))
      implementation <- maybe (assertFailure "no stamp implementation") pure (Map.lookup [Ident "Methods", Ident "Sized", Ident "stamp"] (instFunctions instanceInfo))
      case proveTheorem knowledge theorem of
        Left why -> assertFailure (show why)
        Right _ -> pure ()
      pure (knowledge, theorem, implementation)

errors :: Checked -> [Text]
errors checked = [reportMessage report | report <- checkedReports checked, reportSeverity report == SevError]

definition :: Text -> IO TheoremDef
definition name = do
  parsed <- either (assertFailure . show) pure (parseModule "method-contracts.px" source)
  fixities <- either (assertFailure . show) pure (moduleFixities parsed)
  let (renamed, scopeErrors) = renameModule fixities emptyEnv Map.empty [Ident "Methods"] parsed
  assertBool (show scopeErrors) (null scopeErrors)
  let (_, items) = elabModule fixities emptyEnv renamed
  maybe (assertFailure ("missing theorem " <> T.unpack name)) pure (find ((== [Ident "Methods", Ident name]) . thmQual . tdInfo) [theorem | ITheorem theorem <- items])

source :: Text
source =
  T.unlines
    [ "module Methods where"
    , "data Vec (n : Nat) a where"
    , "  Nil : Vec 0 a"
    , "  Cons : {n : Nat} -> a -> Vec n a -> Vec (S n) a"
    , "data Unit = Mk"
    , "class Sized a where"
    , "  card : Nat"
    , "  enumeration : Vec card a"
    , "  stamp : a -> Vec card a"
    , "  decode : Vec card a -> a"
    , "  same : (x : a) -> x = x"
    , "  sized-self : (xs : Vec card a) -> xs = xs"
    , "generic : Sized a => (x : a) -> stamp x = stamp x"
    , "generic x = rfl"
    , "generic-again : Sized a => (x : a) -> stamp x = stamp x"
    , "generic-again x = by exact generic x"
    , "nullary : Sized a => (x : a) -> enumeration = enumeration"
    , "nullary x = rfl"
    , "nullary-again : Sized a => (x : a) -> enumeration = enumeration"
    , "nullary-again x = by exact nullary x"
    , "generic-sized : Sized a => (x : a) -> enumeration = enumeration"
    , "generic-sized x = by exact sized-self enumeration"
    , "decoded : Sized a => (x : a) -> decode enumeration = decode enumeration"
    , "decoded x = rfl"
    , "decoded-again : Sized a => (x : a) -> decode enumeration = decode enumeration"
    , "decoded-again x = by exact decoded x"
    , "decoded-law : Sized a => (x : a) -> decode enumeration = decode enumeration"
    , "decoded-law x = by exact same (decode enumeration)"
    , "instance Sized Unit where"
    , "  card = 0"
    , "  enumeration = Nil"
    , "  stamp x = Nil"
    , "  decode xs = Mk"
    , "  same x = rfl"
    , "  sized-self xs = rfl"
    , "concrete : (x : Unit) -> stamp x = stamp x"
    , "concrete x = by exact generic x"
    ]
