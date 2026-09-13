{-# LANGUAGE OverloadedStrings #-}

-- | The grammar and the layout of the surface language, on the examples of @test/data@.
module Language.Praxis.Surface.ParserTest (parserTests) where

import Data.Text (Text)
import Data.Text.IO qualified as TIO
import Language.Praxis.Surface.Lexer (renderSyntaxError)
import Language.Praxis.Surface.Parser
import Language.Praxis.Surface.Syntax.Raw
import Test.Tasty
import Test.Tasty.HUnit

parserTests :: TestTree
parserTests =
  testGroup
    "parser"
    [ testCase "the List example: declarations in order" $ do
        m <- parseFile "test/data/list.px"
        unLocated (moduleName m) @?= QName [Ident "Data"] (Ident "List")
        map (declKind . unLocated) (moduleDecls m)
          @?= ["data", "signature", "clause", "clause", "fixity", "signature", "clause", "clause", "signature", "clause"]
    , testCase "an infix constructor, and the fixity with a rational precedence" $ do
        m <- parseFile "test/data/list.px"
        case map unLocated (moduleDecls m) of
          DData d : _ -> map (unLocated . constructorName . unLocated) (dataConstructors d) @?= [Ident "Nil", Op ":"]
          _ -> assertFailure "no data declaration first"
        case [(a, p, map unLocated ops) | DFixity a p ops <- map unLocated (moduleDecls m)] of
          [(AssocRight, 4, ["<>"])] -> pure ()
          other -> assertFailure ("fixity: " <> show other)
    , testCase "identifiers with dashes, and a qualified member of an operator's namespace" $ do
        m <- parseFile "test/data/list.px"
        [n | DSignature (Located _ n) _ <- map unLocated (moduleDecls m)] @?= [Op "<>", Ident "append-nil", Ident "append-nil-tactically"]
        case [unLocated r | DClause (Clause _ r) <- map unLocated (moduleDecls m)] of
          _ : _ : RExpr (Located _ (EName q)) : _ -> q @?= QName [Op "<>"] (Ident "unfold-Nil")
          other -> assertFailure ("the third clause: " <> show (take 3 other))
    , testCase "a calculation laid out after calc, its last step justified by a tactic" $ do
        m <- parseFile "test/data/list.px"
        case [unLocated r | DClause (Clause _ r) <- map unLocated (moduleDecls m)] of
          _ : _ : _ : RCalc c : _ -> do
            length (calcSteps c) @?= 2
            case map (stepProof . unLocated) (calcSteps c) of
              [Nothing, Just (Located _ (RBy [Located _ (TCong (Just _))]))] -> pure ()
              other -> assertFailure ("steps: " <> show other)
          other -> assertFailure ("the fourth clause: " <> show (take 4 other))
    , testCase "a tactic block: induction, then a focused block per goal, a calculation on its own lines" $ do
        m <- parseFile "test/data/list.px"
        case [unLocated r | DClause (Clause _ r) <- map unLocated (moduleDecls m)] of
          [_, _, _, _, RBy tacs] -> case map unLocated tacs of
            [TInduction (Located _ "xs") [] Nothing, TFocus [Located _ TRefl], TFocus [Located _ (TIntros ns), Located _ (TCalc c)]] -> do
              map unLocated ns @?= ["x", "xs"]
              length (calcSteps c) @?= 2
            other -> assertFailure ("tactics: " <> show other)
          other -> assertFailure ("clauses: " <> show (length other))
    , testCase "the FOL example: constructors, operators among them" $ do
        m <- parseFile "test/data/fol.px"
        let ctors = [(unLocated (dataName d), map (unLocated . constructorName . unLocated) (dataConstructors d)) | DData d <- map unLocated (moduleDecls m)]
        ctors
          @?= [ ("Void", [])
              , ("RingE", [Ident "Neg", Op ":+", Op ":*"])
              , ("RingR", [Op ":="])
              , ("ZFR", [Ident "Member"])
              , ("Term", [Ident "FVar", Ident "BVar", Ident "App"])
              , ("Formula", [Ident "Var", Ident "Rel", Ident "Not", Op ":/\\", Op ":\\/", Op ":=>", Ident "Forall", Ident "Exists"])
              ]
    , testCase "binary minus needs spaces; a dash joins an identifier" $ do
        expr "x-y" @?= EName (QName [] (Ident "x-y"))
        case expr "x - y" of
          EOps [Operand _, InfixOp (Located _ (Operator (QName [] (Op "-")) False)), Operand _] -> pure ()
          other -> assertFailure (show other)
    , testCase "a bounded quantifier, with a comma or a spaced dot" $ do
        case expr "∀ i < n, i < m" of
          EQuant Forall [Binder False [Located _ "i"] Nothing] (Just _) _ -> pure ()
          other -> assertFailure (show other)
        case expr "∃ i < n. P i" of
          EQuant Exists _ (Just _) _ -> pure ()
          other -> assertFailure (show other)
    , testCase "a binder before an arrow, a cons pattern otherwise" $ do
        case expr "(xs : List a) -> xs ≡ xs" of
          EPi (Binder False [Located _ "xs"] (Just _)) _ -> pure ()
          other -> assertFailure (show other)
        case expr "(x : xs) <> ys" of
          EOps (Operand (Located _ (EParen _)) : _) -> pure ()
          other -> assertFailure (show other)
    , testCase "an offside token ends the item" $
        case parseModule "<test>" "f x = x\ng y = y\n" of
          Right m -> length (moduleDecls m) @?= 2
          Left err -> assertFailure (renderSyntaxError err)
    ]

parseFile :: FilePath -> IO Module
parseFile path = do
  src <- TIO.readFile path
  either (assertFailure . renderSyntaxError) pure (parseModule path src)

-- | The expression of a one-clause module, @e = 0@.
expr :: Text -> Expr
expr src = case parseModule "<test>" ("x = " <> src) of
  Right (Module _ [Located _ (DClause (Clause _ (Located _ (RExpr (Located _ e)))))]) -> e
  Right m -> error ("not one clause: " <> show m)
  Left err -> error (renderSyntaxError err)

declKind :: Decl -> String
declKind = \case
  DOpen {} -> "open"
  DData {} -> "data"
  DFixity {} -> "fixity"
  DSignature {} -> "signature"
  DClause {} -> "clause"
