{-# LANGUAGE OverloadedStrings #-}

-- | The grammar and the layout of the surface language, on the examples of @test/data@.
module Language.Praxis.Surface.ParserTest (parserTests) where

import Control.Monad (forM_)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Language.Praxis.Surface.Env (emptyEnv)
import Language.Praxis.Surface.Fixity (builtinFixities)
import Language.Praxis.Surface.Lexer (renderSyntaxError)
import Language.Praxis.Surface.Parser
import Language.Praxis.Surface.Rename
import Language.Praxis.Surface.Syntax.Raw
import Test.Tasty
import Test.Tasty.HUnit

parserTests :: TestTree
parserTests =
  testGroup
    "parser"
    [ testCase "the List example: declarations in order" $ do
        m <- parseFile "test/data/list.px"
        fmap unLocated (moduleName m) @?= Just (QName [Ident "Data"] (Ident "List"))
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
              , ("Formula", [Ident "Rel", Ident "Not", Op ":/\\", Op ":\\/", Op ":=>", Ident "Forall", Ident "Exists"])
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
    , testCase "classes, one with a superclass, and instances with their clauses laid out" $ do
        m <- parseFile "test/data/classes.px"
        let decls = map unLocated (moduleDecls m)
        [unLocated (className c) | DClass c <- decls] @?= ["Semigroup", "Monoid"]
        [map (qnameText . unLocated . fst) (classSupers c) | DClass c <- decls] @?= [[], ["Semigroup"]]
        [(qnameText (unLocated (instanceClass i)), length (instanceClauses i)) | DInstance i <- decls]
          @?= [("Semigroup", 1), ("Monoid", 1), ("Semigroup", 2), ("Monoid", 1)]
    , testCase "a data type in the GADT style: constructor signatures, and kinds inline or apart" $ do
        let src =
              "data Vec a (n : nat) where\n  nil : Vec a 0\n  (:-) : {n: nat} -> a -> Vec a n -> Vec a (S n)\n\
              \type Vec2 : type -> nat -> type\ndata Vec2 a n where\n  nil2 : Vec2 a 0\n\
              \data Vec3 : Type -> nat -> Type where\n  nil3 : Vec3 a 0\n\
              \data SameVec {a} {n} {m} (l : Vec a n) (r : Vec a m) where\n  BothNil : SameVec nil nil\n"
        m <- either (assertFailure . renderSyntaxError) pure (parseModule "<test>" src)
        let decls = map unLocated (moduleDecls m)
        map declKind decls @?= ["data", "kind", "data", "data", "data"]
        case [k | DKindSig _ k <- decls] of
          [KArrow KType (KArrow (KValue _) KType)] -> pure ()
          other -> assertFailure ("the kind signature: " <> show other)
        case [d | DData d <- decls] of
          [vec, vec2, vec3, same] -> do
            map (unLocated . fst) (dataSignatures vec) @?= [Ident "nil", Op ":-"]
            [unLocated (dataParamName p) | p <- dataParams vec] @?= ["a", "n"]
            case map dataParamKind (dataParams vec) of
              [Nothing, Just (KValue (Located _ (EName (QName [] (Ident "nat")))))] -> pure ()
              other -> assertFailure ("the parameters' kinds: " <> show other)
            map (unLocated . fst) (dataSignatures vec2) @?= [Ident "nil2"]
            case dataKind vec3 of
              Just (KArrow KType (KArrow (KValue _) KType)) -> pure ()
              other -> assertFailure ("the inline kind: " <> show other)
            map dataParamImplicit (dataParams same) @?= [True, True, True, False, False]
          other -> assertFailure ("data declarations: " <> show (length other))
    , testCase "type synonyms accept annotated and inferred parameters beside kind signatures" $ do
        m <- either (assertFailure . renderSyntaxError) pure (parseModule "<test>" "type Vec : nat -> Type -> Type\ntype Board n a = Vec n (Vec n a)\ntype Grid (n : nat) a = Board n a\n")
        map (declKind . unLocated) (moduleDecls m) @?= ["kind", "type synonym", "type synonym"]
        [map (unLocated . dataParamName) ps | Located _ (DTypeAlias _ ps _) <- moduleDecls m] @?= [["n", "a"], ["n", "a"]]
    , testCase "an offside token ends the item" $
        case parseModule "<test>" "f x = x\ng y = y\n" of
          Right m -> length (moduleDecls m) @?= 2
          Left err -> assertFailure (renderSyntaxError err)
    , testCase "builtin pragmas are declarations with precise role and target spans" $ do
        m <- parsed "{-# BUILTIN FINITE Fin #-}\n"
        moduleDecls m
          @?= [Located (Span (1, 1) (1, 27)) (DBuiltin (Located (Span (1, 13) (1, 19)) "FINITE") (Located (Span (1, 20) (1, 23)) (QName [] (Ident "Fin"))))]
    , testCase "builtin pragmas accept qualified operators and suspend layout inside their delimiters" $ do
        m <- parsed "module Main where {\n  {-# BUILTIN ROLE A.(:<) #-};\n  module Nested where\n    {-#\nBUILTIN ROLE\nA.B.name\n#-}\n}\n"
        case map unLocated (moduleDecls m) of
          [DBuiltin role target, DModule _ [Located _ (DBuiltin role' target')]] -> do
            map unLocated [role, role'] @?= ["ROLE", "ROLE"]
            map unLocated [target, target'] @?= [QName [Ident "A"] (Op ":<"), QName [Ident "A", Ident "B"] (Ident "name")]
          other -> assertFailure (show other)
    , testCase "ordinary nested comments remain whitespace, including pragma-like text inside them" $ do
        m <- parsed "{- outer {- nested -} {-# BUILTIN IGNORED Hidden #-} -}\nf : Nat {- a comment -}\nf = 0 -- a line comment\n{-# BUILTIN ROLE f #-}\n"
        map (declKind . unLocated) (moduleDecls m) @?= ["signature", "clause", "builtin"]
    , testCase "malformed and unknown pragmas are rejected instead of ignored as comments" $
        forM_
          [ "{-# BUILTIN #-}"
          , "{-# BUILTIN ROLE #-}"
          , "{-# BUILTIN ROLE Name"
          , "{-# BUILTIN ROLE Name -}"
          , "{-# BUILTIN ROLE Name extra #-}"
          , "{-# BUILTIN ROLE 0 #-}"
          , "{-# BUILTIN ROLE A. #-}"
          , "{-# UNKNOWN ROLE Name #-}"
          ]
          \source -> case parseModule "<test>" source of
            Left _ -> pure ()
            Right m -> assertFailure ("accepted " <> T.unpack source <> ": " <> show m)
    , testCase "builtin targets resolve in their nested module and retain their original spans" $ do
        m <- parsed "module Main where\ndata Outer = O\nmodule Inner where\n  data Fin = F\n  {-# BUILTIN FINITE Fin #-}\n  {-# BUILTIN FINITE Outer #-}\n{-# BUILTIN FINITE Inner.Fin #-}\n"
        let (renamed, errors) = renameModule builtinFixities emptyEnv Map.empty [Ident "Main"] m
            bindings = [(owner, role, target) | RDecl owner (Located _ (DBuiltin role target)) <- rnDecls renamed]
        errors @?= []
        [(owner, unLocated role, unLocated target) | (owner, role, target) <- bindings]
          @?= [ ([Ident "Main", Ident "Inner"], "FINITE", QName [Ident "Main", Ident "Inner"] (Ident "Fin"))
              , ([Ident "Main", Ident "Inner"], "FINITE", QName [Ident "Main"] (Ident "Outer"))
              , ([Ident "Main"], "FINITE", QName [Ident "Main", Ident "Inner"] (Ident "Fin"))
              ]
        [location target | (_, _, target) <- bindings] @?= [Span (5, 22) (5, 25), Span (6, 22) (6, 27), Span (7, 20) (7, 29)]
    , testCase "builtin targets honor import aliases and member renamings, including operators" $ do
        m <- parsed "module Main where\nimport Source as S renaming (Finite to Small; (:<) to (:<=))\n{-# BUILTIN FINITE S.Small #-}\n{-# BUILTIN ROLE S.(:<=) #-}\nopen import Source renaming (Finite to Small)\n{-# BUILTIN FINITE Small #-}\n"
        let source = [Component "package:lib", Ident "Source"]
            exports = ModuleExports source (Map.fromList [(Ident "Finite", source <> [Ident "Finite"]), (Op ":<", source <> [Op ":<"])]) Map.empty
            imports = Map.singleton (Nothing, [Ident "Source"]) (Right exports)
            (renamed, errors) = renameModule builtinFixities emptyEnv imports [Ident "Main"] m
        errors @?= []
        [unLocated target | RDecl _ (Located _ (DBuiltin _ target)) <- rnDecls renamed]
          @?= [QName source (Ident "Finite"), QName source (Op ":<"), QName source (Ident "Finite")]
    , testCase "ambiguous builtin targets fail at the target name" $ do
        m <- parsed "open import A\nopen import B\n{-# BUILTIN FINITE Fin #-}\n"
        let exports name = ModuleExports [Ident name] (Map.singleton (Ident "Fin") [Ident name, Ident "Fin"]) Map.empty
            imports = Map.fromList [((Nothing, [Ident name]), Right (exports name)) | name <- ["A", "B"]]
            (renamed, errors) = renameModule builtinFixities emptyEnv imports [Ident "Main"] m
        case errors of
          [ScopeError sp message] -> do
            sp @?= Span (3, 20) (3, 23)
            assertBool message ("ambiguous" `T.isInfixOf` T.pack message)
          other -> assertFailure (show other)
        [() | RDecl _ (Located _ (DBuiltin {})) <- rnDecls renamed] @?= []
    ]

parsed :: Text -> IO Module
parsed = either (assertFailure . renderSyntaxError) pure . parseModule "<test>"

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
  DImport {} -> "import"
  DOpenImport {} -> "open import"
  DModule {} -> "module"
  DPrivate {} -> "private"
  DBuiltin {} -> "builtin"
  DData {} -> "data"
  DTypeAlias {} -> "type synonym"
  DFixity {} -> "fixity"
  DSignature {} -> "signature"
  DClause {} -> "clause"
  DClass {} -> "class"
  DInstance {} -> "instance"
  DKindSig {} -> "kind"
