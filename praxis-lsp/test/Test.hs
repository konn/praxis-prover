module Main (main) where

import Data.List (sortOn)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Language.LSP.Protocol.Types (DiagnosticSeverity (..), Position (..), SemanticTokenModifiers (..), SemanticTokenTypes (..))
import Language.Praxis.LSP
import Language.Praxis.LSP.Index (Index (..), Target (..), Token (..))
import Language.Praxis.LSP.Position (columnToChar, fromPosition, linesOf, toPosition)
import Language.Praxis.Surface.Syntax.Raw (Span (..))
import System.FilePath (takeFileName)
import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "praxis-lsp"
    [ testCase "the language is told by the extension" $ do
        languageOf "Lemmas.pra" @?= Just Pra
        languageOf "Definitions.prf" @?= Just Prf
        languageOf "List.px" @?= Just Px
        languageOf "Main.hs" @?= Nothing
    , testCase "a file which certifies reports nothing" $
        analyse Pra proofs @?= []
    , testCase "a sorry is reported as an unproved warning, with the goal" $
        analyse Pra (proofs <> "\ntheorem open : a = 0 |- a = 0 /\\ a = 0\nby ConjR { Id } { sorry }\n")
          @?= [Report 8 19 DiagnosticSeverity_Warning "sorry: the proof stops here\n  H1 : a = 0\n  |- a = 0" Nothing]
    , testCase "a failing tactic is reported at its position" $ do
        let reports = analyse Pra "theorem wrong : |- 2 = 3\nby refl\n"
        map reportLine reports @?= [2]
        map reportSeverity reports @?= [DiagnosticSeverity_Error]
    , testCase "a syntax error is reported where it is" $ do
        let reports = analyse Pra "theorem broken : |- 2 = 2\nby refl {\n"
        map reportSeverity reports @?= [DiagnosticSeverity_Error]
        map reportLine reports @?= [3]
    , testCase "a declaration is a lemma for those after it, and hover shows the goal" $ do
        hoverAt (proofs <> "\ntheorem again : b = 0 |- b + 0 = b\nby Cut (b = 0) { exact H1 } { exact plusZero }\n") 8 20
          @?= Just "H1 : b = 0\n|- b = 0"
        hoverAt (proofs <> "\ntheorem again : b = 0 |- b + 0 = b\nby Cut (b = 0) { exact H1 } { exact plusZero }\n") 8 33
          @?= Just "H1 : b = 0\nH2 : b = 0\n|- b + 0 = b"
    , testCase "a failed declaration remains a draft and makes its users conditional" $
        map reportSeverity (analyse Pra "theorem later : |- 3 = 3\nby sorry\n\ntheorem uses : b = 0 |- 3 = 3\nby exact later\n")
          @?= [DiagnosticSeverity_Warning, DiagnosticSeverity_Warning]
    , testCase "unproved dependencies propagate transitively" $ do
        let source = "theorem a : |- 0 = 1\nby sorry\ntheorem b : |- 0 = 1\nby exact a\ntheorem c : |- 0 = 1\nby exact b\n"
            reports = analyse Pra source
        map reportSeverity reports @?= replicate 3 DiagnosticSeverity_Warning
        map reportMessage (drop 1 reports) @?= replicate 2 "Conditional proof; unproved dependencies: a"
        hoverAt source 6 4 @?= Just "Conditional proof; unproved dependencies: a\n\n|- 0 = 1"
        hoverAt source 2 4 @?= Just "Unproved declaration: a\n\n|- 0 = 1"
    , testCase "a failed tactic also leaves a tracked assumption" $ do
        let reports = analyse Pra "theorem a : |- 0 = 1\nby refl\ntheorem b : |- 0 = 1\nby exact a\n"
        map reportSeverity reports @?= [DiagnosticSeverity_Error, DiagnosticSeverity_Warning]
        map reportMessage (drop 1 reports) @?= ["Conditional proof; unproved dependencies: a"]
    , testCase "unused drafts and failed alternatives do not taint proofs" $ do
        let source = "theorem draft : |- 0 = 1\nby sorry\ntheorem good : |- 0 = 0\nby exact draft | refl\n"
        map reportSeverity (analyse Pra source) @?= [DiagnosticSeverity_Warning]
    , testCase "local premises shadow draft declarations without inheriting their status" $ do
        let source = "theorem D : |- 0 = 1\nby sorry\nrule local (D : |- 0 = 0) : |- 0 = 0\nby exact D\n"
        map reportSeverity (analyse Pra source) @?= [DiagnosticSeverity_Warning]
    , testCase "correcting the root proof clears downstream conditional status" $ do
        let source = "theorem a : |- 0 = 0\nby refl\ntheorem b : |- 0 = 0\nby exact a\ntheorem c : |- 0 = 0\nby exact b\n"
        analyse Pra source @?= []
        hoverAt source 6 4 @?= Just "|- 0 = 0"
    , testCase "later name shadowing cannot retroactively certify a conditional proof" $ do
        let source = "theorem a : |- 0 = 0\nby sorry\ntheorem b : |- 0 = 0\nby exact a\ntheorem a : |- 0 = 0\nby refl\ntheorem c : |- 0 = 0\nby exact b\n"
            reports = analyse Pra source
        map reportSeverity reports @?= replicate 3 DiagnosticSeverity_Warning
        map reportMessage (drop 1 reports) @?= replicate 2 "Conditional proof; unproved dependencies: a"
    , testCase "a module of the surface language is checked, a failed proof reported" $ do
        analyse Px surface @?= []
        map reportSeverity (analyse Px (surface <> "\nwrong : {a : Type} -> (xs : List a) -> xs <> Nil ≡ Nil\nwrong {a} xs = by sorry\n")) @?= [DiagnosticSeverity_Error]
    , testCase "a module of a package is checked with the modules it imports; on its own, its imports fail" $ do
        text <- TIO.readFile "test/data/pkg/src/B.px"
        analyseIn Px "test/data/pkg/src/B.px" text >>= (@?= [])
        case analyse Px text of
          Report _ _ DiagnosticSeverity_Error message _ : _ -> assertBool (T.unpack message) ("checked on its own" `T.isInfixOf` message)
          other -> assertFailure ("no error for the import: " <> show other)
    , testCase "a file of definitions is checked" $ do
        analyse Prf "double 0 = 0\ndouble (S n) = S (S (double n))\n" @?= []
        map reportSeverity (analyse Prf "double 0 = 0\ndouble (S n) = S (S (doubled n))\n") @?= [DiagnosticSeverity_Error]
    , testCase "the unfolding lemmas of the builtin definitions are in scope" $ do
        analyse Pra "theorem addSucc : |- y + S x = S (y + x)\nby exact add_S\n\ntheorem subSucc : x - S y = 3 |- prd (x - y) = 3\nby rewrite sub_S in H1; Id\n" @?= []
        hoverAt "theorem addSucc : |- y + S x = S (y + x)\nby exact add_S\n" 2 4 @?= Just "|- y + S x = S (y + x)"
    , testCase "positions: a tab advances the column to the next multiple of eight, and a character outside the plane counts twice" $ do
        let tabbed = linesOf "a\tb"
        columnToChar "a\tb" 9 @?= 2
        toPosition tabbed (1, 9) @?= Position 0 2
        toPosition tabbed (1, 10) @?= Position 0 3
        fromPosition tabbed (Position 0 2) @?= (1, 9)
        let astral = linesOf "𝔸b"
        toPosition astral (1, 2) @?= Position 0 2
        fromPosition astral (Position 0 2) @?= (1, 2)
        toPosition (linesOf "ab") (2, 1) @?= Position 1 0
    , testCase "the names of a module are tokens: types, constructors, functions, theorems, type variables, values and the words of tactics" $ do
        doc <- analyseDocument Px "<document>" surface
        assertBool "the module parsed" (docParsed doc)
        let toks = tokensOf surface doc
        mapM_
          (\expected -> assertBool ("a token " <> show expected) (expected `elem` toks))
          [ (1, "Data.List", SemanticTokenTypes_Namespace, [SemanticTokenModifiers_Declaration])
          , (2, "List", SemanticTokenTypes_Type, [SemanticTokenModifiers_Declaration])
          , (2, "Nil", SemanticTokenTypes_EnumMember, [SemanticTokenModifiers_Declaration])
          , (2, "a", SemanticTokenTypes_TypeParameter, [SemanticTokenModifiers_Declaration])
          , (3, "(<>)", SemanticTokenTypes_Function, [SemanticTokenModifiers_Declaration])
          , (3, "List", SemanticTokenTypes_Type, [])
          , (4, "(<>)", SemanticTokenTypes_Function, [SemanticTokenModifiers_Definition])
          , (4, "Nil", SemanticTokenTypes_EnumMember, [])
          , (4, "ys", SemanticTokenTypes_Variable, [SemanticTokenModifiers_Declaration])
          , (7, "append-nil", SemanticTokenTypes_Function, [SemanticTokenModifiers_Declaration])
          , (7, "a", SemanticTokenTypes_TypeParameter, [SemanticTokenModifiers_Declaration])
          , (7, "xs", SemanticTokenTypes_Parameter, [SemanticTokenModifiers_Declaration])
          , (8, "a", SemanticTokenTypes_TypeParameter, [SemanticTokenModifiers_Declaration])
          , (8, "(<>)", SemanticTokenTypes_Function, [])
          , (8, "unfold-Nil", SemanticTokenTypes_Function, [])
          , (9, "cong", SemanticTokenTypes_Keyword, [])
          , (9, "append-nil", SemanticTokenTypes_Function, [])
          ]
        -- Every token is on one line, and none overlaps the next.
        let spans = map tokenSpan (indexTokens (docIndex doc))
        assertBool "tokens in order, on one line each" (and (zipWith (\(Span s e) (Span s' _) -> fst s == fst e && e <= s') spans (drop 1 spans)))
    , testCase "classes, instances and tactics: methods, the functions of an instance, keywords in tactic position, the names a tactic introduces" $ do
        doc <- analyseDocument Px "<document>" classes
        assertBool "the module parsed" (docParsed doc)
        let toks = tokensOf classes doc
        mapM_
          (\expected -> assertBool ("a token " <> show expected) (expected `elem` toks))
          [ (3, "Semigroup", SemanticTokenTypes_Class, [SemanticTokenModifiers_Declaration])
          , (3, "a", SemanticTokenTypes_TypeParameter, [SemanticTokenModifiers_Declaration])
          , (4, "(<>)", SemanticTokenTypes_Method, [SemanticTokenModifiers_Declaration])
          , (5, "Semigroup", SemanticTokenTypes_Class, [])
          , (5, "List", SemanticTokenTypes_Type, [])
          , (6, "(<>)", SemanticTokenTypes_Function, [SemanticTokenModifiers_Definition])
          , (9, "nil-left", SemanticTokenTypes_Function, [SemanticTokenModifiers_Declaration])
          , (10, "a", SemanticTokenTypes_TypeParameter, [SemanticTokenModifiers_Declaration])
          , (11, "induction", SemanticTokenTypes_Keyword, [])
          , (11, "xs", SemanticTokenTypes_Variable, [])
          , (12, "rfl", SemanticTokenTypes_Keyword, [])
          , (13, "intros", SemanticTokenTypes_Keyword, [])
          , (13, "y", SemanticTokenTypes_Variable, [SemanticTokenModifiers_Declaration])
          , (14, "IH", SemanticTokenTypes_Variable, [])
          ]
        -- A tactic's word is a keyword only in tactic position: first is a function here.
        assertBool "first is a function, not a tactic" ((15, "first", SemanticTokenTypes_Function, [SemanticTokenModifiers_Declaration]) `elem` toks)
        assertBool "first is defined by its clause" ((16, "first", SemanticTokenTypes_Function, [SemanticTokenModifiers_Definition]) `elem` toks)
    , testCase "a name goes to its definition: a constructor, a theorem, and a lemma of a function to the function" $ do
        doc <- analyseDocument Px "<document>" surface
        let at l c = map targetSpan (definitionsAt surface doc (Position l c))
        -- Nil in the clause (<>) Nil ys = ys, at line 4.
        at 3 5 @?= [Span (2, 15) (2, 18)]
        -- append-nil in cong (append-nil xs), at line 9; and the cursor just after the name.
        at 8 87 @?= [Span (7, 1) (7, 11)]
        at 8 96 @?= [Span (7, 1) (7, 11)]
        -- (<>).unfold-Nil: the operator's namespace, and the lemma to the operator.
        at 7 22 @?= [Span (3, 1) (3, 5)]
        at 7 27 @?= [Span (3, 1) (3, 5)]
        -- A keyword goes nowhere.
        at 8 27 @?= []
    , testCase "a name of an imported module goes to its definition in that module's file" $ do
        text <- TIO.readFile "test/data/pkg/src/B.px"
        doc <- analyseDocument Px "test/data/pkg/src/B.px" text
        let at l c = [(takeFileName (targetPath t), targetSpan t) | t <- definitionsAt text doc (Position l c)]
        -- A, in open import A.
        at 2 12 @?= [("A.px", Span (1, 8) (1, 9))]
        -- List, Nil and <> in the signature of nil-append.
        at 4 34 @?= [("A.px", Span (3, 6) (3, 10))]
        at 4 45 @?= [("A.px", Span (3, 15) (3, 18))]
        at 4 49 @?= [("A.px", Span (5, 1) (5, 5))]
        assertBool "the imported module is a namespace" ((3, "A", SemanticTokenTypes_Namespace, []) `elem` tokensOf text doc)
    , testCase "a document which does not parse has no index, and says so" $ do
        doc <- analyseDocument Px "<document>" (surface <> "\nbroken : {a : Type\n")
        docParsed doc @?= False
        indexTokens (docIndex doc) @?= []
    , testCase "a .pra file: theorems and rules are declared, appeals go to them, and the library's lemmas are its" $ do
        let text = proofs <> "\ntheorem again : b = 0 |- b + 0 = b\nby Cut (b = 0) { exact H1 } { exact plusZero }\n\ntheorem lib : |- y + S x = S (y + x)\nby exact add_S\n"
        doc <- analyseDocument Pra "Lemmas.pra" text
        let toks = tokensOf text doc
        assertBool "plusZero declared" ((1, "plusZero", SemanticTokenTypes_Function, [SemanticTokenModifiers_Declaration]) `elem` toks)
        assertBool "plusZero appealed to" ((8, "plusZero", SemanticTokenTypes_Function, []) `elem` toks)
        assertBool "add_S is the library's" ((11, "add_S", SemanticTokenTypes_Function, [SemanticTokenModifiers_DefaultLibrary]) `elem` toks)
        map targetSpan (definitionsAt text doc (Position 7 38)) @?= [Span (1, 9) (1, 17)]
    , testCase "a .prf file: a function is declared at its first equation, and applied elsewhere" $ do
        let text = T.pack "double 0 = 0\ndouble (S n) = S (S (double n))\n"
        doc <- analyseDocument Prf "Definitions.prf" text
        tokensOf text doc
          @?= [ (1, "double", SemanticTokenTypes_Function, [SemanticTokenModifiers_Declaration])
              , (2, "double", SemanticTokenTypes_Function, [SemanticTokenModifiers_Definition])
              , (2, "double", SemanticTokenTypes_Function, [])
              ]
        map targetSpan (definitionsAt text doc (Position 1 23)) @?= [Span (1, 1) (1, 7)]
    ]
  where
    proofs :: Text
    proofs =
      T.unlines
        [ "theorem plusZero : |- y + 0 = y"
        , "by induction y as n { refl } { Defeq (S n + 0) (S (n + 0)); rewrite H1 in (S n + 0 = _); Id }"
        , ""
        , "theorem two : |- 2 = 2"
        , "by refl"
        ]

-- | The tokens of a document, each as its line, its text, its type and its modifiers, in order.
tokensOf :: Text -> Document -> [(Int, Text, SemanticTokenTypes, [SemanticTokenModifiers])]
tokensOf text doc = sortOn (\(l, _, _, _) -> l) [(l, slice l c c', t, ms) | Token (Span (l, c) (_, c')) t ms <- indexTokens (docIndex doc)]
  where
    ls = T.lines text
    slice l c c' =
      let line = if l <= length ls then ls !! (l - 1) else ""
       in T.take (columnToChar line c' - columnToChar line c) (T.drop (columnToChar line c) line)

-- | A module of the surface language: lists, append, and a theorem by clauses.
surface :: Text
surface =
  T.unlines
    [ "module Data.List where"
    , "data List a = Nil | a : List a"
    , "(<>) : List a -> List a -> List a"
    , "(<>) Nil ys = ys"
    , "(<>) (x : xs) ys = x : (xs <> ys)"
    , "infixr 4 <>"
    , "append-nil : {a : Type} -> (xs : List a) -> xs <> Nil ≡ xs"
    , "append-nil {a} Nil = (<>).unfold-Nil"
    , "append-nil {a} (x : xs) = calc (x : xs) <> Nil = x : (xs <> Nil) = x : xs := by cong (append-nil xs)"
    ]

-- | A class, an instance, and a theorem by tactics.
classes :: Text
classes =
  T.unlines
    [ "module Classes where"
    , "data List a = Nil | a : List a"
    , "class Semigroup a where"
    , "  (<>) : a -> a -> a"
    , "instance Semigroup (List a) where"
    , "  (<>) Nil ys = ys"
    , "  (<>) (x : xs) ys = x : (xs <> ys)"
    , "infixr 4 <>"
    , "nil-left : {a : Type} -> (xs : List a) -> Nil <> xs ≡ xs"
    , "nil-left {a} xs = by"
    , "  induction xs"
    , "  { rfl }"
    , "  { intros y ys"
    , "    cong IH }"
    , "first : List a -> List a"
    , "first xs = xs"
    ]
