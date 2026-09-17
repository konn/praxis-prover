{-# LANGUAGE OverloadedStrings #-}

{- |
The index of the files of the core languages, @.pra@ and @.prf@, read
lexically: their parsers keep no position for a name, so the words of the
source are scanned, outside comments, and the declarations found among
them.

In a @.pra@ file, a name after @theorem@ or @rule@ is declared, and a name
after @exact@, @cong@, @rewrite@, @symmetry@, @reflect@ or @reify@ appeals
to a declaration of the file or to a lemma of the library.  In a @.prf@
file, the first word of an equation defines a function, and every other
occurrence of that word applies it.
-}
module Language.Praxis.LSP.Core (
  coreWords,
  indexPra,
  indexPrf,
) where

import Data.Char (isAlpha, isAlphaNum)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Language.LSP.Protocol.Types (SemanticTokenModifiers (..), SemanticTokenTypes (..))
import Language.Praxis.LSP.Index
import Language.Praxis.LSP.Position (Lines, charToColumn, lineAt, lineCount)
import Language.Praxis.Surface.Syntax.Raw (Span (..))

{- |
The words of a document outside its comments, in order, each with its
span: runs of letters, digits, underscores and primes starting with a
letter or an underscore, as the lexers of the core languages read
identifiers.  A line comment runs from @--@ to the end of the line, a block
comment from @{-@ to @-}@, nested.
-}
coreWords :: Lines -> [(Span, Text)]
coreWords ls = go 1 0
  where
    go l depth
      | l > lineCount ls = []
      | otherwise =
          let (ws, depth') = scanLine l depth (lineAt ls l)
           in ws <> go (l + 1) depth'

-- | The words of a line, from a depth of block comments, and the depth after it.
scanLine :: Int -> Int -> Text -> ([(Span, Text)], Int)
scanLine l depth0 line = go 0 depth0 line
  where
    column = charToColumn line
    go i depth cs
      | depth > 0 = case T.uncons cs of
          Nothing -> ([], depth)
          Just ('-', rest) | Just ('}', rest') <- T.uncons rest -> go (i + 2) (depth - 1) rest'
          Just ('{', rest) | Just ('-', rest') <- T.uncons rest -> go (i + 2) (depth + 1) rest'
          Just (_, rest) -> go (i + 1) depth rest
      | otherwise = case T.uncons cs of
          Nothing -> ([], 0)
          Just ('{', rest) | Just ('-', rest') <- T.uncons rest -> go (i + 2) 1 rest'
          Just ('-', rest) | Just ('-', _) <- T.uncons rest -> ([], 0)
          Just (c, _)
            | isAlpha c || c == '_' ->
                let w = T.takeWhile isWordChar cs
                    n = T.length w
                    (ws, depth') = go (i + n) depth (T.drop n cs)
                 in ((Span (l, column i) (l, column (i + n)), w) : ws, depth')
            | isWordChar c -> let n = T.length (T.takeWhile isWordChar cs) in go (i + n) depth (T.drop n cs)
          Just (_, rest) -> go (i + 1) depth rest

isWordChar :: Char -> Bool
isWordChar c = isAlphaNum c || c == '_' || c == '\''

-- | The words after which a name appeals to a lemma in a @.pra@ file.
appealWords :: Set Text
appealWords = Set.fromList ["exact", "cong", "rewrite", "symmetry", "reflect", "reify"]

{- |
The index of a @.pra@ file at a path, given the names of the lemmas in
scope before it: the theorems and rules it declares, and the appeals to
them and to the lemmas.
-}
indexPra :: FilePath -> Lines -> Set Text -> Index
indexPra path ls library = Index (normalizeTokens tokens) refs
  where
    ws = coreWords ls
    pairs = zip ("" : map snd ws) ws
    declared = Map.fromListWith (\_ old -> old) [(n, sp) | (prev, (sp, n)) <- pairs, prev `elem` ["theorem", "rule"]]
    Index tokens refs = foldMap word pairs
    word (prev, (sp, w))
      | prev `elem` ["theorem", "rule"] = token sp SemanticTokenTypes_Function [SemanticTokenModifiers_Declaration]
      | Set.member prev appealWords = case Map.lookup w declared of
          Just dsp -> token sp SemanticTokenTypes_Function [] <> reference sp [Target path dsp]
          Nothing
            | Set.member w library -> token sp SemanticTokenTypes_Function [SemanticTokenModifiers_DefaultLibrary]
            | otherwise -> mempty
      | otherwise = mempty

-- | The words of the @.prf@ grammar, never the head of an equation.
prfWords :: Set Text
prfWords = Set.fromList ["environment", "extends", "if", "then", "else", "forall", "exists"]

{- |
The index of a @.prf@ file at a path: the function each equation defines,
declared at its first equation, and every other occurrence of a function's
name.
-}
indexPrf :: FilePath -> Lines -> Index
indexPrf path ls = Index (normalizeTokens tokens) refs
  where
    ws = coreWords ls
    heads = Set.fromList [sp | (sp, w) <- ws, isHead sp w]
    isHead sp@(Span (l, _) _) w = not (Set.member w prfWords) && firstOnLine sp && "=" `T.isInfixOf` lineAt ls l
    firstOnLine sp@(Span (l, _) _) = case [s | (s@(Span (l', _) _), _) <- ws, l' == l] of
      first : _ -> first == sp
      [] -> False
    defined = Map.fromListWith (\_ old -> old) [(w, sp) | (sp, w) <- ws, Set.member sp heads]
    Index tokens refs = foldMap word ws
    word (sp, w)
      | Set.member sp heads = case Map.lookup w defined of
          Just dsp
            | dsp == sp -> token sp SemanticTokenTypes_Function [SemanticTokenModifiers_Declaration]
            | otherwise -> token sp SemanticTokenTypes_Function [SemanticTokenModifiers_Definition] <> reference sp [Target path dsp]
          Nothing -> mempty
      | Just dsp <- Map.lookup w defined = token sp SemanticTokenTypes_Function [] <> reference sp [Target path dsp]
      | otherwise = mempty
