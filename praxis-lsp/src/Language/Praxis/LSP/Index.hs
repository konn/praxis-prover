{- |
What the server knows of a document beyond its diagnostics: the tokens of
its names, each with the kind of thing it names, for semantic highlighting,
and the references its names make, each to where what it names is
declared, for going to a definition.

Positions are those of the checkers, lines and columns from 1, as
"Language.Praxis.Surface.Syntax.Raw" spans them; "Language.Praxis.LSP.Position"
converts them for the protocol.
-}
module Language.Praxis.LSP.Index (
  -- * The index
  Token (..),
  Target (..),
  Index (..),
  Definitions,

  -- * Building
  token,
  reference,

  -- * Reading
  normalizeTokens,
  referencesAt,
) where

import Data.List (sortOn)
import Data.Map.Strict (Map)
import Language.LSP.Protocol.Types (SemanticTokenModifiers, SemanticTokenTypes)
import Language.Praxis.Surface.Env (QualName)
import Language.Praxis.Surface.Syntax.Raw (Span (..))

-- | A token: where it is, what kind of thing it names, and how.
data Token = Token
  { tokenSpan :: !Span
  , tokenType :: !SemanticTokenTypes
  , tokenModifiers :: ![SemanticTokenModifiers]
  }
  deriving stock (Show, Eq)

-- | Where something is declared: its file, and the span of its name there.
data Target = Target
  { targetPath :: !FilePath
  , targetSpan :: !Span
  }
  deriving stock (Show, Eq, Ord)

-- | The tokens of a document, and the references its names make, each to the declarations it may mean.
data Index = Index
  { indexTokens :: ![Token]
  , indexReferences :: ![(Span, [Target])]
  }
  deriving stock (Show, Eq)

instance Semigroup Index where
  Index ts rs <> Index ts' rs' = Index (ts <> ts') (rs <> rs')

instance Monoid Index where
  mempty = Index [] []

-- | Where every global known is declared, by its canonical name.
type Definitions = Map QualName Target

-- | A token alone.
token :: Span -> SemanticTokenTypes -> [SemanticTokenModifiers] -> Index
token sp t ms = Index [Token sp t ms] []

-- | A reference, when it has somewhere to go.
reference :: Span -> [Target] -> Index
reference _ [] = mempty
reference sp targets = Index [] [(sp, targets)]

{- |
The tokens in the order of the document, one per position: those spanning
more than one line or nothing are left out, and of two overlapping, the one
which starts first, or the one emitted first, is kept.
-}
normalizeTokens :: [Token] -> [Token]
normalizeTokens = go . sortOn (spanStart . tokenSpan) . filter oneLine
  where
    oneLine (Token (Span (l, c) (l', c')) _ _) = l == l' && c' > c
    go = \case
      t : u : rest
        | spanStart (tokenSpan u) < spanEnd (tokenSpan t) -> go (t : rest)
        | otherwise -> t : go (u : rest)
      ts -> ts

{- |
The declarations the name at a position refers to: those of the innermost
reference spanning the position, which may stand just after the name.
-}
referencesAt :: Index -> (Int, Int) -> [Target]
referencesAt ix pos = case sortOn (\(sp, _) -> (size sp, spanStart sp)) [r | r@(sp, _) <- indexReferences ix, contains sp] of
  (_, targets) : _ -> targets
  [] -> []
  where
    contains (Span start end) = start <= pos && pos <= end
    size (Span (l, c) (l', c')) = (l' - l, c' - c)
