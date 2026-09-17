{-# LANGUAGE OverloadedStrings #-}

{- |
Versions of packages, as the Package Versioning Policy of Haskell has them,
and the ranges of versions a dependency or a constraint asks for, in the
syntax of Cabal.

A version is a dot-separated sequence of naturals, @A.B.C.D@, compared as
sequences; @A.B@ is its major version, and @^>= A.B.C@ the versions from
@A.B.C@ below the next major one, @A.(B+1)@.  A range is built from
comparisons, @>= 1.2@, @< 2@, @== 1.2.3@, @^>= 1.2@, and the wildcard
@== 1.2.*@, joined by @&&@ and @||@ (@&&@ binding tighter), grouped by
parentheses; @-any@ is every version, @-none@ none, and a range omitted is
@-any@.
-}
module Language.Praxis.Package.Version (
  -- * Versions
  Version (..),
  parseVersion,
  renderVersion,
  majorVersion,

  -- * Ranges
  VersionRange (..),
  anyVersion,
  parseVersionRange,
  renderVersionRange,
  withinRange,
  versionRangeP,
  versionP,
) where

import Data.Bifunctor (first)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char (char, space, space1, string)
import Text.Megaparsec.Char.Lexer qualified as L

-- * Versions

-- | A version: its components, at least one, compared as sequences, so that @1.0@ comes after @1@.
newtype Version = Version {versionComponents :: [Int]}
  deriving stock (Show, Eq, Ord)

parseVersion :: Text -> Either String Version
parseVersion = first errorBundlePretty . parse (space *> versionP <* space <* eof) "version"

renderVersion :: Version -> Text
renderVersion (Version cs) = T.intercalate "." (map (T.pack . show) cs)

-- | The major version, its first two components, @A.B@ (@A.0@ for @A@ alone): what @^>=@ bounds.
majorVersion :: Version -> Version
majorVersion (Version cs) = Version (take 2 (cs <> [0]))

-- | The versions after every version of the major version given: @A.(B+1)@.
nextMajor :: Version -> Version
nextMajor v = case majorVersion v of
  Version [a, b] -> Version [a, b + 1]
  Version cs -> Version cs

-- * Ranges

data VersionRange
  = AnyVersion
  | NoVersion
  | ThisVersion !Version
  | LaterVersion !Version
  | OrLaterVersion !Version
  | EarlierVersion !Version
  | OrEarlierVersion !Version
  | -- | @^>= v@: from @v@, below the next major version
    MajorBoundVersion !Version
  | -- | @== A.B.*@: the versions starting with @A.B@
    WildcardVersion !Version
  | UnionVersionRanges !VersionRange !VersionRange
  | IntersectVersionRanges !VersionRange !VersionRange
  deriving stock (Show, Eq)

anyVersion :: VersionRange
anyVersion = AnyVersion

-- | Whether a version is in a range.
withinRange :: Version -> VersionRange -> Bool
withinRange v = \case
  AnyVersion -> True
  NoVersion -> False
  ThisVersion w -> v == w
  LaterVersion w -> v > w
  OrLaterVersion w -> v >= w
  EarlierVersion w -> v < w
  OrEarlierVersion w -> v <= w
  MajorBoundVersion w -> v >= w && v < nextMajor w
  WildcardVersion w -> versionComponents w `isPrefixOf'` versionComponents v
  UnionVersionRanges a b -> withinRange v a || withinRange v b
  IntersectVersionRanges a b -> withinRange v a && withinRange v b
  where
    isPrefixOf' xs ys = take (length xs) ys == xs

parseVersionRange :: Text -> Either String VersionRange
parseVersionRange = first errorBundlePretty . parse (space *> versionRangeP <* space <* eof) "version range"

renderVersionRange :: VersionRange -> Text
renderVersionRange = go (0 :: Int)
  where
    go d = \case
      AnyVersion -> "-any"
      NoVersion -> "-none"
      ThisVersion v -> "== " <> renderVersion v
      LaterVersion v -> "> " <> renderVersion v
      OrLaterVersion v -> ">= " <> renderVersion v
      EarlierVersion v -> "< " <> renderVersion v
      OrEarlierVersion v -> "<= " <> renderVersion v
      MajorBoundVersion v -> "^>= " <> renderVersion v
      WildcardVersion v -> "== " <> renderVersion v <> ".*"
      UnionVersionRanges a b -> paren (d > 0) (go 0 a <> " || " <> go 0 b)
      IntersectVersionRanges a b -> paren (d > 1) (go 1 a <> " && " <> go 1 b)
    paren p s = if p then "(" <> s <> ")" else s

-- * Parsing

type P = Parsec Void Text

lexeme :: P a -> P a
lexeme = L.lexeme space

versionP :: P Version
versionP = Version <$> ((:) <$> L.decimal <*> many (try (char '.' *> L.decimal))) <?> "a version"

-- | A range; the version alone after @==@ with @.*@ is a wildcard.
versionRangeP :: P VersionRange
versionRangeP = foldl1 UnionVersionRanges <$> (andP `sepBy1` lexeme (string "||"))
  where
    andP = foldl1 IntersectVersionRanges <$> (termP `sepBy1` lexeme (string "&&"))
    termP =
      choice
        [ between (lexeme (char '(')) (lexeme (char ')')) versionRangeP
        , AnyVersion <$ lexeme (string "-any")
        , NoVersion <$ lexeme (string "-none")
        , lexeme (string "^>=") *> (MajorBoundVersion <$> lexeme versionP)
        , lexeme (string ">=") *> (OrLaterVersion <$> lexeme versionP)
        , lexeme (string "<=") *> (OrEarlierVersion <$> lexeme versionP)
        , lexeme (string ">") *> (LaterVersion <$> lexeme versionP)
        , lexeme (string "<") *> (EarlierVersion <$> lexeme versionP)
        , lexeme (string "==") *> equalP
        ]
        <?> "a comparison with a version"
    equalP = do
      v <- versionP
      wild <- optional (string ".*")
      _ <- optional space1
      pure (maybe (ThisVersion v) (const (WildcardVersion v)) wild)
