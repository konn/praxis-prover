{-# LANGUAGE OverloadedStrings #-}

{- |
Surface names as identifiers of the core.

The surface language names things the core syntax cannot spell —
@Data.List.List.(:)@, @(<>).unfold-Nil@, @append-nil@ — and the core parser
reads a name the signature has as that symbol before any variable, so a
surface variable called @at@ or @add@ would be taken for the prelude's or the
builtin's.  Every name the surface hands to the core is therefore mangled
into a namespace of its own: symbols and lemmas start with @u_@, variables
with @v_@, and nothing of praxis-core or of the prelude does.

Within a name, letters and digits stand for themselves and every other
character is an escape starting with an underscore: @_s@ separates the
segments of a qualified name, @_d@ is a dash, @_q@ a prime, @_u@ an
underscore, and @_x@, the hexadecimal code point and @_@ any other character.
The escape is injective, so distinct surface names are distinct core names.
-}
module Language.Praxis.Surface.Mangle (
  mangleGlobal,
  mangleVariable,
  mangleSegment,
  demangle,
) where

import Data.Char (chr, isAlphaNum, isAsciiLower, isAsciiUpper, isDigit, ord)
import Data.Text (Text)
import Data.Text qualified as T
import Numeric (readHex, showHex)

-- | The core name of a global: a symbol or a lemma, by the segments of its qualified name.
mangleGlobal :: [Text] -> Text
mangleGlobal segments = "u_" <> T.intercalate "_s" (map mangleSegment segments)

-- | The core name of a variable.
mangleVariable :: Text -> Text
mangleVariable name = "v_" <> mangleSegment name

-- | One segment, escaped.
mangleSegment :: Text -> Text
mangleSegment = T.concatMap escape
  where
    escape c
      | isAsciiLower c || isAsciiUpper c || isDigit c = T.singleton c
      | c == '-' = "_d"
      | c == '\'' = "_q"
      | c == '_' = "_u"
      | otherwise = "_x" <> T.pack (showHex (ord c) "") <> "_"

{- |
Every mangled name in a text, such as a message of the core, written back as
the surface name it stands for: the escapes undone, the separators of
qualified names dots again.
-}
demangle :: Text -> Text
demangle = T.concat . go
  where
    go t
      | T.null t = []
      | otherwise =
          let (before, rest) = T.breakOn "_" t
           in case T.unsnoc before of
                Just (pre, c)
                  | c `elem` ['u', 'v'] && startsToken pre -> T.pack [] : pre : name c rest
                _ -> case T.uncons rest of
                  Nothing -> [before]
                  Just (u, more) -> before : T.singleton u : go more
    startsToken pre = maybe True (\(_, p) -> not (isAlphaNum p || p == '_' || p == '\'')) (T.unsnoc pre)
    name _ rest =
      let (tok, after) = T.span (\x -> isAlphaNum x || x == '_' || x == '\'') (T.drop 1 rest)
       in decode tok : go after
    decode tok = case T.uncons tok of
      Nothing -> ""
      Just ('_', more) -> case T.uncons more of
        Just ('s', r) -> "." <> decode r
        Just ('d', r) -> "-" <> decode r
        Just ('q', r) -> "'" <> decode r
        Just ('u', r) -> "_" <> decode r
        Just ('x', r) -> case T.breakOn "_" r of
          (hex, r') | [(n, "")] <- readHex (T.unpack hex) -> T.singleton (chr n) <> decode (T.drop 1 r')
          _ -> "_x" <> decode r
        _ -> "_" <> decode more
      Just (x, more) -> T.cons x (decode more)
