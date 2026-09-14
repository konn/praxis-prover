{-# LANGUAGE OverloadedStrings #-}

{- |
Tokens and layout of the surface language.

Whitespace includes line comments, @--@ to the end of the line (a run of
dashes not followed by another operator character), and nestable block
comments @{\- … -\}@.

Identifiers are alphanumeric segments joined by single dashes, as in Agda:
@append-nil@, @unfold-Nil@; so binary minus needs spaces around it.  The
member of a qualified name may also end in operator segments,
@(<>).unfold-:@.  Qualification is a dot with no whitespace on either side.
Operators are runs of symbol characters; which of them are reserved (@=@,
@->@, @|@, …) is decided by the grammar, not here, so that @:@ and @:=@ may
still be constructors.

Layout is the offside rule, checked token by token: within an item of a block,
every token after the first must stand to the right of the block's column.
A block opened without a brace takes the column of its first token, and a
line starting at that column starts the next item.  Brackets suspend the
layout of the enclosing block, and a closing bracket is never offside.
Inside braces, items are separated by @;@ or, as without braces, by lines at
the column of the first item; a trailing @;@ is ignored.
-}
module Language.Praxis.Surface.Lexer (
  -- * The parser
  Parser,
  Ctx (..),
  Layout (..),
  initialCtx,
  runSurfaceParser,
  SyntaxError,
  renderSyntaxError,
  syntaxErrorPosition,

  -- * Positions
  position,
  located,
  locatedFrom,

  -- * Whitespace
  whitespace,

  -- * Tokens
  keyword,
  keywords,
  symbol,
  closing,
  identifier,
  identifierText,
  operator,
  operatorText,
  natural,
  rational,
  qualifiedName,
  isOperatorChar,

  -- * Layout
  block,
  bracedBlock,
  laidOutBlock,
  wildcard,
  bracketed,
  withStops,
  atLineStart,
) where

import Control.Monad (guard, unless, void)
import Control.Monad.Reader (ReaderT, asks, local, runReaderT)
import Control.Monad.State.Strict (State, get, put, runState)
import Data.Char (isAlpha, isAlphaNum, isAscii, isDigit, isPunctuation, isSymbol)
import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty (..))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Language.Praxis.Surface.Syntax.Raw
import Text.Megaparsec hiding (State, token)
import Text.Megaparsec.Char (char, space1, string)
import Text.Megaparsec.Char.Lexer qualified as L

-- * The parser

-- | The offside rule in force: the column of the enclosing block, and the start of the current item, which is exempt.
data Layout = Layout
  { layoutColumn :: !Int
  , layoutStart :: !(Maybe (Int, Int))
  }

{- |
What a parser reads under: the layout, and the operators and words which
end an expression in this context, such as @:=@ in a @calc@ step or @at@ in
a tactic.
-}
data Ctx = Ctx
  { ctxLayout :: !Layout
  , ctxStopOperators :: ![Text]
  , ctxStopWords :: ![Text]
  }

-- | No layout, and nothing stopping an expression.
initialCtx :: Ctx
initialCtx = Ctx (Layout 0 Nothing) [] []

{- |
The parser: Megaparsec over the source, reading the context and keeping the
end of the last token read, which is where a span ends.
-}
type Parser = ParsecT Void Text (ReaderT Ctx (State (Int, Int)))

type SyntaxError = ParseErrorBundle Text Void

-- | Run a parser over a whole source, leading whitespace included.
runSurfaceParser :: Parser a -> FilePath -> Text -> Either SyntaxError a
runSurfaceParser p file src =
  fst (runState (runReaderT (runParserT (whitespace *> p <* eof) file src) initialCtx) (1, 1))

-- * Positions

-- | The current position, line and column from 1.
position :: Parser (Int, Int)
position = do
  p <- getSourcePos
  pure (unPos (sourceLine p), unPos (sourceColumn p))

-- | The span of what a parser reads, from its first token to the end of its last.
located :: Parser a -> Parser (Located a)
located p = do
  start <- position
  locatedFrom start p

-- | The span from a position to the end of what a parser reads.
locatedFrom :: (Int, Int) -> Parser a -> Parser (Located a)
locatedFrom start p = do
  x <- p
  end <- get
  pure (Located (Span start end) x)

-- * Whitespace

whitespace :: Parser ()
whitespace = L.space space1 lineComment (L.skipBlockCommentNested "{-" "-}")
  where
    lineComment = do
      _ <- try (string "--" *> takeWhileP Nothing (== '-') <* notFollowedBy (satisfy isOperatorChar))
      void (takeWhileP Nothing (/= '\n'))

-- | A token read under the offside rule, then the whitespace after it.
token :: Parser a -> Parser a
token p = do
  offside
  x <- p
  position >>= put
  whitespace
  pure x

-- | Fail, without consuming anything, on a token which is offside.
offside :: Parser ()
offside = do
  here <- position
  Layout col start <- asks ctxLayout
  unless (Just here == start || snd here > col) empty

-- | A token which is never offside: a closing bracket.
unguarded :: Parser a -> Parser a
unguarded p = do
  x <- p
  position >>= put
  whitespace
  pure x

-- * Tokens

-- | The words which are never identifiers.
keywords :: [Text]
keywords =
  [ "module"
  , "where"
  , "open"
  , "using"
  , "hiding"
  , "data"
  , "class"
  , "instance"
  , "infixl"
  , "infixr"
  , "infix"
  , "case"
  , "of"
  , "if"
  , "then"
  , "else"
  , "let"
  , "in"
  , "by"
  , "calc"
  , "Type"
  , "type"
  , "forall"
  , "exists"
  , "fun"
  , "with"
  ]

identStart, identChar :: Char -> Bool
identStart c = (isAlpha c || c == '_') && c /= 'λ'
identChar c = isAlphaNum c || c == '_' || c == '\''

-- | Characters of operators: ASCII symbols, and non-ASCII symbols but for the brackets and binders of the grammar.
isOperatorChar :: Char -> Bool
isOperatorChar c
  | isAscii c = c `elem` ("!#$%&*+./<=>?@\\^|~:-" :: String)
  | otherwise = (isSymbol c || isPunctuation c) && c `notElem` ("⟨⟩·∀∃λ" :: String)

-- | An alphanumeric segment, and more joined by single dashes.
identRaw :: Parser Text
identRaw = do
  first <- segment identStart
  rest <- many (try (char '-' *> segment isAlphaNum))
  pure (T.intercalate "-" (first : rest))
  where
    segment start = T.pack <$> ((:) <$> satisfy start <*> many (satisfy identChar))

-- | The member of a qualified name: an identifier whose later segments may also be operators, @unfold-:-Nil@.
memberRaw :: Parser Text
memberRaw = do
  first <- T.pack <$> ((:) <$> satisfy identStart <*> many (satisfy identChar))
  rest <- many (try (char '-' *> (alnum <|> ops)))
  pure (T.intercalate "-" (first : rest))
  where
    alnum = T.pack <$> ((:) <$> satisfy isAlphaNum <*> many (satisfy identChar))
    ops = T.pack <$> some (satisfy (\c -> isOperatorChar c && c /= '-' && c /= '.'))

-- | A reserved word.
keyword :: Text -> Parser ()
keyword w = token (try (identRaw >>= guard . (== w))) <?> T.unpack w

{- |
A symbol of the grammar: an operator run which is exactly the symbol, so
that @=@ is not the start of @==@, or one of the punctuation characters.
-}
symbol :: Text -> Parser ()
symbol s
  | T.all isOperatorChar s = token (try (opRaw >>= guard . (== s))) <?> show s
  | otherwise = token (void (string s)) <?> show s

-- | A closing bracket, never offside.
closing :: Text -> Parser ()
closing s = unguarded (void (string s)) <?> show s

opRaw :: Parser Text
opRaw = T.pack <$> some (satisfy isOperatorChar)

-- | An identifier which is no keyword, nor a word ending the expression here.
identifier :: Parser (Located Text)
identifier = located identifierText

identifierText :: Parser Text
identifierText = token . try $ do
  w <- identRaw
  stops <- asks ctxStopWords
  if w `elem` keywords || w `elem` stops
    then fail ("reserved word " <> T.unpack w)
    else pure w

{- |
An operator, as it stands between operands: a symbol run which the grammar
does not reserve and which does not end the expression here, or a name in
backquotes.
-}
operator :: Parser (Located Operator)
operator = located do
  ((\o -> Operator (unqualified (Op o)) False) <$> operatorText) <|> backquoted
  where
    backquoted = token (char '`' *> ((\n -> Operator n True) <$> qualifiedRaw) <* char '`')

operatorText :: Parser Text
operatorText = token . try $ do
  o <- opRaw
  stops <- asks ctxStopOperators
  if o `elem` reservedOps || o `elem` stops
    then fail ("reserved operator " <> T.unpack o)
    else pure o
  where
    reservedOps = ["->", "→", "|", "\\", "=>", "⇒", "<-", "←", ".", "<;>", "¬", "⊤", "⊥"]

natural :: Parser Integer
natural = token (L.decimal <* notFollowedBy (satisfy identChar)) <?> "numeral"

-- | A precedence: a natural, a decimal, @6.5@, or a fraction, @9/2@.
rational :: Parser Rational
rational = token do
  whole <- L.decimal
  frac <- optional ((Left <$> (char '.' *> some (satisfy isDigit))) <|> (Right <$> (char '/' *> L.decimal)))
  pure case frac of
    Nothing -> fromInteger whole
    Just (Left ds) -> fromInteger whole + read ds / (10 ^ length ds)
    Just (Right d) -> fromInteger whole / fromInteger d

-- | A name, possibly qualified: @x@, @List.Nil@, @(<>)@, @(<>).unfold-Nil@, @List.(:)@.
qualifiedName :: Parser (Located QName)
qualifiedName = located (token qualifiedRaw)

qualifiedRaw :: Parser QName
qualifiedRaw = do
  first <- headSegment
  rest <- many (try (char '.' *> memberSegment))
  stops <- asks ctxStopWords
  case (first, rest) of
    (Ident w, []) | w `elem` keywords || w `elem` stops -> fail ("reserved word " <> T.unpack w)
    _ -> pure ()
  pure case reverse (first : rest) of
    b : qs -> QName (reverse qs) b
    [] -> error "qualifiedRaw: no segment"
  where
    headSegment = (Ident <$> identRaw) <|> parenOp
    memberSegment = (Ident <$> memberRaw) <|> parenOp
    parenOp = try (char '(' *> (Op <$> opRaw) <* char ')')

-- * Layout

{- |
The items of a block, each read by the parser given: in braces, or by the
offside rule when the next token is no brace.  A block laid out at a column
not to the right of the enclosing one is empty.
-}
block :: Parser a -> Parser [a]
block item = bracedBlock item <|> laidOutBlock item

-- | The items of a block in braces.
bracedBlock :: Parser a -> Parser [a]
bracedBlock item = do
  symbol "{"
  xs <- local (setLayout (Layout 0 Nothing)) do
    (lookAhead (string "}") $> []) <|> (position >>= \(_, col) -> items col item)
  closing "}"
  pure xs

-- | The items of a block laid out from the next token's column; empty when that is not to the right of the enclosing block.
laidOutBlock :: Parser a -> Parser [a]
laidOutBlock item = do
  (_, col) <- position
  outer <- asks (layoutColumn . ctxLayout)
  atEof <- (True <$ eof) <|> pure False
  if col <= outer || atEof then pure [] else items col item

items :: Int -> Parser a -> Parser [a]
items col item = do
  x <- itemAt
  rest <- more
  pure (x : rest)
  where
    itemAt = do
      here <- position
      local (setLayout (Layout col (Just here))) item
    more =
      (unguarded (void (char ';')) *> option [] (items col item))
        <|> (try atColumn *> items col item)
        <|> pure []
    atColumn = do
      (_, c) <- position
      notFollowedBy eof
      notFollowedBy (satisfy (`elem` (")]}⟩" :: String)))
      guard (c == col)

-- | The wildcard @_@, which is no identifier.
wildcard :: Parser ()
wildcard = token (try (void (char '_') <* notFollowedBy (satisfy identChar))) <?> "_"

-- | A parser between brackets, the enclosing layout suspended; the closing bracket is never offside.
bracketed :: Text -> Text -> Parser a -> Parser a
bracketed open close p = do
  symbol open
  x <- local (setLayout (Layout 0 Nothing)) p
  closing close
  pure x

-- | A parser with more operators and words ending its expressions.
withStops :: [Text] -> [Text] -> Parser a -> Parser a
withStops ops ws = local \c -> c {ctxStopOperators = ops <> ctxStopOperators c, ctxStopWords = ws <> ctxStopWords c}

-- | A parser with the stops cleared, as between brackets.
setLayout :: Layout -> Ctx -> Ctx
setLayout l c = c {ctxLayout = l}

-- | Whether the next token starts its line: nothing but whitespace before it on the line.
atLineStart :: Parser Bool
atLineStart = do
  (line, _) <- position
  (lastLine, _) <- get
  pure (line > lastLine)

-- | A syntax error, for a human.
renderSyntaxError :: SyntaxError -> String
renderSyntaxError = errorBundlePretty

-- | Where a syntax error is, line and column from 1.
syntaxErrorPosition :: SyntaxError -> (Int, Int)
syntaxErrorPosition bundle =
  let e = case bundleErrors bundle of
        first :| _ -> first
      (_, st) = reachOffset (errorOffset e) (bundlePosState bundle)
      p = pstateSourcePos st
   in (unPos (sourceLine p), unPos (sourceColumn p))
