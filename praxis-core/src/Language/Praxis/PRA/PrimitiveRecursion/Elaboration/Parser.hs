{-# LANGUAGE OverloadedStrings #-}

{- | Applicative equations with indentation or explicit semicolon separators.

Besides application, infix operators and conditionals, a term may be a
lambda @λ x y. body@ (also @\\x y -> body@), a bounded search
@μ i < bound. body@, or use the variadic arguments @$[xs]@ of the enclosing
schema. Binder occurrences are resolved to locally nameless indices while
parsing, so a name bound by an enclosing lambda or @μ@ never leaks out as a
free identifier.

The term grammar also serves the concrete syntax of PRA terms, in
"Language.Praxis.PRA.Syntax.Parser": a host language adapts it through a
t'TermSyntax', reserving its own words and admitting wildcards.
-}
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Parser (
  Parser,
  spaceConsumer,
  lexeme,
  symbol,
  parens,
  braces,
  decimal,
  reserved,
  identifier,
  anySymbol,
  wildcard,
  TermSyntax (..),
  defaultTermSyntax,
  patternP,
  eqTermP,
  eqTermWith,
  eqAtomWith,
  equationP,
  LocatedEquation (..),
  equationsP,
  parseLocatedEquations,
  parseEqTerm,
  parseEquation,
  parseEquations,
  EquationSyntaxError,
) where

import Control.Applicative (empty)
import Control.Exception (Exception (..))
import Control.Monad (void)
import Data.Either (lefts, rights)
import Data.List (elemIndex, findIndex)
import Data.Text qualified as T
import Data.Void (Void)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax
import Numeric.Natural (Natural)
import Text.Megaparsec (ParseErrorBundle, Parsec, Pos, SourcePos (..), between, eof, errorBundlePretty, getSourcePos, label, many, notFollowedBy, option, parse, sepBy1, sepEndBy, some, try, (<?>), (<|>))
import Text.Megaparsec.Char qualified as CP
import Text.Megaparsec.Char.Lexer qualified as L

type Parser = Parsec Void T.Text

-- | A syntax error. Render it for a human with @displayException@.
newtype EquationSyntaxError = EquationSyntaxError (ParseErrorBundle T.Text Void)
  deriving (Show, Eq)

instance Exception EquationSyntaxError where
  displayException (EquationSyntaxError bundle) = errorBundlePretty bundle

spaceConsumer :: Parser ()
spaceConsumer = L.space CP.space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

symbol :: T.Text -> Parser T.Text
symbol = L.symbol spaceConsumer

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

identRest :: Parser Char
identRest = CP.alphaNumChar <|> CP.char '_' <|> CP.char '\''

decimal :: Parser Natural
decimal = lexeme (L.decimal <* notFollowedBy identRest)

reserved :: T.Text -> Parser ()
reserved op = lexeme (try (void (CP.string op) <* notFollowedBy identRest))

-- | The words which are never identifiers.
keywords :: [T.Text]
keywords = ["if", "then", "else"]

-- | An identifier which is neither a keyword nor one of the given reserved words.
identifier :: [T.Text] -> Parser T.Text
identifier reservedWords = lexeme $ try do
  s <- T.pack <$> ((:) <$> CP.letterChar <*> many identRest)
  if s `elem` keywords || s `elem` reservedWords
    then fail ("reserved word: " <> T.unpack s)
    else pure s

anySymbol :: Parser T.Text
anySymbol = identifier []

-- | A wildcard @_@, which is neither an identifier nor the start of @_|_@.
wildcard :: Parser ()
wildcard = lexeme (try (CP.char '_' *> notFollowedBy (identRest <|> CP.char '|'))) <?> "wildcard"

{- | How a host language adapts the term grammar: its own reserved words,
which are not identifiers, and whether a wildcard @_@ is an atom, read as
the name @_@.
-}
data TermSyntax = TermSyntax
  { syntaxReserved :: ![T.Text]
  , syntaxWildcard :: !Bool
  }

-- | The equation language itself: no further reserved words, no wildcards.
defaultTermSyntax :: TermSyntax
defaultTermSyntax = TermSyntax [] False

-- | The variadic argument group @$[xs]@.
splatP :: Parser T.Text
splatP = (symbol "$[" *> anySymbol <* symbol "]") <?> "variadic argument $[..]"

patternP :: Parser (Pattern T.Text)
patternP = patternWith (pure ())

patternWith :: Parser () -> Parser (Pattern T.Text)
patternWith next =
  next
    *> ( (ZeroP <$ reserved "0")
           <|> (SuccP <$> ((reserved "S" <|> reserved "Succ") *> patternWith next))
           <|> parens patternP
           <|> (VarP <$> anySymbol)
       )

eqTermP :: Parser (EqTerm T.Text)
eqTermP = eqTermWith defaultTermSyntax

-- | A term, in the grammar adapted to a host language.
eqTermWith :: TermSyntax -> Parser (EqTerm T.Text)
eqTermWith syntax = termWith syntax (pure ()) []

{- | A term in argument position: a name, a numeral, a wildcard, or a
parenthesized term. A braced term is an argument only within an application.
-}
eqAtomWith :: TermSyntax -> Parser (EqTerm T.Text)
eqAtomWith syntax = atomWith syntax (pure ()) []

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op = do
  x <- p
  rest x
  where
    rest x =
      ( do
          f <- op
          y <- p
          rest (f x y)
      )
        <|> pure x

-- | Binder groups in scope, innermost first, each in binding order.
type Binders = [[T.Text]]

resolveName :: Binders -> T.Text -> EqTerm T.Text
resolveName binders ident =
  case [(depth, position) | (depth, group) <- zip [0 ..] binders, Just position <- [elemIndex ident group]] of
    (depth, position) : _ -> BoundET depth position
    [] -> NameET ident

-- Lambdas and bounded searches extend as far right as a conditional does.
termWith :: TermSyntax -> Parser () -> Binders -> Parser (EqTerm T.Text)
termWith syntax next binders = expr
  where
    expr = ifExpr <|> lamExpr <|> muExpr <|> cmpExpr

    name = identifier (syntaxReserved syntax)

    ifExpr = do
      next *> reserved "if"
      c <- expr
      reserved "then"
      t <- expr
      reserved "else"
      e <- expr
      pure (IfThenElseET c t e)

    lamExpr = do
      next *> lambdaP
      names <- some name
      binderDot
      body <- termWith syntax next (names : binders)
      pure (LamET (map IrrelevantName names) body)

    muExpr = do
      next *> muP
      ident <- name
      _ <- lexeme (try (CP.char '<' <* notFollowedBy (CP.char '=')))
      bound <- addExpr
      binderDot
      body <- termWith syntax next ([ident] : binders)
      pure (MuET (IrrelevantName ident) bound body)

    lambdaP = void (symbol "λ" <|> symbol "\\") <?> "lambda"
    muP = void (symbol "μ") <?> "bounded search"
    binderDot = void (symbol "." <|> symbol "->")

    -- @==@ is not the start of an implication @==>@ of a host language.
    cmpExpr = do
      l <- addExpr
      option
        l
        ( do
            op <-
              (symbol "<=" *> pure "<=")
                <|> try (symbol "<" <* notFollowedBy (CP.char '='))
                *> pure "<"
                  <|> (lexeme (try (CP.string "==" <* notFollowedBy (CP.char '>'))) *> pure "==")
            r <- addExpr
            pure (InfixET l op r)
        )

    addExpr = chainl1 mulExpr addOp
      where
        addOp =
          (symbol "+" *> pure (\l r -> InfixET l "+" r))
            <|> try (symbol "-" <* notFollowedBy (CP.char '-' <|> CP.char '>'))
            *> pure (\l r -> InfixET l "-" r)

    mulExpr = chainl1 expExpr mulOp
      where
        mulOp = symbol "*" *> pure (\l r -> InfixET l "*" r)

    expExpr = do
      l <- appExpr
      option
        l
        ( do
            _ <- symbol "^"
            r <- expExpr
            pure (InfixET l "^" r)
        )

    appExpr = foldl (:@) <$> atomWith syntax next binders <*> many (argumentWith syntax next binders)

-- Parentheses and braces suspend layout, like nested equations.
atomWith :: TermSyntax -> Parser () -> Binders -> Parser (EqTerm T.Text)
atomWith syntax next binders =
  next
    *> ( (LitET <$> decimal)
           <|> (NameET "_" <$ wildcardAtom)
           <|> parens (termWith syntax (pure ()) binders)
           <|> (SplatET <$> splatP)
           <|> (resolveName binders <$> identifier (syntaxReserved syntax))
       )
  where
    wildcardAtom = if syntaxWildcard syntax then wildcard else empty

-- A schema parameter may be braced, as in the head of a schema's equations.
argumentWith :: TermSyntax -> Parser () -> Binders -> Parser (EqTerm T.Text)
argumentWith syntax next binders =
  atomWith syntax next binders <|> next *> braces (termWith syntax (pure ()) binders)

equationP :: Parser (Equation T.Text)
equationP = do
  start <- getSourcePos
  equationWith (continuation (sourceColumn start) start)

equationWith :: Parser () -> Parser (Equation T.Text)
equationWith next = do
  ident <- anySymbol
  params <- option [] (braces (anySymbol `sepBy1` symbol ","))
  items <- many ((Left <$> (next *> splatP)) <|> (Right <$> patternWith next))
  splat <- case lefts items of
    [] -> pure Nothing
    [_] -> case findIndex (either (const True) (const False)) items of
      Just 0 -> pure (Just SplatFirst)
      Just position | position == length items - 1 -> pure (Just SplatLast)
      _ -> fail "a variadic argument $[..] must be the first or the last argument"
    _ -> fail "at most one variadic argument $[..] is allowed"
  _ <- next *> symbol "="
  rhs <- label "right-hand side (indent continuation lines)" (termWith defaultTermSyntax next [])
  pure (Equation ident params (rights items) (Splat <$> firstSplat items <*> splat) rhs)
  where
    firstSplat items = case lefts items of
      s : _ -> Just s
      [] -> Nothing

-- Whitespace retains source positions even though lexemes consume newlines.
-- Only tokens outside parentheses are subject to the equation's offside rule.
continuation :: Pos -> SourcePos -> Parser ()
continuation column start = do
  here <- getSourcePos
  if sourceLine here == sourceLine start
    then pure ()
    else void (L.indentGuard (pure ()) GT column)

-- | Start position of a clause, retained for compile-time diagnostics.
data LocatedEquation = LocatedEquation
  { equationPosition :: !SourcePos
  , locatedEquation :: !(Equation T.Text)
  }
  deriving (Show, Eq)

{- | A block uses the first equation's column as its layout baseline. A deeper
line continues an equation; an aligned line starts the next one. Parentheses
suspend layout. Semicolons explicitly separate equations at any column, and
an enclosing @{ ... }@ disables layout and requires semicolons throughout.
-}
equationsP :: Parser [LocatedEquation]
equationsP = explicit <|> layout
  where
    located p = LocatedEquation <$> getSourcePos <*> p
    explicit = between (symbol "{") (symbol "}") (located (equationWith (pure ())) `sepEndBy` symbol ";")
    layout = (eof *> pure []) <|> (getSourcePos >>= go . sourceColumn)
    go column = do
      start <- getSourcePos
      eq <- located (equationWith (continuation column start))
      rest <-
        (eof *> pure [])
          <|> (symbol ";" *> ((eof *> pure []) <|> go column))
          <|> do
            void $ label "next equation at the block indentation (or ';')" (L.indentGuard (pure ()) EQ column)
            go column
      pure (eq : rest)

runFully :: Parser a -> T.Text -> Either EquationSyntaxError a
runFully p = either (Left . EquationSyntaxError) Right . parse (spaceConsumer *> p <* eof) "<equation>"

parseEqTerm :: T.Text -> Either EquationSyntaxError (EqTerm T.Text)
parseEqTerm = runFully eqTermP

parseEquation :: T.Text -> Either EquationSyntaxError (Equation T.Text)
parseEquation = runFully equationP

parseEquations :: T.Text -> Either EquationSyntaxError [Equation T.Text]
parseEquations = fmap (map locatedEquation) . parseLocatedEquations

parseLocatedEquations :: T.Text -> Either EquationSyntaxError [LocatedEquation]
parseLocatedEquations = runFully equationsP
