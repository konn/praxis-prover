{-# LANGUAGE OverloadedStrings #-}

-- | Applicative equations with indentation or explicit semicolon separators.
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Parser (
  Parser,
  spaceConsumer,
  lexeme,
  symbol,
  parens,
  decimal,
  reserved,
  anySymbol,
  patternP,
  eqTermP,
  equationP,
  LocatedEquation (..),
  equationsP,
  parseLocatedEquations,
  parseEqTerm,
  parseEquation,
  parseEquations,
) where

import Control.Monad (void)
import Data.Text qualified as T
import Data.Void (Void)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax
import Numeric.Natural (Natural)
import Text.Megaparsec (Parsec, Pos, SourcePos (..), between, eof, errorBundlePretty, getSourcePos, label, many, notFollowedBy, parse, sepEndBy, try, (<|>))
import Text.Megaparsec.Char qualified as CP
import Text.Megaparsec.Char.Lexer qualified as L

type Parser = Parsec Void T.Text

spaceConsumer :: Parser ()
spaceConsumer = L.space CP.space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

symbol :: T.Text -> Parser T.Text
symbol = L.symbol spaceConsumer

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

identRest :: Parser Char
identRest = CP.alphaNumChar <|> CP.char '_' <|> CP.char '\''

decimal :: Parser Natural
decimal = lexeme (L.decimal <* notFollowedBy identRest)

reserved :: T.Text -> Parser ()
reserved op = lexeme (try (void (CP.string op) <* notFollowedBy identRest))

anySymbol :: Parser T.Text
anySymbol = lexeme (T.pack <$> ((:) <$> CP.letterChar <*> many identRest))

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
eqTermP = termWith (pure ())

termWith :: Parser () -> Parser (EqTerm T.Text)
termWith next = foldl (:@) <$> atom <*> many atom
  where
    atom = next *> ((LitET <$> decimal) <|> parens eqTermP <|> (NameET <$> anySymbol))

equationP :: Parser (Equation T.Text)
equationP = do
  start <- getSourcePos
  equationWith (continuation (sourceColumn start) start)

equationWith :: Parser () -> Parser (Equation T.Text)
equationWith next = Equation <$> anySymbol <*> many (patternWith next) <* (next *> symbol "=") <*> label "right-hand side (indent continuation lines)" (termWith next)

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

runFully :: Parser a -> T.Text -> Either String a
runFully p = either (Left . errorBundlePretty) Right . parse (spaceConsumer *> p <* eof) "<equation>"

parseEqTerm :: T.Text -> Either String (EqTerm T.Text)
parseEqTerm = runFully eqTermP

parseEquation :: T.Text -> Either String (Equation T.Text)
parseEquation = runFully equationP

parseEquations :: T.Text -> Either String [Equation T.Text]
parseEquations = fmap (map locatedEquation) . parseLocatedEquations

parseLocatedEquations :: T.Text -> Either String [LocatedEquation]
parseLocatedEquations = runFully equationsP
