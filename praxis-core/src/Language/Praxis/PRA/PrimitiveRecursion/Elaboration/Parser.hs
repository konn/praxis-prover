{-# LANGUAGE OverloadedStrings #-}

-- | Parsing applicative terms and semicolon-separated equations.
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
  parseEqTerm,
  parseEquation,
  parseEquations,
) where

import Control.Monad (void)
import Data.Text qualified as T
import Data.Void (Void)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax
import Numeric.Natural (Natural)
import Text.Megaparsec (Parsec, between, eof, errorBundlePretty, many, notFollowedBy, parse, sepEndBy, try, (<|>))
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
patternP =
  (ZeroP <$ reserved "0")
    <|> (SuccP <$> ((reserved "S" <|> reserved "Succ") *> patternP))
    <|> parens patternP
    <|> (VarP <$> anySymbol)

eqTermP :: Parser (EqTerm T.Text)
eqTermP = foldl (:@) <$> atom <*> many atom
  where
    atom = (LitET <$> decimal) <|> parens eqTermP <|> (NameET <$> anySymbol)

equationP :: Parser (Equation T.Text)
equationP = Equation <$> anySymbol <*> many patternP <* symbol "=" <*> eqTermP

runFully :: Parser a -> T.Text -> Either String a
runFully p = either (Left . errorBundlePretty) Right . parse (spaceConsumer *> p <* eof) "<equation>"

parseEqTerm :: T.Text -> Either String (EqTerm T.Text)
parseEqTerm = runFully eqTermP

parseEquation :: T.Text -> Either String (Equation T.Text)
parseEquation = runFully equationP

parseEquations :: T.Text -> Either String [Equation T.Text]
parseEquations = runFully (equationP `sepEndBy` symbol ";")
