{- |
Concrete syntax for terms, formulae and sequents.

> term    ::= ident                          -- a variable, or a 0-ary symbol
>           | numeral
>           | S ( term )                     -- successor; S(3) is the numeral 4
>           | ident ( term {, term} )        -- a symbol of the signature, arity-checked
>           | _                              -- a wildcard, in patterns only
>           | ( term )
> atom    ::= term = term
> formula ::= atom | _|_ | ~ formula
>           | formula /\ formula | formula \/ formula | formula ==> formula
>           | ( formula )
> sequent ::= [formula {, formula}] |- formula

The fixities are those of "Language.Praxis.PRA.Syntax": @=@ binds tightest,
then conjunction, disjunction and implication, all of them associating to the
right.  @~A@ is sugar for @A ==> _|_@ and binds tighter than the binary
connectives.  The Unicode spellings @∧ ∨ → ⊥ ⊢ ¬@ are accepted for the ASCII
connectives, absurdity, turnstile and negation.  Comments run from @--@ to
the end of the line.

Identifiers start with a letter and continue with letters, digits, @_@ and
@'@.  An identifier the signature names is a symbol; how any other identifier
is read is decided by the 'Scope', which is what lets the same grammar serve
both closed sequents and the schematic ones of a derived rule.

>>> :seti -XDataKinds -XQuasiQuotes -XPatternSynonyms
>>> import Data.Sized (pattern Nil, pattern (:<))
>>> import Data.Type.Ordinal (od)
>>> import Language.Praxis.PRA.PrimitiveRecursion
>>> import Language.Praxis.PRA.Signature
>>> import Language.Praxis.PRA.Syntax.Pretty
>>> plus = Rec (Proj [od|0|]) (Comp Succ (Proj [od|1|] :< Nil)) :: PRFCode 2
>>> sc = plainScope (signature [symbol "plus" plus])
>>> renderFormula (scopeSignature sc) id <$> parseFormula sc "a = 0 ∧ ¬ plus(x, S(y)) = 2 → b = 1"
Right "a = 0 /\\ ~plus(x, S(y)) = 2 ==> b = 1"
>>> renderSequent (scopeSignature sc) id <$> parseSequent sc "a = 0, a = 0 |- a = 0"
Right "a = 0, a = 0 |- a = 0"
>>> either (const "no") (const "yes") (parseTerm sc "plus(x)")
"no"
-}
module Language.Praxis.PRA.Syntax.Parser (
  -- * Scopes
  Scope (..),
  plainScope,

  -- * Parsing
  parseTerm,
  parseAtomic,
  parseFormula,
  parseSequent,
  parseTermPattern,
  parseAtomicPattern,
  parseFormulaPattern,

  -- * The parsers
  Parser,
  runParserFully,
  termP,
  atomicP,
  formulaP,
  sequentP,
  closedP,

  -- * Lexemes
  spaceP,
  lexeme,
  symbolP,
  keywordP,
  identifierP,
  wildcardP,
  parens,
  braces,
  commaP,
  turnstileP,
) where

import Control.Monad (void, when)
import Data.Char (isAlphaNum, isLetter)
import Data.Hashable (Hashable)
import Data.Multiset qualified as MS
import Data.Void (Void)
import Language.Praxis.PRA.Pattern
import Language.Praxis.PRA.Signature
import Language.Praxis.PRA.Syntax
import Numeric.Natural (Natural)
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

{- |
How the identifiers which are not symbols of the signature are read.  The
'plainScope' reads every one of them as an object variable; the quasiquoter
builds scopes in which some of them are the metavariables a derived rule
declares.
-}
data Scope a = Scope
  { scopeSignature :: !Signature
  , scopeReserved :: ![String]
  -- ^ words which are not identifiers, besides @S@
  , scopeVariable :: String -> Either String a
  -- ^ an identifier standing for an object variable, as in @Subst x …@
  , scopeTerm :: String -> Either String (Term a)
  -- ^ an identifier in term position which is not a symbol
  , scopeAtomic :: String -> Maybe (Atomic a)
  -- ^ an identifier standing alone as an atom, excluding formula metavariables
  , scopeFormula :: String -> Maybe (Formula a)
  -- ^ an identifier standing alone as a formula
  , scopeContext :: String -> Maybe (Formula a)
  -- ^ an identifier standing for a context, in an antecedent
  }

-- | Every identifier which is not a symbol is an object variable.
plainScope :: Signature -> Scope String
plainScope sig =
  Scope
    { scopeSignature = sig
    , scopeReserved = []
    , scopeVariable = Right
    , scopeTerm = Right . Var
    , scopeAtomic = const Nothing
    , scopeFormula = const Nothing
    , scopeContext = const Nothing
    }

type Parser = Parsec Void String

-- | Run a parser on a whole input, rendering the error for a human.
runParserFully :: Parser x -> String -> Either String x
runParserFully p = either (Left . errorBundlePretty) Right . parse (spaceP *> p <* eof) ""

parseTerm :: Scope a -> String -> Either String (Term a)
parseTerm sc = runParserFully (closedP (termP sc))

parseAtomic :: Scope a -> String -> Either String (Atomic a)
parseAtomic sc = runParserFully (closedP (atomicP sc))

parseFormula :: Scope a -> String -> Either String (Formula a)
parseFormula sc = runParserFully (closedP (formulaP sc))

parseSequent :: (Hashable a) => Scope a -> String -> Either String (Sequent a)
parseSequent sc = runParserFully (sequentP sc)

parseTermPattern :: Scope a -> String -> Either String (Term (Hole a))
parseTermPattern sc = runParserFully (termP sc)

parseAtomicPattern :: Scope a -> String -> Either String (Atomic (Hole a))
parseAtomicPattern sc = runParserFully (atomicP sc)

parseFormulaPattern :: Scope a -> String -> Either String (Formula (Hole a))
parseFormulaPattern sc = runParserFully (formulaP sc)

-- * Lexemes

spaceP :: Parser ()
spaceP = L.space space1 (L.skipLineComment "--") empty

lexeme :: Parser x -> Parser x
lexeme = L.lexeme spaceP

-- | A punctuation token.
symbolP :: String -> Parser ()
symbolP = void . L.symbol spaceP

identChar :: Parser Char
identChar = satisfy (\c -> isAlphaNum c || c == '_' || c == '\'')

-- | A word which must not run on into an identifier.
keywordP :: String -> Parser ()
keywordP w = lexeme (try (string w *> notFollowedBy identChar)) <?> show w

-- | An identifier which is neither @S@ nor a reserved word of the scope.
identifierP :: Scope a -> Parser String
identifierP sc = lexeme (try (ident >>= check)) <?> "identifier"
  where
    ident = (:) <$> satisfy isLetter <*> many identChar
    check w
      | w == "S" || w `elem` scopeReserved sc = fail ("reserved word " <> show w)
      | otherwise = pure w

wildcardP :: Parser ()
wildcardP = lexeme (try (char '_' *> notFollowedBy (identChar <|> char '|'))) <?> "wildcard"

naturalP :: Parser Natural
naturalP = lexeme L.decimal <?> "numeral"

parens :: Parser x -> Parser x
parens = between (symbolP "(") (symbolP ")")

braces :: Parser x -> Parser x
braces = between (symbolP "{") (symbolP "}")

commaP :: Parser ()
commaP = symbolP ","

-- | @=@, but not the start of @==>@.
equalsP :: Parser ()
equalsP = lexeme (try (char '=' *> notFollowedBy (oneOf "=>"))) <?> "\"=\""

turnstileP :: Parser ()
turnstileP = lexeme (try (void (string "|-") <|> void (char '\8866'))) <?> "\"|-\""

-- | Reject the wildcards of a pattern.
closedP :: (Traversable t) => Parser (t (Hole a)) -> Parser (t a)
closedP p = do
  o <- getOffset
  x <- p
  case closed x of
    Just y -> pure y
    Nothing -> region (setErrorOffset o) (fail "a wildcard is not allowed here")

-- * Terms

termP :: Scope a -> Parser (Term (Hole a))
termP sc =
  choice
    [ Var Wild <$ wildcardP
    , Lit <$> naturalP
    , parens (termP sc)
    , suc <$> (keywordP "S" *> parens (termP sc))
    , applicationP
    ]
    <?> "term"
  where
    applicationP = do
      o <- getOffset
      name <- identifierP sc
      case lookupSymbol name (scopeSignature sc) of
        Just sym -> do
          args <- option [] (parens (termP sc `sepBy` commaP))
          let arity = symbolArity sym
          when (fromIntegral (length args) /= arity) $
            region (setErrorOffset o) $
              fail (name <> " takes " <> show arity <> " arguments, given " <> show (length args))
          maybe (fail "arity") pure (applySymbol sym args)
        Nothing -> case scopeTerm sc name of
          Right t -> pure (fmap Named t)
          Left err -> region (setErrorOffset o) (fail err)

-- * Formulae

atomicP :: Scope a -> Parser (Atomic (Hole a))
atomicP sc = metaAtomicP <|> ((:===) <$> termP sc <* equalsP <*> termP sc)
  where
    metaAtomicP = try do
      name <- identifierP sc
      maybe (fail "not an atom") (pure . fmap Named) (scopeAtomic sc name)

formulaP :: Scope a -> Parser (Formula (Hole a))
formulaP sc = implP
  where
    -- Each level is right-associative.
    implP = binary orP implOp implP (:==>)
    orP = binary andP orOp orP (:\/)
    andP = binary unaryP andOp andP (:/\)
    binary operand op rest con = do
      l <- operand
      option l (con l <$> (op *> rest))
    unaryP =
      choice
        [ (:==> Bot) <$> (negOp *> unaryP)
        , Bot <$ botP
        , try (parens (formulaP sc))
        , metaFormulaP
        , Atm <$> atomicP sc
        ]
        <?> "formula"
    metaFormulaP = try do
      name <- identifierP sc
      maybe (fail "not a formula") (pure . fmap Named) (scopeFormula sc name)
    andOp = lexeme (try (void (string "/\\") <|> void (char '\8743'))) <?> "\"/\\\""
    orOp = lexeme (try (void (string "\\/") <|> void (char '\8744'))) <?> "\"\\/\""
    implOp = lexeme (try (void (string "==>") <|> void (char '\8594'))) <?> "\"==>\""
    negOp = lexeme (void (char '~') <|> void (char '\172')) <?> "\"~\""
    botP = lexeme (try (void (string "_|_") <|> void (char '\8869'))) <?> "\"_|_\""

-- * Sequents

-- | A sequent is closed: it may not contain wildcards.
sequentP :: (Hashable a) => Scope a -> Parser (Sequent a)
sequentP sc = (:|-) <$> antecedentP <* turnstileP <*> closedP (formulaP sc)
  where
    antecedentP = foldr MS.insertOne MS.empty <$> option [] (itemP `sepBy1` commaP)
    itemP = contextP <|> closedP (formulaP sc)
    contextP = try do
      name <- identifierP sc
      maybe (fail "not a context") pure (scopeContext sc name)
