{-# LANGUAGE OverloadedStrings #-}

{- |
Concrete syntax for terms, formulae and sequents.

Terms are written in the applicative syntax of the equation language,
"Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Parser":

> term    ::= arg {arg}                      -- an application, of a symbol of the signature or of S
>           | term op term                   -- + - * ^ < <= ==, through the symbols the signature names
>           | if term then term else term    -- through ifte
>           | μ ident < term . term          -- a bounded search, through the schema mu
> arg     ::= ident                          -- a variable, or a 0-ary symbol
>           | numeral
>           | _                              -- a wildcard, in patterns only
>           | ( term )
>           | { term }                       -- a schema parameter, within an application only
> atom    ::= term = term | term            -- a comparison standing alone is its equation with 1
> formula ::= atom | _|_ | ~ formula
>           | formula /\ formula | formula \/ formula | formula ==> formula
>           | ( formula )
> sequent ::= [formula {, formula}] |- formula

A schema is applied to its parameter first, a symbol name or a lambda
@λ x. body@ closed over its binders, then to its arguments: @mu {lt} 3 0@,
@mu sgn 5@, @mu {λ i. 3 < i} 10@.  The successor is @S@ or @Succ@: @S (S x)@.

The fixities are those of "Language.Praxis.PRA.Syntax": @=@ binds tightest,
then conjunction, disjunction and implication, all of them associating to the
right.  @~A@ is sugar for @A ==> _|_@ and binds tighter than the binary
connectives.  The Unicode spellings @∧ ∨ → ⊥ ⊢ ¬@ are accepted for the ASCII
connectives, absurdity, turnstile and negation.  Comments run from @--@ to
the end of the line, or between @{-@ and @-}@.

An application of a comparison, @<@, @<=@ or @==@, may stand alone as an
atom, for its equation with @1@: @x < y@ is @(x < y) = 1@, and is shown so.

Identifiers start with a letter and continue with letters, digits, @_@ and
@'@.  An identifier the signature names is a symbol; how any other identifier
is read is decided by the 'Scope', which is what lets the same grammar serve
both closed sequents and the schematic ones of a derived rule.

An identifier applied to arguments in parentheses, @P(t)@ or @P(t, s)@, is
a metavariable declared with parameters, which the scope of a derived rule
provides.

>>> :seti -XDataKinds -XQuasiQuotes -XPatternSynonyms
>>> import Data.Sized (pattern Nil, pattern (:<))
>>> import Data.Type.Ordinal (od)
>>> import Language.Praxis.PRA.PrimitiveRecursion
>>> import Language.Praxis.PRA.Signature
>>> import Language.Praxis.PRA.Syntax.Pretty
>>> plus = Rec (Proj [od|0|]) (Comp Succ (Proj [od|1|] :< Nil)) :: PRFCode 2
>>> sc = plainScope (signature [symbol "plus" plus])
>>> renderFormula (scopeSignature sc) id <$> parseFormula sc "a = 0 ∧ ¬ plus x (S y) = 2 → b = 1"
Right "a = 0 /\\ ~x + S y = 2 ==> b = 1"
>>> renderSequent (scopeSignature sc) id <$> parseSequent sc "a = 0, a = 0 |- a = 0"
Right "a = 0, a = 0 |- a = 0"
>>> either (const "no") (const "yes") (parseTerm sc "plus x")
"no"
>>> renderFormula builtin id <$> parseFormula (plainScope builtin) "x < y /\\ (x <= y) = 1"
Right "x < y /\\ x <= y"
-}
module Language.Praxis.PRA.Syntax.Parser (
  -- * Scopes
  Scope (..),
  plainScope,
  SyntaxError,
  syntaxErrorPosition,

  -- * Comparisons
  comparisonSymbols,
  isComparison,

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
  termAtomP,
  atomicP,
  formulaP,
  sequentP,
  hypothesesP,
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

import Control.Exception (Exception (..))
import Control.Monad (guard, unless, void)
import Data.Bifunctor (first)
import Data.Foldable (toList)
import Data.Hashable (Hashable)
import Data.List (nub)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Multiset qualified as MS
import Data.Proxy (Proxy (..))
import Data.Sized qualified as SV
import Data.Text qualified as T
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Type.Natural (sNat)
import Data.Void (Void)
import GHC.TypeNats (KnownNat, natVal)
import Language.Praxis.PRA.Pattern
import Language.Praxis.PRA.PrimitiveRecursion.Code qualified as PR
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Compile (SomeProgram (..), definitionCode, elaborateEquations)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Env qualified as E
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Error (ElaborationError (..))
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Parser (Parser, TermSyntax (..), eqAtomWith, eqTermWith, identifier, spaceConsumer, wildcard)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Parser qualified as EP
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Rename (signatureEnv)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax qualified as E
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Variadic (expandTerm)
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.Signature (Signature, Symbol (..), lookupSymbol, symbolArity)
import Language.Praxis.PRA.Syntax
import Numeric.Natural (Natural)
import Text.Megaparsec (ParseErrorBundle, attachSourcePos, bundleErrors, bundlePosState, choice, eof, errorBundlePretty, errorOffset, getOffset, notFollowedBy, oneOf, option, optional, parse, region, sepBy1, setErrorOffset, sourceColumn, sourceLine, try, unPos, (<?>), (<|>))
import Text.Megaparsec.Char qualified as CP

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
  , scopeApplied :: String -> [Term (Hole a)] -> Either String (Formula (Hole a))
  -- ^ a metavariable applied to arguments, standing as a formula: @P(t)@
  , scopeAppliedAtom :: String -> [Term (Hole a)] -> Either String (Atomic (Hole a))
  -- ^ the same, standing as an atom
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
    , scopeApplied = \n _ -> Left (n <> " takes no arguments")
    , scopeAppliedAtom = \n _ -> Left (n <> " takes no arguments")
    }

-- | A syntax error. Render it for a human with @displayException@.
newtype SyntaxError = SyntaxError (ParseErrorBundle T.Text Void)
  deriving (Show, Eq)

instance Exception SyntaxError where
  displayException (SyntaxError bundle) = errorBundlePretty bundle

-- | Where a syntax error is: line and column, from 1.
syntaxErrorPosition :: SyntaxError -> (Int, Int)
syntaxErrorPosition (SyntaxError bundle) =
  let (errs, _) = attachSourcePos errorOffset (bundleErrors bundle) (bundlePosState bundle)
      pos = snd (NE.head errs)
   in (unPos (sourceLine pos), unPos (sourceColumn pos))

-- | Run a parser on a whole input.
runParserFully :: Parser x -> String -> Either SyntaxError x
runParserFully p = either (Left . SyntaxError) Right . parse (spaceP *> p <* eof) "" . T.pack

parseTerm :: Scope a -> String -> Either SyntaxError (Term a)
parseTerm sc = runParserFully (closedP (termP sc))

parseAtomic :: Scope a -> String -> Either SyntaxError (Atomic a)
parseAtomic sc = runParserFully (closedP (atomicP sc))

parseFormula :: Scope a -> String -> Either SyntaxError (Formula a)
parseFormula sc = runParserFully (closedP (formulaP sc))

parseSequent :: (Hashable a) => Scope a -> String -> Either SyntaxError (Sequent a)
parseSequent sc = runParserFully (sequentP sc)

parseTermPattern :: Scope a -> String -> Either SyntaxError (Term (Hole a))
parseTermPattern sc = runParserFully (termP sc)

parseAtomicPattern :: Scope a -> String -> Either SyntaxError (Atomic (Hole a))
parseAtomicPattern sc = runParserFully (atomicP sc)

parseFormulaPattern :: Scope a -> String -> Either SyntaxError (Formula (Hole a))
parseFormulaPattern sc = runParserFully (formulaP sc)

-- * Comparisons

{- |
The symbols the parser reads the comparisons @<@, @<=@ and @==@ as, when
the signature has them: the first candidate of arity two, as for any
operator.
-}
comparisonSymbols :: Signature -> [Symbol]
comparisonSymbols sig =
  [ sym
  | candidates <- [["lt"], ["le", "lte"], ["eq"]]
  , Just sym <- [listToMaybe (mapMaybe binary candidates)]
  ]
  where
    binary c = do
      sym <- lookupSymbol c sig
      guard (symbolArity sym == 2)
      pure sym

{- |
Whether the term is an application of a comparison.  Standing alone as an
atom, it is its equation with @1@, and "Language.Praxis.PRA.Syntax.Pretty"
shows such an equation the same way.
-}
isComparison :: Signature -> Term b -> Bool
isComparison sig = \case
  App f args | [_, _] <- toList args -> any ((== F.SomeFunction f) . symbolFunction) (comparisonSymbols sig)
  _ -> False

-- * Lexemes

-- | Whitespace and comments, those of the equation language.
spaceP :: Parser ()
spaceP = spaceConsumer

lexeme :: Parser x -> Parser x
lexeme = EP.lexeme

-- | A punctuation token.
symbolP :: String -> Parser ()
symbolP = void . EP.symbol . T.pack

-- | A word which must not run on into an identifier.
keywordP :: String -> Parser ()
keywordP w = EP.reserved (T.pack w) <?> show w

-- | An identifier which is neither @S@ nor a reserved word of the scope.
identifierP :: Scope a -> Parser String
identifierP sc = T.unpack <$> identifier ("S" : reservedWords sc) <?> "identifier"

reservedWords :: Scope a -> [T.Text]
reservedWords = map T.pack . scopeReserved

wildcardP :: Parser ()
wildcardP = wildcard

parens :: Parser x -> Parser x
parens = EP.parens

braces :: Parser x -> Parser x
braces = EP.braces

commaP :: Parser ()
commaP = symbolP ","

-- | @=@, but not the start of @==>@.
equalsP :: Parser ()
equalsP = lexeme (try (CP.char '=' *> notFollowedBy (oneOf ("=>" :: String)))) <?> "\"=\""

turnstileP :: Parser ()
turnstileP = lexeme (try (void (CP.string "|-") <|> void (CP.char '\8866'))) <?> "\"|-\""

-- | Reject the wildcards of a pattern.
closedP :: (Traversable t) => Parser (t (Hole a)) -> Parser (t a)
closedP p = do
  o <- getOffset
  x <- p
  case closed x of
    Just y -> pure y
    Nothing -> region (setErrorOffset o) (fail "a wildcard is not allowed here")

-- * Terms

-- | The term grammar of the equation language, with the scope's reserved words and wildcards.
termSyntax :: Scope a -> TermSyntax
termSyntax sc = TermSyntax {syntaxReserved = reservedWords sc, syntaxWildcard = True}

-- | A term: an application, an operator expression, a conditional or a bounded search.
termP :: Scope a -> Parser (Term (Hole a))
termP sc = resolvedP sc (eqTermWith (termSyntax sc))

-- | A term in argument position: a name, a numeral, a wildcard, or a parenthesized term.
termAtomP :: Scope a -> Parser (Term (Hole a))
termAtomP sc = resolvedP sc (eqAtomWith (termSyntax sc))

-- A term which cannot be resolved is reported at its start.
resolvedP :: Scope a -> Parser (E.EqTerm T.Text) -> Parser (Term (Hole a))
resolvedP sc p = do
  o <- getOffset
  raw <- p
  either (region (setErrorOffset o) . fail) pure (resolveTerm sc raw)

{- | Resolve a term against the signature and the scope. The symbols and
schemas of the signature, with @S@ and @Succ@ for the successor, take
precedence over the scope, which reads every other identifier. A schema takes
its parameter first, a symbol name or a lambda; a bounded search is desugared
into the schema @mu@ over the variables it captures, and a lambda, which must
be closed, is compiled as a definition of its own.
-}
resolveTerm :: forall a. Scope a -> E.EqTerm T.Text -> Either String (Term (Hole a))
resolveTerm sc raw = do
  let initial = signatureEnv (scopeSignature sc)
      variables = nub [n | n <- names raw, Map.notMember n initial, n /= "_"]
  (env, term) <- elaboration (expandTerm initial variables raw)
  go env term
  where
    elaboration :: Either ElaborationError x -> Either String x
    elaboration = first displayException

    go :: E.Env -> E.EqTerm T.Text -> Either String (Term (Hole a))
    go env = \case
      E.LitET n -> Right (Lit n)
      E.NameET "_" -> Right (Var Wild)
      E.IfThenElseET c t e -> case Map.lookup "ifte" env of
        Just (E.SomeFunction (fun :: E.Function m)) -> case testEquality (sNat @m) (sNat @3) of
          Just Refl -> do
            f <- function fun
            c' <- go env c
            t' <- go env t
            e' <- go env e
            pure (App f (c' SV.:< t' SV.:< e' SV.:< SV.Nil))
          Nothing -> elaboration (Left (ConditionalArityMismatch (natVal (Proxy @m))))
        _ -> elaboration (Left ConditionalOutOfScope)
      E.InfixET l op r -> do
        f <- binary env op
        l' <- go env l
        r' <- go env r
        pure (App f (l' SV.:< r' SV.:< SV.Nil))
      E.LamET {} -> elaboration (Left LambdaOutsideSchemaParameter)
      E.MuET {} -> elaboration (Left BoundedSearchOutOfScope)
      E.SplatET xs -> elaboration (Left (SplatOutsideVariadicSchema xs))
      E.BoundET {} -> elaboration (Left BinderOutsideLambda)
      term@(_ E.:@ _) -> application env (spine term)
      term@(E.NameET _) -> application env (term, [])

    application :: E.Env -> (E.EqTerm T.Text, [E.EqTerm T.Text]) -> Either String (Term (Hole a))
    application env (E.NameET n, arguments) = case Map.lookup n env of
      Just (E.SomeFunction (fun :: E.Function m)) -> do
        checkArity n (natVal (Proxy @m)) arguments
        f <- function fun
        args <- traverse (go env) arguments
        applied f args
      Just (E.ImportedSchema sName pArity sArity inst) -> case arguments of
        [] -> elaboration (Left (SchemaArgumentCountMismatch sName 1 0))
        param : rest -> do
          checkArity sName sArity rest
          pFun <- parameter env sName pArity param
          instantiated <- elaboration (first SchemaFailure (inst pFun))
          args <- traverse (go env) rest
          case instantiated of
            F.SomeFunction instFun -> applied instFun args
      Just (E.ImportedVariadic sName fixed _ _) -> elaboration (Left (UnexpandedVariadicApplication sName fixed))
      Just (E.SchemaDef sName _ _ _) -> Left ("internal: a schema definition " <> T.unpack sName <> " in a signature")
      Just (E.VariadicDef tmpl) -> Left ("internal: a template " <> T.unpack (E.templateName tmpl) <> " in a signature")
      Nothing
        | n == "_" -> Left "a wildcard cannot be applied"
        | null arguments -> fmap Named <$> scopeTerm sc (T.unpack n)
        | otherwise -> elaboration (Left (AppliedVariable n))
    application _ (hd, _) = elaboration (Left (InvalidApplicationHead hd))

    checkArity :: T.Text -> Natural -> [x] -> Either String ()
    checkArity n expected arguments =
      unless (fromIntegral (length arguments) == expected) $
        elaboration (Left (ArityMismatch n expected (fromIntegral (length arguments))))

    -- The successor of a numeral is the next numeral.
    applied :: (KnownNat n) => F.Function n -> [Term (Hole a)] -> Either String (Term (Hole a))
    applied fun args = case (fun, args) of
      (F.Primitive PR.Succ, [x]) -> Right (suc x)
      _ -> case SV.fromList' args of
        Just xs -> Right (App fun xs)
        Nothing -> Left "internal: an argument vector of the wrong length"

    -- The binary symbol an operator stands for.
    binary :: E.Env -> T.Text -> Either String (F.Function 2)
    binary env op = search candidates
      where
        candidates = case op of
          "+" -> ["add", "plus"]
          "*" -> ["mul", "times"]
          "<" -> ["lt"]
          "-" -> ["sub"]
          "<=" -> ["le", "lte"]
          "==" -> ["eq"]
          "^" -> ["pow"]
          _ -> []
        search [] = elaboration (Left (if null candidates then UnknownOperator op else OperatorOutOfScope op candidates))
        search (c : cs) = case Map.lookup c env of
          Just (E.SomeFunction (fun :: E.Function m)) | Just Refl <- testEquality (sNat @m) (sNat @2) -> function fun
          _ -> search cs

    -- A schema parameter: a symbol of the parameter arity, or a lambda of it.
    parameter :: E.Env -> T.Text -> Natural -> E.EqTerm T.Text -> Either String F.SomeFunction
    parameter env sName pArity = \case
      E.NameET p -> case Map.lookup p env of
        Just (E.SomeFunction (fun :: E.Function k)) -> do
          unless (natVal (Proxy @k) == pArity) $
            elaboration (Left (SchemaArgumentArityMismatch p pArity (natVal (Proxy @k))))
          F.SomeFunction <$> function fun
        Just _ -> elaboration (Left (SchemaArgumentIsSchema p))
        Nothing -> elaboration (Left (UnknownName p))
      E.LamET hints body -> do
        unless (fromIntegral (length hints) == pArity) $
          elaboration (Left (LambdaArityMismatch sName pArity (fromIntegral (length hints))))
        compileLambda env hints body
      other -> elaboration (Left (InvalidSchemaArgument other))

    -- A closed lambda is compiled as a definition over its binders.
    compileLambda :: E.Env -> [E.IrrelevantName] -> E.EqTerm T.Text -> Either String F.SomeFunction
    compileLambda env hints body = do
      let hinted = map E.rawName hints
          params
            | nub hinted == hinted = hinted
            | otherwise = ["λ" <> T.pack (show i) | i <- [0 .. length hints - 1]]
          equation =
            E.Equation
              { E.name = lambdaName
              , E.schemaParams = []
              , E.args = map E.VarP params
              , E.variadic = Nothing
              , E.clause = openLambda params 0 body
              }
      definitions <- elaboration (elaborateEquations env [equation])
      case definitionCode <$> Map.lookup lambdaName definitions of
        Just (SomeProgram code) -> Right (F.SomeFunction (F.Inline code))
        Nothing -> Left "internal: the lambda was not compiled"

    lambdaName :: T.Text
    lambdaName = "λ"

    -- Replace the occurrences of a lambda's own binders by pattern variables.
    openLambda :: [T.Text] -> Int -> E.EqTerm T.Text -> E.EqTerm T.Text
    openLambda params = open
      where
        open depth = \case
          E.BoundET d i | d == depth, i < length params -> E.NameET (params !! i)
          E.LamET hs b -> E.LamET hs (open (depth + 1) b)
          E.MuET h bound b -> E.MuET h (open depth bound) (open (depth + 1) b)
          f E.:@ x -> open depth f E.:@ open depth x
          E.InfixET l op r -> E.InfixET (open depth l) op (open depth r)
          E.IfThenElseET c t e -> E.IfThenElseET (open depth c) (open depth t) (open depth e)
          t -> t

    function :: E.Function n -> Either String (F.Function n)
    function = \case
      E.Primitive code -> Right (F.Primitive code)
      E.Bound fun -> Right fun
      E.Defined ident -> Left ("internal: an unbound definition " <> T.unpack ident)
      E.SchemaApp sName _ -> Left ("internal: an uninstantiated application of the schema " <> T.unpack sName)

    -- The free names of a term, in order of occurrence.
    names :: E.EqTerm T.Text -> [T.Text]
    names = \case
      E.NameET n -> [n]
      f E.:@ x -> names f <> names x
      E.InfixET l _ r -> names l <> names r
      E.IfThenElseET c t e -> names c <> names t <> names e
      E.LamET _ b -> names b
      E.MuET _ bound b -> names bound <> names b
      _ -> []

    spine :: E.EqTerm T.Text -> (E.EqTerm T.Text, [E.EqTerm T.Text])
    spine = collect []
      where
        collect xs (f E.:@ x) = collect (x : xs) f
        collect xs f = (f, xs)

-- * Formulae

atomicP :: Scope a -> Parser (Atomic (Hole a))
atomicP sc = metaAtomicP <|> equationP
  where
    -- A comparison may stand alone, for its equation with 1.
    equationP = do
      s <- termP sc
      if isComparison (scopeSignature sc) s
        then option (s :=== Lit 1) ((s :===) <$> (equalsP *> termP sc))
        else (s :===) <$> (equalsP *> termP sc)
    metaAtomicP = try do
      name <- identifierP sc
      optional (parens (termP sc `sepBy1` commaP)) >>= \case
        Nothing -> maybe (fail "not an atom") (pure . fmap Named) (scopeAtomic sc name)
        Just args -> either fail pure (scopeAppliedAtom sc name args)

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
    -- An atom before a parenthesized formula: (x < y) may begin an equation, (x < y) = 0.
    unaryP =
      choice
        [ (:==> Bot) <$> (negOp *> unaryP)
        , Bot <$ botP
        , Atm <$> try (atomicP sc)
        , try (parens (formulaP sc))
        , metaFormulaP
        ]
        <?> "formula"
    metaFormulaP = try do
      name <- identifierP sc
      optional (parens (termP sc `sepBy1` commaP)) >>= \case
        Nothing -> maybe (fail "not a formula") (pure . fmap Named) (scopeFormula sc name)
        Just args -> either fail pure (scopeApplied sc name args)
    andOp = lexeme (try (void (CP.string "/\\") <|> void (CP.char '\8743'))) <?> "\"/\\\""
    orOp = lexeme (try (void (CP.string "\\/") <|> void (CP.char '\8744'))) <?> "\"\\/\""
    implOp = lexeme (try (void (CP.string "==>") <|> void (CP.char '\8594'))) <?> "\"==>\""
    negOp = lexeme (void (CP.char '~') <|> void (CP.char '\172')) <?> "\"~\""
    botP = lexeme (try (void (CP.string "_|_") <|> void (CP.char '\8869'))) <?> "\"_|_\""

-- * Sequents

-- | A sequent is closed: it may not contain wildcards.
sequentP :: (Hashable a) => Scope a -> Parser (Sequent a)
sequentP sc = (\(hs, c) -> foldr MS.insertOne MS.empty hs :|- c) <$> hypothesesP sc

-- | A sequent as written: its hypotheses in order, and its succedent.
hypothesesP :: Scope a -> Parser ([Formula a], Formula a)
hypothesesP sc = (,) <$> option [] (itemP `sepBy1` commaP) <* turnstileP <*> closedP (formulaP sc)
  where
    itemP = contextP <|> closedP (formulaP sc)
    contextP = try do
      name <- identifierP sc
      maybe (fail "not a context") pure (scopeContext sc name)
