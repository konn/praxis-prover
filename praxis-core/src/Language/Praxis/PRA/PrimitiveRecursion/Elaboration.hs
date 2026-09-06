{-# LANGUAGE OverloadedStrings #-}

{- | Applicative equation syntax and arity-checked name resolution.
Applications associate to the left; nested arguments use parentheses.
Multiple equations are separated by semicolons (no Haskell layout rule).
Renaming checks scope and arity; it does not compile recursion to PRF codes.
-}
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration (
  Equation (..),
  Pattern (..),
  EqTerm (..),
  Function (..),
  SomeFunction (..),
  Env,
  FunctionalTerm (..),
  RenamedEquation (..),
  signatureEnv,
  equationEnv,
  renameTerm,
  renameEquation,
  renameEquations,
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

import Control.Monad (foldM, void)
import Data.Hashable (Hashable)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Proxy (Proxy (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Sized qualified as SV
import Data.Text qualified as T
import Data.Void (Void)
import GHC.Generics (Generic)
import GHC.TypeNats (KnownNat, SomeNat (..), natVal, someNatVal)
import Language.Praxis.PRA.PrimitiveRecursion (PRFCode, V)
import Language.Praxis.PRA.PrimitiveRecursion qualified as PR
import Language.Praxis.PRA.Signature qualified as Sig
import Numeric.Natural (Natural)
import Text.Megaparsec (Parsec, between, eof, errorBundlePretty, many, notFollowedBy, parse, sepEndBy, try, (<|>))
import Text.Megaparsec.Char qualified as CP
import Text.Megaparsec.Char.Lexer qualified as L

data Equation name = Equation
  { name :: !name
  , args :: ![Pattern name]
  , clause :: !(EqTerm name)
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (Hashable)

data Pattern name = VarP !name | SuccP !(Pattern name) | ZeroP
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (Hashable)

-- | Unresolved syntax: identifiers have no variable/function distinction.
data EqTerm name
  = LitET !Natural
  | NameET !name
  | EqTerm name :@ EqTerm name
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (Hashable)

infixl 9 :@

-- | A reference to a top-level definition, or an existing primitive code.
data Function n = Defined !T.Text | Primitive !(PRFCode n)

deriving instance (KnownNat n) => Show (Function n)

data SomeFunction = forall n. (KnownNat n) => SomeFunction !(Function n)

deriving instance Show SomeFunction

type Env = Map T.Text SomeFunction

{- | Each application carries a vector of exactly the callee's arity.
Variables retain their textual names from the source patterns.
-}
data FunctionalTerm
  = LitFT !Natural
  | VarFT !T.Text
  | forall n. (KnownNat n) => AppFT !(Function n) !(V n FunctionalTerm)

deriving instance Show FunctionalTerm

data RenamedEquation = RenamedEquation
  { renamedName :: !T.Text
  , renamedArgs :: ![Pattern T.Text]
  , renamedClause :: !FunctionalTerm
  }
  deriving (Show)

{- | Existing symbols, with S and Succ as built-in successor aliases.
Explicit signature entries take precedence over the aliases.
-}
signatureEnv :: Sig.Signature -> Env
signatureEnv sig = Map.fromList (map entry (Sig.symbols sig)) <> builtins
  where
    entry sym = case Sig.symbolCode sym of
      Sig.SomeCode code -> (T.pack (Sig.symbolName sym), SomeFunction (Primitive code))
    builtins = Map.fromList [("S", SomeFunction (Primitive PR.Succ)), ("Succ", SomeFunction (Primitive PR.Succ))]

{- | Collect all definitions before renaming, allowing forward and self references.
Clauses of a definition must agree on arity. Existing names cannot be redefined.
-}
equationEnv :: Env -> [Equation T.Text] -> Either String Env
equationEnv initial equations = (<> initial) <$> foldM add Map.empty equations
  where
    add env eq
      | Map.member (name eq) initial = Left ("Function already defined: " <> T.unpack (name eq))
      | Just (SomeFunction (f :: Function n)) <- Map.lookup (name eq) env =
          if natVal (Proxy @n) == arity
            then Right (Map.insert (name eq) (SomeFunction f) env)
            else Left ("Inconsistent arity for " <> T.unpack (name eq))
      | otherwise = case someNatVal arity of
          SomeNat (_ :: Proxy n) -> Right (Map.insert (name eq) (SomeFunction (Defined (name eq) :: Function n)) env)
      where
        arity = fromIntegral (length (args eq))

-- | Local variables shadow global functions and cannot be applied.
renameTerm :: Env -> Set T.Text -> EqTerm T.Text -> Either String FunctionalTerm
renameTerm env locals term = case spine term [] of
  (LitET n, []) -> Right (LitFT n)
  (NameET ident, arguments)
    | Set.member ident locals ->
        if null arguments then Right (VarFT ident) else Left ("Cannot apply variable " <> T.unpack ident)
    | Just (SomeFunction (fun :: Function n)) <- Map.lookup ident env -> do
        let expected = natVal (Proxy @n)
        if fromIntegral (length arguments) /= expected
          then Left (T.unpack ident <> " takes " <> show expected <> " arguments, given " <> show (length arguments))
          else do
            renamed <- traverse (renameTerm env locals) arguments
            case SV.fromList' renamed of
              Just xs -> Right (AppFT fun xs)
              Nothing -> Left ("Invalid argument vector for " <> T.unpack ident)
    | otherwise -> Left ("Unknown name: " <> T.unpack ident)
  _ -> Left "Only named functions can be applied"
  where
    spine (f :@ x) xs = spine f (x : xs)
    spine f xs = (f, xs)

{- | Rename a clause in an environment containing its top-level definition.
Patterns must be jointly linear: each variable may occur at most once
across all arguments, including beneath successor patterns.
-}
renameEquation :: Env -> Equation T.Text -> Either String RenamedEquation
renameEquation env eq = do
  case Map.lookup (name eq) env of
    Nothing -> Left ("Unknown function: " <> T.unpack (name eq))
    Just (SomeFunction (_ :: Function n))
      | natVal (Proxy @n) /= fromIntegral (length (args eq)) -> Left ("Inconsistent arity for " <> T.unpack (name eq))
      | otherwise -> Right ()
  locals <- foldM bind Set.empty (args eq)
  body <- renameTerm env locals (clause eq)
  pure (RenamedEquation (name eq) (args eq) body)
  where
    bind locals ZeroP = Right locals
    bind locals (SuccP p) = bind locals p
    bind locals (VarP ident)
      | Set.member ident locals = Left ("Nonlinear pattern: repeated variable " <> T.unpack ident)
      | otherwise = Right (Set.insert ident locals)

renameEquations :: Env -> [Equation T.Text] -> Either String [RenamedEquation]
renameEquations env equations = do
  env' <- equationEnv env equations
  traverse (renameEquation env') equations

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
