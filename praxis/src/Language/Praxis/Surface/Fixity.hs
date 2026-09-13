{-# LANGUAGE OverloadedStrings #-}

{- |
Fixities, and the association of the operator sequences the parser leaves.

Operators come in three tiers, which never mix by precedence:

* term operators — the arithmetic of @Nat@ (@+@ and @-@ @infixl 6@, @*@
  @infixl 7@, @^@ @infixr 8@) and every operator a module declares, with a
  rational precedence, as in Haskell; an undeclared one is @infixl 9@;
* relations — @≡@ (also @=@), @≠@, @<@, @≤@, @>@, @≥@ and their ASCII
  spellings — which are non-associative and bind looser than every term
  operator, so that @xs <> Nil ≡ xs@ needs no parentheses whatever @<>@'s
  precedence;
* connectives, with Lean's precedences: @¬@ (prefix) 40, @∧@ 35 and @∨@ 30
  to the right, @↔@ 20.

The arrow binds loosest of all and is no operator: the parser handles it.
The fixities of a module hold throughout it, declarations before and after
their uses alike.  Sequences are associated by the algorithm of the Haskell
2010 report (§10.6), with @¬@ in the place of negation.
-}
module Language.Praxis.Surface.Fixity (
  -- * Fixities
  Fixity (..),
  Fixities,
  builtinFixities,
  moduleFixities,
  fixityOf,
  isRelation,
  isConnective,

  -- * Association
  resolveExpr,
  resolveOps,

  -- * Errors
  FixityError (..),
  renderFixityError,
) where

import Control.Monad (foldM, when)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Syntax.Raw

-- * Fixities

-- | An associativity and a precedence, the latter on one scale for all tiers.
data Fixity = Fixity
  { fixityAssoc :: !Assoc
  , fixityPrecedence :: !Rational
  }
  deriving stock (Show, Eq)

-- | The fixities of the term operators, by the operator's text.
type Fixities = Map Text Fixity

-- | Term operators sit above every relation and connective on the common scale.
termTier :: Rational -> Rational
termTier = (1000 +)

-- | The fixities of the arithmetic of @Nat@.
builtinFixities :: Fixities
builtinFixities =
  Map.fromList
    [ ("+", Fixity AssocLeft (termTier 6))
    , ("-", Fixity AssocLeft (termTier 6))
    , ("*", Fixity AssocLeft (termTier 7))
    , ("^", Fixity AssocRight (termTier 8))
    ]

relations :: [Text]
relations = ["≡", "=", "≠", "/=", "<", "≤", "<=", ">", "≥", ">="]

connectives :: Map Text Fixity
connectives =
  Map.fromList
    [ ("∧", Fixity AssocRight 35)
    , ("/\\", Fixity AssocRight 35)
    , ("∨", Fixity AssocRight 30)
    , ("\\/", Fixity AssocRight 30)
    , ("↔", Fixity AssocNone 20)
    , ("<->", Fixity AssocNone 20)
    ]

-- | Whether an operator is a relation between terms.
isRelation :: Text -> Bool
isRelation = (`elem` relations)

-- | Whether an operator is a connective between propositions.
isConnective :: Text -> Bool
isConnective = (`Map.member` connectives)

relationFixity :: Fixity
relationFixity = Fixity AssocNone 50

notPrecedence :: Rational
notPrecedence = 40

-- | The fixity of an operator: a relation, a connective, or a term operator, declared or not.
fixityOf :: Fixities -> Operator -> Fixity
fixityOf fx op
  | isRelation name = relationFixity
  | Just f <- Map.lookup name connectives = f
  | otherwise = Map.findWithDefault (Fixity AssocLeft (termTier 9)) name fx
  where
    name = case operatorName op of
      QName _ (Op t) -> t
      QName _ (Ident t) -> t

-- | The fixities a module declares, over the built-in ones; relations and connectives cannot be redeclared.
moduleFixities :: Module -> Either FixityError Fixities
moduleFixities m = foldM declare builtinFixities [d | Located _ d <- moduleDecls m]
  where
    declared = Map.fromListWith (<>) [(unLocated o, [o]) | DFixity _ _ os <- map unLocated (moduleDecls m), o <- os]
    declare fx = \case
      DFixity assoc prec ops -> foldM (one assoc prec) fx ops
      _ -> pure fx
    one assoc prec fx (Located sp o) = do
      when (isRelation o || isConnective o) $ Left (ReservedFixity (Located sp o))
      case Map.lookup o declared of
        Just (_ : second : _) -> Left (DuplicateFixity second)
        _ -> pure ()
      pure (Map.insert o (Fixity assoc (termTier prec)) fx)

-- * Association

data Tok
  = TOperand !(Located Expr)
  | TOp !(Located Operator) !Fixity
  | TNot !Span

{- |
Associate every operator sequence of an expression, down to its proofs,
which are associated when they are elaborated.
-}
resolveExpr :: Fixities -> Located Expr -> Either FixityError (Located Expr)
resolveExpr fx = go
  where
    go (Located sp e) = case e of
      EOps elems -> traverse element elems >>= resolveOps fx
      EApp f x -> Located sp <$> (EApp <$> go f <*> go x)
      EImplicitApp f x -> Located sp <$> (EImplicitApp <$> go f <*> go x)
      EInfix op l r -> Located sp <$> (EInfix op <$> go l <*> go r)
      ENot x -> Located sp . ENot <$> go x
      EParen x -> Located sp . EParen <$> go x
      ETuple xs -> Located sp . ETuple <$> traverse go xs
      ELam ns b -> Located sp . ELam ns <$> go b
      ECase s alts -> Located sp <$> (ECase <$> go s <*> traverse alt alts)
      EIf c t f -> Located sp <$> (EIf <$> go c <*> go t <*> go f)
      EPi b body -> Located sp <$> (EPi <$> binder b <*> go body)
      EArrow a b -> Located sp <$> (EArrow <$> go a <*> go b)
      EQuant q bs bound body ->
        Located sp <$> (EQuant q <$> traverse binder bs <*> traverse (traverse go) bound <*> go body)
      _ -> pure (Located sp e)
    element = \case
      Operand x -> Operand <$> go x
      other -> pure other
    alt (Located sp (Alt p b)) = Located sp <$> (Alt <$> go p <*> go b)
    binder (Binder i ns t) = Binder i ns <$> traverse go t

-- | Associate one sequence, whose operands are associated already.
resolveOps :: Fixities -> [OpElem] -> Either FixityError (Located Expr)
resolveOps fx elems = do
  (e, rest) <- parseNeg (Fixity AssocNone (-1)) (map tok elems)
  case rest of
    [] -> pure e
    TOp op _ : _ -> Left (MissingOperand op)
    _ -> Left (Internal "an operand after an operand")
  where
    tok = \case
      Operand x -> TOperand x
      InfixOp op -> TOp op (fixityOf fx (unLocated op))
      PrefixNot sp -> TNot sp

    parseNeg :: Fixity -> [Tok] -> Either FixityError (Located Expr, [Tok])
    parseNeg op1 = \case
      TOperand e : rest -> parse1 op1 e rest
      TNot sp : rest
        | fixityPrecedence op1 >= notPrecedence -> Left (MisplacedNot sp)
        | otherwise -> do
            (r, rest') <- parseNeg (Fixity AssocLeft notPrecedence) rest
            parse1 op1 (Located (spanning sp (location r)) (ENot r)) rest'
      TOp op _ : _ -> Left (MissingOperand op)
      [] -> Left (Internal "an empty operator sequence")

    parse1 :: Fixity -> Located Expr -> [Tok] -> Either FixityError (Located Expr, [Tok])
    parse1 op1 e1 = \case
      [] -> Right (e1, [])
      toks@(TOp op2 f2 : rest)
        | p1 == p2 && (a1 /= a2 || a1 == AssocNone) -> Left (Ambiguous op2 f2 op1)
        | p1 > p2 || (p1 == p2 && a1 == AssocLeft) -> Right (e1, toks)
        | otherwise -> do
            (r, rest') <- parseNeg f2 rest
            parse1 op1 (Located (spanning (location e1) (location r)) (EInfix op2 e1 r)) rest'
        where
          Fixity a1 p1 = op1
          Fixity a2 p2 = f2
      TNot sp : _ -> Left (MisplacedNot sp)
      TOperand e : _ -> Left (Internal ("an operand after an operand at " <> show (spanStart (location e))))

-- * Errors

data FixityError
  = -- | two operators of one precedence which do not associate, the second and the fixity of the first
    Ambiguous !(Located Operator) !Fixity !Fixity
  | -- | @¬@ after an operator binding at least as tightly
    MisplacedNot !Span
  | -- | an operator with no operand after it
    MissingOperand !(Located Operator)
  | -- | a second fixity declaration of an operator
    DuplicateFixity !(Located Text)
  | -- | a fixity declared for a relation or a connective
    ReservedFixity !(Located Text)
  | Internal !String
  deriving stock (Show, Eq)

renderFixityError :: FixityError -> (Span, String)
renderFixityError = \case
  Ambiguous (Located sp op) _ _ ->
    (sp, "the operator " <> T.unpack (qnameText (operatorName op)) <> " does not associate with the one before it at the same precedence; add parentheses")
  MisplacedNot sp -> (sp, "¬ cannot follow an operator binding more tightly than it; add parentheses")
  MissingOperand (Located sp op) -> (sp, "the operator " <> T.unpack (qnameText (operatorName op)) <> " lacks an operand")
  DuplicateFixity (Located sp o) -> (sp, "a second fixity declaration for " <> T.unpack o)
  ReservedFixity (Located sp o) -> (sp, T.unpack o <> " is a relation or a connective, whose fixity is fixed")
  Internal msg -> (noSpan, "internal: " <> msg)
