{- |
The textual syntax of tactics, and of the declarations which use them.

> tactic  ::= alt {; alt}                  -- t ; u       : u on every goal t leaves
> alt     ::= simple {| simple}            -- t | u       : u if t fails; committed
> simple  ::= basic {'{' tactic '}'}       -- t {u1} … {un}: t must leave n goals, ui gets goal i
> basic   ::= Rule {arg}                   -- a rule of the calculus, applied backwards
>           | refl | symmetry atom | rewrite atom in atom
>           | induction ident [as ident] | assumption | exact ident
>           | skip | try basic | repeat basic | ( tactic )
> arg     ::= _ | ident | term | ( atom ) | ( formula )   -- by the sort of the parameter
>
> decl    ::= theorem ident : sequent by tactic
>           | rule ident {binder} : sequent by tactic
> binder  ::= ( ident {ident} : sort )      -- metavariables
>           | ( ident : sequent )           -- a premise, for exact
> sort    ::= var | term | atom | formula | ctx

The primitive tactics are the rule labels of "Language.Praxis.PRA.Rule.G3i",
verbatim: @ConjL@, @ImplR@, @Ind@ and so on.  Their arguments follow the
parameters of the rule in order; trailing arguments may be omitted and any
argument may be @_@, in which case it is inferred from the goal.  Term and
variable arguments are written bare, atom and formula arguments in
parentheses.  Context parameters are never written.  A metavariable must be
declared before the premises which mention it.

The words above, the rule labels and @S@ are reserved.
-}
module Language.Praxis.PRA.Tactic.Parser (
  -- * Declarations
  Decl (..),
  Binder (..),
  binderMetas,
  parseDecls,
  parseGoal,
  parseTactic,

  -- * The parsers
  declsP,
  declP,
  goalP,
  tacticP,

  -- * Scopes
  tacticKeywords,
  withTacticScope,
  plainMetaScope,
) where

import Data.Hashable (Hashable)
import Language.Praxis.PRA.Pattern (Hole (..))
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.Rule qualified as R
import Language.Praxis.PRA.Signature (Signature)
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Syntax.Parser
import Language.Praxis.PRA.Tactic
import Text.Megaparsec
import Text.Megaparsec.Char (char)

-- * Scopes

-- | The reserved words of the tactic language, besides @S@.
tacticKeywords :: [String]
tacticKeywords =
  map (R.ruleLabel . ruleSpec) [minBound .. maxBound]
    <> words "refl symmetry rewrite in induction as assumption exact skip try repeat"
    <> words "theorem rule by var term atom formula ctx"

-- | Reserve the words of the tactic language in a scope.
withTacticScope :: Scope a -> Scope a
withTacticScope sc = sc {scopeReserved = tacticKeywords <> scopeReserved sc}

{- |
A scope for a declaration over plain names.  A @var@ or @term@ metavariable is
simply a variable; the other sorts have no counterpart among plain names, and
are refused.
-}
plainMetaScope :: Signature -> [(String, R.Sort)] -> Scope String
plainMetaScope sig metas =
  (plainScope sig)
    { scopeVariable = \n -> n <$ plain n
    , scopeTerm = \n -> Var n <$ plain n
    }
  where
    plain n = case lookup n metas of
      Just s
        | s `elem` [R.AtomS, R.FormS, R.CtxS] ->
            Left (n <> " is a " <> sortName s <> " metavariable, which only the quasiquoter supports")
      _ -> Right ()
    sortName = \case
      R.VarS -> "var"
      R.TermS -> "term"
      R.AtomS -> "atom"
      R.FormS -> "formula"
      R.CtxS -> "ctx"

-- * Declarations

data Binder a
  = -- | metavariables of a sort
    MetaBinder ![String] !R.Sort
  | -- | a premise, with the sequent it is declared to establish
    PremiseBinder !String !(Sequent a)
  deriving (Show, Eq)

-- | The metavariables a list of binders declares, in order.
binderMetas :: [Binder a] -> [(String, R.Sort)]
binderMetas bs = [(n, s) | MetaBinder ns s <- bs, n <- ns]

-- | A theorem, or a derived rule when it has binders.
data Decl a = Decl
  { declName :: !String
  , declBinders :: ![Binder a]
  , declGoal :: !(Sequent a)
  , declTactic :: !(Tactic a)
  }
  deriving (Show, Eq)

{- |
Parse declarations.  The function builds the scope in which the sequents and
the tactic of a declaration are read, from the metavariables it declares;
'plainMetaScope' serves for plain names.
-}
parseDecls :: (Hashable a) => ([(String, R.Sort)] -> Scope a) -> String -> Either String [Decl a]
parseDecls mkScope = runParserFully (declsP mkScope)

-- | Parse @sequent by tactic@.
parseGoal :: (Hashable a) => Scope a -> String -> Either String (Sequent a, Tactic a)
parseGoal sc = runParserFully (goalP sc)

parseTactic :: Scope a -> String -> Either String (Tactic a)
parseTactic sc = runParserFully (tacticP sc)

declsP :: (Hashable a) => ([(String, R.Sort)] -> Scope a) -> Parser [Decl a]
declsP mkScope = many (declP mkScope)

declP :: forall a. (Hashable a) => ([(String, R.Sort)] -> Scope a) -> Parser (Decl a)
declP mkScope = theoremP <|> ruleP
  where
    theoremP = do
      keywordP "theorem"
      name <- nameP
      symbolP ":"
      uncurry (Decl name []) <$> goalP (mkScope [])
    ruleP = do
      keywordP "rule"
      name <- nameP
      binders <- bindersP []
      symbolP ":"
      uncurry (Decl name binders) <$> goalP (mkScope (binderMetas binders))
    nameP = identifierP (withTacticScope (mkScope []))

    bindersP :: [Binder a] -> Parser [Binder a]
    bindersP acc =
      optional (binderP (withTacticScope (mkScope (binderMetas acc)))) >>= \case
        Nothing -> pure acc
        Just b -> bindersP (acc <> [b])
    binderP sc = parens (try (metaBinderP sc) <|> premiseBinderP sc)
    metaBinderP sc = MetaBinder <$> some (identifierP sc) <* symbolP ":" <*> sortP
    premiseBinderP sc = PremiseBinder <$> identifierP sc <* symbolP ":" <*> sequentP sc
    sortP =
      choice
        [ R.VarS <$ keywordP "var"
        , R.TermS <$ keywordP "term"
        , R.AtomS <$ keywordP "atom"
        , R.FormS <$ keywordP "formula"
        , R.CtxS <$ keywordP "ctx"
        ]
        <?> "sort"

-- | @sequent by tactic@.
goalP :: (Hashable a) => Scope a -> Parser (Sequent a, Tactic a)
goalP sc0 = (,) <$> sequentP sc <* keywordP "by" <*> tacticP sc
  where
    sc = withTacticScope sc0

-- * Tactics

tacticP :: forall a. Scope a -> Parser (Tactic a)
tacticP sc0 = seqP
  where
    sc = withTacticScope sc0

    seqP = foldl1 Then <$> altP `sepBy1` symbolP ";"
    altP = foldl1 OrElse <$> simpleP `sepBy1` orP
    orP = lexeme (try (char '|' *> notFollowedBy (char '-'))) <?> "\"|\""
    simpleP = do
      t <- basicP
      blocks <- many (braces seqP)
      pure (if null blocks then t else Dispatch t blocks)

    basicP :: Parser (Tactic a)
    basicP = do
      pos <- getSourcePos
      let loc = Loc (unPos (sourceLine pos)) (unPos (sourceColumn pos))
      At loc
        <$> choice
          ( [ parens seqP
            , Refl <$ keywordP "refl"
            , Symmetry <$> (keywordP "symmetry" *> atomArgP)
            , Rewrite <$> (keywordP "rewrite" *> atomArgP) <*> (keywordP "in" *> atomArgP)
            , Induction <$> (keywordP "induction" *> variableP) <*> optional (keywordP "as" *> variableP)
            , Assumption <$ keywordP "assumption"
            , Exact <$> (keywordP "exact" *> identifierP sc)
            , Skip <$ keywordP "skip"
            , Try <$> (keywordP "try" *> basicP)
            , Repeat <$> (keywordP "repeat" *> basicP)
            ]
              <> [rule r | r <- [minBound .. maxBound]]
          )
        <?> "tactic"

    rule :: RuleName -> Parser (Tactic a)
    rule r = Apply r <$> (keywordP (R.ruleLabel spec) *> argsP (R.ruleParams spec))
      where
        spec = ruleSpec r

    -- Arguments are taken in order; the first one missing ends them.
    argsP :: [R.Param] -> Parser [Maybe (Arg (Hole a))]
    argsP [] = pure []
    argsP (p : ps) = case p of
      R.PCtx _ -> (Nothing :) <$> argsP ps
      _ ->
        optional (argP p) >>= \case
          Nothing -> pure (map (const Nothing) (p : ps))
          Just arg -> (arg :) <$> argsP ps

    argP :: R.Param -> Parser (Maybe (Arg (Hole a)))
    argP p =
      (Nothing <$ wildcardP)
        <|> Just
        <$> case p of
          R.PVar _ -> ArgVar . Named <$> variableP
          R.PTerm _ -> ArgTerm <$> termP sc
          R.PAtom _ -> ArgAtom <$> parens (atomicP sc)
          R.PForm _ -> ArgForm <$> parens (formulaP sc)
          R.PCtx _ -> empty

    -- An atomic pattern, with or without parentheses.
    atomArgP = try (parens atomArgP) <|> atomicP sc

    variableP :: Parser a
    variableP = do
      o <- getOffset
      n <- identifierP sc
      either (region (setErrorOffset o) . fail) pure (scopeVariable sc n)
