{- |
The textual syntax of tactics, and of the declarations which use them.

> tactic  ::= alt {; alt}                  -- t ; u       : u on every goal t leaves
> alt     ::= simple {| simple}            -- t | u       : u if t fails; committed
> simple  ::= basic {'{' tactic '}'}       -- t {u1} … {un}: t must leave n goals, ui gets goal i
> basic   ::= step [on ident {ident}] [as ident {ident}]
> step    ::= Rule {arg}                   -- a rule of the calculus, applied backwards
>           | refl | symmetry sel | rewrite sel in sel | cong [sel]
>           | induction arg [as ident {ident}] | assumption
>           | exact ident {arg}            -- a premise, a hypothesis, or a lemma with the arguments for its metavariables
>           | calc term {= term [by simple]} -- a chain of equations, each step by its tactic, or by refl
>           | have [ident :] ( formula ) '{' tactic '}'  -- a lemma proved in the block, then a hypothesis
>           | skip | sorry | try basic | repeat basic | ( tactic )
> sel     ::= ident | ( atom )             -- a hypothesis by name, a lemma stating an equation, or the unique hypothesis matching the pattern
> arg     ::= _ | ident | numeral | ( term ) | ( atom ) | ( formula )   -- by the sort of the parameter
>
> quote   ::= [library ident] {decl}       -- the header names a binding for the lemmas in scope
> decl    ::= theorem ident : sequent by tactic
>           | rule ident {binder} : sequent by tactic
> binder  ::= ( ident {ident} : sort )      -- metavariables
>           | ( ident : sequent )           -- a premise, for exact
> sort    ::= var | term | atom | formula | ctx

The primitive tactics are the rule labels of "Language.Praxis.PRA.Rule.G3i",
verbatim: @ConjL@, @ImplR@, @Ind@ and so on.  Their arguments follow the
parameters of the rule in order; trailing arguments may be omitted and any
argument may be @_@, in which case it is inferred from the goal.  A variable
argument is bare; a term argument is a name, a numeral or a parenthesized
term; atom and formula arguments are parenthesized.  Context parameters are
never written.  A metavariable must be
declared before the premises which mention it.

The hypotheses of a goal are named: @H1@, @H2@, … in the order the sequent
lists them, a context metavariable by its own name, and a hypothesis a step
introduces by the next number, or as @as@ says.  @on@ names the hypotheses
a rule acts on, in the order of its principal formulas, or those of a lemma
appealed to; @as@ names the hypotheses the step introduces, in the order of
its premises.  Under @induction t as n H…@ the first name after the
eigenvariable is for the induction hypothesis, the rest for the hypotheses
reintroduced.

@exact@ names a premise of the rule being proved, a hypothesis which is the
succedent, or a lemma: a theorem or rule declared earlier, whose
metavariables take arguments the same way, in the order of its binders.  The
lemmas in scope, with the sorts of their metavariables, are the 'Lemmas' the
parsers are given; a declaration is in scope for the declarations after it.

@calc t0 = t1 by u1 = t2 by u2 …@ proves the goal @t0 = tn@ as a chain: each
step @t(i-1) = ti@ is proved by its tactic under the hypotheses of the goal,
by @refl@ when none is given, and the steps are chained by transitivity.

@cong H@ closes the goal @u = v@ by the hypothesis @H : t = s@, when @v@ is
@u@ with occurrences of @t@ replaced by @s@, or the other way round; @cong@
alone uses the first hypothesis which fits.

@have H: (A) { u }@ proves @A@ by @u@ and goes on with @A@ as the hypothesis
@H@; without a name, the hypothesis is @H@, or the next @H<n>@ when @H@ is
taken.  Blocks after it are for the goal it leaves, as for any step.

Where @symmetry@, @rewrite@ and @cong@ take a hypothesis, they also take the
name of a lemma stating an equation, @|- t = s@ under no hypotheses but a
context metavariable: @cong zeroMinus@ finds the instance of @0 - t = 0@
where the sides of the goal differ, @rewrite zeroMinus in H@ at the first
subterm of @H@ that @0 - t@ matches, and @symmetry@ takes a closed equation;
the instance is cut in and proved by the lemma.

@sorry@ abandons the proof at its goal, which the error then reports; neither
@|@, @try@ nor @repeat@ catches it, so a script may end in @sorry@ to see
where it stands.

The words above, the rule labels and @S@ are reserved.
-}
module Language.Praxis.PRA.Tactic.Parser (
  -- * Declarations
  Decl (..),
  Binder (..),
  binderMetas,
  declLemma,
  Lemmas,
  parseDecls,
  parseDeclsIn,
  parseQuoteIn,
  parseGoal,
  parseGoalIn,
  parseTactic,
  parseTacticIn,
  SyntaxError,

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

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
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
    <> words "refl symmetry rewrite in cong induction as on assumption exact calc have skip sorry try repeat"
    <> words "theorem rule library by var term atom formula ctx"

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
  , declGoal :: !(Goal a)
  , declTactic :: !(Tactic a)
  }
  deriving (Show, Eq)

-- | The lemma a declaration states, once proved; it binds no metavariable, as far as the statement tells.
declLemma :: (Schematic a) => Decl a -> Lemma a
declLemma d =
  Lemma
    { lemmaMetas = binderMetas (declBinders d)
    , lemmaPremises = [(n, s) | PremiseBinder n s <- declBinders d]
    , lemmaGoal = goalSequent (declGoal d)
    , lemmaBound = []
    }

-- | The lemmas a script may appeal to, each with the sorts of its metavariables in the order of its binders.
type Lemmas = Map String [R.Sort]

{- |
Parse declarations.  The function builds the scope in which the sequents and
the tactic of a declaration are read, from the metavariables it declares;
'plainMetaScope' serves for plain names.  Each declaration is a lemma for
those after it.
-}
parseDecls :: (Schematic a) => ([(String, R.Sort)] -> Scope a) -> String -> Either SyntaxError [Decl a]
parseDecls = parseDeclsIn Map.empty

-- | 'parseDecls', with lemmas in scope from the start.
parseDeclsIn :: (Schematic a) => Lemmas -> ([(String, R.Sort)] -> Scope a) -> String -> Either SyntaxError [Decl a]
parseDeclsIn lemmas mkScope = runParserFully (declsP lemmas mkScope)

{- |
Parse a declaration quote: an optional @library ident@ header, naming the
binding the quasiquoter makes for the lemmas in scope, then declarations.
-}
parseQuoteIn :: (Schematic a) => Lemmas -> ([(String, R.Sort)] -> Scope a) -> String -> Either SyntaxError (Maybe String, [Decl a])
parseQuoteIn lemmas mkScope =
  runParserFully ((,) <$> optional (keywordP "library" *> identifierP (withTacticScope (mkScope []))) <*> declsP lemmas mkScope)

-- | Parse @sequent by tactic@.
parseGoal :: (Schematic a) => Scope a -> String -> Either SyntaxError (Goal a, Tactic a)
parseGoal = parseGoalIn Map.empty

parseGoalIn :: (Schematic a) => Lemmas -> Scope a -> String -> Either SyntaxError (Goal a, Tactic a)
parseGoalIn lemmas sc = runParserFully (goalP lemmas sc)

parseTactic :: Scope a -> String -> Either SyntaxError (Tactic a)
parseTactic = parseTacticIn Map.empty

parseTacticIn :: Lemmas -> Scope a -> String -> Either SyntaxError (Tactic a)
parseTacticIn lemmas sc = runParserFully (tacticP lemmas sc)

declsP :: (Schematic a) => Lemmas -> ([(String, R.Sort)] -> Scope a) -> Parser [Decl a]
declsP lemmas0 mkScope = go lemmas0
  where
    go lemmas =
      optional (declP lemmas mkScope) >>= \case
        Nothing -> pure []
        Just d -> (d :) <$> go (Map.insert (declName d) (map snd (binderMetas (declBinders d))) lemmas)

declP :: forall a. (Schematic a) => Lemmas -> ([(String, R.Sort)] -> Scope a) -> Parser (Decl a)
declP lemmas mkScope = theoremP <|> ruleP
  where
    theoremP = do
      keywordP "theorem"
      name <- nameP
      symbolP ":"
      uncurry (Decl name []) <$> goalP lemmas (mkScope [])
    ruleP = do
      keywordP "rule"
      name <- nameP
      binders <- bindersP []
      symbolP ":"
      uncurry (Decl name binders) <$> goalP lemmas (mkScope (binderMetas binders))
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

-- | @sequent by tactic@; the hypotheses are named in the order written.
goalP :: (Schematic a) => Lemmas -> Scope a -> Parser (Goal a, Tactic a)
goalP lemmas sc0 = (,) <$> (uncurry mkGoal <$> hypothesesP sc) <* keywordP "by" <*> tacticP lemmas sc
  where
    sc = withTacticScope sc0

-- * Tactics

tacticP :: forall a. Lemmas -> Scope a -> Parser (Tactic a)
tacticP lemmas sc0 = seqP
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
      t <-
        choice
          ( [ parens seqP
            , Refl <$ keywordP "refl"
            , Symmetry <$> (keywordP "symmetry" *> selectorP)
            , Rewrite <$> (keywordP "rewrite" *> selectorP) <*> (keywordP "in" *> selectorP)
            , Cong <$> (keywordP "cong" *> optional selectorP)
            , inductionP
            , Assumption <$ keywordP "assumption"
            , exactP
            , calcP
            , haveP
            , Skip <$ keywordP "skip"
            , Sorry <$ keywordP "sorry"
            , Try <$> (keywordP "try" *> basicP)
            , Repeat <$> (keywordP "repeat" *> basicP)
            ]
              <> [rule r | r <- [minBound .. maxBound]]
          )
          <?> "tactic"
      on <- optional (keywordP "on" *> some nameP)
      as <- optional (keywordP "as" *> some nameP)
      pure (At loc (maybe id As as (maybe id On on t)))

    -- The names of hypotheses.
    nameP = identifierP sc

    -- The eigenvariable, then the names for the induction hypothesis and the hypotheses reintroduced.
    inductionP = do
      keywordP "induction"
      t <- closedP (termAtomP sc)
      names <- optional (keywordP "as" *> ((,) <$> variableP <*> many nameP))
      pure case names of
        Nothing -> Induction t Nothing
        Just (n, []) -> Induction t (Just n)
        Just (n, hs) -> As hs (Induction t (Just n))

    -- A chain of equations, each step proved by the tactic after by, or by refl.
    calcP = do
      keywordP "calc"
      t0 <- closedP (termP sc)
      steps <- some ((,) <$> (symbolP "=" *> closedP (termP sc)) <*> option Refl (keywordP "by" *> simpleP))
      pure (Calc t0 steps)

    -- A lemma proved in the block, then a hypothesis: named, or H, or the next H<n>.
    haveP = do
      keywordP "have"
      name <- optional (try (nameP <* symbolP ":"))
      case name of
        Nothing -> () <$ optional (symbolP ":")
        Just _ -> pure ()
      f <- closedP (parens (formulaP sc))
      Have name f <$> braces seqP

    -- A premise takes no arguments; a lemma takes those of its metavariables.
    exactP = do
      keywordP "exact"
      name <- identifierP sc
      Exact name <$> argsP (Map.findWithDefault [] name lemmas)

    rule :: RuleName -> Parser (Tactic a)
    rule r = Apply r <$> (keywordP (R.ruleLabel spec) *> argsP (map R.paramSort (R.ruleParams spec)))
      where
        spec = ruleSpec r

    -- Arguments are taken in order; the first one missing ends them.
    argsP :: [R.Sort] -> Parser [Maybe (Arg (Hole a))]
    argsP [] = pure []
    argsP (s : ss) = case s of
      R.CtxS -> (Nothing :) <$> argsP ss
      _ ->
        optional (argP s) >>= \case
          Nothing -> pure (map (const Nothing) (s : ss))
          Just arg -> (arg :) <$> argsP ss

    argP :: R.Sort -> Parser (Maybe (Arg (Hole a)))
    argP s =
      (Nothing <$ wildcardP)
        <|> Just
        <$> case s of
          R.VarS -> ArgVar . Named <$> variableP
          R.TermS -> ArgTerm <$> termAtomP sc
          R.AtomS -> ArgAtom <$> parens (atomicP sc)
          R.FormS -> ArgForm <$> parens (formulaP sc)
          R.CtxS -> empty

    -- A hypothesis: the one named, or the unique one matching a parenthesized atomic pattern.
    selectorP = (ByPattern <$> parens (atomicP sc)) <|> (ByName <$> nameP)

    variableP :: Parser a
    variableP = do
      o <- getOffset
      n <- identifierP sc
      either (region (setErrorOffset o) . fail) pure (scopeVariable sc n)
