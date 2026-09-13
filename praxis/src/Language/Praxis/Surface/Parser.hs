{-# LANGUAGE OverloadedStrings #-}

{- |
The grammar of the surface language, over the tokens and the layout of
"Language.Praxis.Surface.Lexer".

> module   ::= ['module' qname 'where'] {decl}
> decl     ::= 'open' qname ['using' (names) | 'hiding' (names)]
>            | 'data' Name {param} ['=' ctor {'|' ctor}]
>            | 'class' [constraints '=>'] Name name 'where' {name ':' expr}
>            | 'instance' [name ':'] [constraints '=>'] qname atom 'where' {clause}
>            | ('infixl' | 'infixr' | 'infix') rational op {op}
>            | name ':' expr                          -- a signature
>            | expr '=' rhs                           -- a clause
> ctor     ::= Con {atom} | atom {atom} conop atom {atom}   -- conop starts with ':'
> rhs      ::= 'by' tactics | 'calc' calc | expr
> expr     ::= binders ('->' | '→') expr              -- {a : Type} -> …, (x : T) -> …
>            | ('∀' | '∃') qbinders [rel term] (',' | '.') expr
>            | ('\' | 'λ' | 'fun') names ('->' | '=>' | '.') expr
>            | 'if' expr 'then' expr 'else' expr | 'case' expr 'of' {pat '->' expr}
>            | 'by' tactics | 'calc' calc
>            | ops [('->' | '→') expr]
> ops      ::= {'¬'} app {op {'¬'} app}               -- associated by the fixities later
> app      ::= atom {atom | '{' expr '}'}
> atom     ::= qname | numeral | '_' | 'Type' | '⊤' | '⊥' | '(' expr ')' | '⟨' expr, … '⟩'
> calc     ::= term {step} | block of: term {step}, then {step}
> step     ::= ['_'] ('=' | '≡') term [':=' rhs]
> tactic   ::= atomic ['<;>' tactic]

The tactics are those of 'Tactic', spelt as in Lean 4 with Rocq aliases:
@intro@, @intros@, @exact@, @apply@, @rfl@ (@refl@, @reflexivity@), @symm@,
@trans@, @rw@ (@rewrite@) @[e, ← e] at h@, @unfold@, @simp only@,
@constructor@ (@split@), @left@, @right@, @exfalso@, @contradiction@,
@absurd@, @assumption@, @trivial@, @decide@, @cong@ (@congr@), @cases@
(@destruct@), @induction x generalizing y with | C a b ih => …@,
@obtain ⟨x, h⟩ := e@, @exists@ (@use@), @have h : A := proof@, @show@
(@change@), @calc@, @revert@, @clear@, @by_cases h : A@, @sorry@ (@admit@),
@try@, @repeat@, @first | t | u@, @all_goals@, @any_goals@, @case C x =>
tactics@, @{ tactics }@ and @· tactics@; any other expression is a proof term
closing the goal as it can.  The tactic words are not reserved elsewhere.
-}
module Language.Praxis.Surface.Parser (
  parseModule,
  moduleP,
  declP,
  exprP,
  rhsP,
  tacticP,
  tacticsP,
  calcP,
) where

import Data.Functor (($>))
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Lexer
import Language.Praxis.Surface.Syntax.Raw
import Text.Megaparsec hiding (State, token)

-- | Parse a module; the file name is for error messages.
parseModule :: FilePath -> Text -> Either SyntaxError Module
parseModule = runSurfaceParser moduleP

moduleP :: Parser Module
moduleP = do
  name <- option (Located noSpan (unqualified (Ident "Main"))) (keyword "module" *> qualifiedName <* keyword "where")
  Module name <$> block declP

-- | A node spanning from a position to the end of the last token read.
spanned :: (Int, Int) -> a -> Parser (Located a)
spanned start x = locatedFrom start (pure x)

-- * Declarations

declP :: Parser (Located Decl)
declP = located (choice [openP, dataP, classP, instanceP, fixityP, try signatureP, clauseP]) <?> "declaration"

openP :: Parser Decl
openP = do
  keyword "open"
  n <- qualifiedName
  spec <-
    option OpenAll $
      (keyword "using" *> (OpenUsing <$> names)) <|> (keyword "hiding" *> (OpenHiding <$> names))
  pure (DOpen n spec)
  where
    names = bracketed "(" ")" (nameSegment `sepBy` symbol ",")

-- | An unqualified name: an identifier, or an operator in parentheses.
nameSegment :: Parser (Located Segment)
nameSegment = do
  Located sp q <- qualifiedName
  case q of
    QName [] s -> pure (Located sp s)
    _ -> fail "an unqualified name"

dataP :: Parser Decl
dataP = do
  keyword "data"
  n <- identifier
  params <- many paramP
  ctors <- option [] (symbol "=" *> (ctorP `sepBy1` symbol "|"))
  pure (DData (DataDecl n params ctors))
  where
    paramP =
      ((,Nothing) <$> identifier)
        <|> bracketed "(" ")" ((,) <$> identifier <* symbol ":" <*> (Just <$> kindP))

kindP :: Parser Kind
kindP = foldr1 KArrow <$> (kindAtom `sepBy1` arrowTok)
  where
    kindAtom = (KType <$ keyword "Type") <|> bracketed "(" ")" kindP

{- |
A constructor: a name applied to the types of its fields, or two types
around a constructor operator, one starting with @:@ or a name in backquotes.
-}
ctorP :: Parser (Located Constructor)
ctorP = located do
  start <- position
  atoms <- some atomP
  optional (try conOperator) >>= \case
    Just op -> do
      lhs <- applied start atoms
      rhsStart <- position
      rhs <- applied rhsStart =<< some atomP
      pure (Constructor (fmap (operatorName `seq` (qnameBase . operatorName)) op) [lhs, rhs])
    Nothing -> case atoms of
      Located sp (EName (QName [] seg)) : fields -> pure (Constructor (Located sp seg) fields)
      _ -> fail "a constructor: a name applied to the types of its fields, or two types around an operator starting with ':'"
  where
    conOperator = do
      op <- operator
      case unLocated op of
        Operator (QName [] (Op o)) False | ":" `T.isPrefixOf` o -> pure op
        Operator _ True -> pure op
        _ -> fail "a constructor operator, starting with ':'"

-- | Atoms applied to one another, left to right.
applied :: (Int, Int) -> [Located Expr] -> Parser (Located Expr)
applied start = \case
  [] -> fail "an expression"
  f : xs -> pure (foldl (\acc x -> Located (Span start (spanEnd (location x))) (EApp acc x)) f xs)

fixityP :: Parser Decl
fixityP = do
  assoc <- (AssocLeft <$ keyword "infixl") <|> (AssocRight <$ keyword "infixr") <|> (AssocNone <$ keyword "infix")
  prec <- rational
  ops <- some (located operatorText <|> fmap (qnameText . operatorName) <$> backquotedP)
  pure (DFixity assoc prec ops)
  where
    backquotedP = try do
      op <- operator
      if operatorBackquoted (unLocated op) then pure op else fail "an operator"

signatureP :: Parser Decl
signatureP = do
  n <- nameSegment
  symbol ":"
  DSignature n <$> exprP

clauseP :: Parser Decl
clauseP = DClause <$> clauseBodyP

-- | A clause, @lhs = rhs@.
clauseBodyP :: Parser Clause
clauseBodyP = do
  lhs <- withStops ["="] [] opsP
  symbol "="
  Clause lhs <$> located rhsP

-- | Constraints on type variables: @C a@, or @(C a, D b)@.
constraintsP :: Parser [TyConstraint]
constraintsP = bracketed "(" ")" (constraintP `sepBy1` symbol ",") <|> fmap pure constraintP
  where
    constraintP = (,) <$> qualifiedName <*> identifier

{- |
A class: @class [constraints =>] Name param where@, and the signatures of its
methods, laid out or in braces.
-}
classP :: Parser Decl
classP = do
  keyword "class"
  supers <- option [] (try (constraintsP <* symbol "=>"))
  n <- identifier
  param <- identifier
  keyword "where"
  members <- block ((,) <$> nameSegment <* symbol ":" <*> exprP)
  pure (DClass (ClassDecl supers n param members))

{- |
An instance: @instance [name :] [constraints =>] Class type where@, and the
clauses of its methods, laid out or in braces.
-}
instanceP :: Parser Decl
instanceP = do
  keyword "instance"
  name <- optional (try (identifier <* symbol ":"))
  context <- option [] (try (constraintsP <* symbol "=>"))
  cls <- qualifiedName
  ty <- atomP
  keyword "where"
  clauses <- block (located clauseBodyP)
  pure (DInstance (InstanceDecl name context cls ty clauses))

-- | A right side: a tactic proof, a calculation, or an expression.
rhsP :: Parser Rhs
rhsP =
  (keyword "by" *> (RBy <$> tacticsP))
    <|> (keyword "calc" *> (RCalc <$> calcP))
    <|> (RExpr <$> exprP)

-- * Expressions

arrowTok :: Parser ()
arrowTok = symbol "->" <|> symbol "→"

exprP :: Parser (Located Expr)
exprP = constrainedP <|> piP <|> quantP <|> lamP <|> ifP <|> caseP <|> proofP <|> arrowP <?> "expression"

-- | A type under constraints on its type variables, @C a => T@ or @(C a, D b) => T@.
constrainedP :: Parser (Located Expr)
constrainedP = do
  start <- position
  cs <- try (constraintsP <* symbol "=>")
  body <- exprP
  spanned start (EConstrained cs body)

-- | Binders before an arrow, @{a : Type} (xs : List a) -> B@.
piP :: Parser (Located Expr)
piP = do
  start <- position
  bs <- try (some binderGroupP <* arrowTok)
  body <- exprP
  let wrap b acc = Located (Span start (spanEnd (location acc))) (EPi b acc)
  pure (foldr wrap body bs)

binderGroupP :: Parser Binder
binderGroupP = implicitB <|> explicitB
  where
    implicitB = bracketed "{" "}" (Binder True <$> some identifier <*> optional (symbol ":" *> exprP))
    explicitB = bracketed "(" ")" (Binder False <$> some identifier <*> (Just <$> (symbol ":" *> exprP)))

quantP :: Parser (Located Expr)
quantP = do
  start <- position
  q <- (Forall <$ (symbol "∀" <|> keyword "forall")) <|> (Exists <$ (symbol "∃" <|> keyword "exists"))
  bs <- some binderP
  bound <- optional ((,) <$> try boundRelation <*> opsP)
  symbol "," <|> symbol "."
  body <- exprP
  spanned start (EQuant q bs bound body)
  where
    binderP =
      ((\n -> Binder False [n] Nothing) <$> identifier)
        <|> bracketed "(" ")" (Binder False <$> some identifier <*> (Just <$> (symbol ":" *> exprP)))
    boundRelation = do
      op <- operator
      case operatorName (unLocated op) of
        QName [] (Op o) | o `elem` ["<", "≤", "<="] -> pure op
        _ -> fail "a bound, < or ≤"

lamP :: Parser (Located Expr)
lamP = do
  start <- position
  symbol "\\" <|> symbol "λ" <|> keyword "fun"
  ns <- some identifier
  arrowTok <|> symbol "=>" <|> symbol "."
  body <- exprP
  spanned start (ELam ns body)

ifP :: Parser (Located Expr)
ifP = do
  start <- position
  keyword "if"
  c <- exprP
  keyword "then"
  t <- exprP
  keyword "else"
  e <- exprP
  spanned start (EIf c t e)

caseP :: Parser (Located Expr)
caseP = do
  start <- position
  keyword "case"
  scrutinee <- exprP
  keyword "of"
  alts <- block (located (Alt <$> opsP <* arrowTok <*> exprP))
  spanned start (ECase scrutinee alts)

proofP :: Parser (Located Expr)
proofP = do
  start <- position
  rhs <- (keyword "by" *> (RBy <$> tacticsP)) <|> (keyword "calc" *> (RCalc <$> calcP))
  spanned start (EProof rhs)

arrowP :: Parser (Located Expr)
arrowP = do
  start <- position
  lhs <- opsP
  optional (arrowTok *> exprP) >>= \case
    Nothing -> pure lhs
    Just rhs -> spanned start (EArrow lhs rhs)

-- | Operands and operators, before the fixities associate them.
opsP :: Parser (Located Expr)
opsP = do
  start <- position
  elems <- elemsP
  case elems of
    [Operand e] -> pure e
    _ -> spanned start (EOps elems)
  where
    elemsP = do
      nots <- many (PrefixNot . location <$> located (symbol "¬"))
      e <- appP
      rest <- optional ((:) . InfixOp <$> operator <*> elemsP)
      pure (nots <> [Operand e] <> maybe [] id rest)

appP :: Parser (Located Expr)
appP = do
  start <- position
  f <- atomP
  args <- many ((Left <$> atomP) <|> (Right <$> bracketed "{" "}" exprP))
  pure (foldl (step start) f args)
  where
    step start acc = \case
      Left x -> Located (Span start (spanEnd (location x))) (EApp acc x)
      Right x -> Located (Span start (spanEnd (location x))) (EImplicitApp acc x)

atomP :: Parser (Located Expr)
atomP =
  choice
    [ located (ENat . fromInteger <$> natural)
    , located (EType <$ keyword "Type")
    , located (EWildcard <$ wildcard)
    , located (EName (unqualified (Op "⊤")) <$ symbol "⊤")
    , located (EName (unqualified (Op "⊥")) <$ symbol "⊥")
    , located (ETuple <$> bracketed "⟨" "⟩" (exprP `sepBy` symbol ","))
    , fmap EName <$> qualifiedName
    , located (EParen <$> bracketed "(" ")" exprP)
    ]
    <?> "atom"

-- * Calculations

{- |
A calculation: its first term and steps on the @calc@ line, further steps on
the lines after, deeper than the item @calc@ belongs to; or, when nothing
follows @calc@ on its line, a block whose first item is the first term and
the rest steps.
-}
calcP :: Parser Calc
calcP = do
  onNextLine <- atLineStart
  if onNextLine then blockForm else Calc <$> calcTermP <*> many stepP
  where
    blockForm = do
      itemsRead <- laidOutBlock ((,) <$> optional calcTermP <*> many stepP)
      case itemsRead of
        (Just first, steps) : rest
          | all (validLater . fst) rest -> pure (Calc first (steps <> concatMap snd rest))
        _ -> fail "a calculation: a first term, then steps = t := proof"
    validLater = \case
      Nothing -> True
      Just (Located _ EWildcard) -> True
      _ -> False

-- | A term of a calculation, which ends at a relation or at @:=@.
calcTermP :: Parser (Located Expr)
calcTermP = withStops ["=", "≡", ":="] [] opsP

stepP :: Parser (Located CalcStep)
stepP = located do
  _ <- optional wildcard
  rel <- located (relation "=" <|> relation "≡")
  t <- calcTermP
  p <- optional (symbol ":=" *> located rhsP)
  pure (CalcStep rel t p)
  where
    relation r = symbol r $> Operator (unqualified (Op r)) False

-- * Tactics

-- | The tactics of a block.
tacticsP :: Parser [Located Tactic]
tacticsP = block tacticP

tacticP :: Parser (Located Tactic)
tacticP = do
  start <- position
  t <- located atomicTacticP
  optional (symbol "<;>" *> tacticP) >>= \case
    Nothing -> pure t
    Just u -> spanned start (TThenAll t u)

-- | A tactic word, which is a word only here.
word :: Text -> Parser ()
word = keyword

atomicTacticP :: Parser Tactic
atomicTacticP =
  choice
    [ TFocus <$> bracedBlock tacticP
    , symbol "·" *> (TFocus <$> laidOutBlock tacticP)
    , word "intros" *> (TIntros <$> many identifier)
    , word "intro" *> (TIntro <$> many identifier)
    , word "exact" *> (TExact <$> exprP)
    , word "apply" *> (TApply <$> exprP)
    , TRefl <$ (word "rfl" <|> word "refl" <|> word "reflexivity")
    , TSymm <$ (word "symm" <|> word "symmetry")
    , (word "trans" <|> word "transitivity") *> (TTrans <$> exprP)
    , (word "rw" <|> word "rewrite") *> (TRewrite <$> rulesP <*> locationP)
    , word "unfold" *> (TUnfold <$> withStops [] ["at"] (some qualifiedName) <*> locationP)
    , word "simp" *> word "only" *> (TSimpOnly <$> rulesP <*> locationP)
    , TConstructor <$ (word "constructor" <|> word "split")
    , TLeft <$ word "left"
    , TRight <$ word "right"
    , TExfalso <$ word "exfalso"
    , TContradiction <$ word "contradiction"
    , word "absurd" *> (TAbsurd <$> exprP)
    , TAssumption <$ word "assumption"
    , TTrivial <$ word "trivial"
    , TDecide <$ word "decide"
    , (word "cong" <|> word "congr") *> (TCong <$> optional exprP)
    , (word "cases" <|> word "destruct") *> (TCases <$> withStops [] ["with"] exprP <*> optional armsP)
    , word "induction" *> (TInduction <$> identifier <*> option [] (word "generalizing" *> some identifier) <*> optional armsP)
    , word "obtain" *> (TObtain <$> bracketed "⟨" "⟩" (identifier `sepBy1` symbol ",") <* symbol ":=" <*> exprP)
    , (word "exists" <|> word "use") *> (TExists <$> (exprP `sepBy1` symbol ","))
    , haveP
    , (word "show" <|> word "change") *> (TShow <$> exprP)
    , word "calc" *> (TCalc <$> calcP)
    , word "revert" *> (TRevert <$> some identifier)
    , word "clear" *> (TClear <$> some identifier)
    , word "by_cases" *> (TByCases <$> identifier <* symbol ":" <*> exprP)
    , TSorry <$ (word "sorry" <|> word "admit")
    , word "try" *> (TTry <$> tacticP)
    , word "repeat" *> (TRepeat <$> tacticP)
    , word "first" *> (TFirst <$> some (symbol "|" *> tacticP))
    , word "all_goals" *> (TAllGoals <$> tacticP)
    , word "any_goals" *> (TAnyGoals <$> tacticP)
    , word "case" *> (TCase <$> constructorSegment <*> many identifier <* symbol "=>" <*> tacticsP)
    , TTerm <$> exprP
    ]
    <?> "tactic"
  where
    rulesP = bracketed "[" "]" (ruleP `sepBy1` symbol ",")
    ruleP = RewriteRule <$> (isJust <$> optional (symbol "←" <|> symbol "<-")) <*> exprP
    locationP = option AtGoal (word "at" *> (AtHypotheses <$> some identifier))
    armsP = keyword "with" *> many armP
    armP = located do
      symbol "|"
      c <- constructorSegment
      ns <- many identifier
      symbol "=>"
      Arm c ns <$> tacticsP
    haveP = do
      word "have" <|> word "assert"
      name <- optional (try (identifier <* lookAhead (symbol ":" <|> symbol ":=")))
      ty <- optional (symbol ":" *> withStops [":="] [] exprP)
      symbol ":="
      THave name ty <$> located rhsP

-- | The constructor an alternative is for, by the last segment of its name: @Nil@, @(:)@, @List.Nil@.
constructorSegment :: Parser (Located Segment)
constructorSegment = fmap qnameBase <$> qualifiedName
