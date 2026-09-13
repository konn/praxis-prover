{-# LANGUAGE OverloadedStrings #-}

{- |
The syntax of the surface language as it is parsed: names unresolved,
operator applications unassociated, every node with its source span.

Types, propositions and terms share one expression grammar, as in Agda: which
is which is decided when names are resolved and types checked, where the
fixities of the whole module are known.  Binders here are named; resolution
turns them into the locally nameless syntax of
"Language.Praxis.Surface.Syntax".
-}
module Language.Praxis.Surface.Syntax.Raw (
  -- * Positions
  Span (..),
  noSpan,
  spanning,
  Located (..),

  -- * Names
  Segment (..),
  QName (..),
  segmentText,
  qnameText,
  unqualified,

  -- * Modules and declarations
  Module (..),
  Decl (..),
  OpenSpec (..),
  Assoc (..),
  DataDecl (..),
  Constructor (..),
  Kind (..),
  Clause (..),
  Rhs (..),

  -- * Expressions
  Expr (..),
  Operator (..),
  OpElem (..),
  Binder (..),
  Quantifier (..),
  Alt (..),

  -- * Proofs
  Calc (..),
  CalcStep (..),
  Tactic (..),
  Arm (..),
  RewriteRule (..),
  Location (..),
) where

import Data.Text (Text)
import Data.Text qualified as T
import Numeric.Natural (Natural)

-- * Positions

-- | A region of the source: its first character, and the position after its last, lines and columns from 1.
data Span = Span
  { spanStart :: !(Int, Int)
  , spanEnd :: !(Int, Int)
  }
  deriving stock (Show, Eq, Ord)

-- | The span of generated syntax, which has none.
noSpan :: Span
noSpan = Span (0, 0) (0, 0)

-- | The span from the start of one to the end of another.
spanning :: Span -> Span -> Span
spanning a b = Span (spanStart a) (spanEnd b)

-- | A node with its span.
data Located a = Located
  { location :: !Span
  , unLocated :: !a
  }
  deriving stock (Show, Eq, Functor, Foldable, Traversable)

-- * Names

-- | A segment of a qualified name: an identifier, or an operator written in parentheses in prefix position.
data Segment
  = Ident !Text
  | Op !Text
  deriving stock (Show, Eq, Ord)

-- | A name, with the namespaces qualifying it: @List.Nil@, @(<>).unfold-Nil@, @List.(:)@.
data QName = QName
  { qualifiers :: ![Segment]
  , qnameBase :: !Segment
  }
  deriving stock (Show, Eq, Ord)

segmentText :: Segment -> Text
segmentText = \case
  Ident t -> t
  Op t -> "(" <> t <> ")"

-- | The name as it is written, qualifiers first.
qnameText :: QName -> Text
qnameText (QName qs b) = T.intercalate "." (map segmentText (qs <> [b]))

unqualified :: Segment -> QName
unqualified = QName []

-- * Modules and declarations

data Module = Module
  { moduleName :: !(Located QName)
  , moduleDecls :: ![Located Decl]
  }
  deriving stock (Show, Eq)

data Decl
  = -- | @open T@, @open T using (a, b)@, @open T hiding (a)@
    DOpen !(Located QName) !OpenSpec
  | DData !DataDecl
  | -- | @infixr 4 <>@: associativity, precedence, operators
    DFixity !Assoc !Rational ![Located Text]
  | -- | @name : type@
    DSignature !(Located Segment) !(Located Expr)
  | -- | a clause of a function or of a proof
    DClause !Clause
  deriving stock (Show, Eq)

data OpenSpec
  = OpenAll
  | OpenUsing ![Located Segment]
  | OpenHiding ![Located Segment]
  deriving stock (Show, Eq)

data Assoc = AssocLeft | AssocRight | AssocNone
  deriving stock (Show, Eq, Ord)

data DataDecl = DataDecl
  { dataName :: !(Located Text)
  , dataParams :: ![(Located Text, Maybe Kind)]
  , dataConstructors :: ![Located Constructor]
  }
  deriving stock (Show, Eq)

{- |
A constructor: prefix, @Neg t@, or infix, @t :+ t@; its fields are type
expressions, in order.
-}
data Constructor = Constructor
  { constructorName :: !(Located Segment)
  , constructorFields :: ![Located Expr]
  }
  deriving stock (Show, Eq)

data Kind = KType | KArrow !Kind !Kind
  deriving stock (Show, Eq)

{- |
A clause, @lhs = rhs@.  The left side is kept as an unassociated expression,
@(<>) Nil ys@ or @Nil <> ys@, since which operator heads it is known only once
the fixities are.
-}
data Clause = Clause
  { clauseLhs :: !(Located Expr)
  , clauseRhs :: !(Located Rhs)
  }
  deriving stock (Show, Eq)

-- | A right side: a tactic proof, a calculation, or an expression, which is a term or a proof term.
data Rhs
  = RBy ![Located Tactic]
  | RCalc !Calc
  | RExpr !(Located Expr)
  deriving stock (Show, Eq)

-- * Expressions

data Expr
  = EName !QName
  | ENat !Natural
  | -- | @_@
    EWildcard
  | -- | @Type@
    EType
  | -- | an application to an explicit argument
    EApp !(Located Expr) !(Located Expr)
  | -- | an application to an implicit argument, @f {Nat}@
    EImplicitApp !(Located Expr) !(Located Expr)
  | -- | operands and operators, in order, before the fixities associate them
    EOps ![OpElem]
  | -- | an infix application, once the fixities have associated it
    EInfix !(Located Operator) !(Located Expr) !(Located Expr)
  | -- | @¬ A@, once the fixities have associated it
    ENot !(Located Expr)
  | EParen !(Located Expr)
  | -- | @⟨a, b⟩@
    ETuple ![Located Expr]
  | -- | @\\x y -> body@
    ELam ![Located Text] !(Located Expr)
  | ECase !(Located Expr) ![Located Alt]
  | EIf !(Located Expr) !(Located Expr) !(Located Expr)
  | -- | @{a : Type} -> B@, @(x : T) -> B@: a dependent arrow, the binder implicit or not
    EPi !Binder !(Located Expr)
  | -- | @A -> B@
    EArrow !(Located Expr) !(Located Expr)
  | -- | @∀ x < t, A@ with a bound, @∀ (x : T), A@ without
    EQuant !Quantifier ![Binder] !(Maybe (Located Operator, Located Expr)) !(Located Expr)
  | -- | a proof where a term is expected: @by …@, @calc …@
    EProof !Rhs
  deriving stock (Show, Eq)

-- | An infix operator as written: a symbol, or a name in backquotes.
data Operator = Operator
  { operatorName :: !QName
  , operatorBackquoted :: !Bool
  }
  deriving stock (Show, Eq)

-- | Names bound together, with the type they have, if written.
data Binder = Binder
  { binderImplicit :: !Bool
  , binderNames :: ![Located Text]
  , binderType :: !(Maybe (Located Expr))
  }
  deriving stock (Show, Eq)

data Quantifier = Forall | Exists
  deriving stock (Show, Eq)

-- | An alternative of a case expression: @pattern -> body@.
data Alt = Alt
  { altPattern :: !(Located Expr)
  , altBody :: !(Located Expr)
  }
  deriving stock (Show, Eq)

-- * Proofs

-- | @calc t₀ (rel tᵢ [:= proof])…@
data Calc = Calc
  { calcFirst :: !(Located Expr)
  , calcSteps :: ![Located CalcStep]
  }
  deriving stock (Show, Eq)

-- | A step: the relation, the next term, and its justification when one is given; @_ = t@ writes the previous term as @_@.
data CalcStep = CalcStep
  { stepRelation :: !(Located Operator)
  , stepTerm :: !(Located Expr)
  , stepProof :: !(Maybe (Located Rhs))
  }
  deriving stock (Show, Eq)

data Tactic
  = -- | @intro x h@: exactly as many as named
    TIntro ![Located Text]
  | -- | @intros x xs@: everything pending, the first ones named as given
    TIntros ![Located Text]
  | TExact !(Located Expr)
  | TApply !(Located Expr)
  | -- | @rfl@, @refl@, @reflexivity@
    TRefl
  | -- | @symm@, @symmetry@
    TSymm
  | -- | @trans t@, @transitivity t@
    TTrans !(Located Expr)
  | -- | @rw [e, ← e'] at h@
    TRewrite ![RewriteRule] !Location
  | TUnfold ![Located QName] !Location
  | -- | @simp only [e, …] at h@
    TSimpOnly ![RewriteRule] !Location
  | -- | @constructor@, @split@
    TConstructor
  | TLeft
  | TRight
  | TExfalso
  | TContradiction
  | TAbsurd !(Located Expr)
  | TAssumption
  | TTrivial
  | TDecide
  | -- | @cong e@, @congr@
    TCong !(Maybe (Located Expr))
  | -- | @cases h@, @cases x with | C a b => …@
    TCases !(Located Expr) !(Maybe [Located Arm])
  | -- | @induction x generalizing y with | C a b ih => …@
    TInduction !(Located Text) ![Located Text] !(Maybe [Located Arm])
  | -- | @obtain ⟨x, h⟩ := e@
    TObtain ![Located Text] !(Located Expr)
  | -- | @exists t@, @use t@
    TExists ![Located Expr]
  | -- | @have h : A := proof@
    THave !(Maybe (Located Text)) !(Maybe (Located Expr)) !(Located Rhs)
  | -- | @show A@, @change A@
    TShow !(Located Expr)
  | TCalc !Calc
  | TRevert ![Located Text]
  | TClear ![Located Text]
  | -- | @by_cases h : A@
    TByCases !(Located Text) !(Located Expr)
  | -- | @sorry@, @admit@
    TSorry
  | TTry !(Located Tactic)
  | TRepeat !(Located Tactic)
  | TFirst ![Located Tactic]
  | TAllGoals !(Located Tactic)
  | TAnyGoals !(Located Tactic)
  | -- | @t <;> u@
    TThenAll !(Located Tactic) !(Located Tactic)
  | -- | @{ tacs }@, @· tacs@: the main goal, closed by the tactics
    TFocus ![Located Tactic]
  | -- | @case C x y => tacs@
    TCase !(Located Segment) ![Located Text] ![Located Tactic]
  | -- | a proof term standing as a tactic, @by IH@: it closes the goal as it can
    TTerm !(Located Expr)
  deriving stock (Show, Eq)

-- | An alternative of @cases@ or @induction@: @| C a b ih => tacs@.
data Arm = Arm
  { armConstructor :: !(Located Segment)
  , armNames :: ![Located Text]
  , armBody :: ![Located Tactic]
  }
  deriving stock (Show, Eq)

-- | An equation to rewrite with, right to left when marked @←@.
data RewriteRule = RewriteRule
  { rewriteBackwards :: !Bool
  , rewriteBy :: !(Located Expr)
  }
  deriving stock (Show, Eq)

-- | Where a rewrite acts: the goal, or the hypotheses named after @at@.
data Location
  = AtGoal
  | AtHypotheses ![Located Text]
  deriving stock (Show, Eq)

-- | An element of an operator sequence, as parsed: an operand, an infix operator, or the prefix @¬@.
data OpElem
  = Operand !(Located Expr)
  | InfixOp !(Located Operator)
  | PrefixNot !Span
  deriving stock (Show, Eq)
