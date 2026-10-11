{-# LANGUAGE OverloadedStrings #-}

{- |
Source views of desugared quantifiers. These records are elaborator metadata,
never constructors of Praxis Core. A consumer must reconstruct and match the
lowered quantifier before using a view, because proof transformations can
change or duplicate the syntax at a source location.
-}
module Language.Praxis.Surface.SourceView (
  QuantifierView (..),
  QuantifierViews,
  quantifierViews,
  rhsQuantifierViews,
  quantifierViewCandidates,
  quantifierViewsList,
  tagQuantifierViews,
  withTypeBindings,
  withScope,
) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Language.Praxis.Surface.Syntax.Raw (Located (..), Segment, Span)
import Language.Praxis.Surface.Syntax.Raw qualified as R
import Language.Praxis.Surface.Types (Ty, TyScope)

-- | The declaration and scope that gave one source binder its meaning.
data QuantifierView = QuantifierView
  { qvOwner :: ![Segment]
  , qvBuiltins :: !(Map Text [Segment])
  , qvScope :: !TyScope
  , qvTypeBindings :: ![(Text, Ty)]
  , qvSpan :: !Span
  , qvQuantifier :: !R.Quantifier
  , qvBinder :: !(Located Text)
  , qvDomain :: !(Located R.Expr)
  , qvNumeric :: !Bool
  , qvDomainBinders :: ![Located Text]
  -- ^ Quantifiers in scope before this entire binder group's annotation.
  , qvBodyBinders :: ![Located Text]
  -- ^ Quantifiers in scope immediately before this binder.
  , qvSameGroup :: ![Located Text]
  -- ^ Remaining names sharing this binder's already elaborated type.
  , qvBody :: !(Located R.Expr)
  }
  deriving stock (Show, Eq)

-- | Locations are unique only within their original declaration.
newtype QuantifierViews = QuantifierViews (Map ([Segment], Span) QuantifierView)
  deriving stock (Show, Eq)
  deriving newtype (Semigroup, Monoid)

-- | All finite-style quantifier binders in a signature or proposition.
quantifierViews :: [Segment] -> Map Text [Segment] -> TyScope -> Located R.Expr -> QuantifierViews
quantifierViews owner builtins scope = expressionViews (Origin owner builtins scope [])

-- | Views in local annotations, proof arguments, calculations and tactic blocks.
rhsQuantifierViews :: [Segment] -> Map Text [Segment] -> TyScope -> Located R.Rhs -> QuantifierViews
rhsQuantifierViews owner builtins scope = rhsViews (Origin owner builtins scope []) . unLocated

{- | Candidates retain their separate source identities. Matching a span alone
never authorizes using a view from another declaration.
-}
quantifierViewCandidates :: Span -> QuantifierViews -> [QuantifierView]
quantifierViewCandidates span' (QuantifierViews views) = [view | ((_, at), view) <- Map.toList views, at == span']

-- | Inspect source scopes when specializing a reusable checked theorem.
quantifierViewsList :: QuantifierViews -> [QuantifierView]
quantifierViewsList (QuantifierViews views) = Map.elems views

{- | Each application keeps its lexical substitutions independent of other
applications of the same source theorem in the proof context.
-}
tagQuantifierViews :: Segment -> QuantifierViews -> QuantifierViews
tagQuantifierViews tag (QuantifierViews views) = QuantifierViews (Map.fromList [((tag : owner, sp), view {qvOwner = tag : qvOwner view}) | ((owner, sp), view) <- Map.toList views])

-- | Instance specialization supplies ordinary lexical type aliases.
withTypeBindings :: [(Text, Ty)] -> QuantifierViews -> QuantifierViews
withTypeBindings bindings (QuantifierViews views) = QuantifierViews (fmap (\view -> view {qvTypeBindings = bindings <> qvTypeBindings view}) views)

-- | The ambient type/index scope of a specialized instance law.
withScope :: TyScope -> QuantifierViews -> QuantifierViews
withScope scope (QuantifierViews views) = QuantifierViews (fmap (\view -> view {qvScope = scope}) views)

data Origin = Origin ![Segment] !(Map Text [Segment]) !TyScope ![Located Text]

expressionViews :: Origin -> Located R.Expr -> QuantifierViews
expressionViews origin written@(Located _ expression) = case expression of
  R.EName _ -> mempty
  R.ENat _ -> mempty
  R.EWildcard -> mempty
  R.EAbsurd -> mempty
  R.EType -> mempty
  R.EApp f x -> rec f <> rec x
  R.EImplicitApp f x -> rec f <> rec x
  R.EOps pieces -> foldMap (\case R.Operand value -> rec value; _ -> mempty) pieces
  R.EInfix _ x y -> rec x <> rec y
  R.ENot value -> rec value
  R.EParen value -> rec value
  R.ETuple values -> foldMap rec values
  R.ELam _ body -> rec body
  R.ECase value alternatives -> rec value <> foldMap (\(Located _ alternative) -> rec (R.altPattern alternative) <> rec (R.altBody alternative)) alternatives
  R.EIf condition yes no -> rec condition <> rec yes <> rec no
  R.EPi binder body -> foldMap rec (R.binderType binder) <> rec body
  R.EArrow x y -> rec x <> rec y
  R.EQuant quantifier binders bound body ->
    binderViews origin quantifier binders bound body
      <> foldMap (rec . snd) bound
  R.EProof rhs -> rhsViews origin rhs
  R.EConstrained _ body -> rec body
  where
    rec = expressionViews origin
    binderViews current _ [] _ body = expressionViews current body
    binderViews current quantifier (binder : rest) bound body =
      foldMap (expressionViews current) (R.binderType binder)
        <> names current (R.binderNames binder)
      where
        names inside [] = binderViews inside quantifier rest bound body
        names inside (name : more) =
          let remaining = [binder {R.binderNames = more} | not (null more)] <> rest
              inner = if null remaining then body else written {unLocated = R.EQuant quantifier remaining bound body}
              Origin owner builtins scope lexical = inside
              Origin _ _ _ domainLexical = current
              domain = case R.binderType binder of
                Just annotation -> annotation
                Nothing -> Located (location name) (R.EName (R.QName [] (R.Ident "Nat")))
              value = QuantifierView owner builtins scope [] (location name) quantifier name domain (maybe False (const True) bound) domainLexical lexical more inner
              views = QuantifierViews (Map.singleton (owner, location name) value)
              after = Origin owner builtins scope (lexical <> [name])
           in views <> names after more

rhsViews :: Origin -> R.Rhs -> QuantifierViews
rhsViews origin = \case
  R.RBy tactics -> foldMap (tacticViews origin . unLocated) tactics
  R.RCalc calculation -> calcViews origin calculation
  R.RExpr value -> expressionViews origin value
  R.RAbsurd -> mempty

calcViews :: Origin -> R.Calc -> QuantifierViews
calcViews origin calculation =
  expressionViews origin (R.calcFirst calculation)
    <> foldMap (\(Located _ step) -> expressionViews origin (R.stepTerm step) <> foldMap (rhsViews origin . unLocated) (R.stepProof step)) (R.calcSteps calculation)

tacticViews :: Origin -> R.Tactic -> QuantifierViews
tacticViews origin = \case
  R.TIntro _ -> mempty
  R.TIntros _ -> mempty
  R.TExact value -> expression value
  R.TApply value -> expression value
  R.TRefl -> mempty
  R.TSymm -> mempty
  R.TTrans value -> expression value
  R.TRewrite rules _ -> foldMap rewrite rules
  R.TUnfold _ _ -> mempty
  R.TSimpOnly rules _ -> foldMap rewrite rules
  R.TConstructor -> mempty
  R.TLeft -> mempty
  R.TRight -> mempty
  R.TExfalso -> mempty
  R.TContradiction -> mempty
  R.TAbsurd value -> expression value
  R.TAssumption -> mempty
  R.TTrivial -> mempty
  R.TDecide -> mempty
  R.TCong value -> foldMap expression value
  R.TCases value arms -> expression value <> foldMap (foldMap arm) arms
  R.TInduction _ _ arms -> foldMap (foldMap arm) arms
  R.TObtain _ value -> expression value
  R.TExists values -> foldMap expression values
  R.THave _ annotation rhs -> foldMap expression annotation <> rhsViews origin (unLocated rhs)
  R.TShow value -> expression value
  R.TCalc calculation -> calcViews origin calculation
  R.TRevert _ -> mempty
  R.TClear _ -> mempty
  R.TByCases _ value -> expression value
  R.TSorry -> mempty
  R.TTry nested -> tactic nested
  R.TRepeat nested -> tactic nested
  R.TFirst nested -> foldMap tactic nested
  R.TAllGoals nested -> tactic nested
  R.TAnyGoals nested -> tactic nested
  R.TThenAll first second -> tactic first <> tactic second
  R.TFocus nested -> foldMap tactic nested
  R.TCase _ _ nested -> foldMap tactic nested
  R.TTerm value -> expression value
  where
    expression = expressionViews origin
    tactic = tacticViews origin . unLocated
    rewrite = expression . R.rewriteBy
    arm (Located _ branch) = foldMap tactic (R.armBody branch)
