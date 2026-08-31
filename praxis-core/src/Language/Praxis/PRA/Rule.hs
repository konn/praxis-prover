{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
The symbolic presentation of an inference rule.

This module is the single source of truth for the shape of a rule: which
metavariables it abstracts over, what sits above the line, what sits below it,
and which side conditions guard it.  "Language.Praxis.PRA.Rule.G3i" gives the
fourteen rules of the calculus in this language, and
"Language.Praxis.PRA.Rule.TH" compiles them into the @Proof@ datatype, its base
functor, the rule-name enumeration and the checker.

The pattern language is deliberately first-order and deliberately small.  A
metavariable is bound in exactly one of three ways:

* it is a 'Param' of the rule, hence a field of the generated constructor;
* it is the tail 'CtxM' of some premise's context, bound to whatever remains
  after the listed formulae have been discharged;
* it is the /entire/ succedent of some premise, bound to whatever that premise
  concluded.

Everything else is determined, and is only ever checked.  No unification is
needed anywhere, which is what keeps the compiler in
"Language.Praxis.PRA.Rule.TH" a syntax-directed transcription.
-}
module Language.Praxis.PRA.Rule (
  -- * Metavariables
  VarM (..),
  TermM (..),
  AtomM (..),
  FormM (..),
  CtxM (..),
  Sort (..),
  MetaRef (..),

  -- * Patterns
  TermPat (..),
  AtomPat (..),
  FormPat (..),
  CtxPat (..),
  SeqPat (..),
  (===),
  (/\),
  (\/),
  (==>),

  -- * Rules
  Param (..),
  Target (..),
  Side (..),
  Rule (..),
  paramRef,
  paramSort,

  -- * Free metavariables
  HasMetas (..),

  -- * Well-formedness
  Position (..),
  RuleError (..),
  validateRule,

  -- * Rendering
  renderRule,
  renderSeqPat,
  renderFormPat,
  renderTermPat,
) where

import Data.List (intercalate, nub)
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax (Lift)
import Numeric.Natural (Natural)

-- * Metavariables

-- | A metavariable standing for an object variable, i.e. an inhabitant of @a@.
newtype VarM = VarM String
  deriving (Show, Eq, Ord, Generic, Lift)

-- | A metavariable standing for a @'Language.Praxis.PRA.Syntax.Term' a@.
newtype TermM = TermM String
  deriving (Show, Eq, Ord, Generic, Lift)

-- | A metavariable standing for an @'Language.Praxis.PRA.Syntax.Atomic' a@.
newtype AtomM = AtomM String
  deriving (Show, Eq, Ord, Generic, Lift)

-- | A metavariable standing for a @'Language.Praxis.PRA.Syntax.Formula' a@.
newtype FormM = FormM String
  deriving (Show, Eq, Ord, Generic, Lift)

-- | A metavariable standing for a context, i.e. a multiset of formulae.
newtype CtxM = CtxM String
  deriving (Show, Eq, Ord, Generic, Lift)

{- |
The sort of a metavariable.  Sorts are carried in the types of the pattern
constructors, so this enumeration exists only to report and compare
metavariables uniformly; it never drives instantiation.
-}
data Sort = VarS | TermS | AtomS | FormS | CtxS
  deriving (Show, Eq, Ord, Enum, Bounded, Generic, Lift)

-- | A metavariable with its sort erased, for scope checking and diagnostics.
data MetaRef = MetaRef {refSort :: !Sort, refName :: !String}
  deriving (Show, Eq, Ord, Generic, Lift)

-- * Patterns

-- | A term schema.
data TermPat
  = -- | a metavariable of sort 'TermS'
    TMeta !TermM
  | -- | the term @'Language.Praxis.PRA.Syntax.var' x@, for @x@ of sort 'VarS'
    TOfVar !VarM
  | -- | a numeral
    TLit !Natural
  | -- | @'Language.Praxis.PRA.Syntax.suc' t@
    TSuc !TermPat
  deriving (Show, Eq, Ord, Generic, Lift)

-- | An atomic-formula schema.
data AtomPat
  = -- | a metavariable of sort 'AtomS'
    AMeta !AtomM
  | !TermPat :=== !TermPat
  deriving (Show, Eq, Ord, Generic, Lift)

infix 5 :===

-- | A formula schema.
data FormPat
  = -- | a metavariable of sort 'FormS'
    FMeta !FormM
  | -- | an atomic formula, viewed as a formula
    FAtm !AtomPat
  | FBot
  | !FormPat :/\ !FormPat
  | !FormPat :\/ !FormPat
  | !FormPat :==> !FormPat
  | -- | @A[x := t]@; a computation, not a matchable pattern
    FSubst !VarM !TermPat !FormPat
  deriving (Show, Eq, Ord, Generic, Lift)

infixr 4 :/\

infixr 3 :\/

infixr 2 :==>

{- |
A context schema: the principal formulae the rule names, followed by the tail
metavariable standing for everything else.

The order of the list is observable — it is the order in which the formulae are
discharged, hence the order in which a 'MissingAssumption' is reported — so it
should match the order the rule is displayed in.
-}
data CtxPat = ![FormPat] :+ !CtxM
  deriving (Show, Eq, Ord, Generic, Lift)

infix 2 :+

-- | A sequent schema.
data SeqPat = !CtxPat :|- !FormPat
  deriving (Show, Eq, Ord, Generic, Lift)

infix 1 :|-

-- | @s '===' t@ is the atomic equation @s = t@, viewed as a formula.
(===) :: TermPat -> TermPat -> FormPat
(===) s t = FAtm (s :=== t)

infix 5 ===

(/\), (\/), (==>) :: FormPat -> FormPat -> FormPat
(/\) = (:/\)
(\/) = (:\/)
(==>) = (:==>)

infixr 4 /\

infixr 3 \/

infixr 2 ==>

-- * Rules

{- |
A parameter of a rule: a metavariable which cannot be recovered from the
premises, and therefore becomes a field of the generated constructor.  The
order of a rule's parameters is the order of those fields.
-}
data Param
  = PVar !VarM
  | PTerm !TermM
  | PAtom !AtomM
  | PForm !FormM
  | PCtx !CtxM
  deriving (Show, Eq, Ord, Generic, Lift)

-- | What an eigenvariable condition ranges over.
data Target
  = InTerm !TermPat
  | InCtx !CtxM
  deriving (Show, Eq, Ord, Generic, Lift)

-- | A side condition.
data Side
  = -- | the two terms are identified by the trusted evaluator
    DefEq !TermPat !TermPat
  | -- | the eigenvariable condition
    NotFreeIn !VarM !Target
  deriving (Show, Eq, Ord, Generic, Lift)

-- | An inference rule.
data Rule = Rule
  { ruleLabel :: !String
  -- ^ drives the generated names: @ConjL@, @ConjLF@, @ConjLRule@
  , ruleParams :: ![Param]
  -- ^ constructor fields, in order
  , rulePremises :: ![SeqPat]
  -- ^ subproof fields, in order
  , ruleConclusion :: !SeqPat
  , ruleSides :: ![Side]
  }
  deriving (Show, Eq, Generic, Lift)

paramRef :: Param -> MetaRef
paramRef (PVar (VarM n)) = MetaRef VarS n
paramRef (PTerm (TermM n)) = MetaRef TermS n
paramRef (PAtom (AtomM n)) = MetaRef AtomS n
paramRef (PForm (FormM n)) = MetaRef FormS n
paramRef (PCtx (CtxM n)) = MetaRef CtxS n

paramSort :: Param -> Sort
paramSort = refSort . paramRef

-- * Free metavariables

-- | The metavariables occurring in a schema.
class HasMetas t where
  metas :: t -> Set MetaRef

instance HasMetas VarM where
  metas (VarM n) = Set.singleton (MetaRef VarS n)

instance HasMetas CtxM where
  metas (CtxM n) = Set.singleton (MetaRef CtxS n)

instance HasMetas TermPat where
  metas (TMeta (TermM n)) = Set.singleton (MetaRef TermS n)
  metas (TOfVar x) = metas x
  metas (TLit _) = Set.empty
  metas (TSuc t) = metas t

instance HasMetas AtomPat where
  metas (AMeta (AtomM n)) = Set.singleton (MetaRef AtomS n)
  metas (s :=== t) = metas s <> metas t

instance HasMetas FormPat where
  metas (FMeta (FormM n)) = Set.singleton (MetaRef FormS n)
  metas (FAtm p) = metas p
  metas FBot = Set.empty
  metas (p :/\ q) = metas p <> metas q
  metas (p :\/ q) = metas p <> metas q
  metas (p :==> q) = metas p <> metas q
  metas (FSubst x t p) = metas x <> metas t <> metas p

instance HasMetas CtxPat where
  metas (fs :+ g) = foldMap metas fs <> metas g

instance HasMetas SeqPat where
  metas (c :|- f) = metas c <> metas f

instance HasMetas Target where
  metas (InTerm t) = metas t
  metas (InCtx g) = metas g

instance HasMetas Side where
  metas (DefEq s t) = metas s <> metas t
  metas (NotFreeIn x tgt) = metas x <> metas tgt

instance HasMetas Rule where
  metas r =
    foldMap metas (rulePremises r)
      <> metas (ruleConclusion r)
      <> foldMap metas (ruleSides r)

-- * Well-formedness

-- | Where a scope violation was found.
data Position
  = AtPremise !Int
  | AtConclusion
  | AtSide !Int
  deriving (Show, Eq, Ord, Generic, Lift)

data RuleError
  = -- | one name used at two sorts, or twice as a parameter
    DuplicateMeta !String
  | -- | used before anything could have bound it
    UnboundMeta !Position !MetaRef
  | -- | declared but never mentioned
    UnusedParam !MetaRef
  deriving (Show, Eq, Ord, Generic, Lift)

{- |
Check that a rule is well-scoped.  An empty list means the rule is admissible
input to the compiler; the compiler assumes, and does not re-establish, every
property checked here.

Sort errors cannot arise: the pattern constructors are typed, so an ill-sorted
rule is rejected by the compiler of /this/ module.  What remains is scoping,
which the types cannot see.
-}
validateRule :: Rule -> [RuleError]
validateRule r = duplicates <> scopeErrors <> unused
  where
    params = ruleParams r

    names = map (refName . paramRef) params
    allRefs = Set.toList (metas r) <> map paramRef params
    duplicates =
      map DuplicateMeta . nub $
        [n | n <- names, length (filter (== n) names) > 1]
          <> [ refName p
             | p <- allRefs
             , q <- allRefs
             , refName p == refName q
             , refSort p /= refSort q
             ]

    initial = Set.fromList (map paramRef params)

    -- Walk the premises in order, threading the set of bound metavariables.
    (finalBound, premiseErrors) = foldl step (initial, []) (zip [0 ..] (rulePremises r))

    step (bound, errs) (i, fs :+ g :|- c) =
      let ctxErrs = missing (AtPremise i) bound (foldMap metas fs)
          gRef = let CtxM gn = g in MetaRef CtxS gn
          bound' = Set.insert gRef bound
          -- a bare, still-unbound succedent metavariable binds; anything else is checked
          (bound'', succErrs) = case c of
            FMeta (FormM n)
              | let ref = MetaRef FormS n
              , not (ref `Set.member` bound') ->
                  (Set.insert ref bound', [])
            _ -> (bound', missing (AtPremise i) bound' (metas c))
       in (bound'', errs <> ctxErrs <> succErrs)

    scopeErrors =
      premiseErrors
        <> missing AtConclusion finalBound (metas (ruleConclusion r))
        <> concat
          [ missing (AtSide i) finalBound (metas s)
          | (i, s) <- zip [0 ..] (ruleSides r)
          ]

    missing pos bound needed =
      [UnboundMeta pos ref | ref <- Set.toList (needed Set.\\ bound)]

    used = metas r
    unused = [UnusedParam ref | p <- params, let ref = paramRef p, not (ref `Set.member` used)]

-- * Rendering

renderTermPat :: TermPat -> String
renderTermPat (TMeta (TermM n)) = n
renderTermPat (TOfVar (VarM x)) = x
renderTermPat (TLit n) = show n
renderTermPat (TSuc t) = "Succ " <> atomic t
  where
    atomic u@(TSuc _) = "(" <> renderTermPat u <> ")"
    atomic u = renderTermPat u

renderAtomPat :: AtomPat -> String
renderAtomPat (AMeta (AtomM n)) = n
renderAtomPat (s :=== t) = renderTermPat s <> " = " <> renderTermPat t

-- | Render a formula, parenthesising according to the fixities in "Language.Praxis.PRA.Syntax".
renderFormPat :: FormPat -> String
renderFormPat = go (0 :: Int)
  where
    go _ (FMeta (FormM n)) = n
    go _ (FAtm p) = renderAtomPat p
    go _ FBot = "_|_"
    go d (p :/\ q) = paren (d > 4) (go 5 p <> " /\\ " <> go 4 q)
    go d (p :\/ q) = paren (d > 3) (go 4 p <> " \\/ " <> go 3 q)
    go d (p :==> q) = paren (d > 2) (go 3 p <> " ==> " <> go 2 q)
    go _ (FSubst (VarM x) t p) =
      go 6 p <> "[" <> x <> " := " <> renderTermPat t <> "]"
    paren True s = "(" <> s <> ")"
    paren False s = s

renderSeqPat :: SeqPat -> String
renderSeqPat (fs :+ CtxM g :|- c) =
  intercalate ", " (map renderFormPat fs <> [g]) <> " |- " <> renderFormPat c

{- |
Render a rule as the inference figure which documents it.  The result is the
body of a Haddock code block, and is what the compiler attaches to the
generated constructor.
-}
renderRule :: Rule -> String
renderRule r =
  unlines $
    [replicate leftPad ' ' <> above | not (null above)]
      <> [replicate barPad ' ' <> replicate barWidth '-' <> " " <> signature]
      <> [replicate concPad ' ' <> below]
      <> sideLines
  where
    above = intercalate "    " (map renderSeqPat (rulePremises r))
    below = renderSeqPat (ruleConclusion r)
    barWidth = max (length above) (length below)
    barPad = 2
    leftPad = barPad + (barWidth - length above) `div` 2
    concPad = barPad + (barWidth - length below) `div` 2

    signature = ruleLabel r <> "(" <> intercalate "; " groups <> ")"
      where
        groups =
          [ intercalate ", " ps
          | ps <- [map (refName . paramRef) (ruleParams r), subproofNames]
          , not (null ps)
          ]
    -- Derivations, not formulae: @P@ is already taken as a parameter by 'Subst'.
    subproofNames = ["D" <> show i | i <- [1 .. length (rulePremises r)]]

    sideLines = case ruleSides r of
      [] -> []
      ss -> ["", "where " <> intercalate ", and " (map renderSide ss) <> "."]

    renderSide (DefEq s t) =
      renderTermPat s <> " and " <> renderTermPat t <> " are definitionally equal"
    renderSide (NotFreeIn (VarM x) tgt) = x <> " is not free in " <> renderTarget tgt
    renderTarget (InTerm t) = renderTermPat t
    renderTarget (InCtx (CtxM g)) = g
