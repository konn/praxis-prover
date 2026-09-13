{- |
The resolved syntax of the surface language: every name is either a global
reference, 'Global', or a variable, and every binder is locally nameless.

Binders use @bound@: a scope over a Π binder, a quantifier or a λ holds its
bound occurrences as de Bruijn indices ('Bound.B') and the variables of the
enclosing scope as 'Bound.F'.  The names the source gave to binders survive
only as 'Hint's, which are all equal, so equality of expressions is
α-equivalence and a bound name can never be captured by, or leak into, a
free one.  Source spans are kept the same way, irrelevant to equality.

Types, propositions and terms share this one syntax, as they share one
grammar; "Language.Praxis.Surface.Elab" checks which is which.
-}
module Language.Praxis.Surface.Syntax (
  -- * Irrelevant data
  Hint (..),
  Irrelevant (..),

  -- * Global references
  Ref (..),
  RefKind (..),

  -- * Expressions
  Expr (..),
  Pattern (..),
  RelOp (..),
  Connective (..),
  Quantifier (..),
  BoundRel (..),
  stripLocations,
  spine,
  apps,
  mapGlobals,
  rewriteApps,
  globalsOf,

  -- * Patterns
  patternVariables,
  patternHints,

  -- * Binding
  abstractNames,
  instantiateNames,
) where

import Bound (Scope, abstract, fromScope, instantiate, (>>>=))
import Bound.Scope (hoistScope)
import Control.Monad (ap)
import Data.Functor.Classes (Eq1 (..), Show1 (..), eq1, showsPrec1)
import Data.List (elemIndex)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Language.Praxis.Surface.Syntax.Raw (Quantifier (..), Span)
import Numeric.Natural (Natural)
import Text.Show (showListWith)

-- * Irrelevant data

-- | A name kept for display only: any two are equal.
newtype Hint = Hint {hintText :: Text}
  deriving newtype (Show)

instance Eq Hint where
  _ == _ = True

instance Ord Hint where
  compare _ _ = EQ

-- | A value kept for reports only, such as a source span: any two are equal.
newtype Irrelevant a = Irrelevant {relevant :: a}
  deriving newtype (Show)

instance Eq (Irrelevant a) where
  _ == _ = True

-- * Global references

-- | What a global name refers to.
data RefKind
  = -- | a constructor of a data type
    RefConstructor
  | -- | a function defined by clauses
    RefFunction
  | -- | a theorem, or a lemma the elaborator generated
    RefTheorem
  | -- | a data type
    RefType
  | -- | a symbol of the core, such as the arithmetic of @Nat@
    RefBuiltin
  | {- | a function standing as the parameter of a schema: the method of an
    instance a dictionary passes, or a parameter of the enclosing function's
    own dictionary, applied or passed on
    -}
    RefStatic
  | {- | a value of the enclosing function's dictionary, a method taking no
    argument, by its position among the dictionary's values
    -}
    RefValueParam
  | {- | the function of an instance applied to the dictionary its schema
    takes, standing as the parameter of a schema: the number of values it
    takes before that dictionary's values
    -}
    RefPartial !Int
  deriving stock (Show, Eq, Ord)

-- | A global name, fully qualified by its module and namespaces: @Data.List.List.Nil@.
data Ref = Ref
  { refKind :: !RefKind
  , refName :: !Text
  }
  deriving stock (Show, Eq, Ord)

-- * Expressions

-- | A relation between terms.
data RelOp = RelEq | RelNe | RelLt | RelLe | RelGt | RelGe
  deriving stock (Show, Eq, Ord)

-- | A binary connective between propositions.
data Connective = And | Or | Iff
  deriving stock (Show, Eq, Ord)

-- | The bound of a bounded quantifier: below @t@, or at most @t@.
data BoundRel = Below | AtMost
  deriving stock (Show, Eq, Ord)

-- | A pattern of a clause or of a case alternative; its variables are numbered from the left, from 0.
data Pattern
  = PVar !Hint
  | PWild
  | PCon !Ref ![Pattern]
  | PNat !Natural
  | PSucc !Pattern
  deriving stock (Show, Eq)

{- |
An expression over variables @a@.  A @case@ alternative binds the variables
of its pattern, in order; a λ binds its parameters, in order.
-}
data Expr a
  = Var a
  | Global !Ref
  | Nat !Natural
  | App (Expr a) (Expr a)
  | -- | where the expression was written
    At !(Irrelevant Span) (Expr a)
  | Lam ![Hint] (Scope Int Expr a)
  | Case (Expr a) [(Pattern, Scope Int Expr a)]
  | If (Expr a) (Expr a) (Expr a)
  | -- | @{a : T} -> B@ when implicit, @(x : T) -> B@ otherwise
    Pi !Hint !Bool (Expr a) (Scope () Expr a)
  | -- | a function type, or an implication
    Arrow (Expr a) (Expr a)
  | -- | a quantifier: the bound, if any, and the type of the variable, if written
    Quant !Quantifier !Hint (Maybe (BoundRel, Expr a)) (Maybe (Expr a)) (Scope () Expr a)
  | Rel !RelOp (Expr a) (Expr a)
  | Conn !Connective (Expr a) (Expr a)
  | Not (Expr a)
  | Top
  | Bottom
  | -- | @Type@
    Universe
  | -- | @_@
    Hole
  deriving stock (Functor, Foldable, Traversable)

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  m >>= k = case m of
    Var a -> k a
    Global r -> Global r
    Nat n -> Nat n
    App f x -> App (f >>= k) (x >>= k)
    At sp e -> At sp (e >>= k)
    Lam hs b -> Lam hs (b >>>= k)
    Case s alts -> Case (s >>= k) [(p, b >>>= k) | (p, b) <- alts]
    If c t e -> If (c >>= k) (t >>= k) (e >>= k)
    Pi h i d b -> Pi h i (d >>= k) (b >>>= k)
    Arrow a b -> Arrow (a >>= k) (b >>= k)
    Quant q h bound ty b -> Quant q h (fmap (fmap (>>= k)) bound) (fmap (>>= k) ty) (b >>>= k)
    Rel r a b -> Rel r (a >>= k) (b >>= k)
    Conn c a b -> Conn c (a >>= k) (b >>= k)
    Not a -> Not (a >>= k)
    Top -> Top
    Bottom -> Bottom
    Universe -> Universe
    Hole -> Hole

-- | α-equivalence: binders compare by index, hints and spans not at all.
instance Eq1 Expr where
  liftEq eq = go
    where
      go (At _ e) f = go e f
      go e (At _ f) = go e f
      go (Var a) (Var b) = eq a b
      go (Global r) (Global s) = r == s
      go (Nat m) (Nat n) = m == n
      go (App f x) (App g y) = go f g && go x y
      go (Lam _ b) (Lam _ c) = liftEq eq b c
      go (Case s as) (Case t bs) = go s t && liftEq (\(p, b) (q, c) -> p == q && liftEq eq b c) as bs
      go (If a b c) (If a' b' c') = go a a' && go b b' && go c c'
      go (Pi _ i d b) (Pi _ j e c) = i == j && go d e && liftEq eq b c
      go (Arrow a b) (Arrow c d) = go a c && go b d
      go (Quant q _ bd ty b) (Quant r _ be tz c) =
        q == r && liftEq (\(x, s) (y, t) -> x == y && go s t) bd be && liftEq go ty tz && liftEq eq b c
      go (Rel r a b) (Rel s c d) = r == s && go a c && go b d
      go (Conn r a b) (Conn s c d) = r == s && go a c && go b d
      go (Not a) (Not b) = go a b
      go Top Top = True
      go Bottom Bottom = True
      go Universe Universe = True
      go Hole Hole = True
      go _ _ = False

-- | For debugging: the constructors, spans left out.
instance Show1 Expr where
  liftShowsPrec :: forall a. (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> Expr a -> ShowS
  liftShowsPrec sp sl = go
    where
      go d = \case
        Var a -> con d "Var" [flip sp a]
        Global r -> con d "Global" [flip showsPrec r]
        Nat n -> con d "Nat" [flip showsPrec n]
        App f x -> con d "App" [flip go f, flip go x]
        At _ e -> go d e
        Lam hs b -> con d "Lam" [flip showsPrec hs, scope b]
        Case s alts -> con d "Case" [flip go s, \_ -> showListWith (\(p, b) -> showChar '(' . showsPrec 0 p . showString ", " . scope b 0 . showChar ')') alts]
        If a b c -> con d "If" [flip go a, flip go b, flip go c]
        Pi h i dom b -> con d "Pi" [flip showsPrec h, flip showsPrec i, flip go dom, scope b]
        Arrow a b -> con d "Arrow" [flip go a, flip go b]
        Quant q h bd ty b -> con d "Quant" [flip showsPrec q, flip showsPrec h, \_ -> maybe (showString "Nothing") (\(r, t) -> showsPrec 11 r . showChar ' ' . go 11 t) bd, \_ -> maybe (showString "Nothing") (go 11) ty, scope b]
        Rel r a b -> con d "Rel" [flip showsPrec r, flip go a, flip go b]
        Conn c a b -> con d "Conn" [flip showsPrec c, flip go a, flip go b]
        Not a -> con d "Not" [flip go a]
        Top -> showString "Top"
        Bottom -> showString "Bottom"
        Universe -> showString "Universe"
        Hole -> showString "Hole"
      scope :: forall b. (Show b) => Scope b Expr a -> Int -> ShowS
      scope b d = liftShowsPrec sp sl d b
      con d name fields = showParen (d > 10) (showString name . foldr (\f acc -> showChar ' ' . f 11 . acc) id fields)

instance (Eq a) => Eq (Expr a) where
  (==) = eq1

instance (Show a) => Show (Expr a) where
  showsPrec = showsPrec1

-- | The expression without its source spans, at every depth but under binders.
stripLocations :: Expr a -> Expr a
stripLocations = \case
  At _ e -> stripLocations e
  App f x -> App (stripLocations f) (stripLocations x)
  e -> e

-- | An application as its head and arguments, spans removed along the spine.
spine :: Expr a -> (Expr a, [Expr a])
spine = go []
  where
    go args = \case
      App f x -> go (x : args) f
      At _ e -> go args e
      e -> (e, args)

-- | A head applied to arguments.
apps :: Expr a -> [Expr a] -> Expr a
apps = foldl App

-- | Every global reference replaced as the function says, under binders too.
mapGlobals :: (Ref -> Ref) -> Expr a -> Expr a
mapGlobals f = go
  where
    go :: Expr x -> Expr x
    go = \case
      Var a -> Var a
      Global r -> Global (f r)
      Nat n -> Nat n
      App g x -> App (go g) (go x)
      At sp e -> At sp (go e)
      Lam hs b -> Lam hs (hoistScope go b)
      Case s alts -> Case (go s) [(p, hoistScope go b) | (p, b) <- alts]
      If c t e -> If (go c) (go t) (go e)
      Pi h i d b -> Pi h i (go d) (hoistScope go b)
      Arrow a b -> Arrow (go a) (go b)
      Quant q h bound ty b -> Quant q h (fmap (fmap go) bound) (fmap go ty) (hoistScope go b)
      Rel r a b -> Rel r (go a) (go b)
      Conn c a b -> Conn c (go a) (go b)
      Not a -> Not (go a)
      Top -> Top
      Bottom -> Bottom
      Universe -> Universe
      Hole -> Hole

{- |
Every application of a global rewritten as the function says, given the
global and its arguments, themselves rewritten, under binders too; a global
the function leaves stays, its arguments rewritten.  Spans along a spine are
dropped.
-}
rewriteApps :: (forall x. Ref -> [Expr x] -> Maybe (Expr x)) -> Expr a -> Expr a
rewriteApps f = go
  where
    go :: Expr x -> Expr x
    go = \case
      e@(App _ _) -> case spine e of
        (Global r, as) -> let as' = map go as in fromMaybe (apps (Global r) as') (f r as')
        (h, as) -> apps (go h) (map go as)
      Global r -> fromMaybe (Global r) (f r [])
      Var a -> Var a
      Nat n -> Nat n
      At sp e -> At sp (go e)
      Lam hs b -> Lam hs (hoistScope go b)
      Case s alts -> Case (go s) [(p, hoistScope go b) | (p, b) <- alts]
      If c t e -> If (go c) (go t) (go e)
      Pi h i d b -> Pi h i (go d) (hoistScope go b)
      Arrow a b -> Arrow (go a) (go b)
      Quant q h bound ty b -> Quant q h (fmap (fmap go) bound) (fmap go ty) (hoistScope go b)
      Rel r a b -> Rel r (go a) (go b)
      Conn c a b -> Conn c (go a) (go b)
      Not a -> Not (go a)
      Top -> Top
      Bottom -> Bottom
      Universe -> Universe
      Hole -> Hole

-- | The global references of an expression, under binders too.
globalsOf :: Expr a -> [Ref]
globalsOf = go
  where
    go :: Expr x -> [Ref]
    go = \case
      Global r -> [r]
      App f x -> go f <> go x
      At _ e -> go e
      Lam _ b -> go (fromScope b)
      Case s alts -> go s <> concatMap (go . fromScope . snd) alts
      If c t e -> go c <> go t <> go e
      Pi _ _ d b -> go d <> go (fromScope b)
      Arrow a b -> go a <> go b
      Quant _ _ bound ty b -> maybe [] (go . snd) bound <> maybe [] go ty <> go (fromScope b)
      Rel _ a b -> go a <> go b
      Conn _ a b -> go a <> go b
      Not a -> go a
      _ -> []

-- * Patterns

-- | The number of variables a pattern binds.
patternVariables :: Pattern -> Int
patternVariables = length . patternHints

-- | The hints of the variables a pattern binds, in order.
patternHints :: Pattern -> [Hint]
patternHints = \case
  PVar h -> [h]
  PWild -> []
  PCon _ ps -> concatMap patternHints ps
  PNat _ -> []
  PSucc p -> patternHints p

-- * Binding

-- | Bind the given variables, the first as index 0.
abstractNames :: (Eq a) => [a] -> Expr a -> Scope Int Expr a
abstractNames names = abstract (`elemIndex` names)

-- | Instantiate the bound variables of a scope by the given expressions, index 0 first.
instantiateNames :: [Expr a] -> Scope Int Expr a -> Expr a
instantiateNames xs = instantiate (\i -> if i < length xs then xs !! i else error "Language.Praxis.Surface.Syntax.instantiateNames: an index out of range")
