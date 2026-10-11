{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Praxis.PRA.Syntax (
  Term (Var, Lit, App, (:$)),
  Atomic (..),
  (===),
  Formula (..),
  (/\),
  (\/),
  (==>),
  Sequent (..),
  (|-),
  Substitutable (..),
  canonicalise,
  suc,
  var,
  lit,

  -- * Abstract functions
  abstractFunction,
  abstractName,
  functionMetas,
  functionMetasInCode,
  Abstraction (..),
  abstraction,
  capturedTerms,
  applyAbstraction,
  abstractionAt,
  compileTerm,
) where

import Control.Exception (evaluate)
import Control.Lens (prism', review)
import Data.Foldable qualified as Foldable
import Data.Generics.Labels ()
import Data.HashMap.Strict qualified as HM
import Data.Hashable (Hashable (..), hash)
import Data.IORef
import Data.IntMap.Strict qualified as IM
import Data.List qualified as L
import Data.Multiset (Multiset)
import Data.Proxy (Proxy (..))
import Data.Sized
import Data.Sized qualified as SV
import Data.Text qualified as T
import Data.Type.Equality
import Data.Type.Natural hiding (Succ, Zero)
import Data.Type.Ordinal
import Data.Vector qualified as V
import GHC.Exts (isTrue#, reallyUnsafePtrEquality#)
import GHC.Generics
import Language.Praxis.PRA.PrimitiveRecursion.Code hiding (suc)
import Language.Praxis.PRA.PrimitiveRecursion.Function (Function (..))
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Numeric.Natural
import System.IO.Unsafe (unsafePerformIO)
import System.Mem.StableName (StableName, makeStableName)

data Term a where
  Var :: !a -> Term a
  Lit :: !Natural -> Term a
  -- | An application, with the hash of its shape: built only by 'App', which keeps terms canonical.
  AppC :: (KnownNat n) => Int -> !(Function n) -> !(V n (Term a)) -> Term a

{- |
A function applied to arguments.  Building one spells a numeral canonically —
'Zero' applied is @'Lit' 0@ and the successor of a numeral the next numeral —
and caches the hash of the term's shape ('shapeHash'); matching one sees the
function and its arguments, whatever the spelling.
-}
pattern App :: () => (KnownNat n) => Function n -> V n (Term a) -> Term a
pattern App f xs <- AppC _ f xs
  where
    App f xs = mkApp f xs

{-# COMPLETE Var, Lit, App #-}

mkApp :: (KnownNat n) => Function n -> V n (Term a) -> Term a
mkApp f xs = case f of
  Primitive Zero -> Lit 0
  Primitive Succ | Lit n <- sIndex [od|0|] xs -> Lit (n + 1)
  _ -> AppC (V.foldl' (\h t -> hashWithSalt h (shapeHash t)) (hashWithSalt (2 :: Int) f) (unsized xs)) f xs

{- |
The hash of a term's shape: its numerals, its functions and its structure, but
not the names of its variables, so that renaming keeps it — 'fmap' does — and
building a term needs no 'Hashable' instance for them.  An application caches
it, so it costs constant time.
-}
shapeHash :: Term a -> Int
shapeHash = \case
  Var _ -> 0
  Lit n -> hashWithSalt 1 n
  AppC h _ _ -> h

-- | Compatibility constructor for applications of bare PRA code.
pattern (:$) :: () => (KnownNat n) => PRFCode n -> V n (Term a) -> Term a
pattern code :$ args = App (Primitive code) args

{- | The successor, canonicalised: a numeral steps to the next numeral, so a
syntactic @Succ@ survives only in front of a term which is not itself a
numeral.  This is the invariant the 'Evalable' instance below documents, and
which "Language.Praxis.PRA.Equality" decides against.
-}
suc :: Term a -> Term a
{-# INLINE suc #-}
suc = review _Succ

lit :: Natural -> Term a
{-# INLINE lit #-}
lit = Lit

var :: a -> Term a
{-# INLINE var #-}
var = Var

instance (Show a) => Show (Term a) where
  showsPrec d (Var x) = showParen (d > 10) (showString "Var " . showsPrec 11 x)
  showsPrec d (Lit n) = showParen (d > 10) (showString "Lit " . showsPrec 11 n)
  showsPrec d (App (Primitive f) xs) = showParen (d > 6) (showsPrec 7 f . showString " :$ " . showsPrec 7 xs)
  showsPrec d (App f xs) = showParen (d > 10) (showString "App " . showsPrec 11 f . showString " " . showsPrec 11 xs)

deriving instance Functor Term

deriving instance Foldable Term

deriving instance Traversable Term

{- |
The canonical form of a term, which every term now has by construction: 'App'
spells 'Zero' applied as @'Lit' 0@ at every arity and the successor of a
numeral as the next numeral, the two ways a numeral could be spelled otherwise.
This is the identity, kept for the callers which asked for the canonical form
before it was built in.

Canonical spelling is deliberately /not/ evaluation.  @plus ':$' ['Lit' 2, 'Lit' 3]@
is left alone; deciding that it denotes @'Lit' 5@ is the job of
'Language.Praxis.PRA.Equality.defEq', and of the @Defeq@ rule which appeals to
it.  Were canonicalisation to reduce, a proof could discharge an equation the
calculus requires @Defeq@ to justify.
-}
canonicalise :: Term a -> Term a
canonicalise = id

{- |
Equality is structural: terms are canonical by construction (see 'App'), so
@'Lit' 4@ is the only spelling of @4@.  It does not reduce.

Two terms which are one object are equal at once, and two whose shapes hash
differently are unequal at once.  Otherwise the terms are walked; a term is
stored as a DAG — a residual of partial evaluation shares a subterm at every
level it unrolled — and its tree can be exponentially larger, so a comparison
which visits more than 'equalityBudget' nodes is settled instead by interning
both terms ('eqInterned'), at a cost linear in the size of the DAGs.
-}
instance (Eq a) => Eq (Term a) where
  s == t
    | same s t = True
    | shapeHash s /= shapeHash t = False
    | otherwise = case eqBounded equalityBudget s t of
        Just equal -> equal
        Nothing -> eqInterned s t

-- | Whether two terms are one object in memory, and so equal whatever they are.
same :: Term a -> Term a -> Bool
same s t = isTrue# (reallyUnsafePtrEquality# s t)

-- | The numeral a term spells, if it is one: a 'Lit', 'Zero' applied, or the successor of a numeral.
numeralOf :: Term a -> Maybe Natural
numeralOf = \case
  Lit n -> Just n
  Zero :$ _ -> Just 0
  Succ :$ xs -> (+ 1) <$> numeralOf (sIndex [od|0|] xs)
  _ -> Nothing

-- | How many nodes a structural comparison visits before it is handed to 'eqInterned'.
equalityBudget :: Int
equalityBudget = 50_000

{- |
Structural equality up to the spelling of numerals, visiting at most the given
number of nodes; 'Nothing' when they did not suffice.
-}
eqBounded :: (Eq a) => Int -> Term a -> Term a -> Maybe Bool
eqBounded budget s0 t0 = fst <$> go budget s0 t0
  where
    go n s t
      | n <= 0 = Nothing
      | same s t = Just (True, n - 1)
      | shapeHash s /= shapeHash t = Just (False, n - 1)
      | otherwise = case (s, t) of
          (Var x, Var y) -> Just (x == y, n - 1)
          (Lit a, _) -> Just (numeralOf t == Just a, n - 1)
          (_, Lit b) -> Just (numeralOf s == Just b, n - 1)
          (Zero :$ _, _) -> Just (numeralOf t == Just 0, n - 1)
          (_, Zero :$ _) -> Just (numeralOf s == Just 0, n - 1)
          (App (f :: Function m) xs, App (g :: Function m') ys) -> case testEquality (sNat @m) (sNat @m') of
            Just Refl | f == g -> args (n - 1) (Foldable.toList xs) (Foldable.toList ys)
            _ -> Just (False, n - 1)
          _ -> Just (False, n - 1)
    args n (x : xs) (y : ys) = do
      (equal, n') <- go n x y
      if equal then args n' xs ys else Just (False, n')
    args n _ _ = Just (True, n)

{- |
Equality by interning: both terms are entered into one table, structurally
equal subterms — up to the spelling of numerals — receiving one identity, and a
subterm reached again through the sharing of the DAG recognised by its stable
name rather than walked twice.  The cost is linear in the size of the DAGs,
whatever the size of the trees.  The table is local to the call, which is
therefore pure.
-}
eqInterned :: (Eq a) => Term a -> Term a -> Bool
eqInterned s t = unsafePerformIO do
  table <- newTable
  i <- intern table s
  j <- intern table t
  pure (i == j)
{-# NOINLINE eqInterned #-}

-- | The structure of a term one level deep, over the identities of its subterms.
data Key
  = KVar !Int
  | KLit !Natural
  | KApp !Int !F.SomeFunction ![Int]
  deriving (Eq)

instance Hashable Key where
  hashWithSalt salt = \case
    KVar i -> hashWithSalt salt (0 :: Int, i)
    KLit n -> hashWithSalt salt (1 :: Int, n)
    KApp h _ is -> hashWithSalt salt (2 :: Int, h, is)

data Table a = Table
  { tableVariables :: !(IORef [(a, Int)])
  -- ^ the variables met, numbered
  , tableSeen :: !(IORef (HM.HashMap (StableName (Term a)) Int))
  -- ^ the identity of every node walked, by its stable name
  , tableIdentities :: !(IORef (HM.HashMap Key Int))
  , tableKeys :: !(IORef (IM.IntMap Key))
  -- ^ the key of each identity
  }

newTable :: IO (Table a)
newTable = Table <$> newIORef [] <*> newIORef HM.empty <*> newIORef HM.empty <*> newIORef IM.empty

intern :: (Eq a) => Table a -> Term a -> IO Int
intern table t0 = do
  t <- evaluate t0
  name <- makeStableName t
  walked <- readIORef (tableSeen table)
  case HM.lookup name walked of
    Just i -> pure i
    Nothing -> do
      key <- case t of
        Var x -> KVar <$> variable table x
        Lit n -> pure (KLit n)
        Zero :$ _ -> pure (KLit 0)
        App f xs -> do
          is <- mapM (intern table) (Foldable.toList xs)
          spelled <- readIORef (tableKeys table)
          pure case (f, is) of
            (Primitive Succ, [i]) | Just (KLit n) <- IM.lookup i spelled -> KLit (n + 1)
            _ -> KApp (hash f) (F.SomeFunction f) is
      i <- identity table key
      modifyIORef' (tableSeen table) (HM.insert name i)
      pure i

variable :: (Eq a) => Table a -> a -> IO Int
variable table x = do
  vs <- readIORef (tableVariables table)
  case L.lookup x vs of
    Just i -> pure i
    Nothing -> do
      let i = L.length vs
      writeIORef (tableVariables table) ((x, i) : vs)
      pure i

identity :: Table a -> Key -> IO Int
identity table key = do
  known <- readIORef (tableIdentities table)
  case HM.lookup key known of
    Just i -> pure i
    Nothing -> do
      let i = HM.size known
      writeIORef (tableIdentities table) (HM.insert key i known)
      modifyIORef' (tableKeys table) (IM.insert i key)
      pure i

infix 6 :$

{- |
Agrees with '(==)'.  A variable hashes by its name, and any other term by the
hash of its shape, which an application caches: constant time.
-}
instance (Hashable a) => Hashable (Term a) where
  hashWithSalt salt = \case
    Var x -> hashWithSalt salt (0 :: Int, x)
    t -> hashWithSalt salt (shapeHash t)

{- | Terms are the syntactic model of the primitive-recursive numerals: an
application which cannot be reduced is kept as a
'Language.Praxis.PRA.PrimitiveRecursion.residual', which is what turns
'Language.Praxis.PRA.PrimitiveRecursion.evalPRFCodeM' into a partial evaluator
on open terms.

Numerals are canonicalised to 'Lit', so 'Succ' only survives in front of a term
which is not itself a numeral.  Consequently the prisms are lawful only up to
definitional equality — rebuilding a matched @'Succ' ':$' ['Lit' n]@ yields
@'Lit' (n + 1)@ — which is precisely the equivalence
"Language.Praxis.PRA.Equality" decides.
-}
instance Evalable (Term a) where
  _Zero = prism' (const $ Lit 0) \case
    Lit 0 -> Just ()
    -- 'Zero' denotes the constant @0@ at every arity, so it is a numeral
    -- whatever it is applied to — including @'Zero' ':$' 'SV.Nil'@.
    Zero :$ _ -> Just ()
    _ -> Nothing
  _Succ =
    prism'
      \case
        Lit n -> Lit (n + 1)
        t -> Succ :$ SV.singleton t
      \case
        Lit n | n > 0 -> Just $ Lit (n - 1)
        Succ :$ args -> Just $ sIndex [od|0|] args
        _ -> Nothing
  fromNatural = Lit
  residual = (:$)

data Atomic a = !(Term a) :=== !(Term a)
  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Hashable)

class (Functor t) => Substitutable t where
  subst :: (Eq a) => a -> Term a -> t a -> t a

instance Substitutable Term where
  subst x t (Var y)
    | x == y = t
    | otherwise = Var y
  subst _ _ (Lit n) = Lit n
  subst x t (App f xs) = App f (fmap (subst x t) xs)

instance Substitutable Atomic where
  subst x t (t1 :=== t2) = subst x t t1 :=== subst x t t2

instance Substitutable Formula where
  subst x t (Atm p) = Atm $ subst x t p
  subst x t (f1 :/\ f2) = subst x t f1 :/\ subst x t f2
  subst x t (f1 :\/ f2) = subst x t f1 :\/ subst x t f2
  subst x t (f1 :==> f2) = subst x t f1 :==> subst x t f2
  subst _ _ Bot = Bot

data Formula a
  = Atm !(Atomic a)
  | !(Formula a) :/\ !(Formula a)
  | !(Formula a) :\/ !(Formula a)
  | !(Formula a) :==> !(Formula a)
  | Bot
  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Hashable)

(===) :: Term a -> Term a -> Formula a
(===) = fmap Atm . (:===)

infix 5 :===, ===

(/\) :: Formula a -> Formula a -> Formula a
(/\) = (:/\)

infixr 4 :/\, /\

(\/) :: Formula a -> Formula a -> Formula a
(\/) = (:\/)

infixr 3 :\/, \/

(==>) :: Formula a -> Formula a -> Formula a
(==>) = (:==>)

infixr 2 :==>, ==>

data Sequent a = !(Multiset (Formula a)) :|- !(Formula a)
  deriving (Show, Eq, Generic)
  deriving anyclass (Hashable)

(|-) :: Multiset (Formula a) -> Formula a -> Sequent a
(|-) = (:|-)

infix 1 |-, :|-

-- * Abstract functions

{- |
A function known by name only: what a term metavariable with parameters
stands for in the statement of a derived rule, applied as @p(t)@ or standing
as the parameter of a schema, @mu {p} b@.  Its identity records its name
and the names of its parameters; its arity is their number.
-}
abstractFunction :: String -> [String] -> F.SomeFunction
abstractFunction n ps = case someNatVal (fromIntegral (L.length ps)) of
  SomeNat (_ :: Proxy k) -> F.SomeFunction (Abstract (F.DefId (T.pack (n <> "«" <> L.unwords ps <> "»"))) :: Function k)

-- | The name and the parameters of an abstract function, and 'Nothing' for any other function.
abstractName :: Function n -> Maybe (String, [String])
abstractName = \case
  Abstract (F.DefId txt) -> decodeAbstract txt
  _ -> Nothing

decodeAbstract :: T.Text -> Maybe (String, [String])
decodeAbstract txt = case L.break (== '«') (T.unpack txt) of
  (n, '«' : rest) | not (L.null n), not (L.null rest), L.last rest == '»' -> Just (n, L.words (L.init rest))
  _ -> Nothing

{- |
The abstract functions a term mentions, with their parameters: applied, or
as the parameter of a schema instantiated at them, inside the code of the
instance.
-}
functionMetas :: Term a -> [(String, [String])]
functionMetas = L.nub . go
  where
    go = \case
      Var _ -> []
      Lit _ -> []
      App f xs -> functionMetasInCode f <> concatMap go (Foldable.toList xs)

{- | The schematic functions called inside a compiled function, including
calls inside schema parameters and nested lambdas.
-}
functionMetasInCode :: (KnownNat n) => Function n -> [(String, [String])]
functionMetasInCode = L.nub . foldr (\x acc -> maybe acc (: acc) (decodeAbstract x)) [] . F.opaqueCalls . F.functionProgram

{- |
What a term metavariable with parameters is instantiated by.  As a term, a
body over placeholder variables for the parameters, which an application
@p(t1, …, tk)@ substitutes for; as a function, the closed code of that body
over the parameters and then the variables it captures, with the terms to
pass for those, which an instance of a schema at the function takes as
further arguments.  The two agree: the body is the code applied to the
parameters and the captured terms.
-}
data Abstraction a = Abstraction
  { abstractionParameters :: ![a]
  , abstractionBody :: !(Term a)
  , abstractionFunction :: !F.SomeFunction
  , abstractionCaptured :: ![Term a]
  }
  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

{- |
The abstraction of a term over parameters.  A function applied to the
parameters, in order, is that function.  Otherwise the code is the term over
the parameters and then one slot for each maximal subterm mentioning no
parameter, in the order they occur, which is captured.

Capturing whole subterms, numerals included, rather than variables makes the
abstraction canonical: the abstraction of a body with terms substituted for
its free variables is the abstraction of the body with the substitution
applied to what it captures.  So an instance of a schema at it is the same
function whatever the captured terms become, as after an induction or at the
instance of a lemma.
-}
abstraction :: (Eq a) => [a] -> Term a -> Abstraction a
abstraction params body
  | App f xs <- body'
  , notInline f
  , Foldable.toList xs == L.map Var params
  , L.nub params == params =
      Abstraction params body (F.SomeFunction f) []
  | otherwise = Abstraction params body (closureCode params (L.length captured) body') captured
  where
    body' = canonicalise body
    captured = capturedTerms params body'
    -- Inline code, an instance of a schema, is compiled like any body, as the quantifiers compile it.
    notInline :: F.Function n -> Bool
    notInline = \case
      F.Inline _ -> False
      _ -> True

-- | The maximal subterms mentioning none of the variables, in the order they occur.
capturedTerms :: (Eq a) => [a] -> Term a -> [Term a]
capturedTerms params t
  | not (mentions params t) = [t]
  | App _ xs <- t = L.concatMap (capturedTerms params) (Foldable.toList xs)
  | otherwise = []

mentions :: (Eq a) => [a] -> Term a -> Bool
mentions params = L.any (`L.elem` params) . Foldable.toList

-- | The code of a term over the parameters and then a slot for each of the given number of captured subterms, in order.
closureCode :: forall a. (Eq a) => [a] -> Int -> Term a -> F.SomeFunction
closureCode params slots body = case someNatVal (fromIntegral (L.length params + slots)) of
  SomeNat (_ :: Proxy n) -> F.SomeFunction (F.programFunction (snd (go @n (L.length params) body)))
  where
    go :: forall n. (KnownNat n) => Int -> Term a -> (Int, F.Program n)
    go next t
      | not (mentions params t) = (next + 1, F.Base (Proj (ordinals @n L.!! next)))
      | Var v <- t, Just i <- L.elemIndex v params = (next, F.Base (Proj (ordinals @n L.!! i)))
      | App f xs <- t = F.Comp (F.functionProgram f) <$> L.mapAccumL (go @n) next xs
      | otherwise = (next, F.Base Zero)
    ordinals :: forall n. (KnownNat n) => [Ordinal n]
    ordinals = Foldable.toList (SV.generate (sNat @n) id :: V n (Ordinal n))

-- | The abstraction applied: its body with the arguments substituted for the parameters, at once; 'Nothing' for the wrong number of them.
applyAbstraction :: (Eq a) => Abstraction a -> [Term a] -> Maybe (Term a)
applyAbstraction a args
  | L.length args /= L.length (abstractionParameters a) = Nothing
  | otherwise = Just (go (abstractionBody a))
  where
    pairs = L.zip (abstractionParameters a) args
    go = \case
      Var y -> maybe (Var y) id (L.lookup y pairs)
      Lit n -> Lit n
      App f xs -> App f (fmap go xs)

-- | 'applyAbstraction', for arguments which are known to be as many as the parameters.
abstractionAt :: (Eq a) => Abstraction a -> [Term a] -> Term a
abstractionAt a args = case applyAbstraction a args of
  Just t -> t
  Nothing -> error ("Language.Praxis.PRA.Syntax.abstractionAt: " <> show (L.length args) <> " arguments for " <> show (L.length (abstractionParameters a)) <> " parameters")

{- |
A term over variables as the closed code over those variables, in the order
given: a variable is the projection of its slot, and every other symbol
keeps its code.  A variable which is not a slot is read as zero.
-}
compileTerm :: forall a. (Eq a) => [a] -> Term a -> F.SomeFunction
compileTerm slots body = case someNatVal (fromIntegral (L.length slots)) of
  SomeNat (_ :: Proxy n) -> F.SomeFunction (F.programFunction (go @n (canonicalise body)))
  where
    go :: forall n. (KnownNat n) => Term a -> F.Program n
    go = \case
      Var v -> case L.lookup v (L.zip slots (Foldable.toList (SV.generate (sNat @n) id :: V n (Ordinal n)))) of
        Just i -> F.Base (Proj i)
        Nothing -> F.Base Zero
      Lit k -> numeral k
      App f xs -> F.Comp (F.functionProgram f) (fmap go xs)
    numeral :: forall n. (KnownNat n) => Natural -> F.Program n
    numeral 0 = F.Base Zero
    numeral k = F.Comp (F.Base Succ) (SV.singleton (numeral (k - 1)))
