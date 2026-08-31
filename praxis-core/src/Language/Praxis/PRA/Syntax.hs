{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Praxis.PRA.Syntax (
  Term (..),
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
) where

import Control.Lens (prism', review)
import Data.Generics.Labels ()
import Data.Hashable (Hashable (..))
import Data.Multiset (Multiset)
import Data.Sized
import Data.Sized qualified as SV
import Data.Type.Equality
import Data.Type.Natural hiding (Succ, Zero)
import Data.Type.Ordinal
import Data.Vector qualified as V
import GHC.Generics
import Language.Praxis.PRA.PrimitiveRecursion hiding (suc)
import Numeric.Natural

data Term a where
  Var :: !a -> Term a
  Lit :: !Natural -> Term a
  (:$) :: (KnownNat n) => !(PRFCode n) -> !(V n (Term a)) -> Term a

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

deriving instance (Show a) => Show (Term a)

deriving instance Functor Term

deriving instance Foldable Term

deriving instance Traversable Term

{- |
Quotient out the redundancy in 'Term''s representation: a successor of a
numeral is the next numeral, and an application of 'Zero' is @'Lit' 0@ at every
arity.  These are the two ways the same numeral can be spelled, and this is
the invariant the 'Evalable' instance below describes.

This is deliberately /not/ evaluation.  @plus ':$' ['Lit' 2, 'Lit' 3]@ is left
alone; deciding that it denotes @'Lit' 5@ is the job of
'Language.Praxis.PRA.Equality.defEq', and of the @Defeq@ rule which appeals to
it.  Were canonicalisation to reduce, a proof could discharge an equation the
calculus requires @Defeq@ to justify.
-}
canonicalise :: Term a -> Term a
canonicalise t@Var {} = t
canonicalise t@Lit {} = t
canonicalise (Zero :$ _) = Lit 0
canonicalise (Succ :$ xs) = suc (canonicalise (sIndex [od|0|] xs))
canonicalise (f :$ xs) = f :$ fmap canonicalise xs

{- |
Equality identifies the spellings 'canonicalise' conflates, so a rule which
builds @'Lit' 4@ meets a context which spells it @'Succ' ':$' ['Lit' 3]@.  It
does not reduce: see 'canonicalise'.
-}
instance (Eq a) => Eq (Term a) where
  t1 == t2 = eqCanonical (canonicalise t1) (canonicalise t2)

-- | Structural equality, on terms already in canonical form.
eqCanonical :: (Eq a) => Term a -> Term a -> Bool
eqCanonical (Var x1) (Var x2) = x1 == x2
eqCanonical Var {} _ = False
eqCanonical (Lit n1) (Lit n2) = n1 == n2
eqCanonical Lit {} _ = False
eqCanonical ((f1 :: PRFCode m) :$ xs1) ((f2 :: PRFCode m') :$ xs2) =
  case testEquality (sNat @m) (sNat @m') of
    Nothing -> False
    Just Refl -> f1 == f2 && V.and (V.zipWith eqCanonical (unsized xs1) (unsized xs2))
eqCanonical (:$) {} _ = False

infix 6 :$

-- | Agrees with '(==)': both work on the canonical form.
instance (Hashable a) => Hashable (Term a) where
  hashWithSalt salt = hashCanonical salt . canonicalise

hashCanonical :: (Hashable a) => Int -> Term a -> Int
hashCanonical salt (Var x) = hashWithSalt salt (0 :: Int, x)
hashCanonical salt (Lit n) = hashWithSalt salt (1 :: Int, n)
hashCanonical salt (f :$ xs) =
  V.foldl' hashCanonical (hashWithSalt salt (2 :: Int, f)) (unsized xs)

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
  subst x t (f :$ xs) = f :$ fmap (subst x t) xs

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
