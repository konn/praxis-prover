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

instance (Hashable a) => Hashable (Term a) where
  hashWithSalt salt (Var x) = hashWithSalt salt (0 :: Int, x)
  hashWithSalt salt (Lit n) = hashWithSalt salt (1 :: Int, n)
  hashWithSalt salt (f :$ xs) = hashWithSalt salt (2 :: Int, f, V.toList $ unsized xs)

instance (Eq a) => Eq (Term a) where
  Var x1 == Var x2 = x1 == x2
  Var {} == _ = False
  Lit n1 == Lit n2 = n1 == n2
  Lit {} == _ = False
  (f1 :: PRFCode m) :$ xs1 == (f2 :: PRFCode m') :$ xs2 =
    case testEquality (sNat @m) (sNat @m') of
      Nothing -> False
      Just Refl -> f1 == f2 && xs1 == xs2
  (:$) {} == _ = False

infix 6 :$

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
