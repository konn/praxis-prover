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
  Proof (..),
  ProofF (..),
  RuleName (..),
  HasRuleName (..),
  Substitutable (..),
) where

import Data.Functor.Foldable.TH (MakeBaseFunctor (makeBaseFunctor))
import Data.Generics.Labels ()
import Data.Hashable (Hashable (..))
import Data.Multiset (Multiset)
import Data.Sized
import Data.Type.Equality
import Data.Type.Natural hiding (Succ)
import Data.Vector qualified as V
import GHC.Generics
import Language.Praxis.PRA.PrimitiveRecursion
import Numeric.Natural

data Term a where
  Var :: !a -> Term a
  Lit :: !Natural -> Term a
  (:$) :: (KnownNat n) => !(PRFCode n) -> !(V n (Term a)) -> Term a

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
  deriving (Show, Eq, Generic, Functor)
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

{- |
A proof tree in qunatifier-free fragment of G3i calculus,
an intuitionistic sequent calculus with all rules invertible,
which is well-suited for proof search.
-}
data Proof a
  = {- |
    The identity law for atomic formula @A@.

    @
      ---------- 'Id'(A, Γ)
      A, Γ |- A
    @
    -}
    Id !(Atomic a) !(Multiset (Formula a))
  | {- |
    Ex falso quodlibet.

    @
      ---------- 'ExFalso'(Γ, A), if ⊥ ∈ Γ
      ⊥, Γ |- A
    @
    -}
    ExFalso !(Multiset (Formula a)) !(Formula a)
  | {- |
    The left-introduction rule for '/\'.

    @
            :
            P
            :
        A, B, Γ |- C
      --------------- 'ConjL'(A, B; P)
      A /\ B, Γ |- C
    @
    -}
    ConjL !(Formula a) !(Formula a) !(Proof a)
  | {- |
    The right-introduction rule for '/\'.

    @
        :         :
        P         Q
        :         :
      Γ |- A    Γ |- B
      ------------------- 'ConjR'(P, Q)
         Γ |- A '/\' B
    @
    -}
    ConjR !(Proof a) !(Proof a)
  | {- |
      The left-introduction rule for '\/'.

      @
               :             :
               P             Q
               :             :
          A, Γ |- C     B, Γ |- C
          ------------------------ 'DisjL'(A, B; P, Q)
              A \/ B, Γ |- C
      @
    -}
    DisjL !(Formula a) !(Formula a) !(Proof a) !(Proof a)
  | {- |
      The right-introduction rule for '\/' (first position).

      @
          :
          P
          :
        Γ |- B
        -------------- 'DisjR1'(A; P)
        Γ |- A '\/' B
      @
    -}
    DisjR1 !(Formula a) !(Proof a)
  | {- |
      The right-introduction rule for '\/' (second position).

      @
          :
          P
          :
        Γ |- B
        -------------- 'DisjR2'(A; P)
        Γ |- B '\/' A
      @
    -}
    DisjR2 !(Formula a) !(Proof a)
  | {- |
      The left-introduction rule for '==>'.

      @
                 :            :
                 P            Q
                 :            :
      A ==> B, Γ |- A    B, Γ |- C
      ----------------------------- 'ImplL'(A, B; P, Q)
            A ==> B, Γ |- C
      @
    -}
    ImplL !(Formula a) !(Formula a) !(Proof a) !(Proof a)
  | {- |
      The right-introduction rule for '==>'.

      @
             :
             P
             :
        A, Γ |- B
        ------------------ 'ImplR'(A; P)
           Γ |- A '==>' B
      @
    -}
    ImplR !(Formula a) !(Proof a)
  | -- Equality Rules

    {- |
      Definitional equality:

      @
                 :
                 P
                 :
               Γ |- C
        ------------- Defeq(s, t; P)
        s ≡ t, Γ |- C
      @

      where, @≡@ is the definitional equality of terms, checked by the trusted evaluator of primitive-recursive functions.
    -}
    Defeq !(Term a) !(Term a) !(Proof a)
  | {- |
      Substitution rule (for P: atomic):

      @
          :
          P
          :
        t = s, P[x := t], P[x := s], Γ |- C
        ------------------------------------ 'Subst'(x, t, s; P)
                   t = s, P[x := t], Γ |- C
      @
    -}
    Subst !a !(Term a) !(Term a) !(Atomic a) !(Proof a)
  deriving (Show, Eq)

makeBaseFunctor ''Proof

data RuleName
  = IdRule
  | ExFalsoRule
  | ConjLRule
  | ConjRRule
  | DisjLRule
  | DisjR1Rule
  | DisjR2Rule
  | ImplLRule
  | ImplRRule
  | DefeqRule
  deriving (Show, Eq, Generic)
  deriving anyclass (Hashable)

class HasRuleName a where
  ruleName :: a -> RuleName

instance HasRuleName (Proof a) where
  ruleName Id {} = IdRule
  ruleName ExFalso {} = ExFalsoRule
  ruleName ConjL {} = ConjLRule
  ruleName ConjR {} = ConjRRule
  ruleName DisjL {} = DisjLRule
  ruleName DisjR1 {} = DisjR1Rule
  ruleName DisjR2 {} = DisjR2Rule
  ruleName ImplL {} = ImplLRule
  ruleName ImplR {} = ImplRRule
  ruleName Defeq {} = DefeqRule

instance HasRuleName (ProofF a b) where
  ruleName IdF {} = IdRule
  ruleName ExFalsoF {} = ExFalsoRule
  ruleName ConjLF {} = ConjLRule
  ruleName ConjRF {} = ConjRRule
  ruleName DisjLF {} = DisjLRule
  ruleName DisjR1F {} = DisjR1Rule
  ruleName DisjR2F {} = DisjR2Rule
  ruleName ImplLF {} = ImplLRule
  ruleName ImplRF {} = ImplRRule
  ruleName DefeqF {} = DefeqRule
