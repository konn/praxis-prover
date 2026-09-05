{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE QuasiQuotes #-}

{- |
Patterns over the syntax: terms and formulae whose variables may be wildcards.

A wildcard stands for any term.  There is deliberately no formula-level
wildcard: a hypothesis is selected by the shape of its atoms, and a tactic
parameter which is left open is omitted rather than written as a wildcard
inside a formula.
-}
module Language.Praxis.PRA.Pattern (
  Hole (..),
  wild,
  closed,
  matchTerm,
  matchAtomic,
  matchFormula,
) where

import Control.Lens ((^?))
import Data.Hashable (Hashable)
import Data.Sized qualified as SV
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Type.Natural (sNat)
import Data.Type.Ordinal (od)
import GHC.Generics (Generic)
import Language.Praxis.PRA.PrimitiveRecursion
import Language.Praxis.PRA.Syntax

-- | A variable position in a pattern: a wildcard, or a variable proper.
data Hole a = Wild | Named !a
  deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Hashable)

-- | The pattern matching any term.
wild :: Term (Hole a)
wild = Var Wild

-- | A pattern without wildcards, as the thing it denotes.
closed :: (Traversable t) => t (Hole a) -> Maybe (t a)
closed = traverse \case
  Wild -> Nothing
  Named x -> Just x

{- |
Whether a term matches a pattern.  Numerals are compared up to the two
spellings 'canonicalise' identifies, so @S(_)@ matches @4@.
-}
matchTerm :: (Eq a) => Term (Hole a) -> Term a -> Bool
matchTerm pat = go (canonicalise pat) . canonicalise
  where
    go :: (Eq a) => Term (Hole a) -> Term a -> Bool
    go (Var Wild) _ = True
    go (Var (Named x)) u = u == Var x
    go (Lit n) u = u == Lit n
    go (Succ :$ ps) u = case u ^? _Succ of
      Just u' -> go (SV.sIndex [od|0|] ps) u'
      Nothing -> False
    go ((f :: PRFCode n) :$ ps) ((g :: PRFCode m) :$ us) =
      case testEquality (sNat @n) (sNat @m) of
        Just Refl -> f == g && and (zipWith go (SV.toList ps) (SV.toList us))
        Nothing -> False
    go (_ :$ _) _ = False

matchAtomic :: (Eq a) => Atomic (Hole a) -> Atomic a -> Bool
matchAtomic (p :=== q) (s :=== t) = matchTerm p s && matchTerm q t

matchFormula :: (Eq a) => Formula (Hole a) -> Formula a -> Bool
matchFormula (Atm p) (Atm q) = matchAtomic p q
matchFormula Bot Bot = True
matchFormula (p :/\ q) (f :/\ g) = matchFormula p f && matchFormula q g
matchFormula (p :\/ q) (f :\/ g) = matchFormula p f && matchFormula q g
matchFormula (p :==> q) (f :==> g) = matchFormula p f && matchFormula q g
matchFormula _ _ = False
