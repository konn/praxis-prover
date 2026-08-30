{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

module Language.Praxis.PRA.PrimitiveRecursion (
  PRFCode (..),
  V,
  evalPRFCode,
  Evalable (..),
  zero,
) where

import Control.Lens (Prism', prism', re, (^.), (^?))
import Control.Lens.Extras (is)
import Data.Hashable (Hashable (..))
import Data.Sized
import Data.Sized qualified as SV
import Data.Type.Equality
import Data.Type.Natural hiding (Succ, Zero)
import Data.Type.Ordinal
import Data.Vector qualified as V
import Numeric.Natural

type V = Sized V.Vector

{- | A code of primitive-recursive function.
For convenience, we also include addition and multiplication as primitive-recursive functions.
-}
data PRFCode m where
  Zero :: PRFCode k
  Succ :: PRFCode 1
  Proj :: !(Ordinal n) -> PRFCode n
  Comp :: (KnownNat m) => !(PRFCode m) -> !(V m (PRFCode n)) -> PRFCode n
  Rec :: !(PRFCode k) -> !(PRFCode (k + 2)) -> PRFCode (k + 1)

deriving instance (KnownNat n) => Show (PRFCode n)

instance (KnownNat n) => Hashable (PRFCode n) where
  hashWithSalt salt Zero = hashWithSalt salt (0 :: Int)
  hashWithSalt salt Succ = hashWithSalt salt (1 :: Int)
  hashWithSalt salt (Proj i) = hashWithSalt salt (2 :: Int, ordToNatural i)
  hashWithSalt salt (Comp f gs) = hashWithSalt salt (3 :: Int, f, V.toList $ unsized gs)
  hashWithSalt salt (Rec g h) = hashWithSalt salt (4 :: Int, g, h)

instance (KnownNat n) => Eq (PRFCode n) where
  Zero == Zero = True
  Zero == _ = False
  Succ == Succ = True
  Succ == _ = False
  Proj i1 == Proj i2 = i1 == i2
  Proj {} == _ = False
  Comp (f1 :: PRFCode m) gs1 == Comp (f2 :: PRFCode m') gs2 =
    case testEquality (sNat @m) (sNat @m') of
      Nothing -> False
      Just Refl -> f1 == f2 && gs1 == gs2
  Comp {} == _ = False
  Rec g1 h1 == Rec g2 h2 = g1 == g2 && h1 == h2
  Rec {} == _ = False

class Evalable a where
  _Succ :: Prism' a a
  _Zero :: Prism' a ()
  fromNatural :: Natural -> a

zero :: (Evalable a) => a
zero = () ^. re _Zero

instance Evalable Natural where
  _Succ = prism' (+ 1) (\x -> if x == 0 then Nothing else Just (x - 1))
  _Zero = prism' (const 0) (\x -> if x == 0 then Just () else Nothing)
  fromNatural = id
  {-# INLINE fromNatural #-}

evalPRFCode :: (KnownNat n, Evalable a) => PRFCode n -> V n a -> a
evalPRFCode Zero _ = () ^. re _Zero
evalPRFCode Succ x = sIndex [od|0|] x
evalPRFCode (Proj i) tuple = sIndex i tuple
evalPRFCode (Comp f gs) tuple = evalPRFCode f (fmap (`evalPRFCode` tuple) gs)
evalPRFCode (Rec g h) (yxs :: V (k + 1) a) = f (SV.head yxs) (SV.tail yxs)
  where
    f :: a -> V k a -> a
    f y xs =
      if
        | is _Zero y -> evalPRFCode g xs
        | Just !y' <- y ^? _Succ ->
            let !z = f y' xs
             in evalPRFCode h (y' :< z :< xs)
        | otherwise -> undefined
