{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

module Language.Praxis.PRA.PrimitiveRecursion (
  PRFCode (..),
  V,
  evalPRFCode,
  evalPRFCodeM,
  Evalable (..),
  zero,
  suc,
) where

import Control.Lens (Prism', prism', review, (^?))
import Control.Lens.Extras (is)
import Data.Functor.Identity (Identity (..))
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

{- | A domain in which a 'PRFCode' can be run.

Besides the numerals themselves ('_Zero', '_Succ' and 'fromNatural'), an instance
must say what an application that /cannot/ be reduced any further looks like
('residual').  Fully-evaluated domains such as 'Natural' have no such form and
may therefore only be used with the total evaluator 'evalPRFCode'; syntactic
domains such as @'Language.Praxis.PRA.Syntax.Term' a@ keep the application
around symbolically, which is what turns 'evalPRFCodeM' into a partial
evaluator.
-}
class Evalable a where
  _Succ :: Prism' a a
  _Zero :: Prism' a ()
  fromNatural :: Natural -> a

  {- | The value standing for an application of @f@ to @args@ which is stuck,
  either because an argument is neither zero nor a successor, or because the
  evaluation budget of 'evalPRFCodeM' ran out.
  -}
  residual :: (KnownNat n) => PRFCode n -> V n a -> a

zero :: (Evalable a) => a
zero = review _Zero ()

suc :: (Evalable a) => a -> a
suc = review _Succ

instance Evalable Natural where
  _Succ = prism' (+ 1) (\x -> if x == 0 then Nothing else Just (x - 1))
  _Zero = prism' (const 0) (\x -> if x == 0 then Just () else Nothing)
  fromNatural = id
  {-# INLINE fromNatural #-}
  residual code _ =
    error $
      "evalPRFCodeM: `Natural' has no residual form, but the reduction of `"
        <> show code
        <> "' was aborted; use `evalPRFCode' instead."

{- | Evaluates a 'PRFCode', metering every reduction step with the given action.

The step action reports whether reduction may continue; as soon as it answers
'False' the application currently under consideration is left as a 'residual'.
Together with a syntactic 'Evalable' instance this gives budgeted partial
evaluation - see "Language.Praxis.PRA.Equality".
-}
evalPRFCodeM ::
  forall m n a.
  (Monad m, KnownNat n, Evalable a) =>
  -- | consumes one reduction step; 'False' aborts the reduction
  m Bool ->
  PRFCode n ->
  V n a ->
  m a
evalPRFCodeM step = go
  where
    go :: forall k. (KnownNat k) => PRFCode k -> V k a -> m a
    go code args =
      step >>= \case
        False -> pure $ residual code args
        True -> case code of
          Zero -> pure zero
          Succ -> pure $ suc $ sIndex [od|0|] args
          Proj i -> pure $ sIndex i args
          Comp f gs -> go f =<< traverse (`go` args) gs
          Rec g h -> recurse g h (SV.head args) (SV.tail args)

    recurse :: forall k. (KnownNat k) => PRFCode k -> PRFCode (k + 2) -> a -> V k a -> m a
    recurse g h y xs
      | is _Zero y = go g xs
      | Just !y' <- y ^? _Succ =
          step >>= \case
            False -> pure stuck
            True -> do
              !z <- recurse g h y' xs
              go h (y' :< z :< xs)
      | otherwise = pure stuck
      where
        stuck = residual (Rec g h) (y :< xs)

{- | Total evaluation of a 'PRFCode': every reduction step is taken, so
'residual' is never consulted.
-}
evalPRFCode :: (KnownNat n, Evalable a) => PRFCode n -> V n a -> a
evalPRFCode f = runIdentity . evalPRFCodeM (pure True) f
