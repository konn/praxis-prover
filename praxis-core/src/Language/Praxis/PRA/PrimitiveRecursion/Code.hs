{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

module Language.Praxis.PRA.PrimitiveRecursion.Code (
  PRFCode (Zero, Succ, Proj, Comp, Rec),
  codeHash,
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
import GHC.Exts (isTrue#, reallyUnsafePtrEquality#)
import Language.Haskell.TH.Syntax (Lift (..), unTypeCode)
import Language.Praxis.PRA.PrimitiveRecursion.TH.Internal ()
import Numeric.Natural

type V = Sized V.Vector

{- | The bare PRA language: zero, successor, projection, composition and
primitive recursion. Named definitions live in the layer above this module.
-}
data PRFCode m where
  Zero :: PRFCode k
  Succ :: PRFCode 1
  Proj :: !(Ordinal n) -> PRFCode n
  -- | A composition, with its hash: built only by 'Comp'.
  CompC :: (KnownNat m) => !Int -> !(PRFCode m) -> !(V m (PRFCode n)) -> PRFCode n
  -- | A primitive recursion, with its hash: built only by 'Rec'.
  RecC :: !Int -> !(PRFCode k) -> !(PRFCode (k + 2)) -> PRFCode (k + 1)

-- | Composition: @f@ applied to the results of the @gs@, each applied to the arguments.
pattern Comp :: () => (KnownNat m) => PRFCode m -> V m (PRFCode n) -> PRFCode n
pattern Comp f gs <- CompC _ f gs
  where
    Comp f gs = CompC (V.foldl' (\h g -> hashWithSalt h (codeHash g)) (hashWithSalt (3 :: Int) (codeHash f)) (unsized gs)) f gs

{- |
Primitive recursion on the first argument: the base case is given the fixed
arguments, and the successor step the recursion parameter, the result of the
previous step, and then the fixed arguments.
-}
pattern Rec :: forall n. () => forall k. (n ~ (k + 1)) => PRFCode k -> PRFCode (k + 2) -> PRFCode n
pattern Rec g h <- RecC _ g h
  where
    Rec g h = RecC (hashWithSalt (hashWithSalt (4 :: Int) (codeHash g)) (codeHash h)) g h

{-# COMPLETE Zero, Succ, Proj, Comp, Rec #-}

{- |
The hash of a code, cached by the compositions and recursions, so that hashing
a code costs constant time.
-}
codeHash :: PRFCode n -> Int
codeHash = \case
  Zero -> 0
  Succ -> 1
  Proj i -> hashWithSalt (2 :: Int) (ordToNatural i)
  CompC h _ _ -> h
  RecC h _ _ -> h

-- | Whether two codes are one object in memory, and so equal.
sameCode :: PRFCode n -> PRFCode n -> Bool
sameCode f g = isTrue# (reallyUnsafePtrEquality# f g)

instance (KnownNat n) => Show (PRFCode n) where
  showsPrec d = \case
    Zero -> showString "Zero"
    Succ -> showString "Succ"
    Proj i -> showParen (d > 10) (showString "Proj " . showsPrec 11 i)
    Comp f gs -> showParen (d > 10) (showString "Comp " . showsPrec 11 f . showChar ' ' . showsPrec 11 gs)
    Rec g h -> showParen (d > 10) (showString "Rec " . showsPrec 11 g . showChar ' ' . showsPrec 11 h)

-- | Lifted through 'Comp' and 'Rec', so that the hashes are computed again where the code is spliced.
instance (KnownNat n) => Lift (PRFCode n) where
  lift = unTypeCode . liftTyped
  liftTyped = \case
    Zero -> [||Zero||]
    Succ -> [||Succ||]
    Proj i -> [||Proj $$(liftTyped i)||]
    Comp f gs -> [||Comp $$(liftTyped f) $$(liftTyped gs)||]
    Rec g h -> [||Rec $$(liftTyped g) $$(liftTyped h)||]

-- | Agrees with '(==)': the cached hash.
instance (KnownNat n) => Hashable (PRFCode n) where
  hashWithSalt salt code = hashWithSalt salt (codeHash code)

instance (KnownNat n) => Eq (PRFCode n) where
  f == g
    | sameCode f g = True
    | otherwise = case (f, g) of
        (Zero, Zero) -> True
        (Succ, Succ) -> True
        (Proj i1, Proj i2) -> i1 == i2
        (CompC h1 (f1 :: PRFCode m) gs1, CompC h2 (f2 :: PRFCode m') gs2) ->
          h1 == h2 && case testEquality (sNat @m) (sNat @m') of
            Nothing -> False
            Just Refl -> f1 == f2 && gs1 == gs2
        (RecC h1 g1 s1, RecC h2 g2 s2) -> h1 == h2 && g1 == g2 && s1 == s2
        _ -> False

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
