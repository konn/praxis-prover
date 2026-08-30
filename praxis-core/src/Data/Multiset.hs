{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}

module Data.Multiset (
  Multiset,
  empty,
  member,
  uniqueCount,
  population,
  multiplicity,
  removeOne,
  insertOne,
  insertMany,
  toHashSet,
) where

import Data.Coerce (coerce)
import Data.HashMap.Internal.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.HashSet (HashSet)
import Data.Hashable (Hashable)
import Data.Semigroup (stimes)

type role Multiset nominal

-- Invariant: The multiplicity of an element is always positive.
newtype Multiset a = Multiset (HashMap a Word)
  deriving (Eq, Ord)
  deriving newtype (Hashable)

instance (Show a) => Show (Multiset a) where
  showsPrec _ (Multiset m) = shows (HM.toList m)

empty :: (Hashable a) => Multiset a
empty = Multiset mempty

-- | @'removeOne' a@ returns a new multiset with one @a@ removed inside 'Just' present; 'Nothing' otherwise.
removeOne :: (Hashable a) => a -> Multiset a -> Maybe (Multiset a)
{-# INLINE removeOne #-}
removeOne @a =
  coerce $
    HM.alterF @Maybe @a @Word
      ( maybe Nothing \i ->
          if i == 1
            then pure Nothing
            else pure $ Just (i - 1)
      )

insertOne :: (Hashable a) => a -> Multiset a -> Multiset a
{-# INLINE insertOne #-}
insertOne @a = coerce $ HM.alter @a (maybe (Just (1 :: Word)) (Just . (+ 1)))

insertMany :: (Hashable a) => Word -> a -> Multiset a -> Multiset a
insertMany 0 = const id
insertMany @a n = coerce $ HM.alter @a (maybe (Just n) (Just . (+ n)))

-- | Count the total number of elements in the multiset, counting multiplicities.
population :: Multiset a -> Word
{-# INLINE population #-}
population @a = coerce $ sum @(HashMap a) @Word

multiplicity :: (Hashable a) => a -> Multiset a -> Word
{-# INLINE multiplicity #-}
multiplicity @a = coerce $ HM.lookupDefault @a @Word 0

-- | Convert a multiset to a set by discarding multiplicities.
toHashSet :: Multiset a -> HashSet a
{-# INLINE toHashSet #-}
toHashSet @a = coerce $ HM.keysSet @a @Word

uniqueCount :: Multiset a -> Word
{-# INLINE uniqueCount #-}
uniqueCount @a = coerce $ fromIntegral @Int @Word . HM.size @a @Word

union :: (Hashable a) => Multiset a -> Multiset a -> Multiset a
{-# INLINE union #-}
union @a = coerce $ HM.unionWith @a @Word (+)

instance (Hashable a) => Semigroup (Multiset a) where
  (<>) = union
  {-# INLINE (<>) #-}

instance (Hashable a) => Monoid (Multiset a) where
  mempty = empty
  {-# INLINE mempty #-}

instance Foldable Multiset where
  foldMap @a @w f = coerce $ HM.foldMapWithKey @a @w @Word \k v ->
    stimes v (f k)
  {-# INLINE foldMap #-}

member :: (Hashable a) => a -> Multiset a -> Bool
{-# INLINE member #-}
member @a = coerce $ HM.member @a @Word
