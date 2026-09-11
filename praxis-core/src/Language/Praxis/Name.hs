-- | Names, and choosing them apart from others.
module Language.Praxis.Name (
  Fresh (..),
) where

import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)

-- | Names which can be chosen apart from any finite set of others.
class (Hashable a) => Fresh a where
  -- | A name not in the set, derived from the hint.
  freshen :: HashSet a -> a -> a

  -- | The hint to start from when nothing suggests one.
  anyName :: a

-- | Primes are appended until the name is new: @x@, @x'@, @x''@, and so on.
instance Fresh String where
  freshen used = go
    where
      go n
        | n `HS.member` used = go (n <> "'")
        | otherwise = n
  anyName = "x"
