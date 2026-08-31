{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | A small library of 'PRFCode's to test against.
module Language.Praxis.PRA.PrimitiveRecursion.Examples (
  predC,
  plus,
  mult,
  expo,
) where

import Data.Sized (pattern Nil, pattern (:<))
import Data.Type.Ordinal (od)
import Language.Praxis.PRA.PrimitiveRecursion

-- | @predC n = n - 1@, truncated at zero.
predC :: PRFCode 1
predC = Rec Zero (Proj [od|0|])

-- | @plus (y, x) = y + x@, by recursion on @y@.
plus :: PRFCode 2
plus = Rec (Proj [od|0|]) (Comp Succ (Proj [od|1|] :< Nil))

-- | @mult (y, x) = y * x@, by recursion on @y@.
mult :: PRFCode 2
mult = Rec Zero (Comp plus (Proj [od|1|] :< Proj [od|2|] :< Nil))

-- | @expo (y, x) = x ^ y@, by recursion on @y@.
expo :: PRFCode 2
expo = Rec (Comp Succ (Zero :< Nil)) (Comp mult (Proj [od|1|] :< Proj [od|2|] :< Nil))
