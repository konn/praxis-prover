{-# LANGUAGE QuasiQuotes #-}

-- | Arity-indexed primitive-recursive codes and a small arithmetic library.
module Language.Praxis.PRA.PrimitiveRecursion (
  module Language.Praxis.PRA.PrimitiveRecursion.Code,
  add,
  mul,
  pow,
  arithmetic,
) where

import Language.Praxis.PRA.PrimitiveRecursion.Code
import Language.Praxis.PRA.PrimitiveRecursion.Quote (prf)

[prf|
  environment arithmetic

  add n 0 = n
  add n (S m) = S (add n m)

  mul n 0 = 0
  mul n (S m) =
    add n
        (mul n m)

  pow n 0 = 1
  pow n (S m) = mul n (pow n m)
|]
