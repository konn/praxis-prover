{-# LANGUAGE QuasiQuotes #-}

-- | Arity-indexed primitive-recursive codes and a small arithmetic library.
module Language.Praxis.PRA.PrimitiveRecursion (
  module Language.Praxis.PRA.PrimitiveRecursion.Code,
  add,
  mul,
  pow,
  sgn,
  sub,
  prd,
  lt,
  isZero,
  ifte,
  triangle,
  pair,
  cons,
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

  sgn (S n) = 1
  sgn 0 = 0

  prd 0 = 0
  prd (S n) = n

  sub n 0 = n
  sub n (S m) = prd (sub n m)

  lt n m = sgn (sub m n)

  isZero 0 = 1
  isZero (S n) = 0

  ifte 0 t e = e
  ifte (S n) t e = t

  triangle 0 = 0
  triangle (S n) = add (triangle n) (S n)

  pair x y = add (triangle (add x y)) y

  cons x y = S (pair x y)
|]
