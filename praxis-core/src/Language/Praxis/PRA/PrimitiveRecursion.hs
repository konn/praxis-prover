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
  mu,
  projW,
  godelPi1,
  godelPi2,
  lft,
  rgt,
  arithmetic,
) where

import Language.Praxis.PRA.PrimitiveRecursion.Code
import Language.Praxis.PRA.PrimitiveRecursion.Quote (prf)

[prf|
  environment arithmetic

  add n 0 = n
  add n (S m) = S (add n m)

  mul n 0 = 0
  mul n (S m) = n + (n * m)

  pow n 0 = 1
  pow n (S m) = n * (pow n m)

  sgn (S n) = 1
  sgn 0 = 0

  prd 0 = 0
  prd (S n) = n

  sub n 0 = n
  sub n (S m) = prd (sub n m)

  lt n m = sgn (m - n)

  isZero 0 = 1
  isZero (S n) = 0

  ifte 0 t e = e
  ifte (S n) t e = t

  triangle 0 = 0
  triangle (S n) = triangle n + S n

  pair x y = triangle (x + y) + y

  cons x y = S (pair x y)

  mu {P} 0 xs = 0
  mu {P} (S n) xs =
    if mu P n xs < n
      then mu P n xs
      else if P n xs then n else S n
  
  projAuxP k z = z < triangle (k + 1)

  projW z = mu {projAuxP} (S z) z
  godelPi2 z = z - triangle (projW z)
  godelPi1 z = projW z - godelPi2 z

  lft p = godelPi1 (prd p)
  rgt p = godelPi2 (prd p)
|]
