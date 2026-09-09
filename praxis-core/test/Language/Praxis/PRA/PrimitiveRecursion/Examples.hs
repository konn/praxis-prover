{-# LANGUAGE QuasiQuotes #-}

-- | Quote-defined arithmetic, explicitly erased for the bare-kernel fixtures.
module Language.Praxis.PRA.PrimitiveRecursion.Examples (
  predC,
  plus,
  mult,
  expo,
) where

import Control.Exception (displayException)
import Language.Praxis.PRA.PrimitiveRecursion.Code (PRFCode)
import Language.Praxis.PRA.PrimitiveRecursion.Function
import Language.Praxis.PRA.PrimitiveRecursion.Quote (prf)
import Language.Praxis.PRA.Signature (signatureKernelEnv)

[prf|
  environment examples
  predecessor 0 = 0
  predecessor (S n) = n

  addition 0 x = x
  addition (S y) x = S (addition y x)

  multiplication 0 x = 0
  multiplication (S y) x = addition (multiplication y x) x

  exponentiation 0 x = 1
  exponentiation (S y) x = multiplication (exponentiation y x) x
|]

predC :: PRFCode 1
predC = either (error . displayException) id (signatureKernelEnv examples >>= (`eraseFunction` predecessor))

plus, mult, expo :: PRFCode 2
plus = either (error . displayException) id (signatureKernelEnv examples >>= (`eraseFunction` addition))
mult = either (error . displayException) id (signatureKernelEnv examples >>= (`eraseFunction` multiplication))
expo = either (error . displayException) id (signatureKernelEnv examples >>= (`eraseFunction` exponentiation))
