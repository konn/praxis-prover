{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
A quasiquoter over a signature of the tests' own, besides the default @pra@
over the builtin signature.  It lives in a module of its own because a
quasiquoter must be imported into the module which uses it.
-}
module Language.Praxis.PRA.QuoteSignature (testPra, testSignature) where

import Language.Haskell.TH.Quote (QuasiQuoter)
import Language.Praxis.PRA.PrimitiveRecursion.Examples (mult, plus)
import Language.Praxis.PRA.Signature
import Language.Praxis.PRA.Tactic.Quote (praQuoter)

testSignature :: Signature
testSignature = signature [symbolNamed "plus" 'plus plus, symbolNamed "mult" 'mult mult]

testPra :: QuasiQuoter
testPra = praQuoter testSignature
