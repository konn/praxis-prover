{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
The quasiquoter under test.  It lives in a module of its own because a
quasiquoter must be imported into the module which uses it.
-}
module Language.Praxis.PRA.QuoteSignature (pra, testSignature, muPra, arithWithMu) where

import Language.Haskell.TH.Quote (QuasiQuoter)
import Language.Praxis.PRA.PrimitiveRecursion (arithmetic)
import Language.Praxis.PRA.PrimitiveRecursion.Examples (mult, plus)
import Language.Praxis.PRA.Signature
import Language.Praxis.PRA.Tactic.Quote (praQuoter)

testSignature :: Signature
testSignature = signature [symbolNamed "plus" 'plus plus, symbolNamed "mult" 'mult mult]

pra :: QuasiQuoter
pra = praQuoter testSignature

arithWithMu :: Signature
arithWithMu = arithmetic

muPra :: QuasiQuoter
muPra = praQuoter arithWithMu
