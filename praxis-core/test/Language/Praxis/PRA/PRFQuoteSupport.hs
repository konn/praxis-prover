{-# LANGUAGE TemplateHaskellQuotes #-}

module Language.Praxis.PRA.PRFQuoteSupport (arithPRF, arithProof, rawPRF, rawLiftFixture, sharedLiftFixture) where

import Language.Haskell.TH.Quote (QuasiQuoter)
import Language.Praxis.PRA.PrimitiveRecursion (arithmetic)
import Language.Praxis.PRA.PrimitiveRecursion qualified as PR
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.PrimitiveRecursion.Quote (prfQuoter)
import Language.Praxis.PRA.Signature (signatureKernelEnv)
import Language.Praxis.PRA.Signature qualified as Sig
import Language.Praxis.PRA.Tactic.Quote (praQuoter)

arithPRF, arithProof :: QuasiQuoter
arithPRF = prfQuoter arithmetic
arithProof = praQuoter arithmetic

-- Exercise all signature-entry paths: a named bare code, an unnamed nullary
-- code, and an unnamed inline program whose arity must survive lifting.
rawPRF :: QuasiQuoter
rawPRF =
  prfQuoter $
    Sig.signature
      [ Sig.symbolNamed "rawPower" 'rawLiftFixture rawLiftFixture
      , Sig.symbol "rawZero" (PR.Zero :: PR.PRFCode 0)
      , Sig.functionSymbol "rawIdentity" (F.Inline (F.Base (PR.Proj 0 :: PR.PRFCode 1)))
      ]

-- Imported fixtures can be consumed by both typed and untyped TH splices.
rawLiftFixture :: PR.PRFCode 2
rawLiftFixture = either error id (signatureKernelEnv arithmetic >>= (`F.eraseFunction` PR.pow))

sharedLiftFixture :: F.Program 2
sharedLiftFixture = either error id $ do
  env <- signatureKernelEnv arithmetic
  case PR.pow of
    F.Defined ident -> F.lookupDefinition env ident
    _ -> Left "expected a quote-defined function"
