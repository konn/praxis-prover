{-# LANGUAGE TemplateHaskellQuotes #-}

module Language.Praxis.PRA.PRFQuoteSupport (builtinPRF, rawPRF, rawLiftFixture, sharedLiftFixture) where

import Control.Exception (displayException)
import Language.Haskell.TH.Quote (QuasiQuoter)
import Language.Praxis.PRA.PrimitiveRecursion (builtin)
import Language.Praxis.PRA.PrimitiveRecursion qualified as PR
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.PrimitiveRecursion.Quote (prfQuoter)
import Language.Praxis.PRA.Signature (signatureKernelEnv)
import Language.Praxis.PRA.Signature qualified as Sig

-- | Equations extending the builtin signature.
builtinPRF :: QuasiQuoter
builtinPRF = prfQuoter builtin

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
rawLiftFixture = either (error . displayException) id (signatureKernelEnv builtin >>= (`F.eraseFunction` PR.pow))

sharedLiftFixture :: F.Program 2
sharedLiftFixture = either (error . displayException) id $ do
  env <- signatureKernelEnv builtin
  case PR.pow of
    F.Defined ident -> F.lookupDefinition env ident
    _ -> error "expected a quote-defined function"
