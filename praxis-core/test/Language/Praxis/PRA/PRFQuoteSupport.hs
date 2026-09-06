module Language.Praxis.PRA.PRFQuoteSupport (arithPRF, arithProof, rawLiftFixture, sharedLiftFixture) where

import Language.Haskell.TH.Quote (QuasiQuoter)
import Language.Praxis.PRA.PrimitiveRecursion (arithmetic)
import Language.Praxis.PRA.PrimitiveRecursion qualified as PR
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.PrimitiveRecursion.Quote (prfQuoter)
import Language.Praxis.PRA.Signature (signatureKernelEnv)
import Language.Praxis.PRA.Tactic.Quote (praQuoter)

arithPRF, arithProof :: QuasiQuoter
arithPRF = prfQuoter arithmetic
arithProof = praQuoter arithmetic

-- Imported fixtures can be consumed by both typed and untyped TH splices.
rawLiftFixture :: PR.PRFCode 2
rawLiftFixture = either error id (signatureKernelEnv arithmetic >>= (`F.eraseFunction` PR.pow))

sharedLiftFixture :: F.Program 2
sharedLiftFixture = either error id $ do
  env <- signatureKernelEnv arithmetic
  case PR.pow of
    F.Defined ident -> F.lookupDefinition env ident
    _ -> Left "expected a quote-defined function"
