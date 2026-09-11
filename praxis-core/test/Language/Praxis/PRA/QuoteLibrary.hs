{- |
A quasiquoter over the library "Language.Praxis.PRA.QuoteTest" declares.  It
lives in a module of its own because a quasiquoter must be imported into the
module which uses it.
-}
module Language.Praxis.PRA.QuoteLibrary (libraryPra) where

import Language.Haskell.TH.Quote (QuasiQuoter)
import Language.Praxis.PRA.QuoteTest (testLemmas)
import Language.Praxis.PRA.Tactic.Quote (praQuoterIn)

libraryPra :: QuasiQuoter
libraryPra = praQuoterIn testLemmas
