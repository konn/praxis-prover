{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -foptimal-applicative-do #-}

{- |
Proof trees for the quantifier-free fragment of G3i, and the checker which
infers what they prove.

Neither the datatype nor the checker is written out here.  Both are compiled
from "Language.Praxis.PRA.Rule.G3i" by "Language.Praxis.PRA.Rule.TH", so the
calculus has one source of truth; to see what this module actually declares,
build it with @-ddump-splices@.
-}
module Language.Praxis.PRA.Proof (
  -- * Proofs
  Proof (..),
  ProofF (..),

  -- * Rules
  RuleName (..),
  HasRuleName (..),
  ruleSpec,

  -- * Checking
  inferConclusion,
  isProofOf,

  -- * Errors
  ProofError (..),
  ProofErrorReason (..),
  ProofContext (..),
) where

import Data.Functor.Foldable (cata)
import Data.Hashable (Hashable)
import Data.List.NonEmpty (NonEmpty)
import Language.Praxis.PRA.Proof.Internal
import Language.Praxis.PRA.Rule.G3i (allRules)
import Language.Praxis.PRA.Rule.TH (deriveChecker, deriveProofSyntax)
import Language.Praxis.PRA.Syntax

$(deriveProofSyntax allRules)

$(deriveChecker allRules)

{- |
Infer the sequent a proof establishes, or report every reason it fails to
establish one.
-}
inferConclusion ::
  (Hashable a) =>
  Proof a ->
  Either (NonEmpty (ProofError a)) (Sequent a)
inferConclusion = runInferenceMachine . cata inferStep

-- TODO: more efficient and direct implementation.
isProofOf :: (Hashable a) => Proof a -> Sequent a -> Bool
isProofOf prf p = inferConclusion prf == Right p
