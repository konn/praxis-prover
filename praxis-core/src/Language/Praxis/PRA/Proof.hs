{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -foptimal-applicative-do #-}

{- |
Proof trees for the quantifier-free fragment of G3i, and the checker which
infers what they prove.
-}
module Language.Praxis.PRA.Proof (
  -- * Proofs
  Proof (..),
  ProofF (..),

  -- * Steps, generically
  Arg (..),
  stepFields,
  mkStep,

  -- * Rules
  RuleName (..),
  HasRuleName (..),
  ruleSpec,

  -- * Checking
  inferConclusion,
  inferConclusionOpen,
  isProofOf,

  -- * Errors
  ProofError (..),
  ProofErrorReason (..),
  ProofContext (..),
) where

import Control.Monad.Free (Free, iter)
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

{- |
Infer the sequent an /open/ proof establishes.  The leaves of an open proof are
assumptions, each standing for the sequent the first argument assigns to it;
an error raised under a leaf is reported in the context of the premise it sits
in, as for a closed proof.  'inferConclusion' is the case with no leaves.
-}
inferConclusionOpen ::
  (Hashable a) =>
  -- | the sequent each leaf is assumed to establish
  (h -> Sequent a) ->
  Free (ProofF a) h ->
  Either (NonEmpty (ProofError a)) (Sequent a)
inferConclusionOpen leaf = runInferenceMachine . iter inferStep . fmap (pure . leaf)

-- TODO: more efficient and direct implementation.
isProofOf :: (Hashable a) => Proof a -> Sequent a -> Bool
isProofOf prf p = inferConclusion prf == Right p
