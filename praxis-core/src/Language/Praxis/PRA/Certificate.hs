{- | Checked declarations with their derivations and lexical dependencies.
Statements alone are useful to an editor, but are not certificates.
-}
module Language.Praxis.PRA.Certificate (
  Certificate,
  certificateLemma,
  checkCertificate,
  derivationAppeals,
  primitiveCertificate,
  unfoldingCertificates,
  replayCertificate,
) where

import Control.Exception (displayException)
import Control.Monad (unless)
import Control.Monad.Free (Free (..))
import Data.Bifunctor (first)
import Data.Foldable (toList)
import Data.Functor.Foldable (cata, embed)
import Data.HashSet qualified as HS
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Multiset qualified as MS
import Data.Set qualified as Set
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.Proof.Transform (argNames, identityProof, substProof, weakenProof)
import Language.Praxis.PRA.Rule qualified as R
import Language.Praxis.PRA.Signature (Signature)
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Tactic
import Language.Praxis.PRA.Tactic.Parser (Decl (..))
import Language.Praxis.PRA.Tactic.Quote (SchemaName (..), checkDecl, renderSchemaName, schemaScope)
import Language.Praxis.PRA.Tactic.Unfolding (renderUnfoldingError, unfoldingLemmas)

unfoldingCertificates :: Signature -> Either String (Map String Certificate)
unfoldingCertificates sig = do
  env <- first displayException (signatureEnv sig)
  lemmas <- first (renderUnfoldingError sig renderSchemaName) (unfoldingLemmas (schemaScope sig [] []))
  traverse (first show . primitiveCertificate env . (\c -> certifiedProof c [] [])) lemmas

-- The constructor is private. Dependencies are captured at declaration time,
-- so later shadowing cannot change the meaning of a checked derivation.
data Certificate = Certificate
  { storedLemma :: !(Lemma SchemaName)
  , certificateDerivation :: !(Free (Step SchemaName) String)
  , certificateDependencies :: !(Map String Certificate)
  }

{- | The statement established by the retained derivation. This is a read-only
accessor, not an exported record selector that permits record updates.
-}
certificateLemma :: Certificate -> Lemma SchemaName
certificateLemma = storedLemma

checkCertificate :: Env -> Map String Certificate -> Decl SchemaName -> Either (TacticError SchemaName) Certificate
checkCertificate env known decl = do
  (proof, lemma) <- checkDecl env (fmap certificateLemma known) decl
  let dependencies = derivationAppeals proof `Set.difference` Set.fromList (map fst (lemmaPremises lemma))
  pure (Certificate lemma proof (Map.restrictKeys known dependencies))

{- | The lemma names actually used by a derivation, after tactic alternatives
have been resolved. Declaration premises must be removed by the caller.
-}
derivationAppeals :: Free (Step a) h -> Set.Set String
derivationAppeals = \case
  Pure _ -> Set.empty
  Free (LemmaStep appeal subs) -> Set.insert (appealName appeal) (foldMap derivationAppeals subs)
  Free step -> foldMap derivationAppeals step

-- | Import a primitive proof only after the kernel has checked it.
primitiveCertificate :: Env -> Proof SchemaName -> Either (Failure SchemaName) Certificate
primitiveCertificate env proof = do
  conclusion <- first Rejected (inferConclusionIn (envKernel env) proof)
  pure (Certificate (Lemma [] [] conclusion [] []) (cata (Free . RuleStep) proof) Map.empty)

{- | Expand an instance to primitive inference rules and independently check
its conclusion. Supplied premises are checked too, including the fresh
variables of locally quantified premises. No lemma statement is a leaf of
the resulting proof.
-}
replayCertificate :: Env -> Certificate -> Appeal SchemaName -> [Proof SchemaName] -> Either (Failure SchemaName) (Proof SchemaName)
replayCertificate env certificate appeal premises = do
  (expectedPremises, expected) <- instantiateLemma sig (certificateLemma certificate) appeal
  unless (length expectedPremises == length premises) (Left (Malformed "incorrect number of certificate premises"))
  actualPremises <- traverse (first Rejected . inferConclusionIn kernel) premises
  sequence_ [unless (wanted == actual) (Left (WrongPremise (appealName appeal) wanted actual)) | (wanted, actual) <- zip expectedPremises actualPremises]
  proof <- expand certificate appeal premises
  actual <- first Rejected (inferConclusionIn kernel proof)
  unless (actual == expected) (Left (WrongConclusion actual))
  pure proof
  where
    sig = envSignature env
    kernel = envKernel env

    expand cert call supplied = do
      let lemma = certificateLemma cert
          stated = lemmaExternalNames lemma
          body = freshenSubstitutions stated (certificateDerivation cert)
          objects = HS.toList (HS.filter (\case Obj _ -> True; _ -> False) (derivationNames body))
          avoid = stated <> HS.unions (map argNames (appealArgs call) <> [argNames (ArgCtx (appealWeakening call))] <> [HS.fromList (x : toList t) | (x, t) <- appealSubst call])
          (_, renamed) = foldl (\(used, pairs) v -> let w = freshen used v in (HS.insert w used, (v, Var w) : pairs)) (avoid, []) objects
          -- Reserve placeholders before schematic substitution. Restore only
          -- free external occurrences afterwards with capture-avoiding proof
          -- substitution, protecting binders that share an external spelling.
          restore = [(w, fromMaybe (Var v) (lookup v (appealSubst call))) | (v, Var w) <- renamed, v `HS.member` stated]
          binding = call {appealSubst = renamed, appealWeakening = MS.empty}
          parameters = Map.fromList (zip (map fst (lemmaPremises lemma)) supplied)
          locals = Map.fromList (zip (map fst (lemmaPremises lemma)) (premiseRenamings lemma call))
          fields = instantiateArguments sig lemma binding
          context g =
            fields [ArgCtx g] >>= \case
              [ArgCtx g'] -> pure g'
              _ -> Left (Malformed "context instantiation changed its sort")
          go (Pure name) = maybe (Left (UnknownPremise name)) pure (Map.lookup name parameters)
          go (Free (WeakenStep extra sub)) = weakenProof <$> context extra <*> go sub
          go (Free (RuleStep step)) = do
            let (args, subs) = stepFields step
            -- Formula identity is admissible, rather than an atomic Id step.
            case (ruleName step, args) of
              (IdRule, [ArgAtom p, ArgCtx g])
                | Just (R.FormS, _) <- metaAtom p ->
                    fields [ArgForm (Atm p), ArgCtx g] >>= \case
                      [ArgForm f, ArgCtx g'] -> pure (identityProof g' f)
                      _ -> Left (Malformed "identity instantiation changed its sorts")
              _ -> do
                args' <- fields args
                subs' <- traverse go subs
                maybe (Left (Malformed "instantiated rule fields have incorrect sorts")) (pure . embed) (mkStep (ruleName step) args' subs')
          go (Free (LemmaStep nested subs)) = do
            args <- fields (appealArgs nested)
            pairs <-
              traverse
                ( \(x, t) ->
                    fields [ArgTerm t] >>= \case
                      [ArgTerm t'] -> pure (x, t')
                      _ -> Left (Malformed "term instantiation changed its sort")
                )
                (appealSubst nested)
            extra <- context (appealWeakening nested)
            proofs <- traverse go subs
            let name = appealName nested
            case Map.lookup name parameters of
              Just proof -> do
                unless (null args && null proofs) (Left (Malformed "a quantified premise has no schematic arguments"))
                localPairs <-
                  traverse
                    ( \(x, chosen) ->
                        fields [ArgTerm (fromMaybe (Var x) (lookup x (appealSubst nested)))] >>= \case
                          [ArgTerm t] -> pure (chosen, t)
                          _ -> Left (Malformed "local premise instantiation changed its sort")
                    )
                    (Map.findWithDefault [] name locals)
                pure (weakenProof extra (substProof localPairs proof))
              Nothing -> do
                dependency <- maybe (Left (UnknownPremise name)) pure (Map.lookup name (certificateDependencies cert))
                let instantiated = Appeal name args pairs extra
                    declaration = certificateLemma dependency
                    sourceLocals = premiseRenamings declaration nested
                    targetLocals = premiseRenamings declaration instantiated
                -- The child derivations used the local names chosen before
                -- instantiation. Their instantiated names need not be the
                -- canonical fresh names chosen for this new appeal. Abstract
                -- them and supply them at the latter, as export's premise
                -- proof functions do.
                aligned <-
                  sequence
                    [ do
                        renaming <-
                          sequence
                            [ fields [ArgVar source] >>= \case
                                [ArgVar actual] -> pure (actual, Var target)
                                _ -> Left (Malformed "a local premise name changed its sort")
                            | ((_, source), (_, target)) <- zip before after
                            ]
                        pure (substProof renaming proof)
                    | (proof, (before, after)) <- zip proofs (zip sourceLocals targetLocals)
                    ]
                expand dependency instantiated aligned
      weakenProof (appealWeakening call) . substProof restore <$> go body
