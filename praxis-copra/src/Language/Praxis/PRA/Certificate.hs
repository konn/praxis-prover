{- | Checked declarations with their derivations and lexical dependencies.
Statements alone are useful to an editor, but are not certificates.
-}
module Language.Praxis.PRA.Certificate (
  Certificate,
  certificateLemma,
  checkCertificate,
  CertificateStore,
  certificateStore,
  storedCertificates,
  storedLemmas,
  storedMetas,
  checkAndInsertCertificate,
  derivationAppeals,
  primitiveCertificate,
  unfoldingCertificates,
  replayCertificate,
) where

import Control.Exception (displayException)
import Control.Monad (unless)
import Control.Monad.Free (Free (..))
import Control.Monad.Trans.State.Strict (State, gets, modify', runState)
import Data.Bifunctor (first)
import Data.Foldable (toList)
import Data.Functor.Foldable (cata, embed)
import Data.HashMap.Strict qualified as HM
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

{- | An immutable collection of certificates and their derived lookup tables.
The constructor is private: statements cannot be added without certificates.
-}
data CertificateStore
  = CertificateStore
      !(Map String Certificate)
      !(Map String (Lemma SchemaName))
      !(Map String [R.Sort])
      !TermPool

-- | Build the lookup tables once from already checked certificates.
certificateStore :: Map String Certificate -> CertificateStore
certificateStore known =
  let lemmas = fmap certificateLemma known
   in CertificateStore known lemmas (fmap (map snd . lemmaMetas) lemmas) (TermPool HM.empty HM.empty)

storedCertificates :: CertificateStore -> Map String Certificate
storedCertificates (CertificateStore known _ _ _) = known

storedLemmas :: CertificateStore -> Map String (Lemma SchemaName)
storedLemmas (CertificateStore _ lemmas _ _) = lemmas

storedMetas :: CertificateStore -> Map String [R.Sort]
storedMetas (CertificateStore _ _ metas _) = metas

{- | Check and insert one declaration, updating the derived tables incrementally.
Lexical dependencies still refer to the certificates present before insertion.
-}
checkAndInsertCertificate :: Env -> CertificateStore -> Decl SchemaName -> Either (TacticError SchemaName) (Certificate, CertificateStore)
checkAndInsertCertificate env (CertificateStore known lemmas metas pool) decl = do
  checked <- checkWith env known lemmas decl
  let ((certificate, name), pool') = runState ((,) <$> shareCertificate checked <*> shareName (declName decl)) pool
      lemma = certificateLemma certificate
  pure (certificate, CertificateStore (Map.insert name certificate known) (Map.insert name lemma lemmas) (Map.insert name (map snd (lemmaMetas lemma)) metas) pool')

{- | Check against a certificate map. Incremental clients should use
'checkAndInsertCertificate' to avoid rebuilding lookup tables at each step.
-}
checkCertificate :: Env -> Map String Certificate -> Decl SchemaName -> Either (TacticError SchemaName) Certificate
checkCertificate env known = checkWith env known (fmap certificateLemma known)

checkWith :: Env -> Map String Certificate -> Map String (Lemma SchemaName) -> Decl SchemaName -> Either (TacticError SchemaName) Certificate
checkWith env known lemmas decl = do
  (proof, lemma) <- checkDecl env lemmas decl
  let dependencies = derivationAppeals proof `Set.difference` Set.fromList (map fst (lemmaPremises lemma))
  pure (Certificate lemma proof (Map.restrictKeys known dependencies))

-- Interning is structural only: the pool compares complete terms, including
-- variable names, and never evaluates or rewrites an expression. Keep the
-- entire derivation; share identical subterms across its fields and certificates.
data TermPool = TermPool
  { sharedTerms :: !(HM.HashMap (Term SchemaName) (Term SchemaName))
  , sharedNames :: !(HM.HashMap String String)
  }

shareName :: String -> State TermPool String
shareName name = do
  names <- gets sharedNames
  case HM.lookup name names of
    Just shared -> pure shared
    Nothing -> do
      modify' (\pool -> pool {sharedNames = HM.insert name name names})
      pure name

shareTerm :: Term SchemaName -> State TermPool (Term SchemaName)
shareTerm original = do
  pool <- gets sharedTerms
  case HM.lookup original pool of
    Just shared -> pure shared
    Nothing -> do
      shared <- case original of
        App function arguments -> App function <$> traverse shareTerm arguments
        _ -> pure original
      modify' (\pool' -> pool' {sharedTerms = HM.insert shared shared (sharedTerms pool')})
      pure shared

shareAtomic :: Atomic SchemaName -> State TermPool (Atomic SchemaName)
shareAtomic (left :=== right) = (:===) <$> shareTerm left <*> shareTerm right

shareFormula :: Formula SchemaName -> State TermPool (Formula SchemaName)
shareFormula = \case
  Atm atom -> Atm <$> shareAtomic atom
  left :/\ right -> (:/\) <$> shareFormula left <*> shareFormula right
  left :\/ right -> (:\/) <$> shareFormula left <*> shareFormula right
  left :==> right -> (:==>) <$> shareFormula left <*> shareFormula right
  Bot -> pure Bot

shareContext :: MS.Multiset (Formula SchemaName) -> State TermPool (MS.Multiset (Formula SchemaName))
shareContext context = foldr MS.insertOne MS.empty <$> traverse shareFormula (toList context)

shareSequent :: Sequent SchemaName -> State TermPool (Sequent SchemaName)
shareSequent (context :|- conclusion) = (:|-) <$> shareContext context <*> shareFormula conclusion

shareArgument :: Arg SchemaName -> State TermPool (Arg SchemaName)
shareArgument = \case
  argument@ArgVar {} -> pure argument
  ArgTerm value -> ArgTerm <$> shareTerm value
  ArgAtom value -> ArgAtom <$> shareAtomic value
  ArgForm value -> ArgForm <$> shareFormula value
  ArgCtx value -> ArgCtx <$> shareContext value
  ArgFun value -> do
    body <- shareTerm (abstractionBody value)
    captured <- traverse shareTerm (abstractionCaptured value)
    pure (ArgFun value {abstractionBody = body, abstractionCaptured = captured})

shareDerivation :: Free (Step SchemaName) String -> State TermPool (Free (Step SchemaName) String)
shareDerivation source = do
  shared <- shareStep source
  -- Free's field is lazy. Force the rebuilt step now: otherwise the mkStep
  -- fallback below can retain the entire original, unshared rule until replay.
  case shared of
    Pure _ -> pure shared
    Free step -> step `seq` pure shared

shareStep :: Free (Step SchemaName) String -> State TermPool (Free (Step SchemaName) String)
shareStep = \case
  Pure name -> Pure <$> shareName name
  Free (WeakenStep extra child) -> Free <$> (WeakenStep <$> shareContext extra <*> shareDerivation child)
  Free (LemmaStep appeal children) -> do
    name <- shareName (appealName appeal)
    args <- traverse shareArgument (appealArgs appeal)
    bindings <- traverse (\(variable, value) -> (variable,) <$> shareTerm value) (appealSubst appeal)
    extra <- shareContext (appealWeakening appeal)
    children' <- traverse shareDerivation children
    pure (Free (LemmaStep appeal {appealName = name, appealArgs = args, appealSubst = bindings, appealWeakening = extra} children'))
  Free (RuleStep original) -> do
    step <- traverse shareDerivation original
    let (args, children) = stepFields step
    args' <- traverse shareArgument args
    -- Sharing preserves every field's sort and all children. Retaining the
    -- original checked fields is a conservative fallback if reconstruction fails.
    pure (Free (RuleStep (fromMaybe step (mkStep (ruleName step) args' children))))

shareCertificate :: Certificate -> State TermPool Certificate
shareCertificate certificate = do
  let lemma = certificateLemma certificate
  conclusion <- shareSequent (lemmaGoal lemma)
  premises <- traverse (\(name, statement) -> (name,) <$> shareSequent statement) (lemmaPremises lemma)
  proof <- shareDerivation (certificateDerivation certificate)
  pure
    certificate
      { storedLemma = lemma {lemmaGoal = conclusion, lemmaPremises = premises}
      , certificateDerivation = proof
      }

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
