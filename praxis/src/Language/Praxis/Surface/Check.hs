{-# LANGUAGE OverloadedStrings #-}

{- |
Checking a module of the surface language: the driver.

A module is parsed, its fixities collected, and its declarations elaborated
("Language.Praxis.Surface.Elab").  Then, in order, every data type is
encoded and every function compiled into definitions extending the core
signature, and every lemma generated for them, and every theorem, is handed
to the core as a declaration of its concrete syntax and certified by
'checkDecl' against the lemmas certified before it.  A declaration which
fails is reported and never becomes a lemma: what comes after it is checked
without it.

The core is the only judge.  The driver never builds a proof term of its
own; it reads the core's verdict on the text it generated, which it keeps,
so that what was certified can be inspected, and checked again, with the
tools of praxis-core.
-}
module Language.Praxis.Surface.Check (
  -- * Reports
  Severity (..),
  Report (..),
  Checked (..),

  -- * Checking
  checkSource,
  checkSourceWith,

  -- * The core state
  Core (..),
  initialCore,
  addDefinitions,
  certifyDecl,
) where

import Control.Exception (displayException)
import Control.Monad (foldM)
import Data.Bifunctor (first)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration (parseEquations)
import Language.Praxis.PRA.PrimitiveRecursion.Environment (CompiledEnv, compileDefinitions, environmentSignature, extendEnvironment)
import Language.Praxis.PRA.Signature (Signature)
import Language.Praxis.PRA.Tactic qualified as PRA
import Language.Praxis.PRA.Tactic.Parser (Decl (..), parseDeclsIn)
import Language.Praxis.PRA.Tactic.Quote (SchemaName, checkDecl, renderSchemaTacticError, schemaScope)
import Language.Praxis.Surface.Compile (Compiled (..), compileFunction)
import Language.Praxis.Surface.Elab
import Language.Praxis.Surface.Encode (Encoded (..), FieldPred, encodeData)
import Language.Praxis.Surface.Engine (Closure, EngineError (..), IndexSpec (..), Knowledge (..), Spec (..), SpecProof (..), Unfolding (..), indexSpec, indexSpecOf, proveClosure, proveSpec, proveTheorem)
import Language.Praxis.Surface.Env (DataInfo (..), Env, FunInfo (..), TheoremInfo (..), renderQualName)
import Language.Praxis.Surface.Fixity (Fixities, moduleFixities, renderFixityError)
import Language.Praxis.Surface.Lexer (renderSyntaxError, syntaxErrorPosition)
import Language.Praxis.Surface.Mangle (demangle)
import Language.Praxis.Surface.Parser (parseModule)
import Language.Praxis.Surface.Prelude (Prelude (..))
import Language.Praxis.Surface.Syntax.Raw (Span (..))

-- * Reports

data Severity = SevError | SevInfo
  deriving stock (Show, Eq)

-- | A finding about a module: where, how severe, and what.
data Report = Report
  { reportSpan :: !Span
  , reportSeverity :: !Severity
  , reportMessage :: !Text
  }
  deriving stock (Show, Eq)

{- |
The findings, the core text generated, in order, and the theorems certified,
by their surface names; and, once the module elaborated, what the engine and
the core know after it.
-}
data Checked = Checked
  { checkedReports :: ![Report]
  , checkedCore :: ![Text]
  , checkedTheorems :: ![Text]
  , checkedFinal :: !(Maybe (Knowledge, Core))
  }

-- * The core state

-- | What the core knows: the definitions, the environment to check against, the certified lemmas.
data Core = Core
  { coreCompiled :: !CompiledEnv
  , coreSignature :: !Signature
  , coreEnv :: !PRA.Env
  , coreLemmas :: !(Map String (PRA.Lemma SchemaName))
  , coreMembership :: !(Map Text (Text, [Int]))
  -- ^ the membership predicate of each data type encoded, by its qualified name, with the parameters it takes the predicates of
  , coreVariadic :: !(Set Text)
  -- ^ the membership predicates which are variadic templates, taking what a closure given as their parameter captures
  }

initialCore :: Prelude -> Core
initialCore p = Core (preludeCompiled p) (preludeSignature p) (preludeEnv p) (preludeLemmas p) Map.empty Set.empty

-- | Extend the core with definitions, as @prf@ equations.
addDefinitions :: [Text] -> Core -> Either String Core
addDefinitions eqns core = do
  eqs <- first displayException (parseEquations (T.unlines eqns))
  block <- first displayException (compileDefinitions (coreCompiled core) eqs)
  compiled <- first displayException (extendEnvironment (coreCompiled core) block)
  let sig = environmentSignature compiled
  env <- first displayException (PRA.signatureEnv sig)
  pure core {coreCompiled = compiled, coreSignature = sig, coreEnv = env}

-- | Certify a declaration, given as text, and add it as a lemma; the core's verdict, demangled, when it fails.
certifyDecl :: Text -> Core -> Either String Core
certifyDecl text core = do
  decls <- first displayException (parseDeclsIn (fmap (map snd . PRA.lemmaMetas) (coreLemmas core)) (schemaScope (coreSignature core)) (T.unpack text))
  foldM one core decls
  where
    one c d = case checkDecl (coreEnv c) (coreLemmas c) d of
      Right (_, lemma) -> Right c {coreLemmas = Map.insert (declName d) lemma (coreLemmas c)}
      Left err -> Left (renderSchemaTacticError (coreSignature c) err)

-- * Checking

-- | Check a module's source: every report, and what was generated.
checkSource :: Prelude -> FilePath -> Text -> Checked
checkSource = checkSourceWith (\_ _ -> [])

{- |
Check a module's source, proving of each function the specifications given
for it, after its closure lemma: each certified as its lemma @f.#name@, as a
theorem is, and a failure reported.
-}
checkSourceWith :: (Env -> FunDef -> [Spec]) -> Prelude -> FilePath -> Text -> Checked
checkSourceWith specsOf p file src = case parseModule file src of
  Left err ->
    let (l, c) = syntaxErrorPosition err
     in Checked [Report (Span (l, c) (l, c + 1)) SevError (T.pack (renderSyntaxError err))] [] [] Nothing
  Right m -> case moduleFixities m of
    Left ferr ->
      let (sp, msg) = renderFixityError ferr
       in Checked [Report sp SevError (T.pack msg)] [] [] Nothing
    Right fx ->
      let (env, items) = elabModule fx m
       in runItems specsOf fx env (initialCore p) items

data Run = Run
  { runCore :: !Core
  , runReports :: ![Report]
  , runText :: ![Text]
  , runCertified :: ![Text]
  , runMembers :: !(Map Text [(Int, FieldPred)])
  , runUnfoldings :: ![Unfolding]
  , runClosures :: !(Map Text Closure)
  , runIndexSpecs :: !(Map Text IndexSpec)
  }

runItems :: (Env -> FunDef -> [Spec]) -> Fixities -> Env -> Core -> [Item] -> Checked
runItems specsOf fx env core0 items = finish (foldl step (Run core0 [] [] [] Map.empty [] Map.empty Map.empty) items)
  where
    finish r = Checked (reverse (runReports r)) (reverse (runText r)) (reverse (runCertified r)) (Just (knowledge r, runCore r))
    report sp sev msg r = r {runReports = Report sp sev (demangle (T.pack msg)) : runReports r}
    emit t r = r {runText = t : runText r}

    step r = \case
      IFailed (ElabError sp msg) -> report sp SevError msg r
      IData info sp ->
        let Encoded eqns lemmas members params variadic = encodeData (`Map.lookup` coreMembership (runCore r)) (`Set.member` coreVariadic (runCore r)) info
            r1 = foldl (flip emit) r eqns
         in case addDefinitions eqns (runCore r1) of
              Left err -> report sp SevError ("the encoding of " <> T.unpack (renderQualName (dataQual info)) <> " was rejected: " <> err) r1
              Right core' ->
                let core'' =
                      core'
                        { coreMembership = Map.insert (renderQualName (dataQual info)) (dataIs info, params) (coreMembership core')
                        , coreVariadic = (if variadic then Set.insert (dataIs info) else id) (coreVariadic core')
                        }
                 in certifyAll sp (r1 {runCore = core'', runMembers = Map.union (Map.fromList members) (runMembers r1)}) lemmas
      IFun fd -> case compileFunction env fd of
        Left err -> report (fdSpan fd) SevError (T.unpack (renderQualName (funQual (fdInfo fd))) <> ": " <> err) r
        Right (Compiled eqns lemmas unfolds) ->
          let r1 = foldl (flip emit) r eqns
           in case addDefinitions eqns (runCore r1) of
                Left err -> report (fdSpan fd) SevError ("the definition of " <> T.unpack (renderQualName (funQual (fdInfo fd))) <> " was rejected: " <> err) r1
                Right core' ->
                  let r2 = certifyAll (fdSpan fd) (r1 {runCore = core'}) lemmas
                      certified = [Unfolding n l rhs | (n, l, rhs) <- unfolds, Map.member (T.unpack n) (coreLemmas (runCore r2))]
                   in specify fd (indexed fd (closure fd (r2 {runUnfoldings = runUnfoldings r2 <> certified})))
      ITheorem td ->
        let name = T.unpack (renderQualName (thmQual (tdInfo td)))
         in case proveTheorem (knowledge r) td of
              Left (EngineError sp msg) -> report sp SevError msg r
              Right decls -> certifyTheorem (tdSpan td) name r decls

    knowledge r = Knowledge env fx (coreMembership (runCore r)) (runMembers r) (runUnfoldings r) (runClosures r) (coreVariadic (runCore r)) (runIndexSpecs r)

    -- The closure lemma of a function, when its result is of a data type and it can be proved: a failure is a bug of the generator.
    closure fd r = case proveClosure (knowledge r) fd of
      Left (EngineError sp msg) -> report sp SevError ("internal: the closure of " <> T.unpack (renderQualName (funQual (fdInfo fd))) <> ": " <> msg) r
      Right Nothing
        | not (null (fdImpossible fd)) -> report (fdSpan fd) SevError (T.unpack (renderQualName (funQual (fdInfo fd))) <> ": the membership of its results, under the indices of its arguments, could not be proved") r
        | otherwise -> r
      Right (Just (cl, decls)) -> certifyClosure fd cl r decls
    certifyClosure fd cl r = \case
      [] -> r {runClosures = Map.insert (funCore (fdInfo fd)) cl (runClosures r)}
      (name, text) : rest ->
        let r1 = emit text r
         in case certifyDecl text (runCore r1) of
              Right core' -> certifyClosure fd cl (r1 {runCore = core'}) rest
              Left err -> report (fdSpan fd) SevError ("internal: the generated lemma " <> T.unpack name <> " did not certify: " <> err) r1

    -- The indices a function over indexed types gives its result, certified as its lemma f.#index: a failure refuses it.
    indexed fd r = case indexSpecOf (knowledge r) fd of
      Nothing -> r
      Just s
        | null (ixsPost s) -> r {runIndexSpecs = Map.insert (funCore (fdInfo fd)) s (runIndexSpecs r)}
        | otherwise ->
            let name = T.unpack (renderQualName (funQual (fdInfo fd)))
             in case proveSpec (knowledge r) fd (indexSpec s) of
                  Left (EngineError sp msg) -> report sp SevError (name <> ": " <> msg) r
                  Right (Left why) -> report (fdSpan fd) SevError (name <> ": the indices of its result: " <> why) r
                  Right (Right proof) ->
                    let r' = certifyTheorem (fdSpan fd) (name <> ".#index") r (spDecls proof)
                     in if Map.member (T.unpack (ixsLemma s)) (coreLemmas (runCore r')) then r' {runIndexSpecs = Map.insert (funCore (fdInfo fd)) s (runIndexSpecs r')} else r'

    -- The specifications asked of a function, each proved and certified as a theorem is; a failure is reported.
    specify fd r0 = foldl (specified fd) r0 (specsOf env fd)
    specified fd r s =
      let name = T.unpack (renderQualName (funQual (fdInfo fd))) <> "." <> T.unpack (specName s)
       in case proveSpec (knowledge r) fd s of
            Left (EngineError sp msg) -> report sp SevError (name <> ": " <> msg) r
            Right (Left why) -> report (fdSpan fd) SevError (name <> ": " <> why) r
            Right (Right proof) -> certifyTheorem (fdSpan fd) name r (spDecls proof)

    -- A theorem's declarations, the auxiliary ones first; the first failure is the theorem's.
    certifyTheorem sp name r = \case
      [] -> r {runCertified = T.pack name : runCertified r}
      (_, text) : rest ->
        let r1 = emit text r
         in case certifyDecl text (runCore r1) of
              Right core' -> certifyTheorem sp name (r1 {runCore = core'}) rest
              Left err -> report sp SevError (name <> ": " <> err) r1

    -- Generated lemmas: a failure is a bug of the generator, reported where the declaration is.
    certifyAll sp r lemmas = foldl (certifyOne sp) r lemmas
    certifyOne sp r (name, text) =
      let r1 = emit text r
       in case certifyDecl text (runCore r1) of
            Right core' -> r1 {runCore = core'}
            Left err -> report sp SevError ("internal: the generated lemma " <> T.unpack name <> " did not certify: " <> err) r1
