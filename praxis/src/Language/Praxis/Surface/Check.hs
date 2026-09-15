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
without it.  A data type in the GADT style has its index functions defined
between the codes of its constructors and its membership predicate, which
checks the indices of its constructors' entries by them.

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
import Language.Praxis.Surface.CoreText (CT (..), termCT)
import Language.Praxis.Surface.Elab
import Language.Praxis.Surface.Encode (Encoded (..), FieldPred, encodeData)
import Language.Praxis.Surface.Engine (Closure, EngineError (..), Goal (..), IndexSpec (..), Knowledge (..), Spec (..), SpecProof (..), Unfolding (..), asEquation, indexSpec, indexSpecOf, proveClosure, proveSpec, proveTheorem, statementGoal)
import Language.Praxis.Surface.Env (DataInfo (..), Env, FunInfo (..), TheoremInfo (..), indexFunctionCores, renderQualName)
import Language.Praxis.Surface.Fixity (Fixities, moduleFixities, renderFixityError)
import Language.Praxis.Surface.Lexer (renderSyntaxError, syntaxErrorPosition)
import Language.Praxis.Surface.Mangle (demangle)
import Language.Praxis.Surface.Parser (parseModule)
import Language.Praxis.Surface.Prelude (Prelude (..), preludeUnfoldings)
import Language.Praxis.Surface.Syntax (Expr (..), RelOp (..), stripLocations)
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
       in -- The definitions of the prelude and of the core's builtins unfold as a module's own functions do.
          runItems specsOf fx env (initialCore p) [Unfolding n l r | (n, l, r) <- preludeUnfoldings p] items

data Run = Run
  { runCore :: !Core
  , runReports :: ![Report]
  , runText :: ![Text]
  , runCertified :: ![Text]
  , runMembers :: !(Map Text [(Int, FieldPred)])
  , runIndexEqs :: !(Map Text [(CT, CT)])
  -- ^ the equations of indices the branch of each constructor checks, by its core name
  , runUnfoldings :: ![Unfolding]
  , runClosures :: !(Map Text Closure)
  , runIndexSpecs :: !(Map Text IndexSpec)
  , runObligations :: ![(Text, [Text], CT, CT)]
  -- ^ the certified obligations of the function whose lemmas are being proved
  }

runItems :: (Env -> FunDef -> [Spec]) -> Fixities -> Env -> Core -> [Unfolding] -> [Item] -> Checked
runItems specsOf fx env core0 unfoldings0 items = finish (foldl step start items)
  where
    start =
      Run
        { runCore = core0
        , runReports = []
        , runText = []
        , runCertified = []
        , runMembers = Map.empty
        , runIndexEqs = Map.empty
        , runUnfoldings = unfoldings0
        , runClosures = Map.empty
        , runIndexSpecs = Map.empty
        , runObligations = []
        }
    finish r = Checked (reverse (runReports r)) (reverse (runText r)) (reverse (runCertified r)) (Just (knowledge r, runCore r))
    report sp sev msg r = r {runReports = Report sp sev (demangle (T.pack msg)) : runReports r}
    emit t r = r {runText = t : runText r}

    step r = \case
      IFailed (ElabError sp msg) -> report sp SevError msg r
      IData info sp fns -> encode info sp fns r
      IFun fd -> either id (finishFunction fd) (defineFunction fd r)
      ITheorem td -> proveAndCertify r td

    {- A data type: the codes of its constructors; its index functions, by
    which its membership predicate checks the indices of its constructors'
    entries; the predicate; and then what the index functions' own lemmas
    need of the predicate. -}
    encode info sp fns r =
      let self = renderQualName (dataQual info)
          encoded = coreMembership (runCore r)
          -- The index functions of the data types encoded before, and of this one, defined before its predicate.
          indexFns dn = if dn == self || Map.member dn encoded then indexFunctionCores env dn else Nothing
          enc = encodeData (`Map.lookup` encoded) (`Set.member` coreVariadic (runCore r)) indexFns info
          rejected (r', err) = report sp SevError ("the encoding of " <> T.unpack self <> " was rejected: " <> err) r'
       in case define (encodedCodes enc) r of
            Left failure -> rejected failure
            Right r1 ->
              let r2 = certifyAll sp r1 (encodedCodeLemmas enc)
                  (r3, defined) = foldl (\(acc, done) fd -> either (,done) (,done <> [fd]) (defineFunction fd acc)) (r2, []) fns
               in case define (encodedPredicate enc) r3 of
                    Left failure -> rejected failure
                    Right r4 ->
                      let core = runCore r4
                          core' =
                            core
                              { coreMembership = Map.insert self (dataIs info, encodedParams enc) (coreMembership core)
                              , coreVariadic = (if encodedVariadic enc then Set.insert (dataIs info) else id) (coreVariadic core)
                              }
                          r5 =
                            r4
                              { runCore = core'
                              , runMembers = Map.union (Map.fromList (encodedMembers enc)) (runMembers r4)
                              , runIndexEqs = Map.union (Map.fromList (encodedIndexEquations enc)) (runIndexEqs r4)
                              }
                       in foldl (flip finishFunction) (certifyAll sp r5 (encodedLemmas enc)) defined

    -- Definitions extending the core, emitted first; when the core rejects them, what was emitted and why.
    define eqns r
      | null eqns = Right r
      | otherwise =
          let r1 = foldl (flip emit) r eqns
           in either (\err -> Left (r1, err)) (\core -> Right r1 {runCore = core}) (addDefinitions eqns (runCore r1))

    -- A function compiled and defined, its unfolding lemmas certified and its clauses' obligations proved; Left when refused, reported.
    defineFunction fd r = case compileFunction env fd of
      Left err -> Left (report (fdSpan fd) SevError (funName fd <> ": " <> err) r)
      Right (Compiled eqns lemmas unfolds) -> case define eqns r of
        Left (r1, err) -> Left (report (fdSpan fd) SevError ("the definition of " <> funName fd <> " was rejected: " <> err) r1)
        Right r1 ->
          let r2 = certifyAll (fdSpan fd) r1 lemmas
              certified = [Unfolding n l rhs | (n, l, rhs) <- unfolds, Map.member (T.unpack n) (coreLemmas (runCore r2))]
           in -- Then what the proofs its clauses give must prove.
              Right (foldl proveAndCertify (r2 {runUnfoldings = runUnfoldings r2 <> certified}) (fdObligations fd))

    -- A function's lemmas about its results: its closure, their indices, and the specifications asked of it.
    finishFunction fd r = (specify fd (indexed fd (closure fd (r {runObligations = obligationFacts r fd})))) {runObligations = []}

    funName fd = T.unpack (renderQualName (funQual (fdInfo fd)))

    -- The obligations of a function certified: each lemma's name, its variables, and the equation it concludes.
    obligationFacts r fd =
      [ (thmCore (tdInfo td), thmBinders (tdInfo td), l, rhs)
      | td <- fdObligations fd
      , Map.member (T.unpack (thmCore (tdInfo td))) (coreLemmas (runCore r))
      , Right gl <- [statementGoal (coreMembership (runCore r)) td]
      , Rel RelEq a b <- [stripLocations (asEquation (goalConcl gl))]
      , Right l <- [termCT CVar a]
      , Right rhs <- [termCT CVar b]
      ]

    -- A theorem, or the obligation a proof in a function's clause is: proved, and certified.
    proveAndCertify r td =
      let name = T.unpack (renderQualName (thmQual (tdInfo td)))
       in case proveTheorem (knowledge r) td of
            Left (EngineError sp msg) -> report sp SevError msg r
            Right decls -> certifyTheorem (tdSpan td) name r decls

    -- The lemmas of the library a proof may cite by name: those certified, but the module's own, which are mangled.
    knowledge r = Knowledge env fx (coreMembership (runCore r)) (runMembers r) (runIndexEqs r) (runUnfoldings r) (runClosures r) (coreVariadic (runCore r)) (runIndexSpecs r) (runObligations r) (Set.fromList [T.pack n | n <- Map.keys (coreLemmas (runCore r)), take 2 n /= "u_"])

    -- The closure lemma of a function, when its result is of a data type and it can be proved: a failure is a bug of the generator.
    closure fd r = case proveClosure (knowledge r) fd of
      Left (EngineError sp msg) -> report sp SevError ("internal: the closure of " <> funName fd <> ": " <> msg) r
      Right Nothing
        | not (null (fdImpossible fd)) -> report (fdSpan fd) SevError (funName fd <> ": the membership of its results, under the indices of its arguments, could not be proved") r
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
            let name = funName fd
             in case proveSpec (knowledge r) fd (indexSpec s) of
                  Left (EngineError sp msg) -> report sp SevError (name <> ": " <> msg) r
                  Right (Left why) -> report (fdSpan fd) SevError (name <> ": the indices of its result: " <> why) r
                  Right (Right proof) ->
                    let r' = certifyTheorem (fdSpan fd) (name <> ".#index") r (spDecls proof)
                     in if Map.member (T.unpack (ixsLemma s)) (coreLemmas (runCore r')) then r' {runIndexSpecs = Map.insert (funCore (fdInfo fd)) s (runIndexSpecs r')} else r'

    -- The specifications asked of a function, each proved and certified as a theorem is; a failure is reported.
    specify fd r0 = foldl (specified fd) r0 (specsOf env fd)
    specified fd r s =
      let name = funName fd <> "." <> T.unpack (specName s)
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
