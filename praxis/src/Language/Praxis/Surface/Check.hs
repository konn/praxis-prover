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

The modules of a package are checked in the order of their imports, each
against a 'Build': the core after the modules before it, whose definitions
and lemmas it extends, the tables of their globals, and what the engine
knows of their functions.  A module reaches the globals of another only
through its imports; the core, which judges, sees every lemma certified
before, which is sound, a lemma being a lemma.

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
  checkModule,
  headerName,

  -- * The build
  Build (..),
  initialBuild,

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
import Data.Maybe (fromMaybe)
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
import Language.Praxis.Surface.Engine (Closure, EngineError (..), Goal (..), Hyp (..), IndexSpec (..), Knowledge (..), Spec (..), SpecProof (..), Unfolding (..), asEquation, indexSpec, indexSpecOf, proveClosure, proveSpec, proveTheorem, statementGoal)
import Language.Praxis.Surface.Env (DataInfo (..), Env, FunInfo (..), QualName, TheoremInfo (..), displayQualName, emptyEnv, indexFunctionCores, renderQualName)
import Language.Praxis.Surface.Fixity (Fixities, moduleFixitiesWith, renderFixityError)
import Language.Praxis.Surface.Lexer (renderSyntaxError, syntaxErrorPosition)
import Language.Praxis.Surface.Mangle (demangle)
import Language.Praxis.Surface.Parser (parseModule)
import Language.Praxis.Surface.Prelude (Prelude (..), preludeUnfoldings)
import Language.Praxis.Surface.Rename (Imports, ModuleExports (..), Renamed, ScopeError (..), moduleExports, renameModule)
import Language.Praxis.Surface.Syntax (Expr (..), RelOp (..), stripLocations)
import Language.Praxis.Surface.Syntax.Raw (Located (..), QName (..), Segment (..), Span (..))
import Language.Praxis.Surface.Syntax.Raw qualified as R

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
by their surface names; once the module elaborated, what the engine and
the core know after it; and, once it parsed and its fixities resolved, the
module as the renamer left it, every global by its canonical name, for the
tools which follow names to their declarations.
-}
data Checked = Checked
  { checkedReports :: ![Report]
  , checkedCore :: ![Text]
  , checkedTheorems :: ![Text]
  , checkedFinal :: !(Maybe (Knowledge, Core))
  , checkedRenamed :: !(Maybe Renamed)
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

-- * The build

{- |
What a build threads through the modules it checks, in order: the core, the
tables of the environment the modules before filled — their globals,
namespaces, instances and display names — what the engine knows of their
functions and data types, and what each exports.  A module checked on its
own starts from 'initialBuild'.
-}
data Build = Build
  { buildCore :: !Core
  , buildEnv :: !Env
  , buildMembers :: !(Map Text [(Int, FieldPred)])
  , buildIndexEqs :: !(Map Text [(CT, CT)])
  -- ^ the equations of indices the branch of each constructor checks, by its core name, then its preconditions
  , buildProps :: !(Map Text [(CT, CT)])
  -- ^ the preconditions of each constructor, the last of its equations, by its core name
  , buildUnfoldings :: ![Unfolding]
  , buildClosures :: !(Map Text Closure)
  , buildIndexSpecs :: !(Map Text IndexSpec)
  , buildExports :: !(Map QualName ModuleExports)
  -- ^ what each module checked exports, by its name, its library first
  }

-- | A build before any module: the prelude, whose definitions and the core's builtins unfold as a module's own functions do.
initialBuild :: Prelude -> Build
initialBuild p = Build (initialCore p) emptyEnv Map.empty Map.empty Map.empty [Unfolding n l r | (n, l, r) <- preludeUnfoldings p] Map.empty Map.empty Map.empty

-- * Checking

-- | Check a module's source on its own: every report, and what was generated.
checkSource :: Prelude -> FilePath -> Text -> Checked
checkSource = checkSourceWith (\_ _ -> [])

{- |
Check a module's source on its own, proving of each function the
specifications given for it, after its closure lemma: each certified as its
lemma @f.#name@, as a theorem is, and a failure reported.
-}
checkSourceWith :: (Env -> FunDef -> [Spec]) -> Prelude -> FilePath -> Text -> Checked
checkSourceWith specsOf p file src = fst (checkModule specsOf (initialBuild p) Map.empty Nothing file src)

-- | The name a file's header gives its module, or @Main@ when it has none.
headerName :: R.Module -> QualName
headerName m = case R.moduleName m of
  Just (Located _ (QName qs b)) -> qs <> [b]
  Nothing -> [Ident "Main"]

{- |
Check a module's source in a build: given the imports the build resolved
for it, each by the library and the name written, and the module's name,
its library first, or none, for a file on its own, named by its header.
The reports and what was generated; and the build after the module, which
records what it exports when it elaborated.
-}
checkModule :: (Env -> FunDef -> [Spec]) -> Build -> Imports -> Maybe QualName -> FilePath -> Text -> (Checked, Build)
checkModule specsOf build imports name file src = case parseModule file src of
  Left err ->
    let (l, c) = syntaxErrorPosition err
     in (Checked [Report (Span (l, c) (l, c + 1)) SevError (T.pack (renderSyntaxError err))] [] [] Nothing Nothing, build)
  Right m ->
    let modQ = fromMaybe (headerName m) name
        imported = Map.unions [meFixities e | Right e <- Map.elems imports]
     in case moduleFixitiesWith imported m of
          Left ferr ->
            let (sp, msg) = renderFixityError ferr
             in (Checked [Report sp SevError (T.pack msg)] [] [] Nothing Nothing, build)
          Right fx ->
            let (renamed, scopeErrors) = renameModule fx (buildEnv build) imports modQ m
                (env, items) = elabModule fx (buildEnv build) renamed
                (checked, build') = runItems specsOf fx env build (moduleExports fx renamed) [Report sp SevError (T.pack msg) | ScopeError sp msg <- scopeErrors] items
             in (checked {checkedRenamed = Just renamed}, build')

data Run = Run
  { runCore :: !Core
  , runReports :: ![Report]
  , runText :: ![Text]
  , runCertified :: ![Text]
  , runMembers :: !(Map Text [(Int, FieldPred)])
  , runIndexEqs :: !(Map Text [(CT, CT)])
  -- ^ the equations of indices the branch of each constructor checks, by its core name, then its preconditions
  , runProps :: !(Map Text [(CT, CT)])
  -- ^ the preconditions of each constructor, the last of its equations, by its core name
  , runUnfoldings :: ![Unfolding]
  , runClosures :: !(Map Text Closure)
  , runIndexSpecs :: !(Map Text IndexSpec)
  , runObligations :: ![(Text, [Text], CT, CT, [(CT, CT)])]
  -- ^ the certified obligations of the function whose lemmas are being proved
  }

runItems :: (Env -> FunDef -> [Spec]) -> Fixities -> Env -> Build -> ModuleExports -> [Report] -> [Item] -> (Checked, Build)
runItems specsOf fx env build0 exports reports0 items = finish (foldl step start items)
  where
    start =
      Run
        { runCore = buildCore build0
        , runReports = reverse reports0
        , runText = []
        , runCertified = []
        , runMembers = buildMembers build0
        , runIndexEqs = buildIndexEqs build0
        , runProps = buildProps build0
        , runUnfoldings = buildUnfoldings build0
        , runClosures = buildClosures build0
        , runIndexSpecs = buildIndexSpecs build0
        , runObligations = []
        }
    finish r =
      ( Checked (reverse (runReports r)) (reverse (runText r)) (reverse (runCertified r)) (Just (knowledge r, runCore r)) Nothing
      , Build
          { buildCore = runCore r
          , buildEnv = env
          , buildMembers = runMembers r
          , buildIndexEqs = runIndexEqs r
          , buildProps = runProps r
          , buildUnfoldings = runUnfoldings r
          , buildClosures = runClosures r
          , buildIndexSpecs = runIndexSpecs r
          , buildExports = Map.insert (meName exports) exports (buildExports build0)
          }
      )
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
          rejected (r', err) = report sp SevError ("the encoding of " <> T.unpack (displayQualName (dataQual info)) <> " was rejected: " <> err) r'
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
                              , runProps = Map.union (Map.fromList (encodedProps enc)) (runProps r4)
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

    funName fd = T.unpack (displayQualName (funQual (fdInfo fd)))

    -- The obligations of a function certified: each lemma's name, its variables, the equation it concludes, and its hypotheses, the clause's preconditions, as equations.
    obligationFacts r fd =
      [ (thmCore (tdInfo td), thmBinders (tdInfo td), l, rhs, hyps)
      | td <- fdObligations fd
      , Map.member (T.unpack (thmCore (tdInfo td))) (coreLemmas (runCore r))
      , Right gl <- [statementGoal (coreMembership (runCore r)) td]
      , Rel RelEq a b <- [stripLocations (asEquation (goalConcl gl))]
      , Right l <- [termCT CVar a]
      , Right rhs <- [termCT CVar b]
      , let hyps = [(hl, hr) | (_, HProp p) <- goalHyps gl, Rel RelEq a' b' <- [stripLocations (asEquation p)], Right hl <- [termCT CVar a'], Right hr <- [termCT CVar b']]
      ]

    -- A theorem, or the obligation a proof in a function's clause is: proved, and certified.
    proveAndCertify r td =
      let name = T.unpack (displayQualName (thmQual (tdInfo td)))
       in case proveTheorem (knowledge r) td of
            Left (EngineError sp msg) -> report sp SevError msg r
            Right decls -> certifyTheorem (tdSpan td) name r decls

    -- The lemmas of the library a proof may cite by name: those certified, but the modules' own, which are mangled.
    knowledge r = Knowledge env fx (coreMembership (runCore r)) (runMembers r) (runIndexEqs r) (runProps r) (runUnfoldings r) (runClosures r) (coreVariadic (runCore r)) (runIndexSpecs r) (runObligations r) (Set.fromList [T.pack n | n <- Map.keys (coreLemmas (runCore r)), take 2 n /= "u_"])

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
