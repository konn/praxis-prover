{-# LANGUAGE DataKinds #-}

{- |
A language server for the files of praxis: @.px@ modules of the surface
language, @.pra@ files of theorems and rules, as
'Language.Praxis.PRA.Tactic.Quote.praFile' splices them, and @.prf@ files of
definitions, as 'Language.Praxis.PRA.PrimitiveRecursion.Quote.prfFile' does.

A @.px@ document is checked by the driver of the praxis package as a module
of the package enclosing it, its imports resolved and the modules it imports
checked before it, or on its own; every report is a diagnostic where the
driver places it.  What the driver learns of the names of the module —
"Language.Praxis.LSP.Surface" — gives each name a semantic token, a data
type, a constructor, a function, a theorem, a class, a method, a module, a
variable or a keyword of the tactic language, and a definition to go to,
in the document or in a module it imports.

A @.pra@ document is read over the 'builtin' signature, with the lemmas of the
library of praxis-copra, "Language.Praxis.PRA.Library", and the unfolding
lemmas of 'builtin' in scope and each declaration a lemma for those after it,
as the quasiquoter reads it with those lemmas in scope; every declaration is checked, and a failure is a
diagnostic at the tactic which failed, a @sorry@
a warning listing the unfinished goal. Draft statements remain available for
editing, with their unproved dependencies propagated to users and hovers.  Hovering over a
tactic shows the goal it faces, found by running the proof with that tactic
replaced by @sorry@.  A @.prf@ document is checked as the quasiquoter checks
it, over the empty signature.  Both are indexed lexically,
"Language.Praxis.LSP.Core": a theorem, a rule or a definition is a
definition to go to from the names appealing to it.
-}
module Language.Praxis.LSP (
  runPraxisServer,

  -- * Analysis
  Language (..),
  languageOf,
  Report (..),
  Document (..),
  analyse,
  analyseIn,
  analyseDocument,
  hoverAt,

  -- * Navigation
  definitionsAt,
  semanticTokensOf,
) where

import Control.Concurrent (ThreadId, forkIO, killThread, myThreadId, threadDelay)
import Control.Concurrent.MVar (MVar, modifyMVar_, newMVar)
import Control.Exception (IOException, SomeAsyncException, displayException, evaluate, fromException, mask_, throwIO, try)
import Control.Monad (filterM, forM_)
import Control.Monad.IO.Class (liftIO)
import Data.Char (isSpace)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust, listToMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Language.LSP.Diagnostics (DiagnosticsBySource, partitionBySource)
import Language.LSP.Protocol.Message
import Language.LSP.Protocol.Types
import Language.LSP.Server
import Language.LSP.VFS (VFS (..), virtualFileText, virtualFileVersion)
import Language.Praxis.LSP.Core (indexPra, indexPrf)
import Language.Praxis.LSP.Index (Index (..), Target (..), Token (..), referencesAt)
import Language.Praxis.LSP.Position (Lines, fromPosition, lineAt, linesOf, toPosition, toRange)
import Language.Praxis.LSP.Surface (indexModule, moduleDefinitions)
import Language.Praxis.PRA.Certificate (Certificate, certificateLemma, checkCertificate, derivationAppeals)
import Language.Praxis.PRA.Library (certifiedLibrary, libraryCertificates, libraryScope)
import Language.Praxis.PRA.PrimitiveRecursion (builtin)
import Language.Praxis.PRA.PrimitiveRecursion.Quote (checkErrorPosition, checkQuote, renderCheckError)
import Language.Praxis.PRA.Syntax.Parser (syntaxErrorPosition)
import Language.Praxis.PRA.Tactic
import Language.Praxis.PRA.Tactic.Parser
import Language.Praxis.PRA.Tactic.Quote (SchemaName, checkDecl, renderSchemaTacticError, schemaScope)
import Language.Praxis.Package.Build (ModuleResult (..), Prefix, checkFileCached, componentId, locate, prefixPaths, readFileUtf8)
import Language.Praxis.Surface.Check qualified as Surface
import Language.Praxis.Surface.Engine (Knowledge (..))
import Language.Praxis.Surface.Parser (parseModule)
import Language.Praxis.Surface.Prelude (Prelude, prelude, preludeLemmas)
import Language.Praxis.Surface.Syntax.Raw (Segment (..), Span (..))
import System.Directory (canonicalizePath)
import System.Exit (ExitCode (..))
import System.FilePath (takeExtension)

-- * The server

-- | What the server keeps of each document open: its text, and what was found in it.
data Entry = Entry
  { entryText :: !Text
  , entryDocument :: !Document
  }

{- |
The state of the server: what it found in each document open, which the
requests about the document are answered from; the check of each document
pending or running, which the next change of the document abandons; and
what the check of each document reuses from the one before it.
-}
data Server = Server
  { serverEntries :: !(IORef (Map NormalizedUri Entry))
  , serverChecks :: !(MVar (Map NormalizedUri ThreadId))
  , serverPrefixes :: !(IORef (Map NormalizedUri Prefix))
  }

-- | Serve over standard input and output, until the client says goodbye.
runPraxisServer :: IO ExitCode
runPraxisServer = do
  server <- Server <$> newIORef Map.empty <*> newMVar Map.empty <*> newIORef Map.empty
  code <- runServer (definition server)
  pure (if code == 0 then ExitSuccess else ExitFailure code)

definition :: Server -> ServerDefinition ()
definition server =
  ServerDefinition
    { defaultConfig = ()
    , configSection = "praxis"
    , parseConfig = \_ _ -> Right ()
    , onConfigChange = \_ -> pure ()
    , doInitialize = \env _ -> pure (Right env)
    , staticHandlers = \_ -> handlers server
    , interpretHandler = \env -> Iso (runLspT env) liftIO
    , options = defaultOptions {optTextDocumentSync = Just syncOptions}
    }
  where
    syncOptions =
      TextDocumentSyncOptions
        { _openClose = Just True
        , _change = Just TextDocumentSyncKind_Incremental
        , _willSave = Just False
        , _willSaveWaitUntil = Just False
        , _save = Just (InR (SaveOptions (Just False)))
        }

handlers :: Server -> Handlers (LspM ())
handlers server =
  mconcat
    [ notificationHandler SMethod_Initialized \_ -> pure ()
    , -- The library reads the configuration itself; these notifications need no answer.
      notificationHandler SMethod_WorkspaceDidChangeConfiguration \_ -> pure ()
    , notificationHandler SMethod_SetTrace \_ -> pure ()
    , notificationHandler SMethod_WorkspaceDidChangeWatchedFiles \_ -> pure ()
    , notificationHandler SMethod_TextDocumentDidOpen \msg -> schedule server 0 (toNormalizedUri msg._params._textDocument._uri)
    , notificationHandler SMethod_TextDocumentDidChange \msg -> schedule server changeDelay (toNormalizedUri msg._params._textDocument._uri)
    , -- A document saved is checked at once, and so are the other documents open which read it, or whose last check found an error the save may resolve.
      notificationHandler SMethod_TextDocumentDidSave \msg -> do
        let uri = toNormalizedUri msg._params._textDocument._uri
        schedule server 0 uri
        open <- Map.keys . _vfsMap <$> getVirtualFiles
        affected <- liftIO (dependents server uri (filter (/= uri) open))
        mapM_ (schedule server 0) affected
    , notificationHandler SMethod_TextDocumentDidClose \msg -> do
        let uri = toNormalizedUri msg._params._textDocument._uri
        liftIO do
          abandon server uri
          atomicModifyIORef' (serverEntries server) (\m -> (Map.delete uri m, ()))
          atomicModifyIORef' (serverPrefixes server) (\m -> (Map.delete uri m, ()))
        publishDiagnostics 100 uri Nothing (partitionBySource [])
    , requestHandler SMethod_TextDocumentHover \req responder -> do
        let uri = toNormalizedUri req._params._textDocument._uri
        file <- getVirtualFile uri
        let answer = do
              text <- virtualFileText <$> file
              Pra <- languageOf =<< uriToFilePath (fromNormalizedUri uri)
              let (line, column) = fromPosition (linesOf text) req._params._position
              body <- hoverAt text line column
              pure (Hover (InL (MarkupContent MarkupKind_Markdown ("```\n" <> body <> "\n```"))) Nothing)
        responder (Right (maybe (InR Null) InL answer))
    , requestHandler SMethod_TextDocumentSemanticTokensFull \req responder -> do
        let uri = toNormalizedUri req._params._textDocument._uri
        entry <- liftIO (Map.lookup uri <$> readIORef (serverEntries server))
        responder (Right (maybe (InR Null) (\e -> either (const (InR Null)) InL (semanticTokensOf (entryText e) (entryDocument e))) entry))
    , requestHandler SMethod_TextDocumentDefinition \req responder -> do
        let uri = toNormalizedUri req._params._textDocument._uri
            path = uriToFilePath (fromNormalizedUri uri)
        entry <- liftIO (Map.lookup uri <$> readIORef (serverEntries server))
        found <- case entry of
          Nothing -> pure []
          Just e -> mapM (locationOf uri path (entryText e)) (definitionsAt (entryText e) (entryDocument e) req._params._position)
        responder (Right (InL (Definition (InR found))))
    ]

-- | Where a target is, for the client: in the document itself, or in a file, read from the editor when it is open there, else from the disk.
locationOf :: NormalizedUri -> Maybe FilePath -> Text -> Target -> LspM () Location
locationOf uri path text (Target target sp)
  | Just target == path = pure (Location (fromNormalizedUri uri) (toRange (linesOf text) sp))
  | otherwise = do
      let targetUri = filePathToUri target
      open <- getVirtualFile (toNormalizedUri targetUri)
      ls <- case open of
        Just f -> pure (linesOf (virtualFileText f))
        Nothing -> liftIO do
          read' <- try (readFileUtf8 target)
          pure (linesOf (either (\e -> const "" (e :: IOException)) id read'))
      pure (Location targetUri (toRange ls sp))

{- |
How long the server waits after a change before checking the document, in
microseconds: a pause in typing shorter than this starts no check, and a
check started is abandoned by the next change.
-}
changeDelay :: Int
changeDelay = 300000

{- |
Check a document in the background, after the pause given, and publish what
was found, clearing what was published before.  A check of the same document
pending or running is abandoned first, the document having changed since.
Meanwhile the requests about the document are answered from what was found
last.  The documents open stand for the files at their paths, for the modules
the document imports.
-}
schedule :: Server -> Int -> NormalizedUri -> LspM () ()
schedule server delay uri = do
  file <- getVirtualFile uri
  open <- Map.keys . _vfsMap <$> getVirtualFiles
  others <- mapM (\u -> fmap (u,) <$> getVirtualFile u) open
  env <- getLspEnv
  let path = uriToFilePath (fromNormalizedUri uri)
  case (file, languageOf =<< path) of
    (Just f, Just lang) -> do
      let texts = Map.fromList [(p, virtualFileText v) | Just (u, v) <- others, Just p <- [uriToFilePath (fromNormalizedUri u)], languageOf p == Just Px]
      liftIO $ modifyMVar_ (serverChecks server) \checks -> do
        mapM_ killThread (Map.lookup uri checks)
        worker <- forkIO (check server env delay uri (fromMaybe "<document>" path) lang (virtualFileText f) (virtualFileVersion f) texts)
        pure (Map.insert uri worker checks)
    _ -> pure ()

-- | Abandon the check of a document pending or running, if any.
abandon :: Server -> NormalizedUri -> IO ()
abandon server uri = modifyMVar_ (serverChecks server) \checks -> do
  mapM_ killThread (Map.lookup uri checks)
  pure (Map.delete uri checks)

{- |
The documents open whose check a document saved may change: the @.px@
documents whose last check read the file saved, it being among the modules
before theirs, and those whose last check reported an error, which the file
saved may resolve, as a module they import appearing does.
-}
dependents :: Server -> NormalizedUri -> [NormalizedUri] -> IO [NormalizedUri]
dependents server saved open = case uriToFilePath (fromNormalizedUri saved) of
  Just path | languageOf path == Just Px -> do
    canonical <- canonicalizePath path
    entries <- readIORef (serverEntries server)
    prefixes <- readIORef (serverPrefixes server)
    filterM
      ( \u -> case uriToFilePath (fromNormalizedUri u) of
          Just p | languageOf p == Just Px -> do
            read' <- maybe (pure False) (fmap (elem canonical) . mapM canonicalizePath . prefixPaths) (Map.lookup u prefixes)
            let failing = maybe False (any ((== DiagnosticSeverity_Error) . reportSeverity) . docReports . entryDocument) (Map.lookup u entries)
            pure (read' || failing)
          _ -> pure False
      )
      open
  _ -> pure []

{- |
Reports as the diagnostics of the praxis source, the source present even
with none: publishing the same version of a document again replaces its
diagnostics by source, and a source absent would leave those before.
-}
diagnosticsBySource :: Lines -> [Report] -> DiagnosticsBySource
diagnosticsBySource ls reports = Map.insertWith (<>) (Just "praxis") mempty (partitionBySource (map (diagnostic ls) reports))

{- |
A check: after the pause, the analysis, forced where abandoning it costs
nothing; then, all at once, what was found kept and published, so that an
abandoned check leaves nothing half done.  A failure of the checker is
reported as a diagnostic rather than lost.
-}
check :: Server -> LanguageContextEnv () -> Int -> NormalizedUri -> FilePath -> Language -> Text -> Int32 -> Map FilePath Text -> IO ()
check server env delay uri path lang text version texts = do
  threadDelay delay
  previous <- Map.lookup uri <$> readIORef (serverEntries server)
  prefix <- Map.lookup uri <$> readIORef (serverPrefixes server)
  found <- try (analysed prefix)
  (doc, prefix') <- case found of
    Right result -> pure result
    Left e
      | Just (_ :: SomeAsyncException) <- fromException e -> throwIO e
      | otherwise -> pure (Document [Report 1 1 DiagnosticSeverity_Error (T.pack ("the checker failed: " <> displayException e)) Nothing] mempty False, Nothing)
  -- A document which does not parse keeps the index of the text before it, rather than losing its colours as it is typed.
  let doc' = if docParsed doc then doc else doc {docIndex = maybe (docIndex doc) (docIndex . entryDocument) previous}
  mask_ do
    atomicModifyIORef' (serverEntries server) (\m -> (Map.insert uri (Entry text doc') m, ()))
    forM_ prefix' \p -> atomicModifyIORef' (serverPrefixes server) (\m -> (Map.insert uri p m, ()))
    runLspT env (publishDiagnostics 100 uri (Just version) (diagnosticsBySource (linesOf text) (docReports doc)))
  me <- myThreadId
  modifyMVar_ (serverChecks server) (pure . Map.update (\t -> if t == me then Nothing else Just t) uri)
  where
    analysed prefix = do
      (doc, prefix') <- analyseDocumentWith texts prefix lang path text
      mapM_ evaluate (docReports doc)
      mapM_ evaluate (indexTokens (docIndex doc))
      mapM_ evaluate (indexReferences (docIndex doc))
      pure (doc, prefix')

-- | A report as a diagnostic, spanning from its position to its end, or else to the end of the line.
diagnostic :: Lines -> Report -> Diagnostic
diagnostic ls (Report line column severity message stop) =
  Diagnostic
    { _range = Range start end
    , _severity = Just severity
    , _code = Nothing
    , _codeDescription = Nothing
    , _source = Just "praxis"
    , _message = message
    , _tags = Nothing
    , _relatedInformation = Nothing
    , _data_ = Nothing
    }
  where
    start = toPosition ls (line, column)
    end = case stop of
      Just p -> toPosition ls p
      Nothing ->
        let Position l c = start
            Position _ c' = toPosition ls (line, T.length (lineAt ls line) + 1)
         in Position l (max c c')

-- * Analysis

-- | The languages served, told apart by the extension of the file.
data Language = Pra | Prf | Px
  deriving (Show, Eq)

-- | The language of a file, by its extension; nothing for a file the server does not serve.
languageOf :: FilePath -> Maybe Language
languageOf path = case takeExtension path of
  ".pra" -> Just Pra
  ".prf" -> Just Prf
  ".px" -> Just Px
  _ -> Nothing

-- | A finding about a document: where, from line and column 1, how severe, and what.
data Report = Report
  { reportLine :: !Int
  , reportColumn :: !Int
  , reportSeverity :: !DiagnosticSeverity
  , reportMessage :: !Text
  , reportEnd :: !(Maybe (Int, Int))
  -- ^ where it ends, when known: the line, and the column after its last character
  }
  deriving (Show, Eq)

-- | Everything found in a document: its reports, and the index of its names.
data Document = Document
  { docReports :: ![Report]
  , docIndex :: !Index
  , docParsed :: !Bool
  -- ^ whether the document parsed, so that its index is that of its text; when it did not, the index is empty
  }
  deriving (Show, Eq)

-- | Everything to report about a document on its own: a @.px@ document outside any package.
analyse :: Language -> Text -> [Report]
analyse lang text = case lang of
  Pra -> analysePra text
  Prf -> analysePrf text
  Px -> docReports (analysePx "<document>" text)

{- |
Everything to report about a document at a path: a @.px@ document as a
module of the package enclosing the path, when one does, its imports
resolved and the modules it imports checked before it; else on its own.
-}
analyseIn :: Language -> FilePath -> Text -> IO [Report]
analyseIn lang path text = docReports <$> analyseDocument lang path text

-- | Everything found in a document at a path: its reports, as 'analyseIn' finds them, and its index.
analyseDocument :: Language -> FilePath -> Text -> IO Document
analyseDocument lang path text = fst <$> analyseDocumentWith (Map.singleton path text) Nothing lang path text

{- |
'analyseDocument', the texts given standing for the files at their paths,
and a @.px@ document checked from the prefix given, as 'checkFileCached'
checks it: what was found, and the prefix for the next check of the
document, where there is one.
-}
analyseDocumentWith :: Map FilePath Text -> Maybe Prefix -> Language -> FilePath -> Text -> IO (Document, Maybe Prefix)
analyseDocumentWith texts prefix lang path text = case lang of
  Pra -> pure (Document (analysePra text) (indexPra path (linesOf text) libraryNames) True, Nothing)
  Prf -> pure (Document (analysePrf text) (indexPrf path (linesOf text)) True, Nothing)
  Px -> analysePxIn texts prefix path text

-- | The names of the lemmas in scope in a @.pra@ document before any declaration.
libraryNames :: Set Text
libraryNames = either (const Set.empty) (Set.fromList . map T.pack . Map.keys) builtinLemmas

analysePrf :: Text -> [Report]
analysePrf text = case checkQuote mempty Map.empty Set.empty id "" text of
  Left err ->
    let (line, column) = fromMaybe (1, 1) (checkErrorPosition err)
     in [Report line column DiagnosticSeverity_Error (T.pack (renderCheckError err)) Nothing]
  Right _ -> []

{- | Editor assumptions carry their unproved roots. Only Proved entries hold
certificates; a successful proof against a draft remains conditional.
-}
data EditorLemma
  = Proved !Certificate
  | Assumed !(Lemma SchemaName) !(Set String)

editorStatement :: EditorLemma -> Lemma SchemaName
editorStatement (Proved certificate) = certificateLemma certificate
editorStatement (Assumed lemma _) = lemma

unprovedRoots :: EditorLemma -> Set String
unprovedRoots (Proved _) = Set.empty
unprovedRoots (Assumed _ roots) = roots

checkEditorDeclaration :: Env -> Map String EditorLemma -> Decl SchemaName -> (EditorLemma, Maybe (TacticError SchemaName))
checkEditorDeclaration kernel known decl = case checkDecl kernel (fmap editorStatement known) decl of
  Left err -> failed err
  Right (proof, lemma) ->
    let used = derivationAppeals proof `Set.difference` Set.fromList (map fst (lemmaPremises lemma))
        roots = Set.unions (map unprovedRoots (Map.elems (Map.restrictKeys known used)))
     in if Set.null roots
          then case checkCertificate kernel (Map.mapMaybe proved known) decl of
            Right certificate -> (Proved certificate, Nothing)
            Left err -> failed err
          else (Assumed lemma roots, Nothing)
  where
    failed err = (Assumed (declLemma decl) (Set.singleton (declName decl)), Just err)
    proved (Proved certificate) = Just certificate
    proved Assumed {} = Nothing

conditionalMessage :: Set String -> Text
conditionalMessage roots = "Conditional proof; unproved dependencies: " <> T.intercalate ", " (map T.pack (Set.toAscList roots))

{- | Check drafts for useful local feedback, while keeping their conditional
status distinct from certification, including through transitive appeals.
-}
analysePra :: Text -> [Report]
analysePra text = case libraryCertificates of
  Left err -> [Report 1 1 DiagnosticSeverity_Error (T.pack err) Nothing]
  Right base -> case parseQuoteIn (lemmaSorts (fmap certificateLemma base)) (schemaScope builtin) (T.unpack text) of
    Left err ->
      let (line, column) = syntaxErrorPosition err
       in [Report line column DiagnosticSeverity_Error (T.pack (displayException err)) Nothing]
    Right (_, decls) -> case signatureEnv builtin of
      Left err -> [Report 1 1 DiagnosticSeverity_Error (T.pack (displayException err)) Nothing]
      Right kernel -> go kernel (fmap Proved (withoutDeclared decls base)) decls
  where
    go _ _ [] = []
    go kernel known (d : ds) =
      let (entry, failure) = checkEditorDeclaration kernel known d
          reports = case failure of
            Just err -> [report d err]
            Nothing
              | not (Set.null (unprovedRoots entry)) ->
                  let (line, column) = fromMaybe (1, 1) (firstLoc (declTactic d))
                   in [Report line column DiagnosticSeverity_Warning (conditionalMessage (unprovedRoots entry)) Nothing]
            _ -> []
       in reports <> go kernel (Map.insert (declName d) entry known) ds
    report d err =
      let (line, column) = maybe (fromMaybe (1, 1) (firstLoc (declTactic d))) (\(Loc l c) -> (l, c)) (errorLoc err)
          severity = case errorFailure err of
            Unfinished -> DiagnosticSeverity_Warning
            _ -> DiagnosticSeverity_Error
       in Report line column severity (T.pack (unlocated (renderSchemaTacticError builtin err))) Nothing
    -- The position opens the rendering; the diagnostic carries it already.
    unlocated s = case break (== ':') s of
      (l, ':' : rest) | all (`elem` ['0' .. '9']) l, (c, ':' : ' ' : msg) <- break (== ':') rest, all (`elem` ['0' .. '9']) c, not (null c) -> msg
      _ -> s

{- |
The lemmas in scope before any declaration: those of the library,
"Language.Praxis.PRA.Library", and the unfolding lemmas of 'builtin'.
-}
builtinLemmas :: Either String (Map String (Lemma SchemaName))
builtinLemmas = libraryScope

{- |
The lemmas to check the declarations of a document against: all those before
any declaration, but the lemmas of the library the document declares itself.
The library read as a document then appeals only to what comes before, as
when it is certified.
-}
withoutDeclared :: [Decl SchemaName] -> Map String a -> Map String a
withoutDeclared decls = (`Map.withoutKeys` Set.intersection (Set.fromList (map declName decls)) library)
  where
    library = either (const Set.empty) Map.keysSet certifiedLibrary

-- | What the parser needs of the lemmas: the sorts of their arguments.
lemmaSorts :: Map String (Lemma SchemaName) -> Lemmas
lemmaSorts = fmap (map snd . lemmaMetas)

{- |
The goal at a position of a @.pra@ document: that of the innermost tactic
which starts at or before the position, found by running its declaration
with that tactic replaced by @sorry@.
-}
hoverAt :: Text -> Int -> Int -> Maybe Text
hoverAt text line column = do
  base <- either (const Nothing) Just libraryCertificates
  (_, decls) <- either (const Nothing) Just (parseQuoteIn (lemmaSorts (fmap certificateLemma base)) (schemaScope builtin) (T.unpack text))
  kernel <- either (const Nothing) Just (signatureEnv builtin)
  -- The last declaration with a tactic at or before the position, and that tactic.
  (before, d, target) <-
    listToMaybe
      [ (before, d, loc)
      | (before, d) <- reverse (zip (prefixes decls) decls)
      , Just loc <- [locBefore (declTactic d)]
      ]
  let known = editorScope kernel (fmap Proved (withoutDeclared decls base)) before
      (entry, failure) = checkEditorDeclaration kernel known d
      annotation = case failure of
        Just _ -> "Unproved declaration: " <> T.pack (declName d) <> "\n\n"
        Nothing | not (Set.null (unprovedRoots entry)) -> conditionalMessage (unprovedRoots entry) <> "\n\n"
        _ -> ""
      stubbed = d {declTactic = replaceAt target Sorry (declTactic d)}
  case checkDecl kernel (fmap editorStatement known) stubbed of
    Left (TacticError _ goal Unfinished) -> Just (annotation <> renderGoal goal)
    _ -> Nothing
  where
    prefixes ds = [take i ds | i <- [0 .. length ds - 1]]
    locBefore t = listToMaybe (sortOn negateLoc [loc | loc <- locations t, (locLine loc, locColumn loc) <= (line, column)])
    negateLoc (Loc l c) = (negate l, negate c)
    -- The state a sorry reports, without the headline.
    renderGoal goal =
      T.pack
        ( unlines'
            (map (dropWhile isSpace) (drop 1 (lines (renderSchemaTacticError builtin (TacticError Nothing goal Unfinished)))))
        )
    unlines' = foldr1 (\a b -> a <> "\n" <> b)

-- | One status-aware scope construction for diagnostics and hover.
editorScope :: Env -> Map String EditorLemma -> [Decl SchemaName] -> Map String EditorLemma
editorScope kernel = foldl (\known d -> Map.insert (declName d) (fst (checkEditorDeclaration kernel known d)) known)

-- | Every position the parser attached in a tactic.
locations :: Tactic a -> [Loc]
locations = \case
  At loc t -> loc : locations t
  Then t u -> locations t <> locations u
  OrElse t u -> locations t <> locations u
  Try t -> locations t
  Repeat t -> locations t
  Dispatch t us -> locations t <> concatMap locations us
  On _ t -> locations t
  As _ t -> locations t
  Calc _ steps -> concatMap (locations . snd) steps
  Have _ _ t -> locations t
  _ -> []

-- | The first position in a tactic, in source order.
firstLoc :: Tactic a -> Maybe (Int, Int)
firstLoc t = listToMaybe (sortOn id [(l, c) | Loc l c <- locations t])

-- | The tactic at the position, replaced.
replaceAt :: Loc -> Tactic a -> Tactic a -> Tactic a
replaceAt target new = go
  where
    go = \case
      At loc t
        | loc == target -> At loc new
        | otherwise -> At loc (go t)
      Then t u -> Then (go t) (go u)
      OrElse t u -> OrElse (go t) (go u)
      Try t -> Try (go t)
      Repeat t -> Repeat (go t)
      Dispatch t us -> Dispatch (go t) (map go us)
      On ns t -> On ns (go t)
      As ns t -> As ns (go t)
      Calc t0 steps -> Calc t0 [(t, go u) | (t, u) <- steps]
      Have n f t -> Have n f (go t)
      t -> t

-- * The surface language

-- | The prelude of the surface language, certified once for the server's lifetime.
surfacePrelude :: Either String Prelude
surfacePrelude = prelude

-- | A report of the driver, as the server reports it.
surfaceReport :: Surface.Report -> Report
surfaceReport (Surface.Report (Span (l, c) (l', c')) sev msg) = Report (max 1 l) (max 1 c) (severity sev) msg (Just (max 1 l', max 1 c'))
  where
    severity = \case
      Surface.SevError -> DiagnosticSeverity_Error
      Surface.SevInfo -> DiagnosticSeverity_Information

{- |
A module of the surface language, checked by the driver of the praxis
package: each report where the driver places it, a failed proof at its
declaration or at the tactic which failed; and its index, built from the
module as the renamer left it and the environment after it, with the
definitions of the other modules given.
-}
documentOf :: Prelude -> FilePath -> Text -> Map [Segment] Target -> Surface.Checked -> Document
documentOf p path text others checked = Document (map surfaceReport (Surface.checkedReports checked)) index (isJust (Surface.checkedRenamed checked))
  where
    index = case (parseModule path text, Surface.checkedRenamed checked, Surface.checkedFinal checked) of
      (Right raw, Just rn, Just (k, _)) -> indexModule (linesOf text) raw rn (knowEnv k) preludeNames (Map.union (moduleDefinitions path rn) others)
      _ -> mempty
    preludeNames = Set.fromList (map T.pack (Map.keys (preludeLemmas p)))

-- | A module of the surface language on its own, outside any package.
analysePx :: FilePath -> Text -> Document
analysePx path text = case surfacePrelude of
  Left err -> Document [Report 1 1 DiagnosticSeverity_Error (T.pack ("the prelude of the surface language did not certify: " <> err)) Nothing] mempty False
  Right p -> documentOf p path text Map.empty (Surface.checkSource p "<document>" text)

{- |
A module of the surface language at a path: checked as a module of the
package enclosing it, with what it imports, the texts given standing for
the files at their paths, and the modules before it taken from the prefix
given where their sources stand; the reports being the document's own, and
the definitions of every module checked before it in its index.  Or on its
own, when no package encloses it.  With the document, the prefix for its
next check.
-}
analysePxIn :: Map FilePath Text -> Maybe Prefix -> FilePath -> Text -> IO (Document, Maybe Prefix)
analysePxIn texts prefix path text = case surfacePrelude of
  Left err -> pure (Document [Report 1 1 DiagnosticSeverity_Error (T.pack ("the prelude of the surface language did not certify: " <> err)) Nothing] mempty False, Nothing)
  Right p -> do
    inPackage <- checkFileCached (editorBuild p) (Map.insert path text texts) prefix path
    case inPackage of
      Nothing -> pure (analysePx path text, Nothing)
      Just (Left err) -> pure (Document [Report 1 1 DiagnosticSeverity_Error (T.pack err) Nothing] mempty False, Nothing)
      Just (Right (results, prefix', _)) -> do
        located <- locate path
        canonical <- canonicalizePath path
        paths <- mapM (canonicalizePath . mrPath) results
        let mine = case located of
              Just (_, c, name) -> [r | r <- results, mrModule r == name, componentId (mrComponent r) == componentId c]
              Nothing -> take 1 (reverse results)
            -- The definitions of the other modules; a module without a header is at the start of its file.
            others =
              Map.unions
                [ Map.insertWith (\_ old -> old) (Component (componentId (mrComponent r)) : mrModule r) (Target p' (Span (1, 1) (1, 1))) (moduleDefinitions p' rn)
                | (p', r) <- zip paths results
                , p' /= canonical
                , Just rn <- [Surface.checkedRenamed (mrChecked r)]
                ]
        pure
          ( case mine of
              r : _ -> documentOf p path text others (mrChecked r)
              [] -> Document [] mempty False
          , Just prefix'
          )

-- | The build a document's check starts from: the prelude's, keeping no generated text, which nothing in the editor reads.
editorBuild :: Prelude -> Surface.Build
editorBuild p = (Surface.initialBuild p) {Surface.buildRetainGeneratedText = False}

-- * Navigation

-- | The declarations the name at a position of a document refers to.
definitionsAt :: Text -> Document -> Position -> [Target]
definitionsAt text doc position = referencesAt (docIndex doc) (fromPosition (linesOf text) position)

-- | The tokens of a document, encoded by the default legend.
semanticTokensOf :: Text -> Document -> Either Text SemanticTokens
semanticTokensOf text doc = makeSemanticTokens defaultSemanticTokensLegend (map absolute (indexTokens (docIndex doc)))
  where
    ls = linesOf text
    absolute (Token sp t ms) =
      let Range (Position l c) (Position _ c') = toRange ls sp
       in SemanticTokenAbsolute l c (c' - c) t ms
