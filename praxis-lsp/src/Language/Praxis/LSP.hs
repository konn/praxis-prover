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
library of praxis-core, "Language.Praxis.PRA.Library", and the unfolding
lemmas of 'builtin' in scope and each declaration a lemma for those after it,
as the quasiquoter reads it with those lemmas in scope; every declaration is checked, and a failure is a
diagnostic at the tactic which failed, a @sorry@
an information diagnostic listing the goal it stopped at.  Hovering over a
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

import Control.Exception (IOException, displayException, try)
import Control.Monad.IO.Class (liftIO)
import Data.Char (isSpace)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust, listToMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Language.LSP.Diagnostics (partitionBySource)
import Language.LSP.Protocol.Message
import Language.LSP.Protocol.Types
import Language.LSP.Server
import Language.LSP.VFS (virtualFileText, virtualFileVersion)
import Language.Praxis.LSP.Core (indexPra, indexPrf)
import Language.Praxis.LSP.Index (Index (..), Target (..), Token (..), referencesAt)
import Language.Praxis.LSP.Position (Lines, fromPosition, lineAt, linesOf, toPosition, toRange)
import Language.Praxis.LSP.Surface (indexModule, moduleDefinitions)
import Language.Praxis.PRA.Library (certifiedLibrary, libraryScope)
import Language.Praxis.PRA.PrimitiveRecursion (builtin)
import Language.Praxis.PRA.PrimitiveRecursion.Quote (checkErrorPosition, checkQuote, renderCheckError)
import Language.Praxis.PRA.Syntax.Parser (syntaxErrorPosition)
import Language.Praxis.PRA.Tactic
import Language.Praxis.PRA.Tactic.Parser
import Language.Praxis.PRA.Tactic.Quote (SchemaName, checkDecl, renderSchemaTacticError, schemaScope)
import Language.Praxis.Package.Build (ModuleResult (..), checkFile, componentId, locate, readFileUtf8)
import Language.Praxis.Surface.Check qualified as Surface
import Language.Praxis.Surface.Engine (Knowledge (..))
import Language.Praxis.Surface.Parser (parseModule)
import Language.Praxis.Surface.Prelude (Prelude (..), prelude, preludeLemmas)
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

type Cache = IORef (Map NormalizedUri Entry)

-- | Serve over standard input and output, until the client says goodbye.
runPraxisServer :: IO ExitCode
runPraxisServer = do
  cache <- newIORef Map.empty
  code <- runServer (definition cache)
  pure (if code == 0 then ExitSuccess else ExitFailure code)

definition :: Cache -> ServerDefinition ()
definition cache =
  ServerDefinition
    { defaultConfig = ()
    , configSection = "praxis"
    , parseConfig = \_ _ -> Right ()
    , onConfigChange = \_ -> pure ()
    , doInitialize = \env _ -> pure (Right env)
    , staticHandlers = \_ -> handlers cache
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

handlers :: Cache -> Handlers (LspM ())
handlers cache =
  mconcat
    [ notificationHandler SMethod_Initialized \_ -> pure ()
    , -- The library reads the configuration itself; these notifications need no answer.
      notificationHandler SMethod_WorkspaceDidChangeConfiguration \_ -> pure ()
    , notificationHandler SMethod_SetTrace \_ -> pure ()
    , notificationHandler SMethod_WorkspaceDidChangeWatchedFiles \_ -> pure ()
    , notificationHandler SMethod_TextDocumentDidOpen \msg -> publish cache (toNormalizedUri msg._params._textDocument._uri)
    , notificationHandler SMethod_TextDocumentDidChange \msg -> publish cache (toNormalizedUri msg._params._textDocument._uri)
    , notificationHandler SMethod_TextDocumentDidSave \msg -> publish cache (toNormalizedUri msg._params._textDocument._uri)
    , notificationHandler SMethod_TextDocumentDidClose \msg -> do
        let uri = toNormalizedUri msg._params._textDocument._uri
        liftIO (modifyIORef' cache (Map.delete uri))
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
        entry <- liftIO (Map.lookup uri <$> readIORef cache)
        responder (Right (maybe (InR Null) (\e -> either (const (InR Null)) InL (semanticTokensOf (entryText e) (entryDocument e))) entry))
    , requestHandler SMethod_TextDocumentDefinition \req responder -> do
        let uri = toNormalizedUri req._params._textDocument._uri
            path = uriToFilePath (fromNormalizedUri uri)
        entry <- liftIO (Map.lookup uri <$> readIORef cache)
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

-- | Analyse a document, keep what was found, and publish its diagnostics, clearing those published before.
publish :: Cache -> NormalizedUri -> LspM () ()
publish cache uri = do
  file <- getVirtualFile uri
  let path = uriToFilePath (fromNormalizedUri uri)
  case (file, languageOf =<< path) of
    (Just f, Just lang) -> do
      let text = virtualFileText f
      previous <- liftIO (Map.lookup uri <$> readIORef cache)
      doc <- liftIO (analyseDocument lang (fromMaybe "<document>" path) text)
      -- A document which does not parse keeps the index of the text before it, rather than losing its colours as it is typed.
      let doc' = if docParsed doc then doc else doc {docIndex = maybe (docIndex doc) (docIndex . entryDocument) previous}
      liftIO (modifyIORef' cache (Map.insert uri (Entry text doc')))
      publishDiagnostics 100 uri (Just (virtualFileVersion f)) (partitionBySource (map (diagnostic (linesOf text)) (docReports doc)))
    _ -> pure ()

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
analyseDocument lang path text = case lang of
  Pra -> pure (Document (analysePra text) (indexPra path (linesOf text) libraryNames) True)
  Prf -> pure (Document (analysePrf text) (indexPrf path (linesOf text)) True)
  Px -> analysePxIn path text

-- | The names of the lemmas in scope in a @.pra@ document before any declaration.
libraryNames :: Set Text
libraryNames = either (const Set.empty) (Set.fromList . map T.pack . Map.keys) builtinLemmas

analysePrf :: Text -> [Report]
analysePrf text = case checkQuote mempty Map.empty Set.empty id "" text of
  Left err ->
    let (line, column) = fromMaybe (1, 1) (checkErrorPosition err)
     in [Report line column DiagnosticSeverity_Error (T.pack (renderCheckError err)) Nothing]
  Right _ -> []

{- |
Check every declaration, each a lemma for those after it, by its statement
even when its proof fails; one which fails is reported, at the tactic which failed when one is
known, and a @sorry@ as information with the goal it stopped at.
-}
analysePra :: Text -> [Report]
analysePra text = case builtinLemmas of
  Left err -> [Report 1 1 DiagnosticSeverity_Error (T.pack err) Nothing]
  Right base -> case parseQuoteIn (lemmaSorts base) (schemaScope builtin) (T.unpack text) of
    Left err ->
      let (line, column) = syntaxErrorPosition err
       in [Report line column DiagnosticSeverity_Error (T.pack (displayException err)) Nothing]
    Right (_, decls) -> case signatureEnv builtin of
      Left err -> [Report 1 1 DiagnosticSeverity_Error (T.pack (displayException err)) Nothing]
      Right kernel -> go kernel (withoutDeclared decls base) decls
  where
    go _ _ [] = []
    go kernel lemmas (d : ds) = case checkDecl kernel lemmas d of
      Right (_, lemma) -> go kernel (Map.insert (declName d) lemma lemmas) ds
      Left err -> report d err : go kernel (Map.insert (declName d) (declLemma d) lemmas) ds
    report d err =
      let (line, column) = maybe (fromMaybe (1, 1) (firstLoc (declTactic d))) (\(Loc l c) -> (l, c)) (errorLoc err)
          severity = case errorFailure err of
            Unfinished -> DiagnosticSeverity_Information
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
withoutDeclared :: [Decl SchemaName] -> Map String (Lemma SchemaName) -> Map String (Lemma SchemaName)
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
  base <- either (const Nothing) Just builtinLemmas
  (_, decls) <- either (const Nothing) Just (parseQuoteIn (lemmaSorts base) (schemaScope builtin) (T.unpack text))
  kernel <- either (const Nothing) Just (signatureEnv builtin)
  -- The last declaration with a tactic at or before the position, and that tactic.
  (before, d, target) <-
    listToMaybe
      [ (before, d, loc)
      | (before, d) <- reverse (zip (prefixes decls) decls)
      , Just loc <- [locBefore (declTactic d)]
      ]
  let lemmas = certified kernel (withoutDeclared decls base) before
      stubbed = d {declTactic = replaceAt target Sorry (declTactic d)}
  case checkDecl kernel lemmas stubbed of
    Left (TacticError _ goal Unfinished) -> Just (renderGoal goal)
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

-- | The lemmas of the declarations after those given, in order: as certified, or by statement alone when the proof fails.
certified :: Env -> Map String (Lemma SchemaName) -> [Decl SchemaName] -> Map String (Lemma SchemaName)
certified kernel base = foldl step base
  where
    step lemmas d = case checkDecl kernel lemmas d of
      Right (_, lemma) -> Map.insert (declName d) lemma lemmas
      Left _ -> Map.insert (declName d) (declLemma d) lemmas

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
package enclosing it, with what it imports, the reports being the
document's own and the definitions of every module checked before it in
its index; or on its own, when no package encloses it.
-}
analysePxIn :: FilePath -> Text -> IO Document
analysePxIn path text = case surfacePrelude of
  Left err -> pure (Document [Report 1 1 DiagnosticSeverity_Error (T.pack ("the prelude of the surface language did not certify: " <> err)) Nothing] mempty False)
  Right p -> do
    inPackage <- checkFile p path text
    case inPackage of
      Nothing -> pure (analysePx path text)
      Just (Left err) -> pure (Document [Report 1 1 DiagnosticSeverity_Error (T.pack err) Nothing] mempty False)
      Just (Right results) -> do
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
        pure case mine of
          r : _ -> documentOf p path text others (mrChecked r)
          [] -> Document [] mempty False

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
