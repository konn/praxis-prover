{-# LANGUAGE DataKinds #-}

{- |
A language server for the files of praxis: @.pra@ files of theorems and
rules, as 'Language.Praxis.PRA.Tactic.Quote.praFile' splices them, and
@.prf@ files of definitions, as 'Language.Praxis.PRA.PrimitiveRecursion.Quote.prfFile'
does.

A @.pra@ document is read over the 'builtin' signature, with the unfolding
lemmas of 'builtin' in scope and each declaration a lemma for those after it,
as the quasiquoter reads it; every declaration is checked, and a failure is a
diagnostic at the tactic which failed, a @sorry@
an information diagnostic listing the goal it stopped at.  Hovering over a
tactic shows the goal it faces, found by running the proof with that tactic
replaced by @sorry@.  A @.prf@ document is checked as the quasiquoter checks
it, over the empty signature.
-}
module Language.Praxis.LSP (
  runPraxisServer,

  -- * Analysis
  Language (..),
  languageOf,
  Report (..),
  analyse,
  hoverAt,
) where

import Control.Exception (displayException)
import Control.Monad.IO.Class (liftIO)
import Data.Bifunctor (bimap)
import Data.Char (isSpace)
import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Language.LSP.Diagnostics (partitionBySource)
import Language.LSP.Protocol.Message
import Language.LSP.Protocol.Types
import Language.LSP.Server
import Language.LSP.VFS (virtualFileText, virtualFileVersion)
import Language.Praxis.PRA.PrimitiveRecursion (builtin)
import Language.Praxis.PRA.PrimitiveRecursion.Function (KernelEnv)
import Language.Praxis.PRA.PrimitiveRecursion.Quote (checkErrorPosition, checkQuote, renderCheckError)
import Language.Praxis.PRA.Signature (signatureKernelEnv)
import Language.Praxis.PRA.Syntax.Parser (syntaxErrorPosition)
import Language.Praxis.PRA.Tactic
import Language.Praxis.PRA.Tactic.Parser
import Language.Praxis.PRA.Tactic.Quote (SchemaName, checkDecl, renderSchemaName, renderSchemaTacticError, schemaScope)
import Language.Praxis.PRA.Tactic.Unfolding (renderUnfoldingError, unfoldingLemmas)
import System.Exit (ExitCode (..))
import System.FilePath (takeExtension)

-- * The server

-- | Serve over standard input and output, until the client says goodbye.
runPraxisServer :: IO ExitCode
runPraxisServer = do
  code <- runServer definition
  pure (if code == 0 then ExitSuccess else ExitFailure code)

definition :: ServerDefinition ()
definition =
  ServerDefinition
    { defaultConfig = ()
    , configSection = "praxis"
    , parseConfig = \_ _ -> Right ()
    , onConfigChange = \_ -> pure ()
    , doInitialize = \env _ -> pure (Right env)
    , staticHandlers = \_ -> handlers
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

handlers :: Handlers (LspM ())
handlers =
  mconcat
    [ notificationHandler SMethod_Initialized \_ -> pure ()
    , -- The library reads the configuration itself; these notifications need no answer.
      notificationHandler SMethod_WorkspaceDidChangeConfiguration \_ -> pure ()
    , notificationHandler SMethod_SetTrace \_ -> pure ()
    , notificationHandler SMethod_WorkspaceDidChangeWatchedFiles \_ -> pure ()
    , notificationHandler SMethod_TextDocumentDidOpen \msg -> publish (toNormalizedUri msg._params._textDocument._uri)
    , notificationHandler SMethod_TextDocumentDidChange \msg -> publish (toNormalizedUri msg._params._textDocument._uri)
    , notificationHandler SMethod_TextDocumentDidSave \msg -> publish (toNormalizedUri msg._params._textDocument._uri)
    , notificationHandler SMethod_TextDocumentDidClose \msg ->
        publishDiagnostics 100 (toNormalizedUri msg._params._textDocument._uri) Nothing (partitionBySource [])
    , requestHandler SMethod_TextDocumentHover \req responder -> do
        let uri = toNormalizedUri req._params._textDocument._uri
            Position line column = req._params._position
        file <- getVirtualFile uri
        let answer = do
              text <- virtualFileText <$> file
              Pra <- languageOf =<< uriToFilePath (fromNormalizedUri uri)
              body <- hoverAt text (fromIntegral line + 1) (fromIntegral column + 1)
              pure (Hover (InL (MarkupContent MarkupKind_Markdown ("```\n" <> body <> "\n```"))) Nothing)
        responder (Right (maybe (InR Null) InL answer))
    ]

-- | Analyse a document and publish what it found, clearing what was found before.
publish :: NormalizedUri -> LspM () ()
publish uri = do
  file <- getVirtualFile uri
  case (file, languageOf =<< uriToFilePath (fromNormalizedUri uri)) of
    (Just f, Just lang) ->
      publishDiagnostics 100 uri (Just (virtualFileVersion f)) (partitionBySource (map (diagnostic (virtualFileText f)) (analyse lang (virtualFileText f))))
    _ -> pure ()

-- | A report as a diagnostic, spanning from its position to the end of the line.
diagnostic :: Text -> Report -> Diagnostic
diagnostic text (Report line column severity message) =
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
    start = Position (fromIntegral (line - 1)) (fromIntegral (column - 1))
    end = Position (fromIntegral (line - 1)) (fromIntegral (max column (lineLength line)))
    lineLength l = maybe column T.length (listToMaybe (drop (l - 1) (T.lines text)))

-- * Analysis

-- | The languages served, told apart by the extension of the file.
data Language = Pra | Prf
  deriving (Show, Eq)

languageOf :: FilePath -> Maybe Language
languageOf path = case takeExtension path of
  ".pra" -> Just Pra
  ".prf" -> Just Prf
  _ -> Nothing

-- | A finding about a document: where, from line and column 1, how severe, and what.
data Report = Report
  { reportLine :: !Int
  , reportColumn :: !Int
  , reportSeverity :: !DiagnosticSeverity
  , reportMessage :: !Text
  }
  deriving (Show, Eq)

-- | Everything to report about a document.
analyse :: Language -> Text -> [Report]
analyse = \case
  Pra -> analysePra
  Prf -> analysePrf

analysePrf :: Text -> [Report]
analysePrf text = case checkQuote mempty Map.empty Set.empty id "" text of
  Left err ->
    let (line, column) = fromMaybe (1, 1) (checkErrorPosition err)
     in [Report line column DiagnosticSeverity_Error (T.pack (renderCheckError err))]
  Right _ -> []

{- |
Check every declaration, each a lemma for those after it, by its statement
even when its proof fails; one which fails is reported, at the tactic which failed when one is
known, and a @sorry@ as information with the goal it stopped at.
-}
analysePra :: Text -> [Report]
analysePra text = case builtinLemmas of
  Left err -> [Report 1 1 DiagnosticSeverity_Error (T.pack err)]
  Right base -> case parseQuoteIn (lemmaSorts base) (schemaScope builtin) (T.unpack text) of
    Left err ->
      let (line, column) = syntaxErrorPosition err
       in [Report line column DiagnosticSeverity_Error (T.pack (displayException err))]
    Right (_, decls) -> case signatureKernelEnv builtin of
      Left err -> [Report 1 1 DiagnosticSeverity_Error (T.pack (displayException err))]
      Right kernel -> go kernel base decls
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
       in Report line column severity (T.pack (unlocated (renderSchemaTacticError builtin err)))
    -- The position opens the rendering; the diagnostic carries it already.
    unlocated s = case break (== ':') s of
      (l, ':' : rest) | all (`elem` ['0' .. '9']) l, (c, ':' : ' ' : msg) <- break (== ':') rest, all (`elem` ['0' .. '9']) c, not (null c) -> msg
      _ -> s

-- | The lemmas in scope before any declaration: the unfolding lemmas of 'builtin'.
builtinLemmas :: Either String (Map String (Lemma SchemaName))
builtinLemmas = bimap (renderUnfoldingError builtin renderSchemaName) (fmap certifiedLemma) (unfoldingLemmas (schemaScope builtin [] []))

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
  kernel <- either (const Nothing) Just (signatureKernelEnv builtin)
  -- The last declaration with a tactic at or before the position, and that tactic.
  (before, d, target) <-
    listToMaybe
      [ (before, d, loc)
      | (before, d) <- reverse (zip (prefixes decls) decls)
      , Just loc <- [locBefore (declTactic d)]
      ]
  let lemmas = certified kernel base before
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
certified :: KernelEnv -> Map String (Lemma SchemaName) -> [Decl SchemaName] -> Map String (Lemma SchemaName)
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
