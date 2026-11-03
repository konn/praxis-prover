{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}

module Main (main) where

import Control.Monad (when)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Version (showVersion)
import Language.Praxis.Package.Build
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Eval (EvalResult (..), evaluateEntryWithNats, renderValue)
import Language.Praxis.Surface.Prelude
import Language.Praxis.Surface.Syntax.Raw (Span (..))
import Numeric.Natural (Natural)
import Options.Applicative
import Paths_praxis (version)
import System.Directory (doesDirectoryExist)
import System.Exit (exitFailure, exitSuccess)
import System.FilePath (takeExtension, takeFileName)
import System.IO (hPutStrLn, stderr)

-- | What the command line asks for.
data Command = Check CheckOptions | Evaluate FilePath String [Natural] Int Int

data CheckOptions = CheckOptions
  { dumpCore :: !Bool
  , dumpPra :: !Bool
  , alone :: !Bool
  , targets :: ![FilePath]
  }

main :: IO ()
main = do
  requested <- execParser (info (commandP <**> versionP <**> helper) (fullDesc <> header "praxis - a finitistic prover over primitive recursive arithmetic"))
  p <- either (\e -> hPutStrLn stderr ("the prelude did not certify: " <> e) *> exitFailure) pure prelude
  case requested of
    Check CheckOptions {..} -> do
      oks <- mapM (checkTarget p dumpCore dumpPra alone) (if null targets then ["."] else targets)
      if and oks then exitSuccess else exitFailure
    Evaluate source entry arguments fuel depth -> do
      src <- readFileUtf8 source
      hPutStrLn stderr ("Checking " <> source <> "...")
      let checked = fst (checkModule (\_ _ -> []) (initialBuild p) {buildRetainGeneratedText = False} mempty Nothing source src)
      ok <- printChecked False False source checked
      when (not ok) exitFailure
      hPutStrLn stderr ("Evaluating " <> entry <> "...")
      case evaluateEntryWithNats fuel (T.pack entry) arguments checked of
        Left err -> hPutStrLn stderr err *> exitFailure
        Right result -> do
          TIO.putStrLn (renderValue depth (evalValue result))
          hPutStrLn stderr ("Evaluated " <> show (evalCalls result) <> " distinct calls; " <> show (evalNodes result) <> " shared value nodes.")

commandP :: Parser Command
commandP =
  hsubparser $
    command "check" (info (Check <$> checkP) (progDesc "Check the modules of a project, a package, or files, printing every report; fail when one has an error"))
      <> command "eval" (info evalP (progDesc "Check a standalone module and evaluate a first-order definition on shared constructor trees"))

evalP :: Parser Command
evalP = do
  source <- strArgument (metavar "FILE.px")
  entry <- strOption (long "entry" <> metavar "QUALIFIED.NAME" <> help "Definition to evaluate")
  arguments <- many (option auto (long "nat" <> metavar "N" <> help "Natural argument in runtime order; repeat for multiple arguments"))
  fuel <- option auto (long "fuel" <> value 1000000 <> showDefault <> metavar "N" <> help "Maximum evaluation steps")
  depth <- option auto (long "depth" <> value 12 <> showDefault <> metavar "N" <> help "Maximum display depth; deeper values are shown as ...")
  pure (Evaluate source entry arguments fuel depth)

checkP :: Parser CheckOptions
checkP = do
  dumpCore <- switch $ long "dump-core" <> help "Print elaborated declarations in readable surface-like syntax, including imported bodies"
  dumpPra <-
    switch $
      long "dump-pra"
        <> help "Print the PRA text generated, prf definitions and pra declarations, before the reports"
  alone <-
    switch $
      long "alone"
        <> help "Check a .px file on its own, outside the package enclosing it: its imports are not resolved"
  targets <-
    many . strArgument $
      metavar "TARGET..."
        <> action "file"
        <> help "A project.toml, a package.toml, a directory holding one, or a .px file, checked as a module of the package enclosing it; the current directory when none"
  pure CheckOptions {..}

versionP :: Parser (a -> a)
versionP = infoOption (showVersion version) (long "version" <> help "Show the version")

-- | Check a target, printing what was generated when asked and every report; whether it has no error.
checkTarget :: Prelude -> Bool -> Bool -> Bool -> FilePath -> IO Bool
checkTarget p surface dump alone target = do
  isDir <- doesDirectoryExist target
  if
    | isDir || takeFileName target `elem` ["project.toml", "package.toml"] ->
        checkProjectFrom initial target >>= \case
          Left err -> failWith err
          Right results -> and <$> mapM (\r -> printChecked surface dump (mrPath r) (mrChecked r)) results
    | takeExtension target == ".px" -> do
        src <- readFileUtf8 target
        located <- if alone then pure Nothing else checkFileFrom initial target src
        case located of
          Nothing -> printChecked surface dump target (fst (checkModule (\_ _ -> []) initial mempty Nothing target src))
          Just (Left err) -> failWith err
          Just (Right results) -> and <$> mapM (\r -> printChecked surface dump (mrPath r) (mrChecked r)) results
    | otherwise -> failWith (target <> ": not a .px file, a manifest, or a directory holding one")
  where
    initial = (initialBuild p) {buildRetainGeneratedText = dump}
    failWith err = hPutStrLn stderr err *> pure False

-- | The core text of a module when asked, then its reports; whether it has no error.
printChecked :: Bool -> Bool -> FilePath -> Checked -> IO Bool
printChecked surface dump path result = do
  when surface $ maybe (pure ()) (mapM_ TIO.putStrLn . surfaceCore . snd) (checkedFinal result)
  when dump $ mapM_ TIO.putStrLn (checkedCore result)
  mapM_ (TIO.putStrLn . render) (checkedReports result)
  pure (all ((/= SevError) . reportSeverity) (checkedReports result))
  where
    render (Report (Span (l, c) _) sev msg) =
      T.pack (path <> ":" <> show l <> ":" <> show c <> ": " <> severity sev <> ": ") <> msg
    severity = \case
      SevError -> "error"
      SevInfo -> "info"
