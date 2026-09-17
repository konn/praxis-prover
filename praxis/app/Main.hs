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
import Language.Praxis.Surface.Prelude
import Language.Praxis.Surface.Syntax.Raw (Span (..))
import Options.Applicative
import Paths_praxis (version)
import System.Directory (doesDirectoryExist)
import System.Exit (exitFailure, exitSuccess)
import System.FilePath (takeExtension, takeFileName)
import System.IO (hPutStrLn, stderr)

-- | What the command line asks for.
newtype Command = Check CheckOptions

data CheckOptions = CheckOptions
  { dumpCore :: !Bool
  , alone :: !Bool
  , targets :: ![FilePath]
  }

main :: IO ()
main = do
  Check CheckOptions {..} <- execParser (info (commandP <**> versionP <**> helper) (fullDesc <> header "praxis - a finitistic prover over primitive recursive arithmetic"))
  p <- either (\e -> hPutStrLn stderr ("the prelude did not certify: " <> e) *> exitFailure) pure prelude
  oks <- mapM (checkTarget p dumpCore alone) (if null targets then ["."] else targets)
  if and oks then exitSuccess else exitFailure

commandP :: Parser Command
commandP =
  hsubparser $
    command "check" $
      info (Check <$> checkP) (progDesc "Check the modules of a project, a package, or files, printing every report; fail when one has an error")

checkP :: Parser CheckOptions
checkP = do
  dumpCore <-
    switch $
      long "dump-core"
        <> help "Print the core text generated, prf definitions and pra declarations, before the reports"
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
checkTarget :: Prelude -> Bool -> Bool -> FilePath -> IO Bool
checkTarget p dump alone target = do
  isDir <- doesDirectoryExist target
  if
    | isDir || takeFileName target `elem` ["project.toml", "package.toml"] ->
        checkProject p target >>= \case
          Left err -> failWith err
          Right results -> and <$> mapM (\r -> printChecked dump (mrPath r) (mrChecked r)) results
    | takeExtension target == ".px" -> do
        src <- readFileUtf8 target
        located <- if alone then pure Nothing else checkFile p target src
        case located of
          Nothing -> printChecked dump target (checkSource p target src)
          Just (Left err) -> failWith err
          Just (Right results) -> and <$> mapM (\r -> printChecked dump (mrPath r) (mrChecked r)) results
    | otherwise -> failWith (target <> ": not a .px file, a manifest, or a directory holding one")
  where
    failWith err = hPutStrLn stderr err *> pure False

-- | The core text of a module when asked, then its reports; whether it has no error.
printChecked :: Bool -> FilePath -> Checked -> IO Bool
printChecked dump path result = do
  when dump $ mapM_ TIO.putStrLn (checkedCore result)
  mapM_ (TIO.putStrLn . render) (checkedReports result)
  pure (all ((/= SevError) . reportSeverity) (checkedReports result))
  where
    render (Report (Span (l, c) _) sev msg) =
      T.pack (path <> ":" <> show l <> ":" <> show c <> ": " <> severity sev <> ": ") <> msg
    severity = \case
      SevError -> "error"
      SevInfo -> "info"
