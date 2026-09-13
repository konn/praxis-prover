{-# LANGUAGE ApplicativeDo #-}

module Main (main) where

import Control.Monad (when)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Version (showVersion)
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Prelude
import Language.Praxis.Surface.Syntax.Raw (Span (..))
import Options.Applicative
import Paths_praxis (version)
import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr)

-- | What the command line asks for.
newtype Command = Check CheckOptions

data CheckOptions = CheckOptions
  { dumpCore :: !Bool
  , files :: ![FilePath]
  }

main :: IO ()
main = do
  Check opts <- execParser (info (commandP <**> versionP <**> helper) (fullDesc <> header "praxis - a finitistic prover over primitive recursive arithmetic"))
  p <- either (\e -> hPutStrLn stderr ("the prelude did not certify: " <> e) *> exitFailure) pure prelude
  oks <- mapM (checkFile p (dumpCore opts)) (files opts)
  if and oks then exitSuccess else exitFailure

commandP :: Parser Command
commandP =
  hsubparser $
    command "check" $
      info (Check <$> checkP) (progDesc "Check modules of the surface language, printing every report; fail when one has an error")

checkP :: Parser CheckOptions
checkP = do
  dump <-
    switch $
      long "dump-core"
        <> help "Print the core text generated, prf definitions and pra declarations, before the reports"
  paths <-
    some . strArgument $
      metavar "FILE.px..."
        <> action "file"
        <> help "The modules to check"
  pure CheckOptions {dumpCore = dump, files = paths}

versionP :: Parser (a -> a)
versionP = infoOption (showVersion version) (long "version" <> help "Show the version")

-- | Check a file, printing what was generated when asked and every report; whether it has no error.
checkFile :: Prelude -> Bool -> FilePath -> IO Bool
checkFile p dump path = do
  src <- TIO.readFile path
  let result = checkSource p path src
  when dump $ mapM_ TIO.putStrLn (checkedCore result)
  mapM_ (TIO.putStrLn . render) (checkedReports result)
  pure (all ((/= SevError) . reportSeverity) (checkedReports result))
  where
    render (Report (Span (l, c) _) sev msg) =
      T.pack (path <> ":" <> show l <> ":" <> show c <> ": " <> severity sev <> ": ") <> msg
    severity = \case
      SevError -> "error"
      SevInfo -> "info"
