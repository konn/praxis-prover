module Main (main) where

import Control.Monad (when)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Prelude
import Language.Praxis.Surface.Syntax.Raw (Span (..))
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitFailure, exitSuccess, exitWith)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main =
  getArgs >>= \case
    "check" : rest -> do
      let dump = "--dump-core" `elem` rest
          files = filter (/= "--dump-core") rest
      p <- either (\e -> hPutStrLn stderr ("the prelude did not certify: " <> e) *> exitFailure) pure prelude
      oks <- mapM (checkFile p dump) files
      if and oks then exitSuccess else exitFailure
    _ -> hPutStrLn stderr "usage: praxis check [--dump-core] FILE.px…" *> exitWith (ExitFailure 2)

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
