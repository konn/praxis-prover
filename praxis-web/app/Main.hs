{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}

module Main (main) where

import Control.Monad (unless)
import Data.Proxy (Proxy (..))
import Data.Text qualified as T
import Network.Wai (Application)
import Network.Wai.Handler.Warp (Port, run)
import Options.Applicative
import Servant (Raw, Server, serve, serveDirectoryWith)
import System.Directory (doesDirectoryExist)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Text.Read (readMaybe)
import WaiAppStatic.Storage.Filesystem (defaultWebAppSettings)
import WaiAppStatic.Types (MaxAge (..), StaticSettings (..), unsafeToPiece)

data Options = Options
  { port :: !Port
  , directory :: !FilePath
  }

defaultBrowserDirectory :: FilePath
defaultBrowserDirectory = "_build/browser"

defaultPort :: Port
defaultPort = 8080

type BrowserAPI = Raw

browserAPI :: Proxy BrowserAPI
browserAPI = Proxy

browserServer :: FilePath -> Server BrowserAPI
browserServer directory =
  serveDirectoryWith
    (defaultWebAppSettings directory)
      { ssIndices = [unsafeToPiece (T.pack "index.html")]
      , ssMaxAge = NoCache
      }

browserApp :: FilePath -> Application
browserApp = serve browserAPI . browserServer

optionsP :: Parser Options
optionsP = do
  port <-
    option
      portReader
      ( long "port"
          <> short 'p'
          <> metavar "PORT"
          <> value defaultPort
          <> showDefault
          <> help "TCP port to listen on"
      )
  directory <-
    strOption
      ( long "directory"
          <> short 'd'
          <> metavar "DIR"
          <> value defaultBrowserDirectory
          <> showDefault
          <> help "Directory containing the browser bundle"
      )
  pure Options {..}
  where
    portReader =
      eitherReader $ \raw ->
        case readMaybe raw of
          Just p | p > 0 && p <= 65535 -> Right p
          _ -> Left ("invalid port: " <> raw)

main :: IO ()
main = do
  Options {..} <-
    execParser
      ( info
          (optionsP <**> helper)
          (fullDesc <> header "praxis-web - Servant/Warp static server for Praxis browser applications")
      )
  exists <- doesDirectoryExist directory
  unless exists $ do
    hPutStrLn stderr ("Browser bundle directory does not exist: " <> directory <> " (run `cabal run shake-praxis -- browser` first)")
    exitFailure
  putStrLn ("Serving " <> directory <> " at http://localhost:" <> show port)
  run port (browserApp directory)
