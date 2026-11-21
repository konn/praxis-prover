module Main (main) where

import Control.Monad (unless)
import Data.Proxy (Proxy (..))
import Data.Text qualified as T
import Development.Shake
import Development.Shake.FilePath
import Network.Wai (Application)
import Network.Wai.Handler.Warp (Port, run)
import Servant (Raw, Server, serve, serveDirectoryWith)
import System.Console.GetOpt (ArgDescr (..), OptDescr (..))
import System.Directory qualified as Dir
import Text.Read (readMaybe)
import WaiAppStatic.Storage.Filesystem (defaultWebAppSettings)
import WaiAppStatic.Types (MaxAge (..), StaticSettings (..), unsafeToPiece)

data Flag
  = FlagPort !Port
  | FlagDirectory !FilePath
  deriving stock (Eq, Show)

options :: [OptDescr (Either String Flag)]
options =
  [ Option
      "p"
      ["port"]
      (ReqArg parsePort "PORT")
      "TCP port for the `serve` target (default: 8080)."
  , Option
      "d"
      ["directory"]
      (ReqArg (Right . FlagDirectory) "DIR")
      "Directory served by the `serve` target (default: _build/browser)."
  ]
  where
    parsePort raw =
      case readMaybe raw of
        Just port | port > 0 && port <= 65535 -> Right (FlagPort port)
        _ -> Left ("invalid port: " <> raw)

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

serveBrowser :: Port -> FilePath -> IO ()
serveBrowser port directory = run port (browserApp directory)

main :: IO ()
main = do
  homeDirectory <- Dir.getHomeDirectory
  shakeArgsWith shakeOptions {shakeFiles = "_build/shake"} options $ \flags targets -> pure . Just $ do
    let servePort = foldl' (\acc flag -> case flag of FlagPort p -> p; _ -> acc) defaultPort flags
        (customDirectory, serveDirectory) =
          foldl'
            (\acc flag -> case flag of FlagDirectory d -> (True, d); _ -> acc)
            (False, defaultBrowserDirectory)
            flags
        rules = do
          want ["browser"]
          phony "clean" $ removeFilesAfter "_build" ["//*"]
          phony "toolchain" $ command_ [] "bash" ["ci/scripts/setup-wasm.sh"]
          let withWasmPath =
                AddPath
                  [ homeDirectory </> ".ghcup/bin"
                  , homeDirectory </> ".ghc-wasm/wasm-run/bin"
                  , homeDirectory </> ".ghc-wasm/wasmtime/bin"
                  , homeDirectory </> ".ghc-wasm/wasi-sdk/bin"
                  ]
                  []
              generated = "praxis-wasm/generated/Extracted.hs"
              certificate = "_build/othello/Extracted.hs"
          certificate %> \target -> do
            sources <- getDirectoryFiles "" ["praxis/data/libraries/base/src//*.px", "praxis/data/libraries/othello/src//*.px", "praxis/src//*.hs", "praxis-copra/src//*.hs", "praxis-runtime/src//*.hs"]
            need (sources <> ["praxis/praxis.cabal", "praxis-runtime/praxis-runtime.cabal"])
            command_
              []
              "cabal"
              [ "run"
              , "--disable-documentation"
              , "praxis:exe:praxis"
              , "--"
              , "extract"
              , "praxis/data/libraries/othello/src/Game/Othello/Browser.px"
              , "--entry"
              , "othello.Game.Othello.Browser.play"
              , "--output"
              , target
              , "+RTS"
              , "-N1"
              , "-M12G"
              , "-RTS"
              ]
          let bundle output = do
                need [generated, "cabal-wasm.project", "praxis-wasm/praxis-wasm.cabal", "praxis-wasm/app/Main.hs", "web/othello/package-lock.json"]
                command_ [withWasmPath] compiler ["--version"]
                let args = ["--project-file=cabal-wasm.project", "--builddir=_build/dist-wasm"]
                command_ [withWasmPath] "cabal" (args <> ["build", "praxis-wasm", "--disable-documentation"])
                Stdout binary <- command [withWasmPath] "cabal" (args <> ["list-bin", "praxis-wasm"])
                Stdout libdir <- command [withWasmPath] compiler ["--print-libdir"]
                liftIO $ Dir.createDirectoryIfMissing True output
                copyFile' (trim binary) (output </> "praxis.wasm")
                command_ [withWasmPath] "node" [trim libdir </> "post-link.mjs", "--input", output </> "praxis.wasm", "--output", output </> "ghc_wasm_jsffi.js"]
                command_ [Cwd "web/othello"] "npm" ["ci", "--ignore-scripts"]
                files <- getDirectoryFiles "web/othello" ["*.html", "*.css", "*.js"]
                mapM_ (\f -> copyFile' ("web/othello" </> f) (output </> f)) files
                copyFile' "web/othello/package.json" (output </> "package.json")
                vendor <- getDirectoryFiles "web/othello/node_modules/@bjorn3/browser_wasi_shim" ["dist//*.js"]
                mapM_ (\f -> copyFile' ("web/othello/node_modules/@bjorn3/browser_wasi_shim" </> f) (output </> "vendor" </> f)) vendor
          phony "wasm" $ bundle "_build/wasm"
          phony "browser" $ do
            need [certificate]
            copyFile' certificate generated
            bundle defaultBrowserDirectory
            putInfo "Browser app built in _build/browser. Run `cabal run shake-praxis -- serve` to serve it over HTTP."
          phony "serve" $ do
            hasBundle <-
              liftIO $
                (&&)
                  <$> Dir.doesFileExist (serveDirectory </> "index.html")
                  <*> Dir.doesFileExist (serveDirectory </> "praxis.wasm")
            unless (customDirectory || hasBundle) $ need ["browser"]
            exists <- liftIO $ Dir.doesDirectoryExist serveDirectory
            unless exists $
              fail ("Browser bundle directory does not exist: " <> serveDirectory)
            putInfo ("Serving " <> serveDirectory <> " at http://localhost:" <> show servePort)
            liftIO $ serveBrowser servePort serveDirectory
    if null targets then rules else want targets >> withoutActions rules

compiler :: String
compiler = "wasm32-wasi-ghc-9.12.4.20260402"

trim :: String -> String
trim = T.unpack . T.strip . T.pack
