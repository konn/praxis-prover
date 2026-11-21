module Main (main) where

import Data.Text qualified as T
import Development.Shake
import Development.Shake.FilePath
import System.Directory (createDirectoryIfMissing, getHomeDirectory)

main :: IO ()
main = do
  homeDirectory <- getHomeDirectory
  shakeArgs shakeOptions {shakeFiles = "_build/shake"} $ do
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
          liftIO $ createDirectoryIfMissing True output
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
      bundle "_build/browser"
      putInfo "Browser app built in _build/browser. Serve this directory over HTTP."

compiler :: String
compiler = "wasm32-wasi-ghc-9.12.4.20260402"

trim :: String -> String
trim = T.unpack . T.strip . T.pack
