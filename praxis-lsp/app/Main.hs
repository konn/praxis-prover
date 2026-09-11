module Main (main) where

import Language.Praxis.LSP (runPraxisServer)
import System.Exit (exitWith)

main :: IO ()
main = runPraxisServer >>= exitWith
