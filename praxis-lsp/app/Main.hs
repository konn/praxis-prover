module Main (main) where

import Data.Version (showVersion)
import Language.Praxis.LSP (runPraxisServer)
import Options.Applicative
import Paths_praxis_lsp (version)
import System.Exit (exitWith)

main :: IO ()
main = do
  _ <- execParser (info (stdioP <**> versionP <**> helper) (fullDesc <> header "praxis-lsp - a language server for the files of praxis" <> progDesc "Serve .px, .pra and .prf documents over standard input and output"))
  runPraxisServer >>= exitWith

{- |
Standard input and output is the only transport; the flag is accepted
because language clients pass it when they start an executable server.
-}
stdioP :: Parser Bool
stdioP = switch (long "stdio" <> help "Talk to the client over standard input and output (the default, and the only transport)")

versionP :: Parser (a -> a)
versionP = infoOption (showVersion version) (long "version" <> help "Show the version")
