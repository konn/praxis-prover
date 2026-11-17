{-# LANGUAGE CPP #-}

module Main (main) where

import Extracted (program)
import Language.Praxis.Runtime (evaluateJSONText)

#if defined(wasm32_HOST_ARCH)
import Data.Text qualified as T
import GHC.Wasm.Prim (JSString (..), fromJSString, toJSString)

foreign export javascript "praxis_eval" evaluateJSON :: JSString -> IO JSString

evaluateJSON :: JSString -> IO JSString
evaluateJSON input = pure . toJSString . T.unpack $ evaluateJSONText 5000000 program (T.pack (fromJSString input))

main :: IO ()
main = pure ()
#else
-- The identical Haskell target is executable natively for differential tests.
import Data.Text.IO qualified as TIO
import System.IO (isEOF)

main :: IO ()
main = do
  done <- isEOF
  if done then pure () else do
    input <- TIO.getLine
    TIO.putStrLn (evaluateJSONText 5000000 program input)
    main
#endif
