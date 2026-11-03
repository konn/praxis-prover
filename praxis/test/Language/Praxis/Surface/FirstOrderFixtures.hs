{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.FirstOrderFixtures (
  FirstOrderFixture (..),
  loadFirstOrderFixture,
) where

import Control.Monad (foldM)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Prelude (prelude)
import Language.Praxis.Surface.Rename (Imports)
import Language.Praxis.Surface.Syntax.Raw (Segment (..))
import Test.Tasty.HUnit

data FirstOrderFixture = FirstOrderFixture
  { firstOrderBuild :: !Build
  , firstOrderImports :: !Imports
  , firstOrderSyntax :: !Checked
  , firstOrderProof :: !Checked
  , firstOrderPeano :: !Checked
  }

loadFirstOrderFixture :: IO FirstOrderFixture
loadFirstOrderFixture = do
  p <- either assertFailure pure prelude
  (build, imports, checked) <- foldM load ((initialBuild p) {buildRetainGeneratedText = False}, Map.empty, []) ["Syntax", "Proof", "Peano"]
  case checked of
    [syntax, proof, peano] -> pure (FirstOrderFixture build imports syntax proof peano)
    _ -> assertFailure "first-order fixture module count changed"
  where
    load (build, imports, results) name = do
      let path = "data/libraries/logic/src/Logic/FirstOrder/" <> T.unpack name <> ".px"
          key = map Ident ["Logic", "FirstOrder", name]
      source <- TIO.readFile path
      let (checked, next) = checkModule (\_ _ -> []) build imports Nothing path source
      [message | Report _ SevError message <- checkedReports checked] @?= []
      exported <- maybe (assertFailure ("missing exports: " <> T.unpack name)) pure (Map.lookup key (buildExports next))
      pure (next, Map.insert (Nothing, key) (Right exported) imports, results <> [checked])
