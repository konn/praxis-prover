{-# LANGUAGE OverloadedStrings #-}

-- | The checker, end to end: what certifies, and what must not.
module Language.Praxis.Surface.CheckTest (checkTests) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Prelude (Prelude, prelude)
import Language.Praxis.Surface.Syntax.Raw (Span (..))
import Test.Tasty
import Test.Tasty.HUnit

checkTests :: TestTree
checkTests =
  testGroup
    "checker"
    [ testCase "the List example certifies, in the functional and the tactic style" $ do
        c <- checkFile "test/data/list.px"
        errors c @?= []
        checkedTheorems c @?= ["Data.List.append-nil", "Data.List.append-nil-tactically"]
    , testCase "the FOL example's data types are encoded, and their lemmas certify" $ do
        c <- checkFile "test/data/fol.px"
        errors c @?= []
    , testCase "a false theorem, a non-structural recursion, a sorry and an appeal to a failed theorem are refused" $ do
        c <- checkFile "test/data/bad.px"
        checkedTheorems c @?= []
        let lines' = [l | Report (Span (l, _) _) SevError _ <- checkedReports c]
        mapM_ (\(n, ls) -> assertBool ("an error for " <> n) (any (`elem` lines') ls)) [("wrong", [13 .. 19]), ("loop", [22 .. 24]), ("unfinished", [27, 28]), ("uses", [31, 32])]
        assertBool "the non-structural call is named" (any ("recursive call" `T.isInfixOf`) (map reportMessage (checkedReports c)))
        assertBool "sorry shows its goal" (any ("sorry" `T.isInfixOf`) (map reportMessage (checkedReports c)))
    ]

checkFile :: FilePath -> IO Checked
checkFile path = do
  p <- either assertFailure pure prelude
  src <- TIO.readFile path
  pure (check p path src)
  where
    check :: Prelude -> FilePath -> Text -> Checked
    check = checkSource

-- | The errors, rendered with their lines, for a readable failure.
errors :: Checked -> [String]
errors c = [show l <> ": " <> T.unpack m | Report (Span (l, _) _) SevError m <- checkedReports c]
