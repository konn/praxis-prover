{-# LANGUAGE OverloadedStrings #-}

-- | Admission follows complete checking, including failures after code generation.
module Language.Praxis.Surface.BuiltinCheckTest (builtinCheckTests) where

import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Elab (FunDef (..))
import Language.Praxis.Surface.Engine (Knowledge (..), Spec (..), equationCase)
import Language.Praxis.Surface.Env (Env (..), FunInfo (..), QualName)
import Language.Praxis.Surface.Mangle (mangleGlobal)
import Language.Praxis.Surface.Prelude (prelude)
import Language.Praxis.Surface.Syntax (Expr (..), RelOp (..))
import Language.Praxis.Surface.Syntax.Raw (Segment (..))
import Test.Tasty
import Test.Tasty.HUnit

builtinCheckTests :: TestTree
builtinCheckTests =
  testGroup
    "builtin admission"
    [ testCase "checked declarations activate and are returned through Knowledge" $ do
        checked <- check (finDeclaration <> [pragma "FIN" "Fin"] <> rankDeclaration <> [pragma "FIN_TO_NAT" "rank"] <> boundDeclaration <> [pragma "FIN_TO_NAT_BOUND" "bounded"])
        messages checked @?= []
        Map.keys (active checked) @?= ["FIN", "FIN_TO_NAT", "FIN_TO_NAT_BOUND"]
    , testCase "unknown roles never enter the registry" $ do
        checked <- check (finDeclaration <> [pragma "UNKNOWN_FIN" "Fin"])
        hasError "unknown BUILTIN role" checked
        active checked @?= Map.empty
    , testCase "a role cannot be duplicated or rebound" $ do
        duplicate <- check (finDeclaration <> [pragma "FIN" "Fin", pragma "FIN" "Fin"])
        hasError "already registered" duplicate
        rebound <- check (finDeclaration <> [pragma "FIN" "Fin", "data Other (n : Nat) where", "  MkOther : Other 0", pragma "FIN" "Other"])
        hasError "cannot be rebound" rebound
        Map.lookup "FIN" (active rebound) @?= Just [Ident "BuiltinCheck", Ident "Fin"]
    , testCase "registration follows both declarations and prerequisite roles" $ do
        forward <- check ([pragma "FIN" "Fin"] <> finDeclaration)
        hasError "before this registration" forward
        active forward @?= Map.empty
        missing <- check (finDeclaration <> rankDeclaration <> [pragma "FIN_TO_NAT" "rank"])
        hasError "earlier FIN registration" missing
        active missing @?= Map.empty
    , testCase "class registrations cannot precede their declarations" $ do
        checked <- check [pragma "FINITE" "F", "class F a where", "  identity : a -> a"]
        hasError "declared before its registration" checked
        active checked @?= Map.empty
    , testCase "matching names do not compensate for malformed signatures" $ do
        checked <- check (finDeclaration <> [pragma "FIN" "Fin", "wrong : Nat -> Nat", "wrong x = x", pragma "FIN_TO_NAT" "wrong"])
        hasError "exact dependent function signature" checked
        assertBool "the bad function is not activated" (Map.notMember "FIN_TO_NAT" (active checked))
    , testCase "uncertified bridge claims are not admitted" $ do
        checked <- check (finDeclaration <> [pragma "FIN" "Fin"] <> rankDeclaration <> [pragma "FIN_TO_NAT" "rank", "claimed : (i : Fin n) -> rank i < n", "claimed i = by sorry", pragma "FIN_TO_NAT_BOUND" "claimed"])
        hasError "has not completed checking successfully" checked
        assertBool "the failed theorem is not activated" (Map.notMember "FIN_TO_NAT_BOUND" (active checked))
    , testCase "failed erased evidence prevents function activation" $ do
        checked <-
          check
            ( finDeclaration
                <> [ pragma "FIN" "Fin"
                   , "impossible : 0 < 0 -> Nat"
                   , "impossible h = 0"
                   , "bad : Fin n -> Nat"
                   , "bad i = impossible (by rfl)"
                   , pragma "FIN_TO_NAT" "bad"
                   ]
            )
        hasError "has not completed checking successfully" checked
        assertBool "unchecked proof erasure cannot implement a builtin" (Map.notMember "FIN_TO_NAT" (active checked))
    , testCase "a later contract failure prevents activation even when the body exists" $ do
        p <- either assertFailure pure prelude
        let checked = checkSourceWith rejectRank p "builtin-check.px" (source (finDeclaration <> [pragma "FIN" "Fin"] <> rankDeclaration <> [pragma "FIN_TO_NAT" "rank"]))
        hasError "has not completed checking successfully" checked
        (_, core) <- maybe (assertFailure "no checked module") pure (checkedFinal checked)
        assertBool "the regression reaches the post-definition checking phase" (Map.member (mangleGlobal ["BuiltinCheck", "rank"]) (coreBodies core))
        assertBool "the failed contract keeps the role inactive" (Map.notMember "FIN_TO_NAT" (active checked))
    , testCase "a conditional theorem cannot stand in for the unconditional bound law" $ do
        checked <- check (finDeclaration <> [pragma "FIN" "Fin"] <> rankDeclaration <> [pragma "FIN_TO_NAT" "rank", "weak : (i : Fin n) -> rank i < n -> rank i < n", "weak i h = h", pragma "FIN_TO_NAT_BOUND" "weak"])
        hasError "exact proposition" checked
        assertBool "the weaker statement is not activated" (Map.notMember "FIN_TO_NAT_BOUND" (active checked))
    ]

check :: [Text] -> IO Checked
check declarations = do
  p <- either assertFailure pure prelude
  pure (checkSource p "builtin-check.px" (source declarations))

source :: [Text] -> Text
source declarations = T.unlines ("module BuiltinCheck where" : declarations)

pragma :: Text -> Text -> Text
pragma role target = "{-# BUILTIN " <> role <> " " <> target <> " #-}"

messages :: Checked -> [Text]
messages checked = [message | Report _ SevError message <- checkedReports checked]

hasError :: Text -> Checked -> Assertion
hasError expected checked = assertBool ("expected " <> T.unpack expected <> ": " <> show (messages checked)) (any (expected `T.isInfixOf`) (messages checked))

active :: Checked -> Map.Map Text QualName
active = maybe Map.empty (envBuiltins . knowEnv . fst) . checkedFinal

finDeclaration, rankDeclaration, boundDeclaration :: [Text]
finDeclaration =
  [ "data Fin (n : Nat) where"
  , "  FZero : {n : Nat} -> Fin (S n)"
  , "  FSucc : {n : Nat} -> Fin n -> Fin (S n)"
  ]
rankDeclaration =
  [ "rank : Fin n -> Nat"
  , "rank FZero = 0"
  , "rank (FSucc i) = S (rank i)"
  ]
boundDeclaration =
  [ "bounded : (i : Fin n) -> rank i < n"
  , "bounded FZero = rfl"
  , "bounded (FSucc i) = bounded i"
  ]

rejectRank :: Env -> FunDef -> [Spec]
rejectRank _ fd
  | funQual (fdInfo fd) == [Ident "BuiltinCheck", Ident "rank"] = [Spec "#rejected" (const []) (\_ _ -> Rel RelEq (Nat 0) (Nat 1)) (\_ _ -> []) equationCase]
  | otherwise = []
