{-# LANGUAGE TemplateHaskell #-}

module Language.Praxis.PRA.ReplayTest (replayTests) where

import Control.Monad (foldM, forM_)
import Data.Foldable (toList)
import Data.Functor.Foldable (cata, embed)
import Data.Hashable (Hashable)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Multiset qualified as MS
import Language.Praxis.PRA.Certificate
import Language.Praxis.PRA.PrimitiveRecursion (builtin)
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.Proof.Transform (identityProof)
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Tactic
import Language.Praxis.PRA.Tactic.Parser
import Language.Praxis.PRA.Tactic.Quote
import Test.Tasty
import Test.Tasty.HUnit

$(praFile "test/data/replay.pra")

replayTests :: TestTree
replayTests = withResource load (const (pure ())) $ \get ->
  testGroup
    "instantiation preservation"
    [ testCase "capture-sensitive substitution agrees with export" $ do
        known <- get
        forM_ terms $ \t -> forM_ terms $ \s -> forM_ contexts $ \g ->
          agrees known "replaySymm" [ArgTerm t, ArgTerm s, ArgCtx g] [] (replaySymm t s g)
    , testCase "formula identity expands every connective" $ do
        known <- get
        forM_ formulas $ \f -> forM_ contexts $ \g ->
          agrees known "replayId" [ArgForm f, ArgCtx g] [] (replayId f g)
    , testCase "premise weakening preserves the exact multiset" $ do
        known <- get
        forM_ terms $ \t -> forM_ contexts $ \g -> do
          let p = Id (t :=== Lit 0) g
          agrees known "replayWeaken" [ArgTerm t, ArgCtx g] [mapProof p] (replayWeaken t g p)
    , testCase "induction instantiation preserves its eigencondition" $ do
        known <- get
        forM_ ["n", "x", "x'"] $ \n -> do
          let t = Lit 3
              f = Atm (Var n :=== Var n)
              z = Atm (Lit 0 :=== Lit 0)
              sn = suc (Var n)
              base = Defeq (Lit 0) (Lit 0) (Id (Lit 0 :=== Lit 0) MS.empty)
              step = Defeq sn sn (Id (sn :=== sn) (multiset [f]))
          agrees known "replayInd" [ArgVar n, ArgTerm t, ArgCtx MS.empty, ArgForm f] [mapProof base, mapProof step] (replayInd n t MS.empty f base step)
          let cert = known Map.! "replayInd"
              bad = Appeal "replayInd" (map mapArg [ArgVar n, ArgTerm (Var n), ArgCtx MS.empty, ArgForm f]) [] MS.empty
          case replayCertificate environment cert bad [mapProof (identityProof MS.empty z), mapProof step] of
            Left NotEigen {} -> pure ()
            other -> assertFailure ("eigenvariable escape was not rejected: " <> show other)
    , testCase "compiled and nested lambdas substitute closed and captured functions" $ do
        known <- get
        forM_ ["n", "x"] $ \n -> forM_ [Lit 0, Lit 1, Var n, suc (Var n), Var "captured", suc (Var "x")] $ \body -> do
          let f = abstraction [n] body
          agrees known "replayClosure" [ArgVar n, ArgFun f] [] (replayClosure n f)
          agrees known "replayNested" [ArgVar n, ArgFun f] [] (replayNested n f)
    , testCase "free-variable substitution respects binders in separate branches" $ do
        known <- get
        let cert = known Map.! "replayShadowed"
            call = Appeal "replayShadowed" [] [(Obj "n", Lit 2)] MS.empty
        (_, expected) <- right (instantiateLemma builtin (certificateLemma cert) call)
        proof <- right (replayCertificate environment cert call [])
        inferConclusionIn (envKernel environment) proof @?= Right expected
        actual <- right (inferConclusionIn (envKernel environment) (replayShadowedAt :: Proof String))
        mapSequent actual @?= expected
        forM_ terms $ \t -> agrees known "replayFixed" [ArgTerm t] [] (replayFixed t)
    , testCase "premise-local names do not fix internal induction variables" $ do
        known <- get
        forM_ terms $ \t -> do
          let cert = known Map.! "replayLocalFresh"
              call = Appeal "replayLocalFresh" [mapArg (ArgTerm t)] [] MS.empty
          (premises, _) <- right (instantiateLemma builtin (certificateLemma cert) call)
          ps <- traverse proveReflexive premises
          agrees known "replayLocalFresh" [ArgTerm t] ps (replayLocalFresh t reflex)
    , testCase "quantified premise variables stay apart from captured arguments" $ do
        known <- get
        forM_ terms $ \t -> do
          let n = "n"
              f = abstraction [n] (suc (Var "x"))
              args = [ArgVar n, ArgFun f, ArgTerm t]
              cert = known Map.! "replayLocalFunction"
              call = Appeal "replayLocalFunction" (map mapArg args) [] MS.empty
          (premises, _) <- right (instantiateLemma builtin (certificateLemma cert) call)
          ps <- traverse proveReflexive premises
          agrees known "replayLocalFunction" args ps (replayLocalFunction n f t (\_ -> reflex (suc (Var "x"))))
        agrees known "replayLocalAt" [] [] replayLocalAt
    ]
  where
    terms = [Lit 0, Lit 1, Var "x", Var "x'", Var "n", suc (Var "x")]
    atom = Atm (Var "x" :=== Lit 0)
    formulas = [atom, Bot, atom :/\ Bot, atom :\/ Bot, atom :==> atom, (atom :==> Bot) :/\ (Bot :\/ atom)]
    contexts = [MS.empty, multiset [atom], multiset [atom, atom, Atm (Var "x'" :=== Var "n")]]
    load = do
      src <- readFile "test/data/replay.pra"
      ds <- right (parseDeclsIn Map.empty (schemaScope builtin) src)
      foldM (\known d -> do cert <- right (checkCertificate environment known d); pure (Map.insert (declName d) cert known)) Map.empty ds
    agrees known name args premises generated = do
      let cert = known Map.! name
          call = Appeal name (map mapArg args) [] MS.empty
      (_, expected) <- right (instantiateLemma builtin (certificateLemma cert) call)
      expanded <- right (replayCertificate environment cert call premises)
      inferConclusionIn (envKernel environment) expanded @?= Right expected
      actual <- right (inferConclusionIn (envKernel environment) generated)
      mapSequent actual @?= expected
    proveReflexive (g :|- Atm (t :=== s)) | t == s = pure (Defeq t s (Id (t :=== s) g))
    proveReflexive s = assertFailure ("not reflexive: " <> show s)

environment :: Env
environment = either (error . show) id (signatureEnv builtin)

right :: (Show e) => Either e a -> IO a
right = either (assertFailure . show) pure

reflex :: (Hashable a) => Term a -> Proof a
reflex t = Defeq t t (Id (t :=== t) MS.empty)

mapSequent :: Sequent String -> Sequent SchemaName
mapSequent (g :|- f) = multiset (map (fmap Obj) (toList g)) :|- fmap Obj f

mapArg :: Arg String -> Arg SchemaName
mapArg = \case
  ArgVar v -> ArgVar (Obj v)
  ArgTerm t -> ArgTerm (fmap Obj t)
  ArgFun f -> ArgFun (fmap Obj f)
  ArgAtom a -> ArgAtom (fmap Obj a)
  ArgForm f -> ArgForm (fmap Obj f)
  ArgCtx g -> ArgCtx (multiset (map (fmap Obj) (toList g)))

mapProof :: Proof String -> Proof SchemaName
mapProof = cata \step ->
  let (args, subs) = stepFields step
   in embed (fromMaybe (error "mapping names changed rule field sorts") (mkStep (ruleName step) (map mapArg args) subs))

multiset :: (Hashable a) => [a] -> MS.Multiset a
multiset = foldr MS.insertOne MS.empty
