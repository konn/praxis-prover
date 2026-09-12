{- |
Coverage for the bounded quantifiers, @∀ i < t. A@ and @∃ i < t. A@, the codes
of formulas they are built from, and the tactics @reflect@ and @reify@ which
prove a formula and the truth of its code equivalent, by the reflection lemmas
of the library, "Language.Praxis.PRA.Library".
-}
module Language.Praxis.PRA.QuantifierTest (quantifierTests) where

import Control.Exception (displayException)
import Control.Monad (forM_)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Language.Praxis.PRA.Library (certifiedLibrary, libraryScope)
import Language.Praxis.PRA.PrimitiveRecursion (builtin)
import Language.Praxis.PRA.Reflection (decodeFormula, encodeFormula)
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Syntax.Parser
import Language.Praxis.PRA.Syntax.Pretty
import Language.Praxis.PRA.Tactic
import Language.Praxis.PRA.Tactic.Parser
import Language.Praxis.PRA.Tactic.Quote (SchemaName, checkDecl, renderSchemaTacticError, schemaScope)
import System.IO (IOMode (ReadMode), hGetContents', hSetEncoding, utf8, withFile)
import Test.Tasty
import Test.Tasty.HUnit

quantifierTests :: TestTree
quantifierTests =
  testGroup
    "bounded quantifiers and reflection"
    [ testCase "the library certifies, and states the lemmas the tactics appeal to" $ do
        library <- either assertFailure pure certifiedLibrary
        forM_ ["belowIntro", "belowUse", "belowElim", "existsUse", "muLe", "muMin", "muHit", "muLeast", "conjIntro", "disjElim", "impIntro", "eqOne", "belowOne", "pairSurj"] \n ->
          assertBool n (Map.member n library)
    , testCase "the examples of the quantifiers and of reflection certify" $ do
        source <- withFile "test/data/examples.pra" ReadMode \h -> hSetEncoding h utf8 *> hGetContents' h
        certifies [source]
    , testCase "a bounded quantifier is holdsBelow, or mu below its bound, at the code of its body" $ do
        formula "∀ i < t. i < S t" @?= formula "holdsBelow {λ i y. i < y} t (S t) = 1"
        formula "forall i < t. i < S t" @?= formula "∀ i < t. i < S t"
        formula "∃ i < t. 2 < i" @?= formula "mu {λ i y. y < i} t 2 < t"
        formula "exists i < t. 2 < i" @?= formula "∃ i < t. 2 < i"
        formula "∀ i < t. i < x /\\ x < 5" @?= formula "holdsBelow {λ i y z. conj (i < y) z} t x (x < 5) = 1"
        formula "∀ i < t. 0 < sgn i" @?= formula "holdsBelow {sgn} t = 1"
        formula "(∀ i < t. i < x) = 1" @?= formula "∀ i < t. i < x"
        formula "((∃ i < t. 0 < i))" @?= formula "∃ i < t. 0 < i"
        either (assertFailure . displayException) (\a -> Atm a @?= formula "∃ i < t. 0 < i") (parseAtomic sc "(∃ i < t. 0 < i)")
    , testCase "⟦A⟧ is the code of A within a term" $ do
        formula "0 < ⟦x < y /\\ y < z⟧" @?= formula "0 < conj (x < y) (y < z)"
        formula "0 < [[x = y ==> _|_]]" @?= formula "0 < imp (x == y) 0"
    , testCase "a wildcard in the body of a quantifier pattern is captured" $
        either (assertFailure . displayException) (const (pure ())) (parseAtomicPattern sc "∃ i < t. i < _")
    , testCase "an abstract function may stand anywhere in the body of a quantifier" $
        certifies
          [ "rule plusOne (n : var) (t u : term) (Γ : ctx) (p(n) : term) : ∀ i < t. 0 < p(i) + 1, u < t, Γ |- 0 < p(u) + 1 by exact belowElim _ t u"
          , "rule muOf (n : var) (t : term) (Γ : ctx) (p(n) : term) : ∀ i < t. 0 < mu {p} i, Γ |- ∀ i < t. 0 < mu {p} i by assumption"
          ]
    , testCase "the binder shadows every name, and a body extends as far right as it can" $ do
        formula "∀ lt < t. lt < x" @?= formula "∀ i < t. i < x"
        formula "∀ i < t. i < x /\\ x = 0" @?= formula "holdsBelow {λ i y z. conj (i < y) z} t x (x == 0) = 1"
        formula "(∀ i < t. i < x) /\\ x = 0" @?= (formula "∀ i < t. i < x" /\ formula "x = 0")
    , testCase "a quantifier is shown as it is written, and reads back" $ do
        shown "∀ i < t. i < S t" @?= "∀ i < t. i < S t"
        shown "∃ i < t. 2 < i" @?= "∃ i < t. 2 < i"
        shown "(∀ i < t. i < x) /\\ ~(∃ j < x. j = t)" @?= "(∀ i < t. i < x) /\\ ~(∃ i < x. i = t)"
        shown "∀ i < t. ∀ j < i. j < t" @?= "∀ i < t. ∀ j < i. j < t"
        forM_
          [ "∀ i < t. i < S t"
          , "(∀ i < t. i < x) /\\ ~(∃ i < x. i = t)"
          , "∀ i < t. ∀ j < i. j < t"
          , "~∃ i < t. 0 < i + x"
          , "x = 0 /\\ ∃ i < t. i == x"
          , "∀ i < t. 0 < mu {sgn} i"
          , "∀ i < t. ∀ j < i. 0 < sgn j"
          , "∀ i < t. 0 < S i"
          , "(∃ i < t. 1) = 1"
          , "(∀ i < t. 1) = 1"
          , "0 < (∃ i < t. i + x) + 1"
          , "holdsBelow {lt} t x = 1"
          , "mu {lt} 3 0 < 3"
          , "((∃ i < t. 0 < i))"
          ]
          \src -> formula (shown src) @?= formula src
    , testCase "substituting in a quantifier is substituting in what it captures, so it reads as it is shown" $ do
        let f = subst "t" (suc (Var "m")) (formula "∀ i < t. i < S t")
        renderFormula builtin id f @?= "∀ i < S m. i < S (S m)"
        formula (renderFormula builtin id f) @?= f
        let g = subst "x" (Lit 3) (formula "∀ i < t. i < x")
        renderFormula builtin id g @?= "∀ i < t. i < 3"
        formula (renderFormula builtin id g) @?= g
    , testCase "a formula is what its code decodes to" $
        forM_ ["x < y /\\ y = z", "~(x = 0) \\/ 0 < y", "x = 0 ==> _|_", "∀ i < t. i < x", "∃ i < t. i < x", "0 < x + y"] \src -> do
          let f = formula src
          code <- either assertFailure pure (encodeFormula builtin (const False) f)
          decodeFormula builtin code @?= Just f
    , testCase "reflect and reify prove a formula and the truth of its code equivalent" $
        certifies
          [ "theorem a : x < y /\\ y < z |- 0 < conj (x < y) (y < z) by reify H1; assumption"
          , "theorem b : 0 < conj (x < y) (y < z) |- y < z by reflect H1 as K; ConjL on K; assumption"
          , "theorem c : x < y, y < z |- conj (x < y) (y < z) = 1 by reflect; ConjR { assumption } { assumption }"
          , "theorem d : x = y ==> y < z |- 0 < imp (x == y) (y < z) by reify H1; assumption"
          , "theorem e : ∀ i < t. i < x /\\ x < 5, u < t |- u < x by exact belowUse _ t u as Q { reflect Q as R; ConjL on R; assumption }"
          , "theorem f : ∃ i < t. i < x /\\ x < i |- _|_ by exact existsUse _ t as Q { reflect Q as R; ConjL on R as K1 K2; exact ltAsym on K1 K2 }"
          , "theorem reifyGoal : 0 < conj (x < y) (y < z) |- x < y /\\ y < z by reify; assumption"
          , "theorem reflectDisj : 0 < disj (x < y) (y < z) |- x < y \\/ y < z by reflect H1 as K; assumption"
          , "theorem reflectFalse : 0 < conj (x < y) 0 |- _|_ by reflect H1 as K; ConjL on K; assumption"
          , "theorem reflectLe : 0 < (x <= y) |- x <= y by reflect H1 as K; assumption"
          , "theorem reflectBelow : 0 < holdsBelow {sgn} t |- ∀ i < t. 0 < sgn i by reflect H1 as K; assumption"
          , "theorem reflectEq : 0 < (x == y) |- x = y by reflect H1 as K; assumption"
          , "theorem reflectImp : imp (x == y) (y < z) = 1 |- x = y ==> y < z by reflect H1 as K; assumption"
          , "theorem reflectEqGoal : x = y |- (x == y) = 1 by reflect; assumption"
          ]
    , testCase "reflect and reify refuse what they cannot do" $ do
        let nothing = \case NothingToReflect _ -> True; _ -> False
            missing = \case ReflectionLemma "conjIntro" -> True; _ -> False
            noCode = \case NoCode _ -> True; _ -> False
        refusedWith nothing [] "theorem g : x = 1 |- x = 1 by reflect H1; assumption"
        refusedWith nothing [] "theorem g : x < y |- x < y by reflect H1; assumption"
        refusedWith nothing [] "theorem g : ∀ i < t. i < x |- ∀ i < t. i < x by reflect H1; assumption"
        refusedWith nothing [] "theorem g : 0 < y |- 0 < y by reflect H1; assumption"
        refusedWith missing ["conjIntro"] "theorem g : x < y /\\ y < z |- 0 < conj (x < y) (y < z) by reify H1; assumption"
        refusedWith missing [] "theorem g : x < y /\\ y < z |- 0 < conj (x < y) (y < z) by have conjIntro: (x = x) { refl }; reify H1; assumption"
        refusedWith noCode [] "rule g (A : formula) (Γ : ctx) : A, Γ |- 0 < 1 by reify H1; assumption"
    , testCase "a lemma is appealed to at hypotheses named in any order" $
        certifies
          [ "theorem inOrder : x < y, y < z |- x < z by exact ltTrans on H1 H2"
          , "theorem outOfOrder : y < z, x < y |- x < z by exact ltTrans on H1 H2"
          ]
    , testCase "a quantifier over an application of a function alone is at that function" $
        certifies
          [ "theorem q1 : ∀ i < t. 0 < mu {sgn} i, u < t |- 0 < mu {sgn} u by exact belowElim _ t u"
          , "theorem q2 : ∀ i < t. ∀ j < i. 0 < sgn j, u < t |- 0 < holdsBelow {sgn} u by exact belowElim _ t u"
          , "rule overAbstract (n : var) (t : term) (Γ : ctx) (p(n) : term) : ∀ i < t. 0 < p(i), Γ |- holdsBelow {p} t = 1 by assumption"
          ]
    , testCase "an appeal instantiates a var metavariable of a lemma only where the rule declares it fresh" $ do
        let cv2 = "rule cv2 (m : var) (t : term) (Γ : ctx) (q(m) : term) (step : holdsBelow {q} m = 1, Γ |- 0 < q(m)) : Γ |- 0 < q(t)"
        refusedWith (\case NotDeclaredFresh "m" _ -> True; _ -> False) [] (cv2 <> " by exact cvInduction m t { exact step }")
        results <-
          checked
            [ cv2 <> " where m ∉ Γ, t by exact cvInduction m t { exact step }"
            , "theorem bad : x = 5 |- 0 < (0 == 5) by exact cv2 x 0 { calc (0 < (x == 5)) = (0 < (5 == 5)) by cong H1 = 1 }"
            ]
        map (maybe "certified" (const "refused") . snd) results @?= ["certified", "refused" :: String]
    , testCase "a premise is used under hypotheses it does not state, weakened" $
        certifies ["rule w (a : term) (Γ : ctx) (p : a = 0, Γ |- a = 0) : a = 0, a = 1, Γ |- a = 0 by exact p"]
    ]
  where
    sc = plainScope builtin
    formula = either (error . displayException) id . parseFormula sc
    shown = renderFormula builtin id . formula

    -- Every declaration checked in turn, over the library but the lemmas
    -- hidden, each a lemma for those after it when it certifies.
    checkedWithout :: [String] -> [String] -> IO [(String, Maybe (TacticError SchemaName))]
    checkedWithout hidden srcs = do
      env <- either (assertFailure . displayException) pure (signatureEnv builtin)
      scope <- either assertFailure (pure . (`Map.withoutKeys` Set.fromList hidden)) libraryScope
      decls <- either (assertFailure . displayException) pure (parseDeclsIn (Map.map (map snd . lemmaMetas) scope) (schemaScope builtin) (unlines srcs))
      let go _ [] = []
          go known (d : ds) = case checkDecl env known d of
            Right (_, lemma) -> (declName d, Nothing) : go (Map.insert (declName d) lemma known) ds
            Left err -> (declName d, Just err) : go known ds
      pure (go scope decls)
    checked = checkedWithout []
    certifies srcs =
      checked srcs >>= mapM_ \(n, result) ->
        maybe (pure ()) (assertFailure . ((n <> ": ") <>) . renderSchemaTacticError builtin) result
    refusedWith :: (Failure SchemaName -> Bool) -> [String] -> String -> Assertion
    refusedWith expected hidden src =
      checkedWithout hidden [src] >>= \case
        [(_, Just err)]
          | expected (errorFailure err) -> pure ()
          | otherwise -> assertFailure ("refused otherwise: " <> renderSchemaTacticError builtin err)
        _ -> assertFailure ("accepted: " <> src)
