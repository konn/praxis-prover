{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Main (main) where

import Control.Lens ((^?))
import Control.Lens.Extras (is)
import Data.Hashable (hash)
import Data.Sized (pattern Nil, pattern (:<))
import Data.Type.Ordinal (od)
import Language.Praxis.PRA.Equality
import Language.Praxis.PRA.PrimitiveRecursion hiding (suc)
import Language.Praxis.PRA.PrimitiveRecursion.Examples
import Language.Praxis.PRA.ProofTest (proofTests)
import Language.Praxis.PRA.Syntax
import Numeric.Natural
import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main =
  defaultMain $
    testGroup
      "praxis-core"
      [ primitiveRecursionTests
      , evalableTermTests
      , canonicalTermTests
      , normalizeTests
      , defEqTests
      , fuelTests
      , proofTests
      ]

-- | Every term below is closed, so no environment is ever consulted.
noFreeVars :: String -> Natural
noFreeVars v = error $ "unexpected free variable: " <> v

primitiveRecursionTests :: TestTree
primitiveRecursionTests =
  testGroup
    "evalPRFCode"
    [ testCase "Succ is the successor, not the identity" $
        evalPRFCode Succ (3 :< Nil) @?= (4 :: Natural)
    , testCase "Zero is constant at every arity" $
        evalPRFCode Zero (7 :< 8 :< Nil) @?= (0 :: Natural)
    , testCase "Proj selects" $
        evalPRFCode (Proj [od|1|]) (7 :< 8 :< Nil) @?= (8 :: Natural)
    , testCase "pred" $
        map (\n -> evalPRFCode predC (n :< Nil)) [0 .. 4] @?= ([0, 0, 1, 2, 3] :: [Natural])
    , testCase "plus" $
        [evalPRFCode plus (y :< x :< Nil) | y <- range, x <- range]
          @?= [y + x | y <- range, x <- range]
    , testCase "mult" $
        [evalPRFCode mult (y :< x :< Nil) | y <- range, x <- range]
          @?= [y * x | y <- range, x <- range]
    , testCase "expo" $
        [evalPRFCode expo (y :< x :< Nil) | y <- range, x <- range]
          @?= [x ^ y | y <- range, x <- range]
    ]
  where
    range = [0 .. 3] :: [Natural]

evalableTermTests :: TestTree
evalableTermTests =
  testGroup
    "Evalable (Term a)"
    [ testCase "_Zero matches a literal zero" $
        is _Zero (Lit 0 :: Term String) @?= True
    , testCase "_Zero matches a nullary application of Zero" $
        is _Zero (Zero :$ Nil :: Term String) @?= True
    , testCase "_Zero matches an application of Zero at a higher arity" $
        is _Zero (Zero :$ (Var "x" :< Nil)) @?= True
    , testCase "_Zero rejects a non-zero literal" $
        is _Zero (Lit 1 :: Term String) @?= False
    , testCase "_Zero rejects a variable" $
        is _Zero (Var "x") @?= False
    , testCase "_Succ peels a literal" $
        (Lit 3 :: Term String) ^? _Succ @?= Just (Lit 2)
    , testCase "_Succ rejects zero" $
        (Lit 0 :: Term String) ^? _Succ @?= Nothing
    , testCase "_Succ peels a symbolic successor" $
        (Succ :$ (Var "x" :< Nil)) ^? _Succ @?= Just (Var "x")
    , testCase "suc canonicalises numerals to Lit" $
        suc (Lit 3 :: Term String) @?= Lit 4
    , testCase "suc keeps open terms symbolic" $
        suc (Var "x") @?= Succ :$ (Var "x" :< Nil)
    , testCase "zero is a literal" $
        zero @?= (Lit 0 :: Term String)
    ]

normalizeTests :: TestTree
normalizeTests =
  testGroup
    "normalize"
    [ testCase "closed terms reduce to a literal" $
        normalize (plus :$ (Lit 2 :< Lit 3 :< Nil) :: Term String) @?= Lit 5
    , testCase "nested closed terms reduce to a literal" $
        normalize (mult :$ (Lit 3 :< (plus :$ (Lit 2 :< Lit 2 :< Nil)) :< Nil) :: Term String)
          @?= Lit 12
    , testCase "an application of Zero reduces to a literal" $
        normalize (Zero :$ (Var "x" :< Nil)) @?= Lit 0
    , testCase "a numeral recursion argument unrolls over a variable" $
        normalize (plus :$ (Lit 2 :< Var "x" :< Nil))
          @?= Succ :$ ((Succ :$ (Var "x" :< Nil)) :< Nil)
    , testCase "plus 0 is the identity" $
        normalize (plus :$ (Lit 0 :< Var "x" :< Nil)) @?= Var "x"
    , testCase "a variable recursion argument is left as a residual" $
        normalize (plus :$ (Var "y" :< Lit 1 :< Nil))
          @?= plus :$ (Var "y" :< Lit 1 :< Nil)
    , testCase "arguments are normalized even under a residual" $
        normalize (plus :$ (Var "y" :< (plus :$ (Lit 1 :< Lit 1 :< Nil)) :< Nil))
          @?= plus :$ (Var "y" :< Lit 2 :< Nil)
    , testCase "normalization preserves the denotation of a closed term" $
        toNatural (normalize (expo :$ (Lit 3 :< Lit 3 :< Nil) :: Term String)) @?= Just 27
    ]

defEqTests :: TestTree
defEqTests =
  testGroup
    "defEq"
    [ testCase "is reflexive on open terms" $
        defEq (plus :$ (Var "y" :< Var "x" :< Nil)) (plus :$ (Var "y" :< Var "x" :< Nil))
          @?= True
    , testCase "identifies a closed term with its value" $
        defEq (mult :$ (Lit 3 :< Lit 4 :< Nil)) (Lit 12 :: Term String) @?= True
    , testCase "separates distinct closed terms" $
        defEq (mult :$ (Lit 3 :< Lit 4 :< Nil)) (Lit 11 :: Term String) @?= False
    , testCase "identifies open terms with a common normal form" $
        defEq
          (plus :$ (Lit 2 :< Var "x" :< Nil))
          (Succ :$ ((Succ :$ (Var "x" :< Nil)) :< Nil))
          @?= True
    , testCase "separates distinct variables" $
        defEq (Var "x") (Var "y") @?= False
    , testCase "is incomplete: commutativity is not decided by reduction" $
        defEq (plus :$ (Var "x" :< Lit 1 :< Nil)) (plus :$ (Lit 1 :< Var "x" :< Nil))
          @?= False
    , testCase "defEqAtomic agrees with defEq" $
        defEqAtomic (plus :$ (Lit 2 :< Lit 3 :< Nil) :=== (Lit 5 :: Term String)) @?= True
    ]

fuelTests :: TestTree
fuelTests =
  testGroup
    "Fuel"
    [ testCase "an exhausted budget leaves the application residual" $
        normalizeWith (Limited 1) (plus :$ (Lit 2 :< Lit 3 :< Nil) :: Term String)
          @?= plus :$ (Lit 2 :< Lit 3 :< Nil)
    , testCase "an exhausted budget only ever makes defEq fail" $
        defEqWith (Limited 1) (plus :$ (Lit 2 :< Lit 3 :< Nil)) (Lit 5 :: Term String)
          @?= False
    , testCase "an unlimited budget decides the same equation" $
        defEqWith Unlimited (plus :$ (Lit 2 :< Lit 3 :< Nil)) (Lit 5 :: Term String)
          @?= True
    , testCase "every partial evaluation denotes the same number" $
        [ evalTerm noFreeVars $
            normalizeWith (Limited n) (expo :$ (Lit 3 :< Lit 3 :< Nil))
        | n <- [0 .. 40]
        ]
          @?= replicate 41 (27 :: Natural)
    , testCase "evalTerm resolves free variables" $
        evalTerm (const 4) (plus :$ (Lit 2 :< Var "x" :< Nil)) @?= 6
    , testCase "toNatural rejects open terms" $
        toNatural (plus :$ (Lit 2 :< Var "x" :< Nil)) @?= Nothing
    ]

{- |
'Term' has two spellings for a numeral — @'Lit' (n + 1)@ and
@'Succ' ':$' ['Lit' n]@, and @'Lit' 0@ and @'Zero' ':$' _@ — and equality
identifies them, so a rule which builds one meets a context which spells it the
other way.  Equality must not go further and /reduce/: that is
'Language.Praxis.PRA.Equality.defEq'\'s job, and the @Defeq@ rule's, and a
proof which could bypass it would be unsound.
-}
canonicalTermTests :: TestTree
canonicalTermTests =
  testGroup
    "canonical terms"
    [ testCase "a successor of a numeral is the next numeral" $
        (Lit 4 :: Term String) == Succ :$ (Lit 3 :< Nil) @?= True
    , testCase "an application of Zero is zero at every arity" $
        (Zero :$ (Var "x" :< Nil) :: Term String) == Lit 0 @?= True
    , testCase "canonicalisation reaches under a residual application" $
        (Proj [od|0|] :$ ((Succ :$ (Lit 3 :< Nil)) :< Nil) :: Term String)
          == (Proj [od|0|] :$ (Lit 4 :< Nil))
          @?= True
    , testCase "hashing agrees with equality, so contexts merge the two spellings" $
        hash (Lit 4 :: Term String) == hash (Succ :$ (Lit 3 :< Nil) :: Term String) @?= True
    , testCase "equality does NOT reduce a redex to its value" $
        (Proj [od|0|] :$ (Lit 7 :< Nil) :: Term String) == Lit 7 @?= False
    , testCase "but defEq still decides that redex" $
        defEq (Proj [od|0|] :$ (Lit 7 :< Nil) :: Term String) (Lit 7) @?= True
    ]
