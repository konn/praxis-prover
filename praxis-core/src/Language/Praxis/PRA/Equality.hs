{- | Definitional equality of 'Term's — the trusted check which the
'Language.Praxis.PRA.Syntax.Defeq' rule appeals to.

Two terms are definitionally equal when they denote the same numeral under every
assignment of their free variables, /for reasons the evaluator can see/.  The
check proceeds in two stages:

1. on-the-nose syntactic equality, which is cheap and settles the common case;
2. otherwise both sides are partially evaluated ('normalize') and the results
   are compared.

Partial evaluation runs the ordinary primitive-recursive evaluator
('evalPRFCodeM') on 'Term' itself: applications whose recursion argument is not
a numeral — because it mentions a variable — are simply kept as residual terms,
so evaluation makes as much progress as it can and then stops.

The resulting relation is /sound/ (equal normal forms mean the terms really are
equal) but necessarily /incomplete/ on open terms: no amount of reduction can
establish, say, commutativity of addition.  It is also budgeted by 'Fuel', so it
always terminates promptly even when a closed term denotes an astronomically
large numeral.
-}
module Language.Praxis.PRA.Equality (
  -- * Definitional equality
  defEq,
  defEqWith,
  defEqAtomic,
  defEqAtomicWith,

  -- * Partial evaluation
  normalize,
  normalizeWith,

  -- * Total evaluation
  evalTerm,
  toNatural,

  -- * Evaluation budget
  Fuel (..),
  defaultFuel,
) where

import Control.Monad.Trans.State.Strict (State, evalState, state)
import Data.Void (absurd)
import Language.Praxis.PRA.PrimitiveRecursion
import Language.Praxis.PRA.Syntax
import Numeric.Natural

{- $setup
>>> :seti -XDataKinds -XQuasiQuotes -XPatternSynonyms
>>> import Data.Sized (pattern Nil, pattern (:<))
>>> import Data.Type.Ordinal (od)
>>> import Language.Praxis.PRA.PrimitiveRecursion
>>> import Language.Praxis.PRA.Syntax
>>> :{
-- @plus (y, x) = y + x@, by recursion on @y@.
plus :: PRFCode 2
plus = Rec (Proj [od|0|]) (Comp Succ (Proj [od|1|] :< Nil))
:}
-}

{- | How many reduction steps a partial evaluation may take before it gives up
and leaves the application it is looking at as a residual term.
-}
data Fuel
  = -- | at most this many reduction steps
    Limited !Natural
  | -- | reduce until a normal form is reached
    Unlimited
  deriving (Show, Eq, Ord)

{- | The budget used by 'defEq' and 'normalize'.

Generous enough for the terms which occur in proofs, small enough that a term
denoting @10 ^ 10@ is left partially evaluated rather than unrolled into a
numeral nobody asked for.
-}
defaultFuel :: Fuel
defaultFuel = Limited 100_000

-- | Consumes one reduction step, reporting whether there was any left.
spend :: State Fuel Bool
spend = state \case
  Unlimited -> (True, Unlimited)
  Limited 0 -> (False, Limited 0)
  Limited n -> (True, Limited (n - 1))

{- | Partially evaluates a term with the 'defaultFuel'.

>>> normalize (plus :$ (Lit 2 :< Lit 3 :< Nil) :: Term String)
Lit 5

Sub-terms which mention a variable are reduced as far as they can be and then
left alone, so an open term still makes progress:

>>> normalize (plus :$ (Lit 2 :< Var "x" :< Nil))
Succ :$ [Succ :$ [Var "x"]]
-}
normalize :: Term a -> Term a
normalize = normalizeWith defaultFuel

{- | Partially evaluates a term within the given budget.

Reduction is call-by-value: the arguments of an application are normalized
first, and the application itself is then handed to 'evalPRFCodeM', which either
reduces it or hands it back as a residual.

When the budget runs out the application under consideration is handed back
untouched, so the result is always a term denoting the same number:

>>> normalizeWith (Limited 1) (plus :$ (Lit 2 :< Lit 3 :< Nil) :: Term String)
Rec (Proj #(0 / 1)) (Comp Succ [Proj #(1 / 3)]) :$ [Lit 2,Lit 3]
-}
normalizeWith :: Fuel -> Term a -> Term a
normalizeWith fuel = flip evalState fuel . go
  where
    go t@Var {} = pure t
    go t@Lit {} = pure t
    go (f :$ args) = evalPRFCodeM spend f =<< traverse go args

{- | Decides definitional equality of two terms under the 'defaultFuel'.

Syntactically equal terms are accepted outright:

>>> defEq (Var "x") (Var "x")
True

and so are terms which partially evaluate to a common form:

>>> defEq (plus :$ (Lit 2 :< Lit 3 :< Nil)) (Lit 5 :: Term String)
True
>>> defEq (plus :$ (Lit 2 :< Var "x" :< Nil)) (Succ :$ (Succ :$ (Var "x" :< Nil) :< Nil))
True

Being a reduction-based check, it is incomplete on open terms — @x + 1@ and
@1 + x@ denote the same number, but only the latter reduces:

>>> defEq (plus :$ (Var "x" :< Lit 1 :< Nil)) (plus :$ (Lit 1 :< Var "x" :< Nil))
False
-}
defEq :: (Eq a) => Term a -> Term a -> Bool
defEq = defEqWith defaultFuel

{- | Decides definitional equality of two terms within the given budget.

Running out of fuel can only make the check fail, never succeed spuriously:

>>> defEqWith (Limited 3) (plus :$ (Lit 2 :< Lit 3 :< Nil)) (Lit 5 :: Term String)
False
>>> defEqWith Unlimited (plus :$ (Lit 2 :< Lit 3 :< Nil)) (Lit 5 :: Term String)
True
-}
defEqWith :: (Eq a) => Fuel -> Term a -> Term a -> Bool
defEqWith fuel s t = s == t || normalizeWith fuel s == normalizeWith fuel t

{- | Checks whether an equation holds definitionally, under the 'defaultFuel'.

>>> defEqAtomic (plus :$ (Lit 2 :< Lit 3 :< Nil) :=== (Lit 5 :: Term String))
True
-}
defEqAtomic :: (Eq a) => Atomic a -> Bool
defEqAtomic = defEqAtomicWith defaultFuel

-- | Checks whether an equation holds definitionally, within the given budget.
defEqAtomicWith :: (Eq a) => Fuel -> Atomic a -> Bool
defEqAtomicWith fuel (s :=== t) = defEqWith fuel s t

{- | Evaluates a term to the numeral it denotes, resolving its free variables
with the given environment.

This is the trusted evaluator: it takes every reduction step, so it is total but
unbudgeted.

>>> evalTerm (\"x" -> 4) (plus :$ (Lit 2 :< Var "x" :< Nil))
6
-}
evalTerm :: (a -> Natural) -> Term a -> Natural
evalTerm env = go
  where
    go (Var x) = env x
    go (Lit n) = n
    go (f :$ args) = evalPRFCode f (fmap go args)

{- | Evaluates a /closed/ term to the numeral it denotes; 'Nothing' when the
term mentions a variable.

>>> toNatural (plus :$ (Lit 2 :< Lit 3 :< Nil) :: Term String)
Just 5
>>> toNatural (plus :$ (Lit 2 :< Var "x" :< Nil))
Nothing
-}
toNatural :: Term a -> Maybe Natural
toNatural t = evalTerm absurd <$> traverse (const Nothing) t
