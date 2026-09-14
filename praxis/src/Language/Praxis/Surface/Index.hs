{-# LANGUAGE OverloadedStrings #-}

{- |
Indices: their substitution, their unification, and the terms they stand for.

Matching a constructor of an indexed data type against a value of a type
whose indices are known refines what the clause knows: @(x :- xs)@ against
@Vec a (S n)@ says that the implicit length of @xs@ is @n@.  That is
first-order unification of indices, over variables which may still be solved
— the value parameters of the enclosing signature and the implicit arguments
of the constructor — and constructor forms: numerals, the successor and
constructors.  Two different constructor forms clash, and then the
constructor can never match there, which is what lets a function omit it.  A
function applied, whose value nothing here computes, is stuck: neither a
solution nor a clash.

Nothing here is trusted: what the elaborator concludes of indices, the core
checks through the specifications of the functions and the index functions
of the data types.
-}
module Language.Praxis.Surface.Index (
  -- * Substitutions
  Key (..),
  Subst,
  emptySubst,
  substKeys,
  applyIx,
  applyTy,

  -- * Unification
  Unified (..),
  unifyIx,
  unifyAll,

  -- * Terms
  ixToExpr,
  ixToExprWith,
  isPattern,
) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Language.Praxis.Surface.Syntax (Expr (..), Ref (..), RefKind (..), apps)
import Language.Praxis.Surface.Types

-- * Substitutions

-- | A variable of an index: a value parameter of the enclosing signature, by position, or a variable, by name.
data Key = KParam !Int | KVar !Text
  deriving stock (Show, Eq, Ord)

-- | Indices for variables, kept idempotent: no solution mentions a variable solved.
newtype Subst = Subst (Map Key Ix)
  deriving stock (Show, Eq)

emptySubst :: Subst
emptySubst = Subst Map.empty

-- | The variables a substitution solves.
substKeys :: Subst -> [Key]
substKeys (Subst m) = Map.keys m

-- | An index with the variables solved replaced, in normal form.
applyIx :: Subst -> Ix -> Ix
applyIx (Subst m) = normIx . go
  where
    go = \case
      x@(IxParam i) -> Map.findWithDefault x (KParam i) m
      x@(IxVar v) -> Map.findWithDefault x (KVar v) m
      IxSucc x -> IxSucc (go x)
      IxCon c xs -> IxCon c (map go xs)
      IxFun f xs -> IxFun f (map go xs)
      x -> x

-- | A type with the variables of its indices solved replaced.
applyTy :: Subst -> Ty -> Ty
applyTy s = mapIx (applyIx s)

keyOf :: Ix -> Maybe Key
keyOf = \case
  IxParam i -> Just (KParam i)
  IxVar v -> Just (KVar v)
  _ -> Nothing

-- | The variables an index mentions.
keysOf :: Ix -> [Key]
keysOf = \case
  IxParam i -> [KParam i]
  IxVar v -> [KVar v]
  IxSucc x -> keysOf x
  IxCon _ xs -> concatMap keysOf xs
  IxFun _ xs -> concatMap keysOf xs
  _ -> []

-- * Unification

{- |
What unifying indices concludes: a substitution making them equal; a clash,
two different constructor forms, so that they are never equal; or stuck,
where a function or a variable not to be solved stands against something
else, and nothing is concluded.
-}
data Unified
  = Unified !Subst
  | Clash !String
  | Stuck !String
  deriving stock (Show)

{- |
Unify two indices, extending the substitution given, the variables the
predicate says may be solved.  A variable against a term mentioning it under
constructor forms clashes, as @n@ against @S n@ does.
-}
unifyIx :: (Key -> Bool) -> Ix -> Ix -> Subst -> Unified
unifyIx flexible a0 b0 s = go (applyIx s a0) (applyIx s b0)
  where
    go a b
      | a == b = Unified s
      | Just k <- keyOf a, flexible k = bind k b
      | Just k <- keyOf b, flexible k = bind k a
      | otherwise = case (a, b) of
          (IxSucc x, IxSucc y) -> unifyIx flexible x y s
          (IxSucc x, IxNat n)
            | n > 0 -> unifyIx flexible x (IxNat (n - 1)) s
            | otherwise -> Clash (renderIx [] a <> " is a successor, and 0 is not")
          (IxNat n, IxSucc y)
            | n > 0 -> unifyIx flexible (IxNat (n - 1)) y s
            | otherwise -> Clash ("0 is not a successor, and " <> renderIx [] b <> " is")
          (IxNat m, IxNat n) -> Clash (show m <> " is not " <> show n)
          (IxCon c xs, IxCon d ys)
            | c /= d -> Clash (renderIx [] a <> " and " <> renderIx [] b <> " are built by different constructors")
            | length xs == length ys -> unifyAll flexible (zip xs ys) s
          (IxCon {}, IxNat _) -> Clash (renderIx [] a <> " is no numeral")
          (IxCon {}, IxSucc _) -> Clash (renderIx [] a <> " is no successor")
          (IxNat _, IxCon {}) -> Clash (renderIx [] b <> " is no numeral")
          (IxSucc _, IxCon {}) -> Clash (renderIx [] b <> " is no successor")
          _ -> Stuck (renderIx [] a <> " and " <> renderIx [] b <> ": neither is solved by the other")
    bind k t
      | k `elem` keysOf t = if constructorForm t then Clash (renderIx [] t <> " would contain itself") else Stuck (renderIx [] t <> " mentions what it is to solve")
      | otherwise =
          let Subst m = s
              one = Subst (Map.singleton k t)
           in Unified (Subst (Map.insert k t (Map.map (applyIx one) m)))
    constructorForm = \case
      IxSucc x -> constructorForm x || True
      IxCon _ _ -> True
      _ -> False

-- | Unify indices pairwise, left to right; the first clash or stuck pair is the answer.
unifyAll :: (Key -> Bool) -> [(Ix, Ix)] -> Subst -> Unified
unifyAll flexible pairs s0 = foldl step (Unified s0) pairs
  where
    step acc (x, y) = case acc of
      Unified s -> unifyIx flexible x y s
      other -> other

-- * Terms

{- |
The term an index stands for, its variables by the function given, and a
value parameter by none: a value parameter of a signature is implicit, and no
value a function is given.  Nothing when it mentions one, or a hole.
-}
ixToExpr :: (Text -> Maybe (Expr a)) -> Ix -> Maybe (Expr a)
ixToExpr var = ixToExprWith var (const Nothing)

-- | 'ixToExpr', a value parameter by the function given too: where the parameter's value is in scope, as a variable.
ixToExprWith :: (Text -> Maybe (Expr a)) -> (Int -> Maybe (Expr a)) -> Ix -> Maybe (Expr a)
ixToExprWith var param = go
  where
    go = \case
      IxNat n -> Just (Nat n)
      IxSucc x -> App (Global (Ref RefBuiltin "S")) <$> go x
      IxVar v -> var v
      IxCon c xs -> apps (Global (Ref RefConstructor c)) <$> traverse go xs
      IxFun f xs -> apps (Global (Ref (if f `elem` builtins then RefBuiltin else RefFunction) f)) <$> traverse go xs
      IxParam i -> param i
      IxHole -> Nothing
    builtins = ["add", "sub", "mul", "pow"] :: [Text]

-- | Whether an index is a pattern a constructor's result may have: variables, numerals, the successor and constructors, no function.
isPattern :: Ix -> Bool
isPattern = \case
  IxSucc x -> isPattern x
  IxCon _ xs -> all isPattern xs
  IxFun _ _ -> False
  IxHole -> False
  _ -> True
