{-# LANGUAGE OverloadedStrings #-}

{- |
The types of the surface language, and their comparison.

A type is a data type applied to types, @Nat@, a function type, a type
parameter of the enclosing signature — applied to types when its kind is
higher, as @f@ in @data Term r f v = … App (f (Formula r f v) (Term r f v))@
— or a hole, a type nothing has determined where it stands.  Types are
checked, not trusted: nothing in the core depends on them, which sees only
the codes and the membership predicates the encoding derives from the data
declarations.

There are no unification variables.  A type is compared with another by
equality, a hole agreeing with anything; and the parameters of a scheme are
found by matching its type, one-sided, against the types its arguments and
the context determine.
-}
module Language.Praxis.Surface.Types (
  -- * Kinds and types
  Kind (..),
  Ty (..),
  Scheme (..),
  monoScheme,
  renderTy,
  renderKind,
  tyParams,
  firstOrder,
  determined,

  -- * Comparison
  Assignment,
  mergeTy,
  matchTy,
  substScheme,
) where

import Control.Monad (foldM, zipWithM)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import Data.Text (Text)
import Data.Text qualified as T

-- * Kinds and types

data Kind = KType | KArrow !Kind !Kind
  deriving stock (Show, Eq)

data Ty
  = -- | the type parameter of that index of the enclosing signature, applied to types
    TParam !Int ![Ty]
  | {- | a type nothing has determined where it stands: a parameter no argument,
    result or expected type fixes, which the translation erases
    -}
    THole
  | -- | a data type, by its qualified name, applied to types
    TData !Text ![Ty]
  | TNat
  | TArrow !Ty !Ty
  deriving stock (Show, Eq)

{- |
A type over parameters: @List a -> List a -> List a@ is the scheme of one
parameter @a@ of kind @Type@.  Only signatures have schemes, with their
parameters in front: polymorphism is rank 1.
-}
data Scheme = Scheme
  { schemeParams :: ![(Text, Kind)]
  , schemeType :: !Ty
  }
  deriving stock (Show, Eq)

monoScheme :: Ty -> Scheme
monoScheme = Scheme []

-- | The parameters a type mentions, by index.
tyParams :: Ty -> [Int]
tyParams = \case
  TParam i ts -> i : concatMap tyParams ts
  THole -> []
  TData _ ts -> concatMap tyParams ts
  TNat -> []
  TArrow a b -> tyParams a <> tyParams b

{- |
Whether a type is first-order: no function type anywhere in it.  Values are
first-order — numerals and the codes of data types — so every field, binder
and argument has such a type; a function type stands only at the top of a
function's signature, and a function is always applied in full.
-}
firstOrder :: Ty -> Bool
firstOrder = \case
  TParam _ ts -> all firstOrder ts
  THole -> True
  TData _ ts -> all firstOrder ts
  TNat -> True
  TArrow _ _ -> False

-- | Whether a type is determined throughout: no hole anywhere in it.
determined :: Ty -> Bool
determined = \case
  TParam _ ts -> all determined ts
  THole -> False
  TData _ ts -> all determined ts
  TNat -> True
  TArrow a b -> determined a && determined b

-- | A type, its parameters by the names given, qualified data names by their last segment.
renderTy :: [Text] -> Ty -> String
renderTy names = go (0 :: Int)
  where
    go d = \case
      TParam i [] -> name i
      TParam i ts -> paren (d > 1) (unwords (name i : map (go 2) ts))
      THole -> "_"
      TData n [] -> short n
      TData n ts -> paren (d > 1) (unwords (short n : map (go 2) ts))
      TNat -> "Nat"
      TArrow a b -> paren (d > 0) (go 1 a <> " -> " <> go 0 b)
    name i = if i < length names then T.unpack (names !! i) else "#" <> show i
    short = T.unpack . last . T.splitOn "."
    paren True s = "(" <> s <> ")"
    paren False s = s

renderKind :: Kind -> String
renderKind = \case
  KType -> "Type"
  KArrow a b -> atomic a <> " -> " <> renderKind b
  where
    atomic k@KArrow {} = "(" <> renderKind k <> ")"
    atomic k = renderKind k

-- * Comparison

-- | The types found so far for the parameters of a scheme, by index.
type Assignment = IntMap Ty

{- |
What two types say of one type together: each hole of one filled by what
the other has there.  Nothing when they disagree.
-}
mergeTy :: Ty -> Ty -> Maybe Ty
mergeTy a b = case (a, b) of
  (THole, t) -> Just t
  (t, THole) -> Just t
  (TParam i ts, TParam j us) | i == j, length ts == length us -> TParam i <$> zipWithM mergeTy ts us
  (TData m ts, TData n us) | m == n, length ts == length us -> TData m <$> zipWithM mergeTy ts us
  (TNat, TNat) -> Just TNat
  (TArrow x y, TArrow z w) -> TArrow <$> mergeTy x z <*> mergeTy y w
  _ -> Nothing

{- |
Match the type of a scheme of @n@ parameters against a type, one-sided: its
parameters, @TParam i@ for @i < n@, take what the type has where they stand,
together with what they were given before; any other part must agree.  A hole
determines nothing.  A parameter of a higher kind applied, against a type
parameter applied to as many arguments or more, takes that parameter applied
to those in front; against anything else it is opaque, and determines
nothing.  Nothing when the types disagree.
-}
matchTy :: Int -> Ty -> Ty -> Assignment -> Maybe Assignment
matchTy n p t s = case (p, t) of
  (_, THole) -> Just s
  (TParam i [], _) | i < n -> case IM.lookup i s of
    Nothing -> Just (IM.insert i t s)
    Just u -> (\m -> IM.insert i m s) <$> mergeTy u t
  (TParam i ps, TParam j ts)
    | i < n
    , length ts >= length ps ->
        let (front, rest) = splitAt (length ts - length ps) ts
         in matchTy n (TParam i []) (TParam j front) s >>= \s' -> pairs (zip ps rest) s'
  (TParam i _, _) | i < n -> Just s
  (TParam i ps, TParam j ts) | i == j, length ps == length ts -> pairs (zip ps ts) s
  (TData a ps, TData b ts) | a == b, length ps == length ts -> pairs (zip ps ts) s
  (TNat, TNat) -> Just s
  (TArrow a b, TArrow c d) -> pairs [(a, c), (b, d)] s
  _ -> Nothing
  where
    pairs xs s0 = foldM (\acc (x, y) -> matchTy n x y acc) s0 xs

{- |
The type of a scheme of @n@ parameters at the types found for them: a
parameter found for none is a hole.  A parameter of a higher kind applied
takes its arguments after those of the type found for it.
-}
substScheme :: Int -> Assignment -> Ty -> Ty
substScheme n s = go
  where
    go = \case
      TParam i ts
        | i < n -> case (IM.lookup i s, map go ts) of
            (Nothing, _) -> THole
            (Just u, []) -> u
            (Just (TParam j us), ts') -> TParam j (us <> ts')
            (Just (TData d us), ts') -> TData d (us <> ts')
            (Just _, _) -> THole
        | otherwise -> TParam i (map go ts)
      THole -> THole
      TData d ts -> TData d (map go ts)
      TNat -> TNat
      TArrow a b -> TArrow (go a) (go b)
