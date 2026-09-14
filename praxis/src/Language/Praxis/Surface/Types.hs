{-# LANGUAGE OverloadedStrings #-}

{- |
The types of the surface language, and their comparison.

A type is a data type applied to types and to indices, @Nat@, a function
type, a type parameter of the enclosing signature — applied to types when
its kind is higher, as @f@ in @data Term r f v = … App (f (Formula r f v)
(Term r f v))@ — or a hole, a type nothing has determined where it stands.
Types are checked, not trusted: nothing in the core depends on them, which
sees only the codes and the membership predicates the encoding derives from
the data declarations.

An index is a first-order term standing in a type, as @S n@ in @Vec a (S
n)@: a value parameter of the enclosing signature, a variable in scope, a
numeral, the successor, a constructor or a function applied.  The core never
sees an index in a type: an indexed type is its data type, erased, and what
its index says is stated by the index function the data type's declaration
generates.

There are no unification variables.  A type is compared with another by
equality, a hole agreeing with anything, and indices up to the arithmetic of
@Nat@ as the core's definitional equality evaluates it; and the parameters of
a scheme are found by matching its type, one-sided, against the types its
arguments and the context determine.
-}
module Language.Praxis.Surface.Types (
  -- * Kinds and types
  Kind (..),
  Ty (..),
  Ix (..),
  Scheme (..),
  monoScheme,
  renderTy,
  renderTyWith,
  renderIx,
  renderKind,
  tyParams,
  firstOrder,
  determined,
  erase,

  -- * Indices
  normIx,
  ixVars,
  mapIx,
  tyIndices,
  instValues,

  -- * Comparison
  Assignment (..),
  emptyAssignment,
  mergeTy,
  mergeIx,
  matchTy,
  matchIx,
  substScheme,
) where

import Control.Monad (foldM, zipWithM)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import Data.Text (Text)
import Data.Text qualified as T
import Numeric.Natural (Natural)

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
  | -- | a data type, by its qualified name, applied to types and to indices
    TData !Text ![Ty] ![Ix]
  | TNat
  | TArrow !Ty !Ty
  deriving stock (Show, Eq)

{- |
An index: a first-order term standing in a type.  A value parameter of the
enclosing signature, by its position among the signature's value parameters,
as a type parameter is among its type parameters; a variable in scope, by
name; a hole, an index nothing has determined; a numeral; the successor; a
constructor, by its core name, applied; a function, by its core name —
@add@, @sub@, @mul@ and @pow@ for the builtins — applied.
-}
data Ix
  = IxParam !Int
  | IxVar !Text
  | IxHole
  | IxNat !Natural
  | IxSucc !Ix
  | IxCon !Text ![Ix]
  | IxFun !Text ![Ix]
  deriving stock (Show, Eq, Ord)

{- |
A type over parameters: @List a -> List a -> List a@ is the scheme of one
parameter @a@ of kind @Type@, and @Vec a (S n) -> Vec a n@ that of a type
parameter @a@ and a value parameter @n@ of type @Nat@.  Only signatures have
schemes, with their parameters in front: polymorphism is rank 1.  A value
parameter is implicit: it is found, as a type parameter is, by matching.
-}
data Scheme = Scheme
  { schemeParams :: ![(Text, Kind)]
  , schemeValues :: ![(Text, Ty)]
  , schemeType :: !Ty
  }
  deriving stock (Show, Eq)

monoScheme :: Ty -> Scheme
monoScheme = Scheme [] []

-- | The parameters a type mentions, by index.
tyParams :: Ty -> [Int]
tyParams = \case
  TParam i ts -> i : concatMap tyParams ts
  THole -> []
  TData _ ts _ -> concatMap tyParams ts
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
  TData _ ts _ -> all firstOrder ts
  TNat -> True
  TArrow _ _ -> False

-- | Whether a type is determined throughout: no hole anywhere in it, its indices' included.
determined :: Ty -> Bool
determined = \case
  TParam _ ts -> all determined ts
  THole -> False
  TData _ ts xs -> all determined ts && all determinedIx xs
  TNat -> True
  TArrow a b -> determined a && determined b
  where
    determinedIx = \case
      IxHole -> False
      IxSucc x -> determinedIx x
      IxCon _ xs -> all determinedIx xs
      IxFun _ xs -> all determinedIx xs
      _ -> True

-- | A type with its indices erased: what the core's encoding of its values is by.
erase :: Ty -> Ty
erase = \case
  TParam i ts -> TParam i (map erase ts)
  TData n ts _ -> TData n (map erase ts) []
  TArrow a b -> TArrow (erase a) (erase b)
  t -> t

-- | A type, its parameters by the names given, qualified data names by their last segment.
renderTy :: [Text] -> Ty -> String
renderTy names = renderTyWith names []

-- | A type, its type parameters and its value parameters by the names given.
renderTyWith :: [Text] -> [Text] -> Ty -> String
renderTyWith names values = go (0 :: Int)
  where
    go d = \case
      TParam i [] -> name i
      TParam i ts -> paren (d > 1) (unwords (name i : map (go 2) ts))
      THole -> "_"
      TData n [] [] -> short n
      TData n ts xs -> paren (d > 1) (unwords (short n : map (go 2) ts <> map (renderIxAt values 2) xs))
      TNat -> "Nat"
      TArrow a b -> paren (d > 0) (go 1 a <> " -> " <> go 0 b)
    name i = if i < length names then T.unpack (names !! i) else "#" <> show i

-- | An index, its value parameters by the names given.
renderIx :: [Text] -> Ix -> String
renderIx values = renderIxAt values 0

renderIxAt :: [Text] -> Int -> Ix -> String
renderIxAt values = go
  where
    go :: Int -> Ix -> String
    go d = \case
      IxParam i -> if i < length values then T.unpack (values !! i) else "#" <> show i
      IxVar v -> T.unpack v
      IxHole -> "_"
      IxNat n -> show n
      IxSucc x -> paren (d > 1) ("S " <> go 2 x)
      IxCon c [] -> short c
      IxCon c xs -> paren (d > 1) (unwords (short c : map (go 2) xs))
      IxFun f [x, y] | Just o <- lookup f arithmetic -> paren (d > 0) (go 1 x <> " " <> o <> " " <> go 1 y)
      IxFun f [] -> short f
      IxFun f xs -> paren (d > 1) (unwords (short f : map (go 2) xs))
    arithmetic = [("add", "+"), ("sub", "-"), ("mul", "*"), ("pow", "^")] :: [(Text, String)]

short :: Text -> String
short = T.unpack . last . T.splitOn "."

paren :: Bool -> String -> String
paren True s = "(" <> s <> ")"
paren False s = s

renderKind :: Kind -> String
renderKind = \case
  KType -> "Type"
  KArrow a b -> atomic a <> " -> " <> renderKind b
  where
    atomic k@KArrow {} = "(" <> renderKind k <> ")"
    atomic k = renderKind k

-- * Indices

{- |
An index in normal form: numerals for the successors of numerals, and the
builtin arithmetic evaluated as the core's definitional equality does — @add@
by recursion on its second argument, so that @n + 1@ is @S n@ and @n + 0@ is
@n@, but @0 + n@ stays as it is.  Equal normal forms denote equal numbers.
-}
normIx :: Ix -> Ix
normIx = \case
  IxSucc x -> succIx (normIx x)
  IxCon c xs -> IxCon c (map normIx xs)
  IxFun f xs -> arith f (map normIx xs)
  x -> x
  where
    arith f xs = case (f, xs) of
      ("add", [a, IxNat 0]) -> a
      ("add", [IxNat a, IxNat b]) -> IxNat (a + b)
      ("add", [a, IxNat b]) -> succIx (arith "add" [a, IxNat (b - 1)])
      ("add", [a, IxSucc b]) -> succIx (arith "add" [a, b])
      ("sub", [IxNat a, IxNat b]) -> IxNat (if a >= b then a - b else 0)
      ("sub", [a, IxNat 0]) -> a
      ("mul", [IxNat a, IxNat b]) -> IxNat (a * b)
      ("mul", [_, IxNat 0]) -> IxNat 0
      ("pow", [IxNat a, IxNat b]) -> IxNat (a ^ b)
      ("pow", [_, IxNat 0]) -> IxNat 1
      _ -> IxFun f xs

-- | The successor of an index in normal form.
succIx :: Ix -> Ix
succIx = \case
  IxNat n -> IxNat (n + 1)
  x -> IxSucc x

-- | The variables an index mentions, by name.
ixVars :: Ix -> [Text]
ixVars = \case
  IxVar v -> [v]
  IxSucc x -> ixVars x
  IxCon _ xs -> concatMap ixVars xs
  IxFun _ xs -> concatMap ixVars xs
  _ -> []

-- | Every index of a type rewritten by the function given, the indices of its arguments' too.
mapIx :: (Ix -> Ix) -> Ty -> Ty
mapIx f = \case
  TParam i ts -> TParam i (map (mapIx f) ts)
  TData n ts xs -> TData n (map (mapIx f) ts) (map f xs)
  TArrow a b -> TArrow (mapIx f a) (mapIx f b)
  t -> t

-- | The indices a type has, its arguments' included, outermost first.
tyIndices :: Ty -> [Ix]
tyIndices = \case
  TParam _ ts -> concatMap tyIndices ts
  TData _ ts xs -> xs <> concatMap tyIndices ts
  TArrow a b -> tyIndices a <> tyIndices b
  _ -> []

-- | An index, its value parameters replaced by the indices given, by position; one beyond them a hole.
instValues :: [Ix] -> Ix -> Ix
instValues vs = go
  where
    go = \case
      IxParam i -> if i < length vs then vs !! i else IxHole
      IxSucc x -> IxSucc (go x)
      IxCon c xs -> IxCon c (map go xs)
      IxFun f xs -> IxFun f (map go xs)
      x -> x

-- * Comparison

-- | The types and the indices found so far for the parameters of a scheme, by index.
data Assignment = Assignment
  { asTypes :: !(IntMap Ty)
  , asValues :: !(IntMap Ix)
  }
  deriving stock (Show, Eq)

emptyAssignment :: Assignment
emptyAssignment = Assignment IM.empty IM.empty

{- |
What two types say of one type together: each hole of one filled by what
the other has there, and indices compared in normal form.  Nothing when they
disagree.
-}
mergeTy :: Ty -> Ty -> Maybe Ty
mergeTy a b = case (a, b) of
  (THole, t) -> Just t
  (t, THole) -> Just t
  (TParam i ts, TParam j us) | i == j, length ts == length us -> TParam i <$> zipWithM mergeTy ts us
  (TData m ts xs, TData n us ys) | m == n, length ts == length us -> TData m <$> zipWithM mergeTy ts us <*> mergeIndices xs ys
  (TNat, TNat) -> Just TNat
  (TArrow x y, TArrow z w) -> TArrow <$> mergeTy x z <*> mergeTy y w
  _ -> Nothing
  where
    -- An erased type, of no indices, agrees with any indices.
    mergeIndices xs ys
      | null xs = Just ys
      | null ys = Just xs
      | length xs == length ys = zipWithM mergeIx xs ys
      | otherwise = Nothing

-- | What two indices say of one together, in normal form: a hole filled, the rest equal.
mergeIx :: Ix -> Ix -> Maybe Ix
mergeIx a b = go (normIx a) (normIx b)
  where
    go x y = case (x, y) of
      (IxHole, _) -> Just y
      (_, IxHole) -> Just x
      (IxSucc x', IxSucc y') -> succIx <$> go x' y'
      (IxSucc x', IxNat k) | k > 0 -> succIx <$> go x' (IxNat (k - 1))
      (IxNat k, IxSucc y') | k > 0 -> succIx <$> go (IxNat (k - 1)) y'
      (IxCon c xs, IxCon c' ys) | c == c', length xs == length ys -> IxCon c <$> zipWithM go xs ys
      (IxFun f xs, IxFun f' ys) | f == f', length xs == length ys -> IxFun f <$> zipWithM go xs ys
      _ | x == y -> Just x
      _ -> Nothing

{- |
Match the type of a scheme of @n@ type parameters and @m@ value parameters
against a type, one-sided: its parameters, @TParam i@ for @i < n@ and
@IxParam i@ for @i < m@, take what the type has where they stand, together
with what they were given before; any other part must agree, indices in
normal form.  A hole determines nothing.  A parameter of a higher kind
applied, against a type parameter applied to as many arguments or more,
takes that parameter applied to those in front; against anything else it is
opaque, and determines nothing.  Nothing when the types disagree.
-}
matchTy :: (Int, Int) -> Ty -> Ty -> Assignment -> Maybe Assignment
matchTy nm@(n, m) p t s = case (p, t) of
  (_, THole) -> Just s
  (TParam i [], _) | i < n -> case IM.lookup i (asTypes s) of
    Nothing -> Just s {asTypes = IM.insert i t (asTypes s)}
    Just u -> (\v -> s {asTypes = IM.insert i v (asTypes s)}) <$> mergeTy u t
  (TParam i ps, TParam j ts)
    | i < n
    , length ts >= length ps ->
        let (front, rest) = splitAt (length ts - length ps) ts
         in matchTy nm (TParam i []) (TParam j front) s >>= \s' -> pairs (zip ps rest) s'
  (TParam i _, _) | i < n -> Just s
  (TParam i ps, TParam j ts) | i == j, length ps == length ts -> pairs (zip ps ts) s
  (TData a ps xs, TData b ts ys)
    | a == b
    , length ps == length ts ->
        pairs (zip ps ts) s >>= \s' ->
          -- An erased type, of no indices, determines none of them.
          if null xs || null ys
            then Just s'
            else if length xs == length ys then foldM (\acc (x, y) -> matchIx m x y acc) s' (zip xs ys) else Nothing
  (TNat, TNat) -> Just s
  (TArrow a b, TArrow c d) -> pairs [(a, c), (b, d)] s
  _ -> Nothing
  where
    pairs xs s0 = foldM (\acc (x, y) -> matchTy nm x y acc) s0 xs

{- |
Match an index of a scheme of @m@ value parameters against an index, both in
normal form: a parameter, @IxParam i@ for @i < m@, takes what the other has
there; a numeral and the successor against the successors they are; a
constructor or a function against the same one applied, argument by argument.
Nothing when they disagree, as a successor against zero, or a constructor
against a variable, whose value nothing here knows.
-}
matchIx :: Int -> Ix -> Ix -> Assignment -> Maybe Assignment
matchIx m p0 t0 s = go (normIx p0) (normIx t0) s
  where
    go p t acc = case (p, t) of
      (_, IxHole) -> Just acc
      (IxParam i, _) | i < m -> case IM.lookup i (asValues acc) of
        Nothing -> Just acc {asValues = IM.insert i t (asValues acc)}
        Just u -> (\v -> acc {asValues = IM.insert i v (asValues acc)}) <$> mergeIx u t
      (IxSucc p', IxSucc t') -> go p' t' acc
      (IxSucc p', IxNat k) | k > 0 -> go p' (IxNat (k - 1)) acc
      (IxNat k, IxSucc t') | k > 0 -> go (IxNat (k - 1)) t' acc
      (IxCon c ps, IxCon c' ts) | c == c', length ps == length ts -> foldM (\a (x, y) -> go x y a) acc (zip ps ts)
      (IxFun f ps, IxFun f' ts) | f == f', length ps == length ts -> foldM (\a (x, y) -> go x y a) acc (zip ps ts)
      _ | p == t -> Just acc
      _ -> Nothing

{- |
The type of a scheme of @n@ type parameters and @m@ value parameters at the
types and indices found for them: a parameter found for none is a hole.  A
parameter of a higher kind applied takes its arguments after those of the
type found for it.
-}
substScheme :: (Int, Int) -> Assignment -> Ty -> Ty
substScheme (n, m) s = go
  where
    go = \case
      TParam i ts
        | i < n -> case (IM.lookup i (asTypes s), map go ts) of
            (Nothing, _) -> THole
            (Just u, []) -> u
            (Just (TParam j us), ts') -> TParam j (us <> ts')
            (Just (TData d us xs), ts') -> TData d (us <> ts') xs
            (Just _, _) -> THole
        | otherwise -> TParam i (map go ts)
      THole -> THole
      TData d ts xs -> TData d (map go ts) (map ix xs)
      TNat -> TNat
      TArrow a b -> TArrow (go a) (go b)
    ix = \case
      IxParam i | i < m -> maybe IxHole id (IM.lookup i (asValues s))
      IxSucc x -> IxSucc (ix x)
      IxCon c xs -> IxCon c (map ix xs)
      IxFun f xs -> IxFun f (map ix xs)
      x -> x
