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
  -- * Irrelevant data
  Hint (..),

  -- * Kinds and types
  Kind (..),
  Parameter (..),
  orderArguments,
  Ty (..),
  Ix (..),
  Scheme (..),
  monoScheme,
  TyScope (..),
  emptyScope,
  renderTy,
  renderTyWith,
  renderTyWithOrder,
  renderIx,
  renderKind,
  tyParams,
  firstOrder,
  determined,
  erase,

  -- * Telescopes
  Binder (..),
  Telescope,
  namedBinder,
  hiddenBinder,
  openNames,
  openIx,
  openTelescope,

  -- * Indices
  normIx,
  hasHole,
  ixLeaves,
  ixFrees,
  ixLocals,
  ixMetas,
  ixMethods,
  ixDicts,
  mapIx,
  mapIxLeaves,
  tyIndices,
  instValues,

  -- * Comparison
  Unfold,
  noUnfold,
  unfoldDepth,
  unfoldRounds,
  unfoldAll,
  unfoldedBy,
  Assignment (..),
  emptyAssignment,
  mergeTy,
  mergeTyWith,
  mergeIx,
  mergeIxWith,
  transportIndices,
  matchTy,
  matchTyWith,
  matchIx,
  matchIxWith,
  substScheme,
) where

import Control.Monad (foldM, zipWithM)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import Data.List (find)
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Numeric.Natural (Natural)

-- * Irrelevant data

-- | A name kept for display only: any two are equal.
newtype Hint = Hint {hintText :: Text}
  deriving newtype (Show)

instance Eq Hint where
  _ == _ = True

instance Ord Hint where
  compare _ _ = EQ

-- * Kinds and types

data Kind = KType | KArrow !Kind !Kind
  deriving stock (Show, Eq)

-- | A source binder's position in the separate core type and index lists.
data Parameter = TypeParameter !Int | IndexParameter !Int
  deriving stock (Show, Eq)

-- | Restore declaration order. Erased indices have no arguments to print.
orderArguments :: [Parameter] -> [a] -> [a] -> [a]
orderArguments positions types indices = concatMap at positions
  where
    at (TypeParameter i) = take 1 (drop i types)
    at (IndexParameter i) = take 1 (drop i indices)

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
as a type parameter is among its type parameters; a variable bound in the
enclosing telescope, by its de Bruijn level — its position among the value
binders in scope, the outermost 0 — with the name its binder was written by
as a hint, for display only; a variable unification may solve, by an
identity fresh within the clause, the name of the entry it was made for its
hint; a free variable, by name — a binder opened into the tactic engine's
named world, or a name an ascription leaves unbound; the value of the
enclosing dictionary at a position; a dependent member of a class, by its
qualified name, before a dictionary is selected; a hole, an index nothing
has determined; a numeral; the successor; a constructor, by its core name,
applied; a function, by its core name — @add@, @sub@, @mul@ and @pow@ for
the builtins — applied.

A bound variable is never referred to by name: the hint is equal to any
other, so two indices are equal exactly when they refer to the same
positions.
-}
data Ix
  = IxParam !Int
  | IxLocal !Int !Hint
  | IxMeta !Int !Hint
  | IxFree !Text
  | IxDict !Int
  | IxMethod !Text
  | IxHole
  | IxNat !Natural
  | IxSucc !Ix
  | IxCon !Text ![Ix]
  | IxFun !Text ![Ix]
  | -- | a fixed schema supplied to a computation appearing in an index
    IxSchema !Text
  | -- | a schema with source arity, runtime prefix count and captured arguments
    IxPartial !Text !Int !Int ![Ix]
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

{- |
What the names in a type written in a signature, or in a term, stand for:
the type parameters, by position, and the values its indices may mention, as
the indices they are — a value parameter of the signature, or a variable.
-}
data TyScope = TyScope
  { tsTypes :: ![Text]
  , tsValues :: ![(Text, Ix)]
  , tsValueTys :: ![(Text, Ty)]
  -- ^ the types of the values, by name, where known: what the kinds of indices are checked against
  }
  deriving stock (Show, Eq)

-- | No names.
emptyScope :: TyScope
emptyScope = TyScope [] [] []

-- * Telescopes

{- |
A binder of a telescope: the name the source wrote for it, if any — what a
term written under it may refer to it by — the hint it is displayed by, and
its type, whose indices refer to the binders before it by 'IxLocal' level.
A binder written by no name — an implicit value a clause takes without
naming it, an implicit argument of a constructor its pattern leaves out — has
the name of the parameter it stands for as its hint.
-}
data Binder = Binder
  { binderName :: !(Maybe Text)
  , binderHint :: !Hint
  , binderTy :: !Ty
  }
  deriving stock (Show, Eq)

-- | The binders in scope, outermost first: the k-th is the variable of level k.
type Telescope = [Binder]

-- | A binder written by a name.
namedBinder :: Text -> Ty -> Binder
namedBinder n = Binder (Just n) (Hint n)

-- | A binder no name is written for, displayed by the hint given.
hiddenBinder :: Text -> Ty -> Binder
hiddenBinder h = Binder Nothing (Hint h)

{- |
Distinct names for the binders of a telescope, opening it into a named
world — the tactic engine's, or the core text's: a binder keeps the name
written for it, which the source keeps distinct within a telescope; one
written by no name takes its hint, primed until it differs from every name
written and every name taken before it.
-}
openNames :: Telescope -> [Text]
openNames binders = go [] binders
  where
    written = [n | Binder (Just n) _ _ <- binders]
    go _ [] = []
    go taken (Binder (Just n) _ _ : rest) = n : go (n : taken) rest
    go taken (Binder Nothing (Hint h) _ : rest) =
      let name = fromMaybe h (find (\c -> c `notElem` written && c `notElem` taken) (iterate (<> "'") h))
       in name : go (name : taken) rest

-- | An index with the bound variables of a telescope opened: each by the name given for its level.
openIx :: [Text] -> Ix -> Ix
openIx names = go
  where
    go = \case
      IxLocal k h -> maybe (IxLocal k h) IxFree (listToMaybe (drop k names))
      IxSucc x -> IxSucc (go x)
      IxCon c xs -> IxCon c (map go xs)
      IxFun f xs -> IxFun f (map go xs)
      IxPartial f arity prefix xs -> IxPartial f arity prefix (map go xs)
      x -> x

-- | A telescope opened by 'openNames': its binders by those names, the indices of their types opened too.
openTelescope :: Telescope -> [(Text, Ty)]
openTelescope binders = [(n, mapIx (openIx names) (binderTy b)) | (n, b) <- zip names binders]
  where
    names = openNames binders

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
      IxPartial _ _ _ xs -> all determinedIx xs
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
renderTyWith = renderTyWithOrder (const [])

-- | Render applications in source order when their declaration is available.
renderTyWithOrder :: (Text -> [Parameter]) -> [Text] -> [Text] -> Ty -> String
renderTyWithOrder order names values = go (0 :: Int)
  where
    go d = \case
      TParam i [] -> name i
      TParam i ts -> paren (d > 1) (unwords (name i : map (go 2) ts))
      THole -> "_"
      TData n [] [] -> short n
      TData n ts xs ->
        let types = map (go 2) ts
            indices = map (renderIxAt values 2) xs
            args = case order n of [] -> types <> indices; ps -> orderArguments ps types (indices <> repeat "_")
         in paren (d > 1) (unwords (short n : args))
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
      IxLocal _ (Hint h) -> T.unpack h
      IxMeta _ (Hint h) -> T.unpack h
      IxFree v -> T.unpack v
      IxDict i -> "#d" <> show i
      IxMethod q -> short q
      IxHole -> "_"
      IxNat n -> show n
      IxSucc x -> paren (d > 1) ("S " <> go 2 x)
      IxCon c [] -> short c
      IxCon c xs -> paren (d > 1) (unwords (short c : map (go 2) xs))
      IxFun f [x, y] | Just o <- lookup f arithmetic -> paren (d > 0) (go 1 x <> " " <> o <> " " <> go 1 y)
      IxFun f [] -> short f
      IxFun f xs -> paren (d > 1) (unwords (short f : map (go 2) xs))
      IxSchema name -> "{" <> short name <> "}"
      IxPartial name arity prefix xs -> "{partial " <> short name <> " " <> show arity <> "/" <> show prefix <> " " <> unwords (map (go 2) xs) <> "}"
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
  IxPartial f n k xs -> IxPartial f n k (map normIx xs)
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

-- | The atoms an index is built of, left to right: everything under the successor, constructors, functions and partial schemas.
ixLeaves :: Ix -> [Ix]
ixLeaves = \case
  IxSucc x -> ixLeaves x
  IxCon _ xs -> concatMap ixLeaves xs
  IxFun _ xs -> concatMap ixLeaves xs
  IxPartial _ _ _ xs -> concatMap ixLeaves xs
  x -> [x]

-- | The free variables an index mentions, by name.
ixFrees :: Ix -> [Text]
ixFrees x = [v | IxFree v <- ixLeaves x]

-- | The bound variables an index mentions, by level.
ixLocals :: Ix -> [Int]
ixLocals x = [k | IxLocal k _ <- ixLeaves x]

-- | The variables unification may solve an index mentions, by identity.
ixMetas :: Ix -> [Int]
ixMetas x = [m | IxMeta m _ <- ixLeaves x]

-- | The dependent members an index mentions, by qualified name.
ixMethods :: Ix -> [Text]
ixMethods x = [q | IxMethod q <- ixLeaves x]

-- | The dictionary values an index mentions, by position.
ixDicts :: Ix -> [Int]
ixDicts x = [i | IxDict i <- ixLeaves x]

-- | An index with the function given applied at its leaves: under the successor, constructors, functions and partial schemas.
mapIxLeaves :: (Ix -> Ix) -> Ix -> Ix
mapIxLeaves f = go
  where
    go = \case
      IxSucc x -> IxSucc (go x)
      IxCon c xs -> IxCon c (map go xs)
      IxFun g xs -> IxFun g (map go xs)
      IxPartial g arity prefix xs -> IxPartial g arity prefix (map go xs)
      x -> f x

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
      IxPartial f arity prefix xs -> IxPartial f arity prefix (map go xs)
      x -> x

-- * Comparison

{- | The equalities needed to transport a value between two types. Only
indices may change: datatype heads, type parameters and their applications
must retain their structure. Every returned pair needs certified evidence.
-}
transportIndices :: Ty -> Ty -> Maybe [(Ix, Ix)]
transportIndices source target = case (source, target) of
  (TNat, TNat) -> Just []
  (TParam i xs, TParam j ys) | i == j, length xs == length ys -> concat <$> zipWithM transportIndices xs ys
  (TData n ts xs, TData m us ys)
    | n == m
    , length ts == length us
    , length xs == length ys -> do
        nested <- concat <$> zipWithM transportIndices ts us
        pure (nested <> [(normIx x, normIx y) | (x, y) <- zip xs ys, normIx x /= normIx y])
  _ -> Nothing

-- | The types and the indices found so far for the parameters of a scheme, by index.
data Assignment = Assignment
  { asTypes :: !(IntMap Ty)
  , asValues :: !(IntMap Ix)
  }
  deriving stock (Show, Eq)

emptyAssignment :: Assignment
emptyAssignment = Assignment IM.empty IM.empty

{- |
How an index of a function applied unfolds, where the function is an
abbreviation — a definition by one equation over variables, as @nn a = neg
(neg a)@: its right side at the arguments.  Nothing for any other function,
or for an abbreviation applied to fewer arguments than it takes.  Comparing
indices unfolds an abbreviation where the indices differ as they stand, so
that @nn a@ agrees with @(a :=> Bottom) :=> Bottom@.
-}
type Unfold = Text -> [Ix] -> Maybe Ix

-- | Unfold nothing: indices compared as they stand.
noUnfold :: Unfold
noUnfold _ _ = Nothing

{- |
How many abbreviations a comparison of indices unfolds one after another
down one path: a bound, so that the methods of an instance defining one
another in a circle do not unfold without end.
-}
unfoldDepth :: Int
unfoldDepth = 64

{- |
How many times a comparison of indices unfolds both as far as they go and
compares them again: once suffices unless the budget of 'unfoldAll' is
exhausted, as it is by the methods of an instance defining one another in a
circle; a few more rounds then end it.
-}
unfoldRounds :: Int
unfoldRounds = 4

{- |
An index with every abbreviation in it unfolded as far as it goes, within
'unfoldDepth' steps down each path: what two indices equal modulo
abbreviations both come to.
-}
unfoldAll :: Unfold -> Ix -> Ix
unfoldAll unfold = go unfoldDepth
  where
    go :: Int -> Ix -> Ix
    go budget ix
      | budget <= 0 = ix
      | otherwise = case ix of
          IxFun f xs | Just ix' <- unfold f xs -> go (budget - 1) ix'
          IxSucc x -> IxSucc (go budget x)
          IxCon c xs -> IxCon c (map (go budget) xs)
          IxFun f xs -> IxFun f (map (go budget) xs)
          IxPartial f arity prefix xs -> IxPartial f arity prefix (map (go budget) xs)
          _ -> ix

-- | An index unfolded as far as it goes, in normal form: the arithmetic of @Nat@ then sees the successors unfolding exposes.
unfoldedBy :: Unfold -> Ix -> Ix
unfoldedBy unfold = normIx . unfoldAll unfold

-- | Whether an index has a hole somewhere in it.
hasHole :: Ix -> Bool
hasHole = \case
  IxHole -> True
  IxSucc x -> hasHole x
  IxCon _ xs -> any hasHole xs
  IxFun _ xs -> any hasHole xs
  IxPartial _ _ _ xs -> any hasHole xs
  _ -> False

{- |
What two types say of one type together: each hole of one filled by what
the other has there, and indices compared in normal form.  Nothing when they
disagree.
-}
mergeTy :: Ty -> Ty -> Maybe Ty
mergeTy = mergeTyWith noUnfold

-- | 'mergeTy', its indices compared as 'mergeIxWith' compares them, abbreviations unfolded.
mergeTyWith :: Unfold -> Ty -> Ty -> Maybe Ty
mergeTyWith unfold = go
  where
    go a b = case (a, b) of
      (THole, t) -> Just t
      (t, THole) -> Just t
      (TParam i ts, TParam j us) | i == j, length ts == length us -> TParam i <$> zipWithM go ts us
      (TData m ts xs, TData n us ys) | m == n, length ts == length us -> TData m <$> zipWithM go ts us <*> mergeIndices xs ys
      (TNat, TNat) -> Just TNat
      (TArrow x y, TArrow z w) -> TArrow <$> go x z <*> go y w
      _ -> Nothing
    -- An erased type, of no indices, agrees with any indices.
    mergeIndices xs ys
      | null xs = Just ys
      | null ys = Just xs
      | length xs == length ys = zipWithM (mergeIxWith unfold) xs ys
      | otherwise = Nothing

-- | What two indices say of one together, in normal form: a hole filled, the rest equal.
mergeIx :: Ix -> Ix -> Maybe Ix
mergeIx = mergeIxWith noUnfold

{- |
'mergeIx', abbreviations unfolded where the indices differ as they stand:
the two are unfolded as far as they go, once, and compared as they are
then, so that two abbreviations applied to the same arguments cost no more
than their unfolding.  Where they agree only so, the index is as the first
has it, unless that has a hole the other fills, so that a type expected
keeps its form: @nn a@ with @(a :=> Bottom) :=> Bottom@ is @nn a@.
-}
mergeIxWith :: Unfold -> Ix -> Ix -> Maybe Ix
mergeIxWith unfold a b = go unfoldRounds (normIx a) (normIx b)
  where
    go rounds x y = case (x, y) of
      (IxHole, _) -> Just y
      (_, IxHole) -> Just x
      (IxSucc x', IxSucc y') -> succIx <$> go rounds x' y'
      (IxSucc x', IxNat k) | k > 0 -> succIx <$> go rounds x' (IxNat (k - 1))
      (IxNat k, IxSucc y') | k > 0 -> succIx <$> go rounds (IxNat (k - 1)) y'
      (IxCon c xs, IxCon c' ys) | c == c', length xs == length ys -> IxCon c <$> zipWithM (go rounds) xs ys
      (IxFun f xs, IxFun f' ys) | f == f', length xs == length ys, Just zs <- zipWithM (go rounds) xs ys -> Just (IxFun f zs)
      (IxPartial f n k xs, IxPartial g m l ys) | f == g, n == m, k == l, length xs == length ys -> IxPartial f n k <$> zipWithM (go rounds) xs ys
      _ | x == y -> Just x
      -- Differing as they stand: both unfolded as far as they go, and compared as they are then.
      _ | rounds > 0, (x', y') <- (unfoldedBy unfold x, unfoldedBy unfold y), x' /= x || y' /= y -> keep x <$> go (rounds - 1) x' y'
      _ -> Nothing
    keep x merged = if hasHole x then merged else x

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
matchTy = matchTyWith noUnfold

-- | 'matchTy', its indices matched as 'matchIxWith' matches them, abbreviations unfolded.
matchTyWith :: Unfold -> (Int, Int) -> Ty -> Ty -> Assignment -> Maybe Assignment
matchTyWith unfold (n, m) = go
  where
    go p t s = case (p, t) of
      (_, THole) -> Just s
      (TParam i [], _) | i < n -> case IM.lookup i (asTypes s) of
        Nothing -> Just s {asTypes = IM.insert i t (asTypes s)}
        Just u -> (\v -> s {asTypes = IM.insert i v (asTypes s)}) <$> mergeTyWith unfold u t
      (TParam i ps, TParam j ts)
        | i < n
        , length ts >= length ps ->
            let (front, rest) = splitAt (length ts - length ps) ts
             in go (TParam i []) (TParam j front) s >>= \s' -> pairs (zip ps rest) s'
      (TParam i _, _) | i < n -> Just s
      (TParam i ps, TParam j ts) | i == j, length ps == length ts -> pairs (zip ps ts) s
      (TData a ps xs, TData b ts ys)
        | a == b
        , length ps == length ts ->
            pairs (zip ps ts) s >>= \s' ->
              -- An erased type, of no indices, determines none of them.
              if null xs || null ys
                then Just s'
                else if length xs == length ys then foldM (\acc (x, y) -> matchIxWith unfold m x y acc) s' (zip xs ys) else Nothing
      (TNat, TNat) -> Just s
      (TArrow a b, TArrow c d) -> pairs [(a, c), (b, d)] s
      _ -> Nothing
    pairs xs s0 = foldM (\acc (x, y) -> go x y acc) s0 xs

{- |
Match an index of a scheme of @m@ value parameters against an index, both in
normal form: a parameter, @IxParam i@ for @i < m@, takes what the other has
there; a numeral and the successor against the successors they are; a
constructor or a function against the same one applied, argument by argument.
Nothing when they disagree, as a successor against zero, or a constructor
against a variable, whose value nothing here knows.
-}
matchIx :: Int -> Ix -> Ix -> Assignment -> Maybe Assignment
matchIx = matchIxWith noUnfold

{- |
'matchIx', abbreviations unfolded where the indices differ as they stand:
both are unfolded as far as they go, once, and matched as they are then.  A
parameter takes what the other index has where it stands, as it stands.
-}
matchIxWith :: Unfold -> Int -> Ix -> Ix -> Assignment -> Maybe Assignment
matchIxWith unfold m p0 t0 s = go unfoldRounds (normIx p0) (normIx t0) s
  where
    go rounds p t acc = case (p, t) of
      (_, IxHole) -> Just acc
      (IxParam i, _) | i < m -> case IM.lookup i (asValues acc) of
        Nothing -> Just acc {asValues = IM.insert i t (asValues acc)}
        Just u -> (\v -> acc {asValues = IM.insert i v (asValues acc)}) <$> mergeIxWith unfold u t
      (IxSucc p', IxSucc t') -> go rounds p' t' acc
      (IxSucc p', IxNat k) | k > 0 -> go rounds p' (IxNat (k - 1)) acc
      (IxNat k, IxSucc t') | k > 0 -> go rounds (IxNat (k - 1)) t' acc
      (IxCon c ps, IxCon c' ts) | c == c', length ps == length ts -> foldM (\a (x, y) -> go rounds x y a) acc (zip ps ts)
      (IxFun f ps, IxFun f' ts) | f == f', length ps == length ts, Just acc' <- foldM (\a (x, y) -> go rounds x y a) acc (zip ps ts) -> Just acc'
      (IxPartial f n k ps, IxPartial g o l ts) | f == g, n == o, k == l, length ps == length ts -> foldM (\a (x, y) -> go rounds x y a) acc (zip ps ts)
      _ | p == t -> Just acc
      -- Differing as they stand: both unfolded as far as they go, and matched as they are then.
      _ | rounds > 0, (p', t') <- (unfoldedBy unfold p, unfoldedBy unfold t), p' /= p || t' /= t -> go (rounds - 1) p' t' acc
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
      IxPartial f arity prefix xs -> IxPartial f arity prefix (map ix xs)
      x -> x
