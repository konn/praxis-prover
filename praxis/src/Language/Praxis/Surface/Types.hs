{-# LANGUAGE OverloadedStrings #-}

{- |
The types of the surface language, and their unification.

A type is a data type applied to types, @Nat@, a function type, a type
parameter of the enclosing signature — applied to types when its kind is
higher, as @f@ in @data Term r f v = … App (f (Formula r f v) (Term r f v))@
— or a unification variable.  Types are checked, not trusted: nothing in the
core depends on them, which sees only the codes and the membership predicates
the encoding derives from the data declarations.
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

  -- * Unification
  Unify,
  runUnify,
  freshMeta,
  unify,
  unifyWith,
  St,
  initialSt,
  zonk,
  instantiateScheme,
  UnifyError (..),
) where

import Control.Monad (unless, zipWithM_)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State.Strict (MonadState, StateT, evalStateT, gets, modify')
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
  | -- | a unification variable
    TMeta !Int
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
  TMeta _ -> []
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
  TMeta _ -> True
  TData _ ts -> all firstOrder ts
  TNat -> True
  TArrow _ _ -> False

-- | A type, its parameters by the names given, qualified data names by their last segment.
renderTy :: [Text] -> Ty -> String
renderTy names = go (0 :: Int)
  where
    go d = \case
      TParam i [] -> name i
      TParam i ts -> paren (d > 1) (unwords (name i : map (go 2) ts))
      TMeta m -> "?" <> show m
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

-- * Unification

-- | Why two types do not unify.
data UnifyError
  = Mismatch !Ty !Ty
  | Occurs !Int !Ty
  deriving stock (Show, Eq)

-- | Unification variables and their solutions, and the next fresh one.
data St = St
  { stNext :: !Int
  , stSolved :: !(IntMap Ty)
  }

-- | No variables yet.
initialSt :: St
initialSt = St 0 IM.empty

type Unify = StateT St (Either UnifyError)

runUnify :: Unify a -> Either UnifyError a
runUnify m = evalStateT m initialSt

freshMeta :: (MonadState St m) => m Ty
freshMeta = do
  n <- gets stNext
  modify' \s -> s {stNext = n + 1}
  pure (TMeta n)

-- | The type with every solved variable replaced by its solution.
zonk :: (MonadState St m) => Ty -> m Ty
zonk = \case
  TMeta m ->
    gets (IM.lookup m . stSolved) >>= \case
      Nothing -> pure (TMeta m)
      Just t -> do
        t' <- zonk t
        modify' \s -> s {stSolved = IM.insert m t' (stSolved s)}
        pure t'
  TParam i ts -> TParam i <$> traverse zonk ts
  TData n ts -> TData n <$> traverse zonk ts
  TNat -> pure TNat
  TArrow a b -> TArrow <$> zonk a <*> zonk b

unify :: (MonadState St m, MonadError UnifyError m) => Ty -> Ty -> m ()
unify = unifyWith id

-- | Unify, reporting a failure as the error the injection makes of it.
unifyWith :: (MonadState St m, MonadError e m) => (UnifyError -> e) -> Ty -> Ty -> m ()
unifyWith inj t1 t2 = do
  a <- zonk t1
  b <- zonk t2
  case (a, b) of
    (TMeta m, TMeta n) | m == n -> pure ()
    (TMeta m, t) -> bind m t
    (t, TMeta m) -> bind m t
    (TParam i ts, TParam j us) | i == j, length ts == length us -> zipWithM_ (unifyWith inj) ts us
    (TData n ts, TData m us) | n == m, length ts == length us -> zipWithM_ (unifyWith inj) ts us
    (TNat, TNat) -> pure ()
    (TArrow x y, TArrow z w) -> unifyWith inj x z *> unifyWith inj y w
    _ -> throwError (inj (Mismatch a b))
  where
    bind m t = do
      unless (m `notElem` metas t) (throwError (inj (Occurs m t)))
      modify' \s -> s {stSolved = IM.insert m t (stSolved s)}
    metas = \case
      TMeta n -> [n]
      TParam _ ts -> concatMap metas ts
      TData _ ts -> concatMap metas ts
      TNat -> []
      TArrow x y -> metas x <> metas y

-- | The type of a scheme with fresh variables for its parameters, and those variables.
instantiateScheme :: (MonadState St m) => Scheme -> m (Ty, [Ty])
instantiateScheme (Scheme params ty) = do
  metas <- traverse (const freshMeta) params
  pure (subst metas ty, metas)
  where
    subst ms = \case
      TParam i ts
        | i < length ms -> case (ms !! i, ts) of
            (m, []) -> m
            (m, _) -> m -- a higher-kinded parameter applied: its instance is opaque here
        | otherwise -> TParam i (map (subst ms) ts)
      TMeta n -> TMeta n
      TData n ts -> TData n (map (subst ms) ts)
      TNat -> TNat
      TArrow a b -> TArrow (subst ms a) (subst ms b)
