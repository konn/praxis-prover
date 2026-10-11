{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

-- | Reified types of the explicit core. Holes belong to elaboration, not here.
module Language.Praxis.Surface.Core.Types (
  Type (..),
  Index (..),
  SType (..),
  SIndex (..),
  List (..),
  SomeType (..),
  reflectType,
  forgetType,
  sameType,
  mapTypes,
) where

import Data.Kind qualified as K
import Data.Proxy (Proxy (..))
import Data.Text qualified as T
import Data.Type.Equality ((:~:) (..))
import GHC.TypeLits (KnownSymbol, SomeSymbol (..), Symbol, sameSymbol, someSymbolVal, symbolVal)
import GHC.TypeNats (KnownNat, Nat, SomeNat (..), natVal, sameNat, someNatVal)
import Language.Praxis.Surface.Types qualified as S

-- | Types and indices are syntax, not Haskell interpretations of surface values.
data Type
  = Natural
  | Parameter Nat [Type]
  | Family Symbol [Type] [Index]
  | Function Type Type

data Index
  = ParameterIndex Nat
  | VariableIndex Symbol
  | NumberIndex Nat
  | SuccessorIndex Index
  | ConstructorIndex Symbol [Index]
  | FunctionIndex Symbol [Index]

data List (f :: k -> K.Type) (xs :: [k]) where
  Nil :: List f '[]
  Cons :: f x -> List f xs -> List f (x ': xs)

data SType (t :: Type) where
  SNatural :: SType 'Natural
  SParameter :: (KnownNat n) => Proxy n -> List SType ts -> SType ('Parameter n ts)
  SFamily :: (KnownSymbol n) => Proxy n -> List SType ts -> List SIndex is -> SType ('Family n ts is)
  SFunction :: SType a -> SType b -> SType ('Function a b)

data SIndex (i :: Index) where
  SParameterIndex :: (KnownNat n) => Proxy n -> SIndex ('ParameterIndex n)
  SVariableIndex :: (KnownSymbol n) => Proxy n -> SIndex ('VariableIndex n)
  SNumberIndex :: (KnownNat n) => Proxy n -> SIndex ('NumberIndex n)
  SSuccessorIndex :: SIndex n -> SIndex ('SuccessorIndex n)
  SConstructorIndex :: (KnownSymbol n) => Proxy n -> List SIndex xs -> SIndex ('ConstructorIndex n xs)
  SFunctionIndex :: (KnownSymbol n) => Proxy n -> List SIndex xs -> SIndex ('FunctionIndex n xs)

data SomeType where
  SomeType :: SType t -> SomeType

data SomeIndex where
  SomeIndex :: SIndex i -> SomeIndex

data SomeList f where
  SomeList :: List f xs -> SomeList f

mapTypes :: (forall t. SType t -> a) -> List SType ts -> [a]
mapTypes f = listMap f

listMap :: (forall t. f t -> a) -> List f ts -> [a]
listMap _ Nil = []
listMap f (Cons t ts) = f t : listMap f ts

reflectList :: (a -> Either String (Some f)) -> [a] -> Either String (SomeList f)
reflectList _ [] = Right (SomeList Nil)
reflectList f (x : xs) = do
  Some t <- f x
  SomeList ts <- reflectList f xs
  pure (SomeList (Cons t ts))

data Some f where
  Some :: f t -> Some f

reflectType :: S.Ty -> Either String SomeType
reflectType = go
  where
    types ts = reflectList (\t -> do SomeType st <- go t; pure (Some st)) ts
    indices is = reflectList (\i -> do SomeIndex si <- reflectIndex i; pure (Some si)) is
    go S.TNat = Right (SomeType SNatural)
    go S.THole = Left "an unresolved type hole at the explicit core boundary"
    go (S.TParam n ts)
      | n < 0 = Left "a negative type parameter at the explicit core boundary"
      | otherwise = do
          SomeList sts <- types ts
          case someNatVal (fromIntegral n) of
            SomeNat p -> pure (SomeType (SParameter p sts))
    go (S.TData name ts is) = do
      SomeList sts <- types ts
      SomeList sis <- indices is
      case someSymbolVal (T.unpack name) of
        SomeSymbol p -> pure (SomeType (SFamily p sts sis))
    go (S.TArrow a b) = do
      SomeType sa <- go a
      SomeType sb <- go b
      pure (SomeType (SFunction sa sb))

reflectIndex :: S.Ix -> Either String SomeIndex
reflectIndex = go . S.normIx
  where
    indices xs = reflectList (\i -> do SomeIndex si <- go i; pure (Some si)) xs
    go S.IxHole = Left "an unresolved index hole at the explicit core boundary"
    go (S.IxParam n)
      | n < 0 = Left "a negative index parameter at the explicit core boundary"
      | otherwise = case someNatVal (fromIntegral n) of
          SomeNat p -> Right (SomeIndex (SParameterIndex p))
    go (S.IxVar name) = case someSymbolVal (T.unpack name) of
      SomeSymbol p -> Right (SomeIndex (SVariableIndex p))
    go (S.IxNat n) = case someNatVal n of
      SomeNat p -> Right (SomeIndex (SNumberIndex p))
    go (S.IxSucc i) = do
      SomeIndex si <- go i
      pure (SomeIndex (SSuccessorIndex si))
    go (S.IxCon name xs) = do
      SomeList sis <- indices xs
      case someSymbolVal (T.unpack name) of
        SomeSymbol p -> Right (SomeIndex (SConstructorIndex p sis))
    go (S.IxFun name xs) = do
      SomeList sis <- indices xs
      case someSymbolVal (T.unpack name) of
        SomeSymbol p -> Right (SomeIndex (SFunctionIndex p sis))

forgetType :: SType t -> S.Ty
forgetType = \case
  SNatural -> S.TNat
  SParameter p ts -> S.TParam (fromIntegral (natVal p)) (listMap forgetType ts)
  SFamily p ts is -> S.TData (T.pack (symbolVal p)) (listMap forgetType ts) (listMap forgetIndex is)
  SFunction a b -> S.TArrow (forgetType a) (forgetType b)

forgetIndex :: SIndex i -> S.Ix
forgetIndex = \case
  SParameterIndex p -> S.IxParam (fromIntegral (natVal p))
  SVariableIndex p -> S.IxVar (T.pack (symbolVal p))
  SNumberIndex p -> S.IxNat (natVal p)
  SSuccessorIndex i -> S.IxSucc (forgetIndex i)
  SConstructorIndex p xs -> S.IxCon (T.pack (symbolVal p)) (listMap forgetIndex xs)
  SFunctionIndex p xs -> S.IxFun (T.pack (symbolVal p)) (listMap forgetIndex xs)

sameList :: (forall a b. f a -> f b -> Maybe (a :~: b)) -> List f as -> List f bs -> Maybe (as :~: bs)
sameList _ Nil Nil = Just Refl
sameList eq (Cons a as) (Cons b bs) = do
  Refl <- eq a b
  Refl <- sameList eq as bs
  pure Refl
sameList _ _ _ = Nothing

sameType :: SType a -> SType b -> Maybe (a :~: b)
sameType SNatural SNatural = Just Refl
sameType (SParameter p ps) (SParameter q qs) = do
  Refl <- sameNat p q
  Refl <- sameList sameType ps qs
  pure Refl
sameType (SFamily p ps is) (SFamily q qs js) = do
  Refl <- sameSymbol p q
  Refl <- sameList sameType ps qs
  Refl <- sameList sameIndex is js
  pure Refl
sameType (SFunction a b) (SFunction c d) = do
  Refl <- sameType a c
  Refl <- sameType b d
  pure Refl
sameType _ _ = Nothing

sameIndex :: SIndex a -> SIndex b -> Maybe (a :~: b)
sameIndex (SParameterIndex p) (SParameterIndex q) = do Refl <- sameNat p q; pure Refl
sameIndex (SVariableIndex p) (SVariableIndex q) = do Refl <- sameSymbol p q; pure Refl
sameIndex (SNumberIndex p) (SNumberIndex q) = do Refl <- sameNat p q; pure Refl
sameIndex (SSuccessorIndex p) (SSuccessorIndex q) = do Refl <- sameIndex p q; pure Refl
sameIndex (SConstructorIndex p ps) (SConstructorIndex q qs) = do
  Refl <- sameSymbol p q
  Refl <- sameList sameIndex ps qs
  pure Refl
sameIndex (SFunctionIndex p ps) (SFunctionIndex q qs) = do
  Refl <- sameSymbol p q
  Refl <- sameList sameIndex ps qs
  pure Refl
sameIndex _ _ = Nothing
