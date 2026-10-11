{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{- | Lift instances missing from sized-1.1 and type-natural-1.3. Keep these
dependency compatibility instances separate from the PRF data types.
-}
module Language.Praxis.PRA.PrimitiveRecursion.TH.Internal (arityType, liftSizedWith) where

import Data.Proxy (Proxy (..))
import Data.Sized (Sized, pattern Nil, pattern (:<))
import Data.Type.Ordinal (Ordinal, ordToNatural)
import Data.Vector qualified as V
import GHC.TypeNats (KnownNat, natVal)
import Language.Haskell.TH.Desugar qualified as D
import Language.Haskell.TH.Syntax (Code, Lift (..), Quote, TyLit (..), Type, unTypeCode)

instance (KnownNat n) => Lift (Ordinal n) where
  -- Untyped splices also retain the bound: otherwise a lifted ordinal could
  -- default to Integer or be instantiated at an invalid, smaller bound.
  lift index = [|$(unTypeCode (liftTyped index)) :: Ordinal $(arityType @n)|]
  liftTyped index = [||fromInteger $$(liftTyped (toInteger (ordToNatural index)))||]

instance (KnownNat n, Lift a) => Lift (Sized V.Vector n a) where
  lift = unTypeCode . liftTyped
  liftTyped = liftSizedWith liftTyped

-- | A concrete index at an existential or untyped quotation boundary.
arityType :: forall n m. (KnownNat n, Quote m) => m Type
arityType = pure (D.typeToTH (D.DLitT (NumTyLit (toInteger (natVal (Proxy @n))))))

-- | Preserve the length evidence at every step of the quoted constructor spine.
liftSizedWith :: (Quote m, KnownNat n) => (a -> Code m b) -> Sized V.Vector n a -> Code m (Sized V.Vector n b)
liftSizedWith _ Nil = [||Nil||]
liftSizedWith f (x :< xs) = [||$$(f x) :< $$(liftSizedWith f xs)||]
