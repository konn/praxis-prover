{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{- | Lift instances missing from sized-1.1 and type-natural-1.3. Keep these
dependency compatibility instances separate from the PRF data types.
-}
module Language.Praxis.PRA.PrimitiveRecursion.TH.Internal () where

import Data.Proxy (Proxy (..))
import Data.Sized (Sized, pattern Nil, pattern (:<))
import Data.Sized qualified as SV
import Data.Type.Ordinal (Ordinal, ordToNatural)
import Data.Vector qualified as V
import GHC.TypeNats (KnownNat, natVal)
import Language.Haskell.TH.Syntax (Exp (..), Lift (..), Lit (..), TyLit (..), Type (..), unsafeCodeCoerce)

instance (KnownNat n) => Lift (Ordinal n) where
  lift index = pure (SigE (LitE (IntegerL (toInteger (ordToNatural index)))) (AppT (ConT ''Ordinal) (LitT (NumTyLit (toInteger (natVal (Proxy @n)))))))
  liftTyped = unsafeCodeCoerce . lift

instance (Lift a) => Lift (Sized V.Vector n a) where
  lift = foldr (\x rest -> [|$(lift x) :< $rest|]) [|Nil|] . SV.toList

  -- The constructor spine has exactly the length of the original sized value.
  liftTyped = unsafeCodeCoerce . lift
