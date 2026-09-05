{- |
Named function symbols.

A 'Language.Praxis.PRA.PrimitiveRecursion.PRFCode' is structural: a code has
no name, only a shape.  Any concrete syntax for terms therefore needs a table
saying which code @plus@ stands for and at which arity, and that table is a
'Signature'.  A symbol may also record the Haskell binding its code lives in,
which is what the quasiquoter refers to in the code it splices.
-}
module Language.Praxis.PRA.Signature (
  -- * Codes of hidden arity
  SomeCode (..),
  someCodeArity,

  -- * Symbols
  Symbol (..),
  symbol,
  symbolNamed,
  symbolArity,
  applySymbol,

  -- * Signatures
  Signature,
  signature,
  symbols,
  lookupSymbol,
  symbolOfCode,
) where

import Data.List (find)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Proxy (Proxy (..))
import Data.Sized qualified as SV
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Type.Natural (sNat)
import GHC.TypeNats (KnownNat, natVal)
import Language.Haskell.TH.Syntax (Name)
import Language.Praxis.PRA.PrimitiveRecursion (PRFCode)
import Language.Praxis.PRA.Syntax (Term (..))
import Numeric.Natural (Natural)

-- | A code with its arity hidden.
data SomeCode = forall n. (KnownNat n) => SomeCode !(PRFCode n)

instance Show SomeCode where
  showsPrec d (SomeCode c) = showParen (d > 10) (showString "SomeCode " . showsPrec 11 c)

instance Eq SomeCode where
  SomeCode (f :: PRFCode n) == SomeCode (g :: PRFCode m) =
    case testEquality (sNat @n) (sNat @m) of
      Just Refl -> f == g
      Nothing -> False

someCodeArity :: SomeCode -> Natural
someCodeArity (SomeCode (_ :: PRFCode n)) = natVal (Proxy @n)

-- | A code under a name.
data Symbol = Symbol
  { symbolName :: !String
  , symbolCode :: !SomeCode
  , symbolHaskellName :: !(Maybe Name)
  -- ^ the Haskell binding holding the code, for spliced code to refer to
  }
  deriving (Show, Eq)

-- | A symbol for use at run time only.
symbol :: (KnownNat n) => String -> PRFCode n -> Symbol
symbol n c = Symbol n (SomeCode c) Nothing

{- |
A symbol which also records where the code is bound in Haskell, so that the
quasiquoter can splice a reference to it: @'symbolNamed' "plus" \'plus plus@.
-}
symbolNamed :: (KnownNat n) => String -> Name -> PRFCode n -> Symbol
symbolNamed n hs c = Symbol n (SomeCode c) (Just hs)

symbolArity :: Symbol -> Natural
symbolArity = someCodeArity . symbolCode

-- | Apply a symbol to arguments; 'Nothing' when their number is not the arity.
applySymbol :: Symbol -> [Term a] -> Maybe (Term a)
applySymbol sym args = case symbolCode sym of
  SomeCode (code :: PRFCode n)
    | fromIntegral (length args) == natVal (Proxy @n) -> (code :$) <$> SV.fromList' args
    | otherwise -> Nothing

-- | A table of symbols, keyed by name.
newtype Signature = Signature (Map String Symbol)
  deriving (Show, Eq)

-- | Left-biased union.
instance Semigroup Signature where
  Signature l <> Signature r = Signature (Map.union l r)

instance Monoid Signature where
  mempty = Signature Map.empty

-- | A later symbol shadows an earlier one of the same name.
signature :: [Symbol] -> Signature
signature = Signature . Map.fromList . map (\s -> (symbolName s, s))

symbols :: Signature -> [Symbol]
symbols (Signature m) = Map.elems m

lookupSymbol :: String -> Signature -> Maybe Symbol
lookupSymbol n (Signature m) = Map.lookup n m

-- | The symbol standing for a code, if the signature names it.
symbolOfCode :: (KnownNat n) => PRFCode n -> Signature -> Maybe Symbol
symbolOfCode c (Signature m) = find ((== SomeCode c) . symbolCode) (Map.elems m)
