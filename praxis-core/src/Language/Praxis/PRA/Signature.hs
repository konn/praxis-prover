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
  functionSymbol,
  functionSymbolNamed,
  symbolArity,
  applySymbol,

  -- * Schema symbols
  SchemaSymbol (..),
  schemaSymbol,
  schemaSymbolNamed,
  schemaSymbolParamArity,
  schemaSymbolArity,
  applySchemaSymbol,

  -- * Signatures
  Signature,
  signature,
  signatureWithSchemas,
  symbols,
  schemas,
  lookupSymbol,
  lookupSchema,
  symbolOfCode,
  symbolOfFunction,
  signatureKernelEnv,
  withKernelEnv,
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
import Language.Praxis.PRA.PrimitiveRecursion.Code (PRFCode)
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
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
  , symbolFunction :: !F.SomeFunction
  , symbolHaskellName :: !(Maybe Name)
  -- ^ the Haskell binding holding the code, for spliced code to refer to
  }
  deriving (Show, Eq)

-- | A symbol for use at run time only.
symbol :: (KnownNat n) => String -> PRFCode n -> Symbol
symbol n c = functionSymbol n (F.Primitive c)

{- |
A symbol which also records where the code is bound in Haskell, so that the
quasiquoter can splice a reference to it: @'symbolNamed' "plus" \'plus plus@.
-}
symbolNamed :: (KnownNat n) => String -> Name -> PRFCode n -> Symbol
symbolNamed n hs c = Symbol n (F.SomeFunction (F.Primitive c)) (Just hs)

functionSymbol :: (KnownNat n) => String -> F.Function n -> Symbol
functionSymbol n f = Symbol n (F.SomeFunction f) Nothing

functionSymbolNamed :: (KnownNat n) => String -> Name -> F.Function n -> Symbol
functionSymbolNamed n hs f = Symbol n (F.SomeFunction f) (Just hs)

symbolArity :: Symbol -> Natural
symbolArity sym = case symbolFunction sym of
  F.SomeFunction (_ :: F.Function n) -> natVal (Proxy @n)

-- | Apply a symbol to arguments; 'Nothing' when their number is not the arity.
applySymbol :: Symbol -> [Term a] -> Maybe (Term a)
applySymbol sym args = case symbolFunction sym of
  F.SomeFunction (fun :: F.Function n)
    | fromIntegral (length args) == natVal (Proxy @n) -> App fun <$> SV.fromList' args
    | otherwise -> Nothing

-- | A schema symbol that can be instantiated with a concrete function.
data SchemaSymbol = forall k n. (KnownNat k, KnownNat n) => SchemaSymbol
  { schemaSymbolName :: !String
  , schemaSymbolFunction :: !(F.Function k -> F.Function n)
  , schemaSymbolHaskellName :: !(Maybe Name)
  }

instance Show SchemaSymbol where
  showsPrec d s = showParen (d > 10) (showString "SchemaSymbol " . showsPrec 11 (schemaSymbolName s))

instance Eq SchemaSymbol where
  s1 == s2 =
    schemaSymbolName s1 == schemaSymbolName s2
      && schemaSymbolParamArity s1 == schemaSymbolParamArity s2
      && schemaSymbolArity s1 == schemaSymbolArity s2
      && schemaSymbolHaskellName s1 == schemaSymbolHaskellName s2

schemaSymbol :: (KnownNat k, KnownNat n) => String -> (F.Function k -> F.Function n) -> SchemaSymbol
schemaSymbol n f = SchemaSymbol n f Nothing

schemaSymbolNamed :: (KnownNat k, KnownNat n) => String -> Name -> (F.Function k -> F.Function n) -> SchemaSymbol
schemaSymbolNamed n hs f = SchemaSymbol n f (Just hs)

schemaSymbolParamArity :: SchemaSymbol -> Natural
schemaSymbolParamArity (SchemaSymbol _ (_ :: F.Function k -> F.Function n) _) = natVal (Proxy @k)

schemaSymbolArity :: SchemaSymbol -> Natural
schemaSymbolArity (SchemaSymbol _ (_ :: F.Function k -> F.Function n) _) = natVal (Proxy @n)

applySchemaSymbol :: SchemaSymbol -> F.SomeFunction -> Either String F.SomeFunction
applySchemaSymbol (SchemaSymbol _ (inst :: F.Function k -> F.Function n) _) (F.SomeFunction (f :: F.Function m)) =
  case testEquality (sNat @m) (sNat @k) of
    Just Refl -> Right (F.SomeFunction (inst f))
    Nothing -> Left ("Schema parameter arity mismatch: expected " <> show (natVal (Proxy @k)) <> ", given " <> show (natVal (Proxy @m)))

-- | A table of symbols and schemas, keyed by name.
data Signature = Signature
  { sigSymbols :: !(Map String Symbol)
  , sigSchemas :: !(Map String SchemaSymbol)
  , sigEnv :: !(Either String F.KernelEnv)
  }
  deriving (Show, Eq)

{- | Left-biased symbol union. Definition tables are merged only when shared
identities agree; 'signatureKernelEnv' reports a conflicting merge.
-}
instance Semigroup Signature where
  Signature l ls le <> Signature r rs re =
    Signature (Map.union l r) (Map.union ls rs) (le >>= \a -> re >>= F.unionKernelEnv a)

instance Monoid Signature where
  mempty = Signature Map.empty Map.empty (Right F.emptyKernelEnv)

-- | A later symbol shadows an earlier one of the same name.
signature :: [Symbol] -> Signature
signature xs = Signature (Map.fromList (map (\s -> (symbolName s, s)) xs)) Map.empty (Right F.emptyKernelEnv)

signatureWithSchemas :: [Symbol] -> [SchemaSymbol] -> Signature
signatureWithSchemas xs schs =
  Signature
    (Map.fromList (map (\s -> (symbolName s, s)) xs))
    (Map.fromList (map (\s -> (schemaSymbolName s, s)) schs))
    (Right F.emptyKernelEnv)

symbols :: Signature -> [Symbol]
symbols (Signature m _ _) = Map.elems m

schemas :: Signature -> [SchemaSymbol]
schemas (Signature _ m _) = Map.elems m

lookupSymbol :: String -> Signature -> Maybe Symbol
lookupSymbol n (Signature m _ _) = Map.lookup n m

lookupSchema :: String -> Signature -> Maybe SchemaSymbol
lookupSchema n (Signature _ m _) = Map.lookup n m

-- | The symbol standing for a code, if the signature names it.
symbolOfCode :: (KnownNat n) => PRFCode n -> Signature -> Maybe Symbol
symbolOfCode c = symbolOfFunction (F.Primitive c)

symbolOfFunction :: (KnownNat n) => F.Function n -> Signature -> Maybe Symbol
symbolOfFunction f (Signature m _ _) = find ((== F.SomeFunction f) . symbolFunction) (Map.elems m)

-- | Resolve the checked table, reporting any conflicting signature union.
signatureKernelEnv :: Signature -> Either String F.KernelEnv
signatureKernelEnv (Signature _ _ env) = env

withKernelEnv :: F.KernelEnv -> Signature -> Signature
withKernelEnv env (Signature syms schs _) = Signature syms schs (Right env)
