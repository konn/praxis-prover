{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

{- |
Named function symbols.

A 'Language.Praxis.PRA.PrimitiveRecursion.PRFCode' is structural: a code has
no name, only a shape.  Any concrete syntax for terms therefore needs a table
saying which code @plus@ stands for and at which arity, and that table is a
'Signature'.  A symbol may also record the Haskell binding its code lives in,
which is what the quasiquoter refers to in the code it splices, and the
equations it was defined by, which are its unfolding lemmas.

Besides plain symbols, a signature names schemas, which are instantiated at
a parameter function of a fixed arity, and variadic schemas, whose parameter
and result arities both grow with the number of variadic arguments.
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
  definedBy,
  symbolArity,
  applySymbol,

  -- * Schema symbols
  SchemaSymbol (..),
  schemaSymbol,
  schemaSymbolNamed,
  schemaSymbolParamArity,
  schemaSymbolArity,
  applySchemaSymbol,
  SchemaError (..),

  -- * Variadic schema symbols
  VariadicSchemaSymbol (..),
  variadicSchemaSymbol,
  variadicSchemaSymbolNamed,
  instantiateVariadicSchemaSymbol,
  applyVariadicSchemaSymbol,
  applyVariadicSame,
  applyVariadicPlus,
  applyVariadicMinus,
  variadicInstanceSame,
  variadicInstancePlus,
  variadicInstanceMinus,

  -- * Signatures
  Signature,
  signature,
  signatureWithSchemas,
  signatureWithVariadicSchemas,
  symbols,
  schemas,
  variadicSchemas,
  lookupSymbol,
  lookupSchema,
  lookupVariadicSchema,
  symbolOfCode,
  symbolOfFunction,
  signatureKernelEnv,
  withKernelEnv,

  -- * Instances of schemas
  SchemaInstance (..),
  instanceName,
  schemaInstanceOf,
  applySchemaNamed,
  instantiateSchemaAt,
  decompileProgram,
  decompileFunction,
) where

import Control.Exception (displayException)
import Control.Monad (foldM, guard, when)
import Data.Foldable (toList)
import Data.List (find)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Proxy (Proxy (..))
import Data.Sized qualified as SV
import Data.Text qualified as T
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Type.Natural (SBool (..), sNat, (%<=?))
import GHC.TypeNats (KnownNat, SomeNat (..), natVal, someNatVal, type (+), type (-), type (<=))
import Language.Haskell.TH.Syntax (Name)
import Language.Praxis.PRA.PrimitiveRecursion.Code (PRFCode (..), V)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Error (SchemaError (..))
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax (Equation)
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.Syntax (Abstraction (..), Term (..), suc)
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
  , symbolEquations :: ![Equation T.Text]
  {- ^ the clauses the symbol was defined by, in source order, when it was
  defined by equations: its unfolding lemmas, which
  "Language.Praxis.PRA.Tactic.Unfolding" states and proves
  -}
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
symbolNamed n hs c = Symbol n (F.SomeFunction (F.Primitive c)) (Just hs) []

functionSymbol :: (KnownNat n) => String -> F.Function n -> Symbol
functionSymbol n f = Symbol n (F.SomeFunction f) Nothing []

functionSymbolNamed :: (KnownNat n) => String -> Name -> F.Function n -> Symbol
functionSymbolNamed n hs f = Symbol n (F.SomeFunction f) (Just hs) []

{- |
The symbol with the equations it was defined by, in source order.  Each is an
unfolding lemma of the symbol, which "Language.Praxis.PRA.Tactic.Unfolding"
states and proves: the compiler of
"Language.Praxis.PRA.PrimitiveRecursion.Environment" records them, and a
signature spliced by the quasiquoter keeps them.
-}
definedBy :: [Equation T.Text] -> Symbol -> Symbol
definedBy eqs sym = sym {symbolEquations = eqs}

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

-- | Instantiate at a parameter, which must have the schema's parameter arity.
applySchemaSymbol :: SchemaSymbol -> F.SomeFunction -> Either SchemaError F.SomeFunction
applySchemaSymbol (SchemaSymbol name (inst :: F.Function k -> F.Function n) _) (F.SomeFunction (f :: F.Function m)) =
  case testEquality (sNat @m) (sNat @k) of
    Just Refl -> Right (F.SomeFunction (inst f))
    Nothing -> Left (SchemaParameterArityMismatch (T.pack name) (natVal (Proxy @k)) (natVal (Proxy @m)))

{- | A schema with a variadic argument group. With @k@ variadic arguments its
parameter has arity @paramArity + k@ and the instance has arity
@fixedArity + k@; @k@ is therefore determined by either side.
-}
data VariadicSchemaSymbol = VariadicSchemaSymbol
  { variadicSchemaName :: !String
  , variadicSchemaFixedArity :: !Natural
  -- ^ the number of non-variadic arguments
  , variadicSchemaParamArity :: !Natural
  -- ^ the parameter's arity with no variadic arguments
  , variadicSchemaInstance :: Natural -> Either SchemaError SchemaSymbol
  {- ^ the instance at a number of variadic arguments; lazy, as the
  instantiation of a spliced schema refers back to its own signature
  -}
  , variadicSchemaHaskellName :: !(Maybe Name)
  }

instance Show VariadicSchemaSymbol where
  showsPrec d s =
    showParen
      (d > 10)
      ( showString "VariadicSchemaSymbol "
          . showsPrec 11 (variadicSchemaName s)
          . showString " "
          . showsPrec 11 (variadicSchemaFixedArity s)
          . showString " "
          . showsPrec 11 (variadicSchemaParamArity s)
      )

instance Eq VariadicSchemaSymbol where
  s1 == s2 =
    variadicSchemaName s1 == variadicSchemaName s2
      && variadicSchemaFixedArity s1 == variadicSchemaFixedArity s2
      && variadicSchemaParamArity s1 == variadicSchemaParamArity s2
      && variadicSchemaHaskellName s1 == variadicSchemaHaskellName s2

variadicSchemaSymbol :: String -> Natural -> Natural -> (Natural -> Either SchemaError SchemaSymbol) -> VariadicSchemaSymbol
variadicSchemaSymbol n fixed pArity inst = VariadicSchemaSymbol n fixed pArity inst Nothing

variadicSchemaSymbolNamed :: String -> Name -> Natural -> Natural -> (Natural -> Either SchemaError SchemaSymbol) -> VariadicSchemaSymbol
variadicSchemaSymbolNamed n hs fixed pArity inst = VariadicSchemaSymbol n fixed pArity inst (Just hs)

-- | The instance at a number of variadic arguments, checked for its arities.
instantiateVariadicSchemaSymbol :: VariadicSchemaSymbol -> Natural -> Either SchemaError SchemaSymbol
instantiateVariadicSchemaSymbol sym k = do
  inst <- variadicSchemaInstance sym k
  let expectedParam = variadicSchemaParamArity sym + k
      expectedArity = variadicSchemaFixedArity sym + k
  when (schemaSymbolParamArity inst /= expectedParam || schemaSymbolArity inst /= expectedArity) $
    Left
      ( VariadicInstanceArityMismatch
          (T.pack (variadicSchemaName sym))
          k
          (schemaSymbolParamArity inst, schemaSymbolArity inst)
          (expectedParam, expectedArity)
      )
  pure inst

-- | Apply at the number of variadic arguments the parameter's arity determines.
applyVariadicSchemaSymbol :: VariadicSchemaSymbol -> F.SomeFunction -> Either SchemaError F.SomeFunction
applyVariadicSchemaSymbol sym f@(F.SomeFunction (_ :: F.Function m)) = do
  let arity = natVal (Proxy @m)
      least = variadicSchemaParamArity sym
  when (arity < least) $
    Left (VariadicParameterTooSmall (T.pack (variadicSchemaName sym)) least arity)
  inst <- instantiateVariadicSchemaSymbol sym (arity - least)
  applySchemaSymbol inst f

{- | Typed application, for spliced bindings whose arities are checked by the
compiler; the instance's arities are rechecked here and cannot disagree.
-}
applyVariadicAt :: forall m r. (KnownNat m, KnownNat r) => VariadicSchemaSymbol -> F.Function m -> F.Function r
applyVariadicAt sym f = case applyVariadicSchemaSymbol sym (F.SomeFunction f) of
  Left err -> error (variadicSchemaName sym <> ": " <> displayException err)
  Right (F.SomeFunction (g :: F.Function n)) -> case testEquality (sNat @n) (sNat @r) of
    Just Refl -> g
    Nothing ->
      error
        ( variadicSchemaName sym
            <> ": instance arity "
            <> show (natVal (Proxy @n))
            <> " differs from the expected "
            <> show (natVal (Proxy @r))
        )

-- | A variadic schema whose instances have the arity of their parameter.
applyVariadicSame :: forall m. (KnownNat m) => VariadicSchemaSymbol -> F.Function m -> F.Function m
applyVariadicSame = applyVariadicAt

-- | A variadic schema whose instances take @d@ more arguments than their parameter.
applyVariadicPlus :: forall d m. (KnownNat d, KnownNat m) => VariadicSchemaSymbol -> F.Function m -> F.Function (m + d)
applyVariadicPlus = applyVariadicAt

-- | A variadic schema whose instances take @d@ fewer arguments than their parameter.
applyVariadicMinus :: forall d m. (KnownNat d, KnownNat m, d <= m) => VariadicSchemaSymbol -> F.Function m -> F.Function (m - d)
applyVariadicMinus = applyVariadicAt

withArity :: Natural -> (forall m. (KnownNat m) => Proxy m -> r) -> r
withArity n k = case someNatVal n of
  SomeNat proxy -> k proxy

-- | Recover the instances of a variadic schema from its typed Haskell binding.
variadicInstanceSame ::
  String ->
  Natural ->
  (forall m. (KnownNat m) => F.Function m -> F.Function m) ->
  Natural ->
  Either SchemaError SchemaSymbol
variadicInstanceSame n pArity f k = withArity (pArity + k) \(_ :: Proxy m) -> Right (SchemaSymbol n (f @m) Nothing)

variadicInstancePlus ::
  forall d.
  (KnownNat d) =>
  String ->
  Natural ->
  (forall m. (KnownNat m) => F.Function m -> F.Function (m + d)) ->
  Natural ->
  Either SchemaError SchemaSymbol
variadicInstancePlus n pArity f k = withArity (pArity + k) \(_ :: Proxy m) -> Right (SchemaSymbol n (f @m) Nothing)

variadicInstanceMinus ::
  forall d.
  (KnownNat d) =>
  String ->
  Natural ->
  (forall m. (KnownNat m, d <= m) => F.Function m -> F.Function (m - d)) ->
  Natural ->
  Either SchemaError SchemaSymbol
variadicInstanceMinus n pArity f k = withArity (pArity + k) \(_ :: Proxy m) ->
  case sNat @d %<=? sNat @m of
    STrue -> Right (SchemaSymbol n (f @m) Nothing)
    SFalse -> Left (VariadicParameterBelowOffset (T.pack n) (pArity + k) (natVal (Proxy @d)))

-- | A table of symbols and schemas, keyed by name.
data Signature = Signature
  { sigSymbols :: !(Map String Symbol)
  , sigSchemas :: !(Map String SchemaSymbol)
  , sigVariadics :: !(Map String VariadicSchemaSymbol)
  , sigEnv :: !(Either F.KernelError F.KernelEnv)
  }
  deriving (Show, Eq)

{- | Left-biased symbol union. Definition tables are merged only when shared
identities agree; 'signatureKernelEnv' reports a conflicting merge.
-}
instance Semigroup Signature where
  Signature l ls lv le <> Signature r rs rv re =
    Signature (Map.union l r) (Map.union ls rs) (Map.union lv rv) (le >>= \a -> re >>= F.unionKernelEnv a)

instance Monoid Signature where
  mempty = Signature Map.empty Map.empty Map.empty (Right F.emptyKernelEnv)

-- | A later symbol shadows an earlier one of the same name.
signature :: [Symbol] -> Signature
signature xs = signatureWithVariadicSchemas xs [] []

signatureWithSchemas :: [Symbol] -> [SchemaSymbol] -> Signature
signatureWithSchemas xs schs = signatureWithVariadicSchemas xs schs []

signatureWithVariadicSchemas :: [Symbol] -> [SchemaSymbol] -> [VariadicSchemaSymbol] -> Signature
signatureWithVariadicSchemas xs schs vars =
  Signature
    (Map.fromList (map (\s -> (symbolName s, s)) xs))
    (Map.fromList (map (\s -> (schemaSymbolName s, s)) schs))
    (Map.fromList (map (\s -> (variadicSchemaName s, s)) vars))
    (Right F.emptyKernelEnv)

symbols :: Signature -> [Symbol]
symbols (Signature m _ _ _) = Map.elems m

schemas :: Signature -> [SchemaSymbol]
schemas (Signature _ m _ _) = Map.elems m

variadicSchemas :: Signature -> [VariadicSchemaSymbol]
variadicSchemas (Signature _ _ m _) = Map.elems m

lookupSymbol :: String -> Signature -> Maybe Symbol
lookupSymbol n (Signature m _ _ _) = Map.lookup n m

lookupSchema :: String -> Signature -> Maybe SchemaSymbol
lookupSchema n (Signature _ m _ _) = Map.lookup n m

lookupVariadicSchema :: String -> Signature -> Maybe VariadicSchemaSymbol
lookupVariadicSchema n (Signature _ _ m _) = Map.lookup n m

-- | The symbol standing for a code, if the signature names it.
symbolOfCode :: (KnownNat n) => PRFCode n -> Signature -> Maybe Symbol
symbolOfCode c = symbolOfFunction (F.Primitive c)

symbolOfFunction :: (KnownNat n) => F.Function n -> Signature -> Maybe Symbol
symbolOfFunction f (Signature m _ _ _) = find ((== F.SomeFunction f) . symbolFunction) (Map.elems m)

-- | Resolve the checked table, reporting any conflicting signature union.
signatureKernelEnv :: Signature -> Either F.KernelError F.KernelEnv
signatureKernelEnv (Signature _ _ _ env) = env

withKernelEnv :: F.KernelEnv -> Signature -> Signature
withKernelEnv env (Signature syms schs vars _) = Signature syms schs vars (Right env)

-- * Instances of schemas

{- |
A function which instantiates a schema of the signature: the schema, the
number of variadic arguments it was instantiated with, and its parameter.
-}
data SchemaInstance = SchemaInstance
  { instanceSchema :: !(Either SchemaSymbol VariadicSchemaSymbol)
  , instanceExtras :: !Natural
  , instanceParameter :: !F.SomeFunction
  }
  deriving (Show, Eq)

-- | The name of the schema an instance is of.
instanceName :: SchemaInstance -> String
instanceName = either schemaSymbolName variadicSchemaName . instanceSchema

{- |
The schema an inline code instantiates, with its parameter: the code is
matched against the schema instantiated at a placeholder, whose calls bind
the parameter.  The variadic schemas are tried first, each at the number of
variadic arguments the arity of the code leaves, then the plain ones.
-}
schemaInstanceOf :: forall n. (KnownNat n) => Signature -> F.Function n -> Maybe SchemaInstance
schemaInstanceOf sig = \case
  F.Inline code -> listToMaybe (mapMaybe (variadic code) (variadicSchemas sig) <> mapMaybe (plain code) (schemas sig))
  _ -> Nothing
  where
    arity = natVal (Proxy @n)
    variadic code sym = do
      guard (arity >= variadicSchemaFixedArity sym)
      let extras = arity - variadicSchemaFixedArity sym
      inst <- either (const Nothing) Just (instantiateVariadicSchemaSymbol sym extras)
      param <- parameterOf inst code
      pure (SchemaInstance (Right sym) extras param)
    plain code sch = do
      guard (schemaSymbolArity sch == arity)
      param <- parameterOf sch code
      pure (SchemaInstance (Left sch) 0 param)

-- | The parameter a code instantiates a schema at, by matching the code against the instantiation at a placeholder.
parameterOf :: forall n. (KnownNat n) => SchemaSymbol -> F.Program n -> Maybe F.SomeFunction
parameterOf (SchemaSymbol _ (inst :: F.Function k -> F.Function m) _) code =
  case testEquality (sNat @m) (sNat @n) of
    Just Refl -> do
      let template = F.functionProgram (inst (F.Defined (F.DefId placeholder)))
      bound <- unify Nothing template code
      bound
    Nothing -> Nothing
  where
    placeholder = T.pack "«parameter»"

    unify :: forall j. (KnownNat j) => Maybe F.SomeFunction -> F.Program j -> F.Program j -> Maybe (Maybe F.SomeFunction)
    unify acc template code' = case (template, code') of
      (F.Call (F.DefId ident), _)
        | ident == placeholder -> case acc of
            Nothing -> Just (Just (F.SomeFunction (F.programFunction code')))
            Just p
              | p == F.SomeFunction (F.programFunction code') -> Just acc
              | otherwise -> Nothing
      (F.Base x, F.Base y) | x == y -> Just acc
      (F.Call x, F.Call y) | x == y -> Just acc
      (F.Opaque x, F.Opaque y) | x == y -> Just acc
      (F.Comp (g :: F.Program i) xs, F.Comp (h :: F.Program l) ys) -> case testEquality (sNat @i) (sNat @l) of
        Just Refl -> do
          acc' <- unify acc g h
          foldM (\a (x, y) -> unify a x y) acc' (zip (toList xs) (toList ys))
        Nothing -> Nothing
      (F.Rec b s, F.Rec b' s') -> unify acc b b' >>= \acc' -> unify acc' s s'
      _ -> Nothing

{- |
The instance of the schema of the name at a parameter, applied to arguments:
a variadic schema is instantiated at the number of variadic arguments the
arity of the parameter determines, a plain one at its parameter arity.  The
arguments must be as many as the arity of the instance.
-}
applySchemaNamed :: Signature -> String -> F.SomeFunction -> [Term a] -> Either SchemaError (Term a)
applySchemaNamed sig n param args = do
  fun <- case (lookupVariadicSchema n sig, lookupSchema n sig) of
    (Just sym, _) -> applyVariadicSchemaSymbol sym param
    (Nothing, Just sch) -> applySchemaSymbol sch param
    (Nothing, Nothing) -> Left (SchemaNotInSignature (T.pack n))
  case fun of
    F.SomeFunction (f :: F.Function m) -> case SV.fromList' args of
      Just xs -> Right (App f xs)
      Nothing -> Left (InstanceArgumentCountMismatch (T.pack n) (natVal (Proxy @m)) (fromIntegral (length args)))

{- |
The instance of the schema of the name at the function of an abstraction,
applied to the arguments and then to the terms the function captures: what
a proof spliced for a derived rule builds where the rule had the schema at a
term metavariable with parameters.  The rule was checked, so a failure is an
error.
-}
instantiateSchemaAt :: Signature -> String -> Abstraction a -> [Term a] -> Term a
instantiateSchemaAt sig n a args =
  either (\err -> error ("Language.Praxis.PRA.Signature.instantiateSchemaAt: " <> n <> ": " <> displayException err)) id $
    applySchemaNamed sig n (abstractionFunction a) (args <> abstractionCaptured a)

{- |
A program applied to the terms in its slots, its compositions unfolded: the
body of a lambda, over the terms its parameters stand for.
-}
decompileProgram :: forall p b. (KnownNat p) => V p (Term b) -> F.Program p -> Term b
decompileProgram slots = \case
  F.Comp g xs -> apply g (fmap (decompileProgram slots) xs)
  code -> apply code slots
  where
    apply :: forall m. (KnownNat m) => F.Program m -> V m (Term b) -> Term b
    apply g ys = case g of
      F.Base Zero -> Lit 0
      F.Base (Proj i) -> SV.sIndex i ys
      F.Base Succ -> suc (SV.head ys)
      F.Base code -> App (F.Primitive code) ys
      F.Call ident -> App (F.Defined ident) ys
      F.Opaque ident -> App (F.Abstract ident) ys
      _ -> App (F.Inline g) ys

-- | A function applied to terms as a term, its code unfolded; 'Nothing' when they are not as many as its arity.
decompileFunction :: F.SomeFunction -> [Term b] -> Maybe (Term b)
decompileFunction (F.SomeFunction f) slots = (`decompileProgram` F.functionProgram f) <$> SV.fromList' slots
