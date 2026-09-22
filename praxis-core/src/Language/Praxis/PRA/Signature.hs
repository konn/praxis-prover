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
  schemaSymbolWith,
  parameterAt,
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
  applySchemaAt,
  instantiateSchemaAt,
  decompileProgram,
  decompileFunction,

  -- * Schematic substitution
  InstantiationError (..),
  instantiateSchematicTerm,
  instantiateSchematicTermAt,
) where

import Control.Exception (displayException)
import Control.Monad (foldM, forM_, guard, when)
import Data.Foldable (toList)
import Data.HashSet qualified as HS
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
import Language.Praxis.Name (Fresh (..))
import Language.Praxis.PRA.PrimitiveRecursion.Code (PRFCode (..), V)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Error (SchemaError (..))
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax (Equation)
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.Syntax (Abstraction (..), Term (..), abstractName, abstraction, applyAbstraction, suc)
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

{- |
A schema symbol: a function of functions, its parameters, each of an arity
of its own.  An instance is the schema's code with the parameters
substituted for their calls.  A schema recurs with its parameters unchanged,
so an instance at primitive recursive functions is primitive recursive: a
schema abbreviates a family of definitions, and adds nothing to PRA.
-}
data SchemaSymbol = SchemaSymbol
  { schemaSymbolName :: !String
  , schemaSymbolParamArities :: ![Natural]
  -- ^ the arity of each parameter, in order
  , schemaSymbolArity :: !Natural
  -- ^ the arity of every instance
  , schemaSymbolInstantiate :: [F.SomeFunction] -> Either SchemaError F.SomeFunction
  {- ^ the instance at parameters of those arities, which 'applySchemaSymbol'
  checks before it is called
  -}
  , schemaSymbolHaskellName :: !(Maybe Name)
  }

instance Show SchemaSymbol where
  showsPrec d s = showParen (d > 10) (showString "SchemaSymbol " . showsPrec 11 (schemaSymbolName s))

instance Eq SchemaSymbol where
  s1 == s2 =
    schemaSymbolName s1 == schemaSymbolName s2
      && schemaSymbolParamArities s1 == schemaSymbolParamArities s2
      && schemaSymbolArity s1 == schemaSymbolArity s2
      && schemaSymbolHaskellName s1 == schemaSymbolHaskellName s2

-- | A schema of one parameter, from its typed instantiation.
schemaSymbol :: forall k n. (KnownNat k, KnownNat n) => String -> (F.Function k -> F.Function n) -> SchemaSymbol
schemaSymbol n f = schemaSymbolWith n [natVal (Proxy @k)] (natVal (Proxy @n)) \case
  [F.SomeFunction p] -> F.SomeFunction . f <$> parameterAt @k n p
  ps -> Left (SchemaParameterCountMismatch (T.pack n) 1 (length ps))

schemaSymbolNamed :: (KnownNat k, KnownNat n) => String -> Name -> (F.Function k -> F.Function n) -> SchemaSymbol
schemaSymbolNamed n hs f = (schemaSymbol n f) {schemaSymbolHaskellName = Just hs}

-- | A schema of the parameter arities and the arity given, from its instantiation at parameters of those arities.
schemaSymbolWith :: String -> [Natural] -> Natural -> ([F.SomeFunction] -> Either SchemaError F.SomeFunction) -> SchemaSymbol
schemaSymbolWith n arities arity inst = SchemaSymbol n arities arity inst Nothing

-- | A parameter of a schema at the arity a typed instantiation takes it at.
parameterAt :: forall k m. (KnownNat k, KnownNat m) => String -> F.Function m -> Either SchemaError (F.Function k)
parameterAt n f = case testEquality (sNat @m) (sNat @k) of
  Just Refl -> Right f
  Nothing -> Left (SchemaParameterArityMismatch (T.pack n) (natVal (Proxy @k)) (natVal (Proxy @m)))

-- | Instantiate at parameters: as many as the schema has, each of the arity of its place.
applySchemaSymbol :: SchemaSymbol -> [F.SomeFunction] -> Either SchemaError F.SomeFunction
applySchemaSymbol sch params = do
  let name = T.pack (schemaSymbolName sch)
      arities = schemaSymbolParamArities sch
  when (length params /= length arities) $
    Left (SchemaParameterCountMismatch name (length arities) (length params))
  forM_ (zip arities params) \(expected, F.SomeFunction (_ :: F.Function m)) ->
    when (natVal (Proxy @m) /= expected) $
      Left (SchemaParameterArityMismatch name expected (natVal (Proxy @m)))
  schemaSymbolInstantiate sch params

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
  when (schemaSymbolParamArities inst /= [expectedParam] || schemaSymbolArity inst /= expectedArity) $
    Left
      ( VariadicInstanceArityMismatch
          (T.pack (variadicSchemaName sym))
          k
          (schemaSymbolParamArities inst, schemaSymbolArity inst)
          ([expectedParam], expectedArity)
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
  applySchemaSymbol inst [f]

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
variadicInstanceSame n pArity f k = withArity (pArity + k) \(_ :: Proxy m) -> Right (schemaSymbol n (f @m))

variadicInstancePlus ::
  forall d.
  (KnownNat d) =>
  String ->
  Natural ->
  (forall m. (KnownNat m) => F.Function m -> F.Function (m + d)) ->
  Natural ->
  Either SchemaError SchemaSymbol
variadicInstancePlus n pArity f k = withArity (pArity + k) \(_ :: Proxy m) -> Right (schemaSymbol n (f @m))

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
    STrue -> Right (schemaSymbol n (f @m))
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
number of variadic arguments it was instantiated with, and its parameters,
one for each parameter of the schema, in order; a variadic schema has one.
-}
data SchemaInstance = SchemaInstance
  { instanceSchema :: !(Either SchemaSymbol VariadicSchemaSymbol)
  , instanceExtras :: !Natural
  , instanceParameters :: ![F.SomeFunction]
  }
  deriving (Show, Eq)

-- | The name of the schema an instance is of.
instanceName :: SchemaInstance -> String
instanceName = either schemaSymbolName variadicSchemaName . instanceSchema

{- |
The schema an inline code instantiates, with its parameters: the code is
matched against the schema instantiated at placeholders, one for each
parameter, whose calls bind the parameters.  The variadic schemas are tried
first, each at the number of variadic arguments the arity of the code
leaves, then the plain ones.
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
      params <- parametersOf inst code
      pure (SchemaInstance (Right sym) extras params)
    plain code sch = do
      guard (schemaSymbolArity sch == arity)
      params <- parametersOf sch code
      pure (SchemaInstance (Left sch) 0 params)

{- |
The parameters a code instantiates a schema at, by matching the code against
the instantiation at placeholders, one for each parameter.  Every parameter
is called somewhere in the code, as the compiler requires of a schema's
clauses, so every placeholder is bound.
-}
parametersOf :: forall n. (KnownNat n) => SchemaSymbol -> F.Program n -> Maybe [F.SomeFunction]
parametersOf sch code = do
  F.SomeFunction (template :: F.Function m) <- either (const Nothing) Just (applySchemaSymbol sch placeholders)
  Refl <- testEquality (sNat @m) (sNat @n)
  bound <- unify Map.empty (F.functionProgram template) code
  traverse (`Map.lookup` bound) indices
  where
    indices = zipWith const [0 ..] (schemaSymbolParamArities sch)
    placeholders = zipWith placeholder indices (schemaSymbolParamArities sch)
    placeholder :: Int -> Natural -> F.SomeFunction
    placeholder i arity = case someNatVal arity of
      SomeNat (_ :: Proxy k) -> F.SomeFunction (F.Defined (F.DefId (placeholderName i)) :: F.Function k)
    placeholderName i = T.pack ("«parameter " <> show i <> "»")
    placeholderIndex ident = lookup ident [(placeholderName i, i) | i <- indices]

    unify :: forall j. (KnownNat j) => Map Int F.SomeFunction -> F.Program j -> F.Program j -> Maybe (Map Int F.SomeFunction)
    unify acc template code' = case (template, code') of
      (F.Call (F.DefId ident), _)
        | Just i <- placeholderIndex ident ->
            let found = F.SomeFunction (F.programFunction code')
             in case Map.lookup i acc of
                  Nothing -> Just (Map.insert i found acc)
                  Just p
                    | p == found -> Just acc
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
The instance of the schema of the name at parameters, applied to arguments:
a variadic schema, whose one parameter is the only one given, is
instantiated at the number of variadic arguments the arity of the parameter
determines, a plain one at its parameter arities.  The arguments must be as
many as the arity of the instance.
-}
applySchemaNamed :: Signature -> String -> [F.SomeFunction] -> [Term a] -> Either SchemaError (Term a)
applySchemaNamed sig n params args = do
  fun <- case (lookupVariadicSchema n sig, lookupSchema n sig) of
    (Just sym, _) -> case params of
      [param] -> applyVariadicSchemaSymbol sym param
      _ -> Left (SchemaParameterCountMismatch (T.pack n) 1 (length params))
    (Nothing, Just sch) -> applySchemaSymbol sch params
    (Nothing, Nothing) -> Left (SchemaNotInSignature (T.pack n))
  case fun of
    F.SomeFunction (f :: F.Function m) -> case SV.fromList' args of
      Just xs -> Right (App f xs)
      Nothing -> Left (InstanceArgumentCountMismatch (T.pack n) (natVal (Proxy @m)) (fromIntegral (length args)))

{- |
The instance of the schema of the name at its parameters, some of them the
functions of abstractions, applied to the arguments and then to the terms
those abstractions capture, in order: an instance of a schema at term
metavariables with parameters, once they are bound.  Only a variadic schema
passes captured terms on, so an abstraction capturing terms is the parameter
of a variadic schema, or the instance is refused for its arities.
-}
applySchemaAt :: Signature -> String -> [Either F.SomeFunction (Abstraction a)] -> [Term a] -> Either SchemaError (Term a)
applySchemaAt sig n params args =
  applySchemaNamed sig n (map (either id abstractionFunction) params) (args <> concatMap (either (const []) abstractionCaptured) params)

{- |
'applySchemaAt' in a proof spliced for a derived rule, where the rule had the
schema at term metavariables with parameters.  The rule was checked, so a
failure is an error.
-}
instantiateSchemaAt :: Signature -> String -> [Either F.SomeFunction (Abstraction a)] -> [Term a] -> Term a
instantiateSchemaAt sig n params args =
  either (\err -> error ("Language.Praxis.PRA.Signature.instantiateSchemaAt: " <> n <> ": " <> displayException err)) id $
    applySchemaAt sig n params args

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

-- | A schematic term could not be instantiated completely.
data InstantiationError
  = UnboundFunction !String
  | FunctionArgumentMismatch !String !Int
  | UnrecognisedSchematicFunction
  | SchemaInstantiationFailed !String !SchemaError
  deriving (Show, Eq)

{- |
Simultaneous substitution of variables and schematic functions, including
occurrences inside compiled schema parameters. The replacement terms and
abstractions are inserted without substituting inside them again.

A closure is opened over fresh variables and its original captured arguments,
its body instantiated, and then closed again. The old captures are removed
from the schema application before its new captures are appended. This is the
single substitution operation used by both certification and generated proofs.
-}
instantiateSchematicTerm :: forall a b. (Fresh a) => Signature -> Map String (Abstraction a) -> (b -> Term a) -> Term b -> Either InstantiationError (Term a)
instantiateSchematicTerm sig functions = go
  where
    go :: forall v. (v -> Term a) -> Term v -> Either InstantiationError (Term a)
    go variable = \case
      Var v -> pure (variable v)
      Lit n -> pure (Lit n)
      App f xs -> do
        args <- traverse (go variable) xs
        case abstractName f of
          Just (n, _) -> do
            a <- lookupFunction n
            maybe (Left (FunctionArgumentMismatch n (length args))) Right (applyAbstraction a (toList args))
          Nothing
            | null (F.opaqueCalls (F.functionProgram f)) -> pure (App f args)
            | Just code <- closedFunctions (F.functionProgram f) -> pure (App (F.programFunction code) args)
            | Just inst <- schemaInstanceOf sig f -> do
                let params = instanceParameters inst
                    closure (F.SomeFunction g) = abstractName g == Nothing && not (null (F.opaqueCalls (F.functionProgram g)))
                    extras = if any closure params then fromIntegral (instanceExtras inst) else 0
                    (fixed, captured) = splitAt (length args - extras) (toList args)
                    avoid = HS.fromList (concatMap toList args <> concatMap toList (Map.elems functions))
                    slots = freshSlots avoid
                    parameter (F.SomeFunction (g :: F.Function k)) = case abstractName g of
                      Just (n, _) -> Right <$> lookupFunction n
                      Nothing
                        | closure (F.SomeFunction g) -> do
                            let own = fromIntegral (natVal (Proxy @k)) - extras
                                vs = take own slots
                                -- Captures are opaque leaves here: substituting inside an
                                -- already substituted argument would not be simultaneous.
                                inputs = map (Var . Left) vs <> map (Var . Right) captured
                            body <- maybe (Left UnrecognisedSchematicFunction) Right (decompileFunction (F.SomeFunction g) inputs)
                            body' <- go (either Var id) body
                            pure (Right (abstraction vs body'))
                        | otherwise -> pure (Left (F.SomeFunction g))
                params' <- traverse parameter params
                either (Left . SchemaInstantiationFailed (instanceName inst)) Right (applySchemaAt sig (instanceName inst) params' fixed)
            | otherwise -> Left UnrecognisedSchematicFunction

    -- Substitution by closed functions preserves the surrounding program's
    -- representation. In particular, identity substitution leaves lambda
    -- code unchanged. Only replacements with captures need closure conversion.
    closedFunctions :: forall n. (KnownNat n) => F.Program n -> Maybe (F.Program n)
    closedFunctions = \case
      F.Base code -> pure (F.Base code)
      F.Call ident -> pure (F.Call ident)
      F.Opaque ident -> do
        (name, _) <- abstractName (F.Abstract ident)
        a <- Map.lookup name functions
        guard (null (abstractionCaptured a))
        F.SomeFunction (g :: F.Function m) <- pure (abstractionFunction a)
        Refl <- testEquality (sNat @n) (sNat @m)
        pure (F.functionProgram g)
      F.Comp f xs -> F.Comp <$> closedFunctions f <*> traverse closedFunctions xs
      F.Rec base step -> F.Rec <$> closedFunctions base <*> closedFunctions step

    lookupFunction n = maybe (Left (UnboundFunction n)) Right (Map.lookup n functions)
    freshSlots used = let v = freshen used anyName in v : freshSlots (HS.insert v used)

-- | 'instantiateSchematicTerm' in a generated, already certified proof.
instantiateSchematicTermAt :: (Fresh a) => Signature -> Map String (Abstraction a) -> (b -> Term a) -> Term b -> Term a
instantiateSchematicTermAt sig functions variable =
  either (error . ("Language.Praxis.PRA.Signature.instantiateSchematicTermAt: " <>) . show) id . instantiateSchematicTerm sig functions variable
