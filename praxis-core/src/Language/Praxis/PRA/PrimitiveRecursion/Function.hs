{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

{- | Shared definitions above the bare PRA code language. Environments are
constructed only after checking closure, arities and acyclicity.
-}
module Language.Praxis.PRA.PrimitiveRecursion.Function (
  DefId (..),
  Function (..),
  Program (Base, Call, Comp, Rec, Opaque),
  programHash,
  SomeFunction (..),
  Definition (..),
  KernelEnv,
  KernelError (..),
  emptyKernelEnv,
  definitions,
  extendKernelEnv,
  unionKernelEnv,
  lookupDefinition,
  functionProgram,
  opaqueCalls,
  programFunction,
  evalFunction,
  evalFunctionM,
  eraseFunction,
) where

import Control.Exception (Exception (..))
import Control.Lens ((^?))
import Control.Lens.Extras (is)
import Control.Monad (foldM, unless)
import Control.Monad.Trans.Class qualified as Trans
import Control.Monad.Trans.Except (ExceptT (..), runExceptT)
import Data.Functor.Identity (runIdentity)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.Hashable (Hashable (..))
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Proxy (Proxy (..))
import Data.Sized qualified as SV
import Data.Text (Text)
import Data.Text qualified as T
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Type.Natural (sNat)
import GHC.Exts (isTrue#, reallyUnsafePtrEquality#)
import GHC.Generics (Generic)
import GHC.TypeNats (KnownNat, Nat, natVal, type (+))
import Language.Haskell.TH.Syntax (Lift (..), unTypeCode)
import Language.Praxis.PRA.PrimitiveRecursion.Code (Evalable (..), PRFCode, V)
import Language.Praxis.PRA.PrimitiveRecursion.Code qualified as PR
import Numeric.Natural (Natural)

{- | Identity is independent of code shape. Generated identities are qualified
by package and module; an environment checks the arity at every reference.
-}
newtype DefId (n :: Nat) = DefId {definitionName :: Text}
  deriving stock (Show, Eq, Ord, Generic, Lift)
  deriving anyclass (Hashable)

data Function n
  = Primitive !(PRFCode n)
  | Defined !(DefId n)
  | -- | Residual code produced by partial evaluation, still retaining calls.
    Inline !(Program n)
  | {- | A function known by name only: the parameter of a schema left
    abstract, as a term metavariable with parameters stands for one in the
    statement of a derived rule.  An application of it never reduces, and a
    schema instantiated at it unfolds around it.
    -}
    Abstract !(DefId n)

data Program n where
  Base :: !(PRFCode n) -> Program n
  Call :: !(DefId n) -> Program n
  -- | A composition, with its hash: built only by 'Comp'.
  CompC :: (KnownNat m) => !Int -> !(Program m) -> !(V m (Program n)) -> Program n
  -- | A primitive recursion, with its hash: built only by 'Rec'.
  RecC :: !Int -> !(Program k) -> !(Program (k + 2)) -> Program (k + 1)
  -- | A call of an 'Abstract' function, which is left as it is.
  Opaque :: !(DefId n) -> Program n

-- | Composition: the first program applied to the results of the others, each applied to the arguments.
pattern Comp :: () => (KnownNat m) => Program m -> V m (Program n) -> Program n
pattern Comp f xs <- CompC _ f xs
  where
    Comp f xs = CompC (foldl' (\h x -> hashWithSalt h (programHash x)) (hashWithSalt (2 :: Int) (programHash f)) (SV.toList xs)) f xs

-- | Primitive recursion on the first argument, as 'PR.Rec': the base case, and the step.
pattern Rec :: forall n. () => forall k. (n ~ (k + 1)) => Program k -> Program (k + 2) -> Program n
pattern Rec b s <- RecC _ b s
  where
    Rec b s = RecC (hashWithSalt (hashWithSalt (3 :: Int) (programHash b)) (programHash s)) b s

{-# COMPLETE Base, Call, Comp, Rec, Opaque #-}

-- | The hash of a program, cached by the compositions and recursions, so that hashing one costs constant time.
programHash :: Program n -> Int
programHash = \case
  Base code -> hashWithSalt (0 :: Int) (PR.codeHash code)
  Call ident -> hashWithSalt (1 :: Int) ident
  CompC h _ _ -> h
  RecC h _ _ -> h
  Opaque ident -> hashWithSalt (4 :: Int) ident

-- | Whether two programs are one object in memory, and so equal.
sameProgram :: Program n -> Program n -> Bool
sameProgram f g = isTrue# (reallyUnsafePtrEquality# f g)

instance (KnownNat n) => Show (Program n) where
  showsPrec d = \case
    Base code -> showParen (d > 10) (showString "Base " . showsPrec 11 code)
    Call ident -> showParen (d > 10) (showString "Call " . showsPrec 11 ident)
    Comp f xs -> showParen (d > 10) (showString "Comp " . showsPrec 11 f . showChar ' ' . showsPrec 11 xs)
    Rec b s -> showParen (d > 10) (showString "Rec " . showsPrec 11 b . showChar ' ' . showsPrec 11 s)
    Opaque ident -> showParen (d > 10) (showString "Opaque " . showsPrec 11 ident)

deriving instance (KnownNat n) => Show (Function n)

-- | Lifted through 'Comp' and 'Rec', so that the hashes are computed again where the program is spliced.
instance (KnownNat n) => Lift (Program n) where
  lift = unTypeCode . liftTyped
  liftTyped = \case
    Base code -> [||Base $$(liftTyped code)||]
    Call ident -> [||Call $$(liftTyped ident)||]
    Comp f xs -> [||Comp $$(liftTyped f) $$(liftTyped xs)||]
    Rec b s -> [||Rec $$(liftTyped b) $$(liftTyped s)||]
    Opaque ident -> [||Opaque $$(liftTyped ident)||]

deriving stock instance (KnownNat n) => Lift (Function n)

instance (KnownNat n) => Eq (Program n) where
  f == g
    | sameProgram f g = True
    | otherwise = case (f, g) of
        (Base x, Base y) -> x == y
        (Call x, Call y) -> x == y
        (CompC h (f1 :: Program m) xs, CompC h' (g1 :: Program k) ys) ->
          h == h' && case testEquality (sNat @m) (sNat @k) of
            Just Refl -> f1 == g1 && xs == ys
            Nothing -> False
        (RecC h b s, RecC h' c t) -> h == h' && b == c && s == t
        (Opaque x, Opaque y) -> x == y
        _ -> False

instance (KnownNat n) => Eq (Function n) where
  Primitive x == Primitive y = x == y
  Defined x == Defined y = x == y
  Inline x == Inline y = x == y
  Abstract x == Abstract y = x == y
  _ == _ = False

-- | Agrees with '(==)': the cached hash.
instance (KnownNat n) => Hashable (Program n) where
  hashWithSalt salt program = hashWithSalt salt (programHash program)

instance (KnownNat n) => Hashable (Function n) where
  hashWithSalt salt = \case
    Primitive code -> hashWithSalt salt (0 :: Int, code)
    Defined ident -> hashWithSalt salt (1 :: Int, ident)
    Inline code -> hashWithSalt salt (2 :: Int, code)
    Abstract ident -> hashWithSalt salt (3 :: Int, ident)

data SomeFunction = forall n. (KnownNat n) => SomeFunction !(Function n)

deriving instance Show SomeFunction

instance Eq SomeFunction where
  SomeFunction (f :: Function n) == SomeFunction (g :: Function m) = case testEquality (sNat @n) (sNat @m) of
    Just Refl -> f == g
    Nothing -> False

data Definition = forall n. (KnownNat n) => Definition !(DefId n) !(Program n)

deriving instance Show Definition

instance Eq Definition where
  Definition (x :: DefId n) f == Definition (y :: DefId m) g = case testEquality (sNat @n) (sNat @m) of
    Just Refl -> x == y && f == g
    Nothing -> False

newtype KernelEnv = KernelEnv (Map Text Definition)
  deriving (Show, Eq)

{- | Why a definition table could not be built, or a reference could not be
resolved in one. 'displayException' renders the reason for a human.
-}
data KernelError
  = -- | no definition of this name
    UnknownDefinition !Text
  | {- | the definition has another arity: name, the arity expected at the
    reference, the arity found
    -}
    DefinitionArityMismatch !Text !Natural !Natural
  | -- | a definition of this name already exists
    DuplicateDefinition !Text
  | -- | the definitions on a call cycle
    CyclicDefinitions ![Text]
  | -- | names two tables bind to different definitions
    ConflictingDefinitions ![Text]
  deriving (Show, Eq, Generic)

instance Exception KernelError where
  displayException = \case
    UnknownDefinition ident -> "Unknown definition: " <> T.unpack ident
    DefinitionArityMismatch ident expected found ->
      "Definition arity mismatch for " <> T.unpack ident <> ": expected " <> show expected <> ", found " <> show found
    DuplicateDefinition ident -> "Definition already exists: " <> T.unpack ident
    CyclicDefinitions names -> "Cyclic definitions: " <> intercalate ", " (map T.unpack names)
    ConflictingDefinitions names -> "Conflicting definition identities: " <> intercalate ", " (map T.unpack names)

emptyKernelEnv :: KernelEnv
emptyKernelEnv = KernelEnv Map.empty

definitions :: KernelEnv -> [Definition]
definitions (KernelEnv env) = Map.elems env

lookupDefinition :: forall n. (KnownNat n) => KernelEnv -> DefId n -> Either KernelError (Program n)
lookupDefinition (KernelEnv env) (DefId ident) = case Map.lookup ident env of
  Nothing -> Left (UnknownDefinition ident)
  Just (Definition (_ :: DefId m) body) -> case testEquality (sNat @n) (sNat @m) of
    Just Refl -> Right body
    Nothing -> Left (DefinitionArityMismatch ident (natVal (Proxy @n)) (natVal (Proxy @m)))

references :: (KnownNat n) => Program n -> [(Text, Natural)]
references = \case
  Base _ -> []
  Call (DefId ident :: DefId n) -> [(ident, natVal (Proxy @n))]
  Comp f xs -> references f <> foldMap references xs
  Rec b s -> references b <> references s
  Opaque _ -> []

-- | The abstract functions a program calls, by name.
opaqueCalls :: (KnownNat n) => Program n -> [Text]
opaqueCalls = \case
  Base _ -> []
  Call _ -> []
  Comp f xs -> opaqueCalls f <> foldMap opaqueCalls xs
  Rec b s -> opaqueCalls b <> opaqueCalls s
  Opaque (DefId ident) -> [ident]

{- | Reject every call cycle, including self calls. Source self recursion must
already have been reconstructed as 'Rec'. Checks never follow a call edge
while inspecting code, so a bad cycle cannot generate an infinite code.
-}
extendKernelEnv :: KernelEnv -> [Definition] -> Either KernelError KernelEnv
extendKernelEnv (KernelEnv old) new = do
  env <- foldM insert old new
  let graph = [(ident, ident, map fst (references code)) | (ident, Definition _ code) <- Map.toList env]
  mapM_ (\case AcyclicSCC _ -> Right (); CyclicSCC names -> Left (CyclicDefinitions names)) (stronglyConnComp graph)
  mapM_ (\(Definition _ code) -> mapM_ (check env) (references code)) (Map.elems env)
  pure (KernelEnv env)
  where
    insert env def@(Definition (DefId ident) _) = do
      unless (Map.notMember ident env) (Left (DuplicateDefinition ident))
      pure (Map.insert ident def env)
    check env (ident, arity) = case Map.lookup ident env of
      Nothing -> Left (UnknownDefinition ident)
      Just (Definition (_ :: DefId n) _) ->
        unless (arity == natVal (Proxy @n)) (Left (DefinitionArityMismatch ident arity (natVal (Proxy @n))))

-- | Shared ancestors must agree exactly; conflicting identities are errors.
unionKernelEnv :: KernelEnv -> KernelEnv -> Either KernelError KernelEnv
unionKernelEnv (KernelEnv l) (KernelEnv r) = do
  let conflicts = Map.keys (Map.filter not (Map.intersectionWith (==) l r))
  unless (null conflicts) (Left (ConflictingDefinitions conflicts))
  extendKernelEnv emptyKernelEnv (Map.elems (l <> r))

functionProgram :: Function n -> Program n
functionProgram = \case
  Primitive code -> Base code
  Defined ident -> Call ident
  Inline code -> code
  Abstract ident -> Opaque ident

programFunction :: Program n -> Function n
programFunction = \case
  Base code -> Primitive code
  Call ident -> Defined ident
  Opaque ident -> Abstract ident
  code -> Inline code

{- | Explicit erasure to the unchanged bare PRA language. Ordinary evaluation
and term construction do not perform this expansion.  An abstract function
has no code to erase to.
-}
eraseFunction :: (KnownNat n) => KernelEnv -> Function n -> Either KernelError (PRFCode n)
eraseFunction env = go . functionProgram
  where
    go :: (KnownNat k) => Program k -> Either KernelError (PRFCode k)
    go (Base code) = Right code
    go (Call ident) = lookupDefinition env ident >>= go
    go (Comp f xs) = PR.Comp <$> go f <*> traverse go xs
    go (Rec b s) = PR.Rec <$> go b <*> go s
    go (Opaque (DefId ident)) = Left (UnknownDefinition ident)

{- | Environment-aware evaluation with a residual constructor supplied by the
syntactic domain. Named calls and residual programs retain their references,
and a call of an abstract function is residual whatever its arguments.
-}
evalFunctionM :: forall m n a. (Monad m, KnownNat n, Evalable a) => m Bool -> (forall k. (KnownNat k) => Function k -> V k a -> a) -> KernelEnv -> Function n -> V n a -> m (Either KernelError a)
evalFunctionM step stuckFunction env fun args = runExceptT (go (functionProgram fun) args)
  where
    go :: (KnownNat k) => Program k -> V k a -> ExceptT KernelError m a
    go (Base code) xs = Trans.lift (PR.evalPRFCodeM step code xs)
    go (Opaque ident) xs = pure (stuckFunction (Abstract ident) xs)
    go code xs =
      Trans.lift step >>= \case
        False -> pure (stuckFunction (programFunction code) xs)
        True -> case code of
          Call ident -> ExceptT (pure (lookupDefinition env ident)) >>= (`go` xs)
          Comp f gs -> traverse (`go` xs) gs >>= go f
          Rec b s -> recurse b s (SV.head xs) (SV.tail xs)
    recurse :: (KnownNat k) => Program k -> Program (k + 2) -> a -> V k a -> ExceptT KernelError m a
    recurse b s y xs
      | is _Zero y = go b xs
      | Just y' <- y ^? _Succ =
          Trans.lift step >>= \case
            False -> pure stuck
            True -> do
              z <- recurse b s y' xs
              go s (y' SV.:< z SV.:< xs)
      | otherwise = pure stuck
      where
        stuck = stuckFunction (Inline (Rec b s)) (y SV.:< xs)

evalFunction :: (KnownNat n) => KernelEnv -> Function n -> V n Natural -> Either KernelError Natural
evalFunction env f xs = case opaqueCalls (functionProgram f) of
  ident : _ -> Left (UnknownDefinition ident)
  [] -> runIdentity (evalFunctionM (pure True) (\_ _ -> error "unreachable residual in total evaluation") env f xs)
