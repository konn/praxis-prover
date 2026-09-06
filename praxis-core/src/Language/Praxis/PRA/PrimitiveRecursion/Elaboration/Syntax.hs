-- | Equation syntax and arity-indexed terms.
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax (
  Equation (..),
  Pattern (..),
  IrrelevantName (..),
  EqTerm (..),
  Function (..),
  SomeFunction (..),
  Env,
  FunctionalTerm (..),
  RenamedEquation (..),
) where

import Data.Hashable (Hashable (..))
import Data.Map.Strict (Map)
import Data.String (IsString)
import Data.Text qualified as T
import Data.Type.Ordinal (Ordinal)
import GHC.Generics (Generic)
import GHC.TypeNats (KnownNat)
import Language.Praxis.PRA.PrimitiveRecursion (PRFCode, V)
import Numeric.Natural (Natural)

data Equation name = Equation
  { name :: !name
  , args :: ![Pattern name]
  , clause :: !(EqTerm name)
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (Hashable)

data Pattern name = VarP !name | SuccP !(Pattern name) | ZeroP
  deriving (Show, Eq, Ord, Functor, Generic)
  deriving anyclass (Hashable)

-- | Unresolved syntax: identifiers have no variable/function distinction.
data EqTerm name
  = LitET !Natural
  | NameET !name
  | EqTerm name :@ EqTerm name
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (Hashable)

infixl 9 :@

-- | A reference to a top-level definition, or an existing primitive code.
data Function n = Defined !T.Text | Primitive !(PRFCode n)

deriving instance (KnownNat n) => Show (Function n)

data SomeFunction = forall n. (KnownNat n) => SomeFunction !(Function n)

deriving instance Show SomeFunction

type Env = Map T.Text SomeFunction

{- | A term in a context of @n@ argument slots. Variables use zero-based
indices in left-to-right argument order. A variable beneath 'SuccP' refers
to the predecessor bound by that pattern, at the same argument slot;
'ZeroP' binds no variable. Each application independently carries a vector
of exactly the callee's arity.
-}
data FunctionalTerm n
  = LitFT !Natural
  | VarFT !(Ordinal n)
  | forall m. (KnownNat m) => AppFT !(Function m) !(V m (FunctionalTerm n))

deriving instance (KnownNat n) => Show (FunctionalTerm n)

{- | The existential arity ties the pattern vector to the body's index bound.
Pattern names are retained for display only. The renamer only introduces
indices for slots containing a variable, including beneath successors.
-}
data RenamedEquation = forall n. (KnownNat n) => RenamedEquation
  { renamedName :: !T.Text
  , renamedArgs :: !(V n (Pattern IrrelevantName))
  , renamedClause :: !(FunctionalTerm n)
  }

deriving instance Show RenamedEquation

-- | A textual variable name, which is irrelevant for equality and hashing.
newtype IrrelevantName = IrrelevantName {rawName :: T.Text}
  deriving newtype (IsString, Show)

instance Eq IrrelevantName where
  _ == _ = True
  {-# INLINE (==) #-}

instance Ord IrrelevantName where
  compare _ _ = EQ
  {-# INLINE compare #-}
  (<) = const $ const False
  {-# INLINE (<) #-}
  (<=) = const $ const True
  {-# INLINE (<=) #-}
  (>) = const $ const False
  {-# INLINE (>) #-}
  (>=) = const $ const True
  {-# INLINE (>=) #-}

instance Hashable IrrelevantName where
  hashWithSalt salt _ = hash salt
  {-# INLINE hashWithSalt #-}
