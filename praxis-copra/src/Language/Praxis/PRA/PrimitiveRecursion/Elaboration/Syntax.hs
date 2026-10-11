{-# LANGUAGE DeriveLift #-}

-- | Equation syntax and arity-indexed terms.
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax (
  Equation (..),
  Pattern (..),
  Splat (..),
  SplatPosition (..),
  IrrelevantName (..),
  EqTerm (..),
  Quantifier (..),
  quantifierSchema,
  Function (..),
  SchemaArg (..),
  VariadicTemplate (..),
  FunctionalTerm (..),
  RenamedEquation (..),
) where

import Data.Hashable (Hashable (..))
import Data.String (IsString)
import Data.Text qualified as T
import Data.Type.Ordinal (Ordinal)
import GHC.Generics (Generic)
import GHC.TypeNats (KnownNat)
import Language.Haskell.TH.Syntax (Lift)
import Language.Praxis.PRA.PrimitiveRecursion.Code (PRFCode, V)
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Numeric.Natural (Natural)

{- | One clause. The fixed argument patterns exclude the variadic group,
which a schema may declare at the first or the last argument position.
-}
data Equation name = Equation
  { name :: !name
  , schemaParams :: ![name]
  , args :: ![Pattern name]
  , variadic :: !(Maybe (Splat name))
  , clause :: !(EqTerm name)
  }
  deriving (Show, Eq, Ord, Generic, Lift)
  deriving anyclass (Hashable)

data Pattern name = VarP !name | SuccP !(Pattern name) | ZeroP
  deriving (Show, Eq, Ord, Functor, Generic, Lift)
  deriving anyclass (Hashable)

-- | The variadic argument group @$[xs]@ of a schema head.
data Splat name = Splat
  { splatName :: !name
  , splatPosition :: !SplatPosition
  }
  deriving (Show, Eq, Ord, Functor, Generic, Lift)
  deriving anyclass (Hashable)

data SplatPosition = SplatFirst | SplatLast
  deriving (Show, Eq, Ord, Generic, Lift)
  deriving anyclass (Hashable)

{- | Unresolved syntax: free identifiers have no variable/function distinction.
Binders are locally nameless: a lambda or @μ@ keeps its binder names only as
display hints, and an occurrence refers to a binder by the number of binder
groups between them and its position inside that group. Equality and hashing
therefore identify alpha-equivalent binders.
-}
data EqTerm name
  = LitET !Natural
  | NameET !name
  | -- | A binder occurrence: groups outward, then the position in that group.
    BoundET !Int !Int
  | EqTerm name :@ EqTerm name
  | InfixET !(EqTerm name) !name !(EqTerm name)
  | IfThenElseET !(EqTerm name) !(EqTerm name) !(EqTerm name)
  | -- | @λ x₁ … xₚ. body@, a closed anonymous @p@-ary function.
    LamET ![IrrelevantName] !(EqTerm name)
  | -- | @μ i < bound. body@: bounded search, desugared into a @mu@ schema.
    MuET !IrrelevantName !(EqTerm name) !(EqTerm name)
  | {- | @∀ i < bound. body@ or @∃ i < bound. body@: a bounded quantifier over a
    code, desugared into the schema 'quantifierSchema' names.
    -}
    QuantET !Quantifier !IrrelevantName !(EqTerm name) !(EqTerm name)
  | -- | @$[xs]@ as an argument: the variadic arguments of the enclosing schema.
    SplatET !name
  deriving (Show, Eq, Ord, Generic, Lift)
  deriving anyclass (Hashable)

-- | A bounded quantifier: for all, or for some, @i@ below the bound.
data Quantifier = Forall | Exists
  deriving (Show, Eq, Ord, Generic, Lift)
  deriving anyclass (Hashable)

{- | The schema a bounded quantifier searches with: @∀ i < b. c@ is @holdsBelow@
of the code @c@ at @b@, and @∃ i < b. c@ is @mu@ of it at @b@ compared with @b@.
-}
quantifierSchema :: Quantifier -> T.Text
quantifierSchema = \case
  Forall -> T.pack "holdsBelow"
  Exists -> T.pack "mu"

infixl 9 :@

-- | A reference to a top-level definition, or an existing primitive code.
data Function n
  = Defined !T.Text
  | Primitive !(PRFCode n)
  | Bound !(F.Function n)
  | SchemaApp !T.Text ![SchemaArg]

deriving instance (KnownNat n) => Show (Function n)

-- | A schema parameter: a function name, or a closed lambda of its own arity.
data SchemaArg
  = NamedArg !T.Text
  | forall p. (KnownNat p) => LambdaArg !(V p IrrelevantName) !(FunctionalTerm p)

deriving instance Show SchemaArg

{- | A schema with a variadic argument group. Instances at a concrete number
of variadic arguments are ordinary schemas, generated on demand by expanding
the group into that many fresh variables.
-}
data VariadicTemplate = VariadicTemplate
  { templateName :: !T.Text
  , templateParam :: !T.Text
  , templateFixedArity :: !Natural
  -- ^ the number of non-variadic arguments
  , templateParamArity :: !Natural
  -- ^ the parameter's arity with no variadic arguments; each adds one
  , templateEquations :: ![Equation T.Text]
  }
  deriving (Show, Eq, Generic, Lift)

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
  deriving stock (Generic, Lift)

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
