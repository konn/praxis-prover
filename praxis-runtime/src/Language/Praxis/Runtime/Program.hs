{- | Portable, proof-erased surface code. Only the native checker constructs
this representation; browsers receive it compiled into a Haskell module.
-}
module Language.Praxis.Runtime.Program (
  Program (..),
  Function (..),
  Clause (..),
  Pattern (..),
  Term (..),
  Type (..),
  Constructor (..),
  Field (..),
  Location (..),
  Predicate (..),
) where

import Data.Map.Strict (Map)
import Data.Text (Text)
import Numeric.Natural (Natural)

data Program = Program
  { programEntry :: !Text
  , programInputs :: ![Type]
  , programParameters :: ![Maybe Int]
  , programFunctions :: !(Map Text Function)
  , programConstructors :: !(Map Text Constructor)
  , programProjections :: !(Map Text Int)
  }
  deriving stock (Show, Read, Eq)

newtype Function = Function [Clause]
  deriving stock (Show, Read, Eq)

data Clause = Clause [Pattern] Term
  deriving stock (Show, Read, Eq)

data Pattern = Bind | Wild | NumberPattern Natural | Successor Pattern | ConstructorPattern Text [Pattern] | Impossible
  deriving stock (Show, Read, Eq)

data Term
  = Variable Int
  | Literal Natural
  | Call Text [Term]
  | Construct Text [Term]
  | Lambda Int Term
  | Apply Term [Term]
  | -- | Closed callback code: its environment is argument zero.
    Packed Int Term Term
  deriving stock (Show, Read, Eq, Ord)

data Type = NaturalType | DataType Text [Type] [Term] | TypeParameter Int
  deriving stock (Show, Read, Eq, Ord)

data Constructor = Constructor
  { constructorType :: !Text
  , constructorArity :: !Int
  , constructorFields :: ![Field]
  , constructorIndices :: ![Term]
  , constructorGuards :: !(Maybe [Predicate])
  -- ^ Nothing means the constructor cannot cross the JSON boundary.
  }
  deriving stock (Show, Read, Eq)

data Field = Field Type Location
  deriving stock (Show, Read, Eq)

data Location = Stored Int | Recovered Int Int
  deriving stock (Show, Read, Eq)

data Predicate
  = Equal Term Term
  | Less Term Term
  | LessEqual Term Term
  | Conjunction Predicate Predicate
  | Disjunction Predicate Predicate
  | Negation Predicate
  | Truth Bool
  deriving stock (Show, Read, Eq)
