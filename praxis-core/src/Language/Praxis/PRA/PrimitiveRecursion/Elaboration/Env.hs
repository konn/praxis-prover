-- | The environment name resolution consults: what each name stands for.
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Env (
  SomeFunction (..),
  Env,
) where

import Data.Map.Strict (Map)
import Data.Text qualified as T
import GHC.TypeNats (KnownNat)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Error (SchemaError)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Numeric.Natural (Natural)

data SomeFunction
  = forall n. (KnownNat n) => SomeFunction !(Function n)
  | SchemaDef !T.Text ![T.Text] !Natural !Natural
  | ImportedSchema !T.Text !Natural !Natural !(F.SomeFunction -> Either SchemaError F.SomeFunction)
  | VariadicDef !VariadicTemplate
  | {- | Name, fixed arity, parameter arity at zero variadic arguments, and
    the instantiation at a number of variadic arguments.
    -}
    ImportedVariadic !T.Text !Natural !Natural !(Natural -> Either SchemaError (F.SomeFunction -> Either SchemaError F.SomeFunction))

instance Show SomeFunction where
  showsPrec d (SomeFunction f) = showParen (d > 10) (showString "SomeFunction " . showsPrec 11 f)
  showsPrec d (SchemaDef n ps pa fa) =
    showParen
      (d > 10)
      ( showString "SchemaDef "
          . showsPrec 11 n
          . showString " "
          . showsPrec 11 ps
          . showString " "
          . showsPrec 11 pa
          . showString " "
          . showsPrec 11 fa
      )
  showsPrec d (ImportedSchema n pa fa _) =
    showParen
      (d > 10)
      ( showString "ImportedSchema "
          . showsPrec 11 n
          . showString " "
          . showsPrec 11 pa
          . showString " "
          . showsPrec 11 fa
      )
  showsPrec d (VariadicDef tmpl) = showParen (d > 10) (showString "VariadicDef " . showsPrec 11 tmpl)
  showsPrec d (ImportedVariadic n fa pa _) =
    showParen
      (d > 10)
      ( showString "ImportedVariadic "
          . showsPrec 11 n
          . showString " "
          . showsPrec 11 fa
          . showString " "
          . showsPrec 11 pa
      )

type Env = Map T.Text SomeFunction
