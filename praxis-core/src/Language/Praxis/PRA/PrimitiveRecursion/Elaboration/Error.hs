{- | The errors of the equation language.

An 'ElaborationError' arises while expanding, renaming or compiling
equations; a 'SchemaError' while instantiating a schema at a parameter
function. The two embed each other: an imported schema may fail to
instantiate during an elaboration, and the instance of a lifted variadic
template is elaborated on demand during an instantiation. Both render for a
human through 'displayException'.
-}
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Error (
  ElaborationError (..),
  SchemaError (..),
) where

import Control.Exception (Exception (..))
import Data.List (intercalate)
import Data.Text qualified as T
import GHC.Generics (Generic)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax (EqTerm, IrrelevantName (..), Pattern (..))
import Numeric.Natural (Natural)

-- | Why a schema could not be instantiated at a parameter function.
data SchemaError
  = -- | the schema takes another number of parameters: schema, expected, given
    SchemaParameterCountMismatch !T.Text !Int !Int
  | -- | the parameter does not have the schema's parameter arity: schema, expected, given
    SchemaParameterArityMismatch !T.Text !Natural !Natural
  | {- | the parameter has fewer arguments than the variadic schema's parameter
    takes at zero variadic arguments: schema, least, given
    -}
    VariadicParameterTooSmall !T.Text !Natural !Natural
  | {- | a typed variadic binding cannot be instantiated at a parameter arity
    below the number of arguments it subtracts: schema, parameter arity, difference
    -}
    VariadicParameterBelowOffset !T.Text !Natural !Natural
  | {- | an instance disagrees with the recorded arities: schema, number of
    variadic arguments, the (parameter arity, arity) found and expected
    -}
    VariadicInstanceArityMismatch !T.Text !Natural !(Natural, Natural) !(Natural, Natural)
  | {- | the instance of a lifted template could not be elaborated: schema,
    number of variadic arguments, the failure
    -}
    VariadicInstanceElaborationFailed !T.Text !Natural !ElaborationError
  | {- | elaborating a template produced no instance at this number of
    variadic arguments: schema, number of variadic arguments
    -}
    VariadicInstanceMissing !T.Text !Natural
  deriving (Show, Eq, Generic)

instance Exception SchemaError where
  displayException = \case
    SchemaParameterCountMismatch schema expected given ->
      "Schema " <> T.unpack schema <> " takes " <> show expected <> " parameter(s), given " <> show given
    SchemaParameterArityMismatch schema expected given ->
      "Schema " <> T.unpack schema <> " expects a parameter of arity " <> show expected <> ", given " <> show given
    VariadicParameterTooSmall schema least given ->
      T.unpack schema <> " expects a parameter of arity at least " <> show least <> ", given " <> show given
    VariadicParameterBelowOffset schema arity offset ->
      T.unpack schema <> ": parameter arity " <> show arity <> " is below " <> show offset
    VariadicInstanceArityMismatch schema k found expected ->
      T.unpack schema <> ": instance at " <> show k <> " variadic arguments has arities " <> show found <> ", expected " <> show expected
    VariadicInstanceElaborationFailed schema k err ->
      T.unpack schema <> ": instance at " <> show k <> " variadic arguments: " <> displayException err
    VariadicInstanceMissing schema k ->
      "No instance of " <> T.unpack schema <> " at " <> show k <> " variadic arguments"

-- | Why a family of equations could not be elaborated.
data ElaborationError
  = -- | a definition without clauses
    EmptyDefinition
  | -- | clauses given as one definition name different functions
    MixedDefinitionNames !T.Text !T.Text
  | -- | the name is already bound in the initial environment
    FunctionAlreadyDefined !T.Text
  | -- | the clauses redefine a schema of the initial environment
    SchemaAlreadyDefined !T.Text
  | -- | the clauses of a definition disagree on the number of arguments
    InconsistentArity !T.Text
  | -- | the clauses of a definition disagree on whether it is a schema
    InconsistentDefinition !T.Text
  | -- | the clauses of a schema disagree on its parameters or its arity
    InconsistentSchemaDefinition !T.Text
  | -- | a clause of a function the environment does not declare
    UnknownFunction !T.Text
  | -- | a pattern variable bound twice in one clause
    NonlinearPattern !T.Text
  | -- | an identifier which is neither a variable nor in scope
    UnknownName !T.Text
  | -- | a function applied to the wrong number of arguments: name, expected, given
    ArityMismatch !T.Text !Natural !Natural
  | -- | a pattern variable in function position
    AppliedVariable !T.Text
  | -- | an application whose head is not a name
    InvalidApplicationHead !(EqTerm T.Text)
  | -- | an infix operator without a desugaring
    UnknownOperator !T.Text
  | -- | an infix operator none of whose binary functions is in scope: operator, candidates
    OperatorOutOfScope !T.Text ![T.Text]
  | -- | a conditional without a ternary @ifte@ in scope
    ConditionalOutOfScope
  | -- | the @ifte@ in scope has another arity than three
    ConditionalArityMismatch !Natural
  | -- | a schema applied to another number of schema arguments: schema, expected, given
    SchemaArgumentCountMismatch !T.Text !Int !Int
  | -- | a schema recurring without its own parameters: schema, parameters
    SchemaAppliedWithoutParameter !T.Text ![T.Text]
  | -- | a pattern variable passed as a schema argument
    SchemaArgumentIsVariable !T.Text
  | -- | a schema passed as a schema argument
    SchemaArgumentIsSchema !T.Text
  | -- | a schema argument of the wrong arity: argument, expected, given
    SchemaArgumentArityMismatch !T.Text !Natural !Natural
  | -- | a schema argument which is neither a function name nor a lambda
    InvalidSchemaArgument !(EqTerm T.Text)
  | -- | a schema application the compiler has no schema for
    UnknownSchema !T.Text
  | -- | an imported schema failed to instantiate
    SchemaFailure !SchemaError
  | -- | a lambda anywhere but in a schema parameter position
    LambdaOutsideSchemaParameter
  | -- | a lambda of the wrong arity as a schema parameter: schema, expected, given
    LambdaArityMismatch !T.Text !Natural !Natural
  | -- | a lambda mentioning a pattern variable bound outside it
    LambdaCapturesVariable !T.Text
  | -- | a lambda mentioning a binder of an enclosing lambda
    LambdaCapturesBinder
  | -- | a binder occurrence outside every lambda
    BinderOutsideLambda
  | -- | a binder occurrence beyond the arity of its lambda: position
    InvalidBinderIndex !Int
  | -- | a lambda-bound variable in function position
    AppliedBinder
  | -- | a bounded search without a schema @mu@ in scope
    BoundedSearchOutOfScope
  | -- | a clause with a variadic group reached the renamer unexpanded
    UnexpandedVariadicClause !T.Text
  | -- | an application of a variadic schema reached the renamer unexpanded: schema, fixed arity
    UnexpandedVariadicApplication !T.Text !Natural
  | -- | an instance demanded of a name which is not a variadic schema
    UnknownVariadicSchema !T.Text
  | -- | a template with a clause lacking the variadic group
    MissingVariadicGroup !T.Text
  | -- | a template whose clauses disagree on the name or the position of the group
    InconsistentVariadicGroup !T.Text
  | -- | a template without a schema parameter
    VariadicWithoutParameter !T.Text
  | -- | a template with more than one schema parameter
    TooManyVariadicParameters !T.Text
  | -- | a parameter never applied to the variadic group: schema, parameter, group
    VariadicParameterUnapplied !T.Text !T.Text !T.Text
  | -- | a parameter taking the variadic group other than exactly once: schema, parameter, group, times
    VariadicParameterGroupMismatch !T.Text !T.Text !T.Text !Natural
  | -- | a variadic group anywhere but in argument position
    SplatOutsideArgument !T.Text
  | -- | a variadic group outside a variadic schema
    SplatOutsideVariadicSchema !T.Text
  | -- | a variadic group other than the enclosing schema's: given, declared
    UnknownVariadicGroup !T.Text !T.Text
  | {- | a variadic schema applied to fewer arguments than its parameter and
    fixed arguments: schema, fixed arity, given
    -}
    TooFewVariadicArguments !T.Text !Natural !Int
  | -- | a template recurring at another number of variadic arguments: schema, instantiated, applied
    VariadicRecursionChangesArity !T.Text !Natural !Natural
  | -- | arguments no clause matches
    NonExhaustivePatterns ![Pattern IrrelevantName]
  | -- | two clauses matching the same arguments: their identifiers
    OverlappingClauses !Int !Int
  | -- | no argument admits primitive recursion: function, why each argument was rejected
    NoRecursionArgument !T.Text ![(Natural, ElaborationError)]
  | -- | a recursive call in a clause with @0@ in the recursion column: clause
    RecursiveCallInBaseCase !Int
  | -- | a recursion column pattern other than @0@ or @S x@: clause
    InvalidRecursionPattern !Int
  | -- | a recursive call changing a parameter or not passing the immediate predecessor: clause
    InvalidRecursiveCall !Int
  | -- | a recursive call inside a lambda parameter: function
    RecursiveCallInLambda !T.Text
  | -- | a recursive call where no recursive result is available: function
    UnexpectedRecursiveCall !T.Text
  | -- | a call cycle through two or more definitions: a function on it
    MutualRecursion !T.Text
  | -- | a call to a function the compiler has no code for
    NoCompiledCode !T.Text
  | -- | a call to a function whose code has another arity: function, expected, found
    CompiledArityMismatch !T.Text !Natural !Natural
  | -- | an invariant of the elaborator failed: a bug, not a user error
    InternalError !String
  deriving (Show, Eq, Generic)

instance Exception ElaborationError where
  displayException = \case
    EmptyDefinition -> "Empty function definition"
    MixedDefinitionNames self other -> "Mixed function names in definition: " <> T.unpack self <> " and " <> T.unpack other
    FunctionAlreadyDefined ident -> "Function already defined: " <> T.unpack ident
    SchemaAlreadyDefined ident -> "Schema already defined: " <> T.unpack ident
    InconsistentArity ident -> "Inconsistent arity for " <> T.unpack ident
    InconsistentDefinition ident -> "Inconsistent definition for " <> T.unpack ident
    InconsistentSchemaDefinition ident -> "Inconsistent schema definition for " <> T.unpack ident
    UnknownFunction ident -> "Unknown function: " <> T.unpack ident
    NonlinearPattern ident -> "Nonlinear pattern: repeated variable " <> T.unpack ident
    UnknownName ident -> "Unknown name: " <> T.unpack ident
    ArityMismatch ident expected given -> T.unpack ident <> " takes " <> show expected <> " arguments, given " <> show given
    AppliedVariable ident -> "Cannot apply variable " <> T.unpack ident
    InvalidApplicationHead hd -> "Only named functions can be applied, given: " <> show hd
    UnknownOperator op -> "Unknown operator: " <> T.unpack op
    OperatorOutOfScope op candidates ->
      "Operator '" <> T.unpack op <> "' requires binary " <> intercalate " or " (map (quoted . T.unpack) candidates) <> " to be in scope"
    ConditionalOutOfScope -> "'if ... then ... else ...' requires ternary 'ifte' to be in scope"
    ConditionalArityMismatch arity -> "'ifte' in scope has arity " <> show arity <> ", not 3"
    SchemaArgumentCountMismatch schema expected given ->
      "Schema " <> T.unpack schema <> " expects " <> show expected <> " schema argument(s), given " <> show given
    SchemaAppliedWithoutParameter schema params ->
      "Schema " <> T.unpack schema <> " must be applied to its parameter " <> intercalate ", " (map T.unpack params)
    SchemaArgumentIsVariable p -> "Schema argument " <> quoted (T.unpack p) <> " is a variable, not a function"
    SchemaArgumentIsSchema p -> "Schema argument " <> quoted (T.unpack p) <> " is a schema, not a function"
    SchemaArgumentArityMismatch p expected given ->
      "Schema argument " <> quoted (T.unpack p) <> " arity mismatch: expected " <> show expected <> ", given " <> show given
    InvalidSchemaArgument t -> "Schema parameter must be a function name or a lambda, given: " <> show t
    UnknownSchema schema -> "Unknown schema: " <> T.unpack schema
    SchemaFailure err -> displayException err
    LambdaOutsideSchemaParameter -> "A lambda may only be passed as a schema parameter"
    LambdaArityMismatch schema expected given ->
      "Schema " <> T.unpack schema <> " expects a parameter of arity " <> show expected <> ", given a lambda of arity " <> show given
    LambdaCapturesVariable ident ->
      "A lambda refers to " <> T.unpack ident <> ", which is bound outside it; lambdas must be closed (a bounded search 'μ' captures such variables)"
    LambdaCapturesBinder -> "A lambda may not refer to a variable bound by an enclosing lambda; lambdas must be closed"
    BinderOutsideLambda -> "Unexpected binder occurrence outside a lambda"
    InvalidBinderIndex position -> "Invalid binder index: " <> show position
    AppliedBinder -> "Cannot apply a lambda-bound variable"
    BoundedSearchOutOfScope -> "A bounded search 'μ i < b. body' requires a schema 'mu' to be in scope"
    UnexpandedVariadicClause schema -> "Variadic schema " <> T.unpack schema <> " must be instantiated before renaming"
    UnexpandedVariadicApplication schema fixed ->
      "Variadic schema " <> T.unpack schema <> " must be applied to its parameter and at least " <> show fixed <> " arguments"
    UnknownVariadicSchema schema -> "Unknown variadic schema: " <> T.unpack schema
    MissingVariadicGroup schema -> "Every clause of " <> T.unpack schema <> " must declare its variadic argument $[..]"
    InconsistentVariadicGroup schema ->
      "Clauses of " <> T.unpack schema <> " must agree on the name and position of their variadic argument"
    VariadicWithoutParameter schema -> "Variadic arguments require a schema parameter: " <> T.unpack schema
    TooManyVariadicParameters schema -> "A variadic schema takes exactly one schema parameter: " <> T.unpack schema
    VariadicParameterUnapplied schema param group ->
      "The parameter " <> T.unpack param <> " of " <> T.unpack schema <> " must be applied to the variadic arguments " <> splat group
    VariadicParameterGroupMismatch schema param group times ->
      "The parameter " <> T.unpack param <> " of " <> T.unpack schema <> " must take the variadic arguments " <> splat group <> " exactly once, not " <> show times <> " times"
    SplatOutsideArgument group -> "The variadic arguments " <> splat group <> " may only be passed as arguments"
    SplatOutsideVariadicSchema group -> "The variadic arguments " <> splat group <> " are only available inside a variadic schema"
    UnknownVariadicGroup given declared ->
      "Unknown variadic argument " <> splat given <> "; the enclosing schema declares " <> splat declared
    TooFewVariadicArguments schema fixed given ->
      T.unpack schema <> " takes at least " <> show (1 + fixed) <> " arguments (its parameter and " <> show fixed <> " fixed ones), given " <> show given
    VariadicRecursionChangesArity schema instantiated applied ->
      "Variadic schema "
        <> T.unpack schema
        <> " applies itself with "
        <> show applied
        <> " variadic arguments while being instantiated with "
        <> show instantiated
        <> "; recursion must preserve the number of variadic arguments"
    NonExhaustivePatterns [] -> "Non-exhaustive patterns: no clause"
    NonExhaustivePatterns witness -> "Non-exhaustive patterns: no clause matches " <> unwords (map renderPattern witness)
    OverlappingClauses a b -> "Overlapping clauses: " <> show a <> " and " <> show b
    NoRecursionArgument self failures ->
      "No primitive recursion argument for "
        <> T.unpack self
        <> ": "
        <> intercalate "; " ["argument " <> show index <> ": " <> displayException err | (index, err) <- failures]
    RecursiveCallInBaseCase clause -> "recursive call in base case, in clause " <> show clause
    InvalidRecursionPattern clause -> "recursion column must contain only 0 and S x, in clause " <> show clause
    InvalidRecursiveCall clause ->
      "recursive call changes a parameter or does not use the immediate predecessor in clause " <> show clause
    RecursiveCallInLambda self -> "recursive call to " <> T.unpack self <> " inside a lambda"
    UnexpectedRecursiveCall self -> "Unexpected recursive call to " <> T.unpack self
    MutualRecursion ident -> "Mutual recursion is unsupported: " <> T.unpack ident
    NoCompiledCode ident -> "No compiled code for " <> T.unpack ident
    CompiledArityMismatch ident expected found ->
      "Compiled arity mismatch for " <> T.unpack ident <> ": expected " <> show expected <> ", found " <> show found
    InternalError message -> "Internal elaborator error: " <> message
    where
      quoted s = "'" <> s <> "'"
      splat group = "$[" <> T.unpack group <> "]"

-- | A pattern in equation syntax, parenthesized when it is a successor.
renderPattern :: Pattern IrrelevantName -> String
renderPattern = \case
  VarP hint -> T.unpack (rawName hint)
  ZeroP -> "0"
  SuccP p -> "(S " <> renderPattern p <> ")"
