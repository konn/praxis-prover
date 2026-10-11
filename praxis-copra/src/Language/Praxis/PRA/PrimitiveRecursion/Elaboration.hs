{- | Applicative equation syntax and arity-checked name resolution.
Applications associate to the left; nested arguments use parentheses.
Equations use Haskell-like indentation or explicit semicolon separators.
Elaboration expands variadic schemas and binder sugar, checks coverage and
disjointness, then compiles primitive recursion with unchanged parameters and
calls to environmentally bound PRF codes.

This module re-exports the public elaboration API. The implementation lives in
"Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax",
"Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Parser",
"Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Variadic",
"Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Rename",
"Language.Praxis.PRA.PrimitiveRecursion.Elaboration.CaseTree", and
"Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Compile".
-}
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration (
  Equation (..),
  Pattern (..),
  Splat (..),
  SplatPosition (..),
  IrrelevantName (..),
  EqTerm (..),
  Function (..),
  SchemaArg (..),
  SomeFunction (..),
  VariadicTemplate (..),
  Env,
  ElaborationError (..),
  SchemaError (..),
  FunctionalTerm (..),
  RenamedEquation (..),
  ExpandedFamily (..),
  expandFamily,
  expandedEquations,
  instanceName,
  signatureEnv,
  equationEnv,
  renameTerm,
  renameEquation,
  renameEquations,
  EquationRow (..),
  CaseTree (..),
  ElaboratedDefinition (..),
  definitionCode,
  SomeProgram (..),
  ElaboratedSchema (..),
  ElaboratedFamily (..),
  instantiateSchemaFunction,
  buildCaseTree,
  elaborateDefinition,
  elaborateRenamedEquations,
  elaborateEquations,
  elaborateFamilyWith,
  elaborateInstances,
  Parser,
  spaceConsumer,
  lexeme,
  symbol,
  parens,
  braces,
  decimal,
  reserved,
  anySymbol,
  patternP,
  eqTermP,
  equationP,
  parseEqTerm,
  parseEquation,
  parseEquations,
  LocatedEquation (..),
  equationsP,
  parseLocatedEquations,
  EquationSyntaxError,
) where

import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.CaseTree
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Compile
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Env
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Error
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Parser
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Rename
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Variadic
