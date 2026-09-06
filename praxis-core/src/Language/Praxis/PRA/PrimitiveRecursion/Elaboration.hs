{- | Applicative equation syntax and arity-checked name resolution.
Applications associate to the left; nested arguments use parentheses.
Equations use Haskell-like indentation or explicit semicolon separators.
Elaboration checks coverage and disjointness, then compiles primitive recursion
with unchanged parameters and calls to environmentally bound PRF codes.

This module re-exports the public elaboration API. The implementation lives in
"Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax",
"Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Parser",
"Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Rename",
"Language.Praxis.PRA.PrimitiveRecursion.Elaboration.CaseTree", and
"Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Compile".
-}
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration (
  Equation (..),
  Pattern (..),
  IrrelevantName (..),
  EqTerm (..),
  Function (..),
  SomeFunction (..),
  Env,
  FunctionalTerm (..),
  RenamedEquation (..),
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
  buildCaseTree,
  elaborateDefinition,
  elaborateRenamedEquations,
  elaborateEquations,
  Parser,
  spaceConsumer,
  lexeme,
  symbol,
  parens,
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
) where

import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.CaseTree
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Compile
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Parser
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Rename
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax
