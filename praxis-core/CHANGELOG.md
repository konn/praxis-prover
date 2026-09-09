# Changelog for `praxis-core`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## Unreleased

### Added

- A tactic language for the calculus: `Language.Praxis.PRA.Tactic` runs
  tactics against a goal and hands what they build to the checker,
  `Language.Praxis.PRA.Tactic.Parser` reads the textual syntax, and
  `Language.Praxis.PRA.Tactic.Quote` provides the `pra` quasiquoter, which
  certifies theorems and derived rules at compile time and splices the proofs.
- Concrete syntax for terms, formulae and sequents, in
  `Language.Praxis.PRA.Syntax.Parser` and `Language.Praxis.PRA.Syntax.Pretty`,
  over a `Language.Praxis.PRA.Signature` naming the function symbols;
  `Language.Praxis.PRA.Pattern` adds wildcards.
- `Language.Praxis.PRA.Proof`: the generic step view `Arg`, `stepFields` and
  `mkStep`, and `inferConclusionOpen` for proofs with assumed leaves.

### Changed

- Errors are dedicated types rather than `String`s, each rendered for a human
  by `displayException`: `KernelError` in
  `Language.Praxis.PRA.PrimitiveRecursion.Function`, `ElaborationError` and
  `SchemaError` in `Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Error`,
  `EnvironmentError` in `Language.Praxis.PRA.PrimitiveRecursion.Environment`,
  `EquationSyntaxError` in
  `Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Parser` and `SyntaxError`
  in `Language.Praxis.PRA.Syntax.Parser`. `DefinitionResolutionFailed` carries
  a `KernelError`. The renaming environment `Env` and its entries `SomeFunction`
  moved to `Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Env`.

## 0.1.0.0 - YYYY-MM-DD
