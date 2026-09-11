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
- A `sorry` tactic, which abandons the proof at its goal; the error lists the
  assumptions and the goal of that branch, and `|`, `try` and `repeat` do not
  catch it, so a script under construction may end in `sorry` to see where it
  stands.
- The rule `Cut`, in `Language.Praxis.PRA.Rule.G3i`: admissible in pure G3i,
  it is not eliminable in the presence of `Ind`, which needs it to reason
  about hypotheses mentioning the induction term.

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
- PRA terms are written in the applicative syntax of the equation language,
  whose grammar `Language.Praxis.PRA.Syntax.Parser` now shares with
  `Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Parser`: `plus x (S y)`
  for `plus(x, S(y))` and `mu {lt} 3 0` for `mu {lt} (3, 0)`, with lambdas
  as schema parameters and the bounded search `μ i < b. body`. A term
  argument of a tactic is a name, a numeral or a parenthesized term, as in
  `Defeq (S t) (S t)`. `Language.Praxis.PRA.Syntax.Pretty` renders terms the
  same way, and `{- -}` comments are accepted throughout.
- The library signature `arithmetic` is now `builtin`, and
  `Language.Praxis.PRA.Tactic.Quote` exports `pra`, the quasiquoter over it;
  `praQuoter` remains for signatures of one's own.
- `Language.Praxis.PRA.Syntax.Pretty` renders through the notations the parser
  reads whenever the signature has their symbols: operators infix, `ifte` as a
  conditional, a schema instance with its parameter in braces or as a lambda,
  and an instance of `mu` at a lambda as the bounded search `μ i < b. body`.
- `induction` takes a term, `induction (S x) as n` or a term metavariable of a
  rule, and abstracts its occurrences into the eigenvariable; the hypotheses
  mentioning the term are generalized into the induction formula through
  `Cut` and reintroduced in each case, where the induction hypothesis is an
  implication from them.
- The errors of schematic proofs render metavariables by name, through
  `renderSchemaTacticError` and the hooked renderers of
  `Language.Praxis.PRA.Syntax.Pretty`, so a `sorry` report reads `Γ |- A`.

## 0.1.0.0 - YYYY-MM-DD
