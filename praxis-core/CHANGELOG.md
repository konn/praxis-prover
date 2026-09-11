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
- Appeals to lemmas: `exact name` refers to a theorem or derived rule
  certified before, besides the premises of the rule being proved. The
  metavariables of the lemma are inferred by matching its statement against
  the goal or given as arguments, `exact symm a b`; its context metavariable
  takes the hypotheses it does not mention, and otherwise they are weakened
  in; the free variables of a theorem are instantiated by the goal; the
  premises of a rule become goals, `exact conjSwap { Id } { Id }`. In the
  engine, `Lemma`, `Certified`, `proveWith` and `proveOpenWith` carry the
  lemmas, a partial proof is a `Free (Step a)` whose `LemmaStep` records the
  `Appeal`, and `certify` checks an appeal against the lemma's statement
  instantiated afresh. In the quasiquoter, a declaration is a lemma for the
  declarations after it, across the quotes of a module.
- Named hypotheses. A goal is a `Goal`, whose hypotheses are named `H1`,
  `H2`, … in the order the sequent lists them, a context metavariable by its
  own name; a hypothesis a step introduces takes the next number the branch
  has not used, or the name `as` gives it, `Cut (a = 0) as H`, `ConjL as HA
  HB`, `induction t as n IH H'`. `symmetry`, `rewrite` and `exact` accept a
  name, `rewrite H1 in H2`, and `on` names the hypotheses a rule or a lemma
  acts on, `ImplL on H2`. A `sorry` report lists the hypotheses by name.
  `parseGoal` and `Decl` carry goals, `prove` takes one, and `goalOf` makes
  one from a sequent.
- Lemma libraries, across modules: a quote opening with `library name` also
  binds `name :: Library`, the lemmas in scope at its end with their
  statements and the global names of their bindings, and `praQuoterIn name`,
  in a module of its own, is a quasiquoter whose quotes appeal to them, as
  `prfQuoter` reuses a signature. `quoteFile`, `praFile` and `prfFile` splice
  a file of declarations in place of a quote, relative to the package
  directory, and recompile the module when the file changes.
- For tools such as the language server of `praxis-lsp`: `checkDecl` in
  `Language.Praxis.PRA.Tactic.Quote` certifies a declaration without
  generating anything, `checkQuote` in
  `Language.Praxis.PRA.PrimitiveRecursion.Quote` checks a quote of
  definitions the same way, reporting a `CheckError` with its position, and
  `syntaxErrorPosition` locates a `SyntaxError`.
- Calculational proofs: `calc t0 = t1 by u1 = t2 by u2 …` proves the goal
  `t0 = tn` as a chain of equations, each step proved by its tactic under the
  hypotheses of the goal, by `refl` when none is given; the steps are cut in
  as one conjunction, split by `ConjL` and chained by `Subst` down to `Id`.
- `Language.Praxis.PRA.Proof.Transform`: `substProof` and `weakenProof`,
  the substitution and weakening of a proof, renaming the variables its steps
  bind apart; the spliced proof of an appeal to a theorem is built with them.
  `identityProof` derives `Γ, A |- A` for any formula, and the quasiquoter
  splices it where a script closes a goal by `Id` or `assumption` on a
  `formula` metavariable, so `rule r (A : formula) (Γ : ctx) : A, Γ |- A by
  assumption` certifies, as does generalized induction under a `formula`
  metavariable.

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
- `Fresh` lives in `Language.Praxis.Name`, re-exported by
  `Language.Praxis.PRA.Tactic`, whose engine now runs over `Schematic` names,
  which tell the metavariables of a lemma's statement apart from its free
  variables. `Exact` carries the arguments of the appeal, `proveOpen` returns
  a `Free (Step a) String`, and an opaque formula or context metavariable is
  never selected by `symmetry`, `rewrite` or the atomic patterns of a rule.

## 0.1.0.0 - YYYY-MM-DD
