# Changelog for `praxis-core`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## Unreleased

### Added

- Term metavariables with parameters, `(p(n) : term)`: an abstract function,
  written applied, `p(n)`, and standing as the parameter of a schema,
  `holdsBelow {p} n`, which the checker unfolds around it. So a derived rule
  states course-of-values induction with the step as its only premise,
  `(step : holdsBelow {p} n = 1, Γ |- 0 < p(n)) : Γ |- 0 < p(t)`, and proves it
  once. An appeal infers `p` by abstracting the arguments in the goal, at
  `p(t)`, or from an instance of the schema in the goal, at `holdsBelow {p} n`;
  the variables the function found captures are passed to the schema as
  further variadic arguments. In the kernel, `Function` gains `Abstract` and
  `Program` gains `Opaque`, a call left as it is by evaluation; `Signature`
  recognises the instances of its schemas, `schemaInstanceOf`, and
  instantiates them again, `applySchemaNamed`; the engine takes an `Env`, the
  definitions and the signature, where it took a `KernelEnv`; `Arg` gains
  `ArgFun`, an `Abstraction`.

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
- `cong`: `cong H` closes an equation `u = v` by the hypothesis `H : t = s`
  when `v` is `u` with occurrences of `t` replaced by `s`, or the other way
  round, and `cong` alone by the first hypothesis which fits; the context of
  the occurrences is inferred by comparing the sides, and the proof is `Defeq`
  on `u = u`, `Subst` and `Id`.
- A comparison standing alone as an atom: `x < y`, `x <= y` and `x == y`
  are read as `(x < y) = 1` and so on, in a formula or a pattern, and
  `renderAtomic` shows such an equation the same way; `comparisonSymbols`
  and `isComparison` in `Language.Praxis.PRA.Syntax.Parser` name the symbols
  involved. `builtin` gains `le`, with `n <= m` as `n < S m`.
- `have H: (A) { u }`: proves `A` by `u` and goes on with it as the
  hypothesis `H`, a `Cut` whose second branch is the rest of the script;
  without a name, the hypothesis is `H`, or the next `H<n>` when `H` is
  taken.
- A lemma stating an equation may be named wherever `symmetry`, `rewrite`
  and `cong` take a hypothesis: its instance is found where it is used, at
  the differing subterms of the goal for `cong` and at the first subterm the
  left side matches for `rewrite`, cut in and proved by the lemma.
  `LemmaNotEquation` and `Undetermined` report a lemma of another shape, or
  an instance the use does not determine.
- Metavariables with parameters: `(P(n) : formula)` declares `P` over the
  `var` metavariable `n`, and `P(0)`, `P(S n)`, `P(t)` are the formula at
  those arguments, so a derived rule can state induction. Appealing to such
  a rule infers `P` by abstracting the argument in the goal, every
  occurrence of it; the `Schematic` class gains `metaApplied`, `Bindings`
  keep the names placeholders must avoid, and `Language.Praxis.PRA.Proof.Transform`
  exports `substFormula` and `substAtomic`, which the spliced rule uses.
- Eigenvariable conditions, declared: `rule … : Γ |- P(t) where n ∉ Γ, t`,
  or `where n not free in Γ, t`, states which metavariables the `var`
  metavariable `n` is not free in, as the figures of the primitive rules do.
  An induction on `n` in the proof is accepted only where the declaration
  covers every metavariable of its context, its term and its motive, but
  one `n` parameterizes, and `NotDeclaredFresh` says what to add; the
  eigenvariables of a lemma are the ones declared, no longer inferred from
  its proof. `Decl` carries `declSides`, and `proveOpenDeclared` and
  `runTacticDeclared` take the declarations.
- `Language.Praxis.PRA.Proof.Transform`: `substProof` and `weakenProof`,
  the substitution and weakening of a proof, renaming the variables its steps
  bind apart; the spliced proof of an appeal to a theorem is built with them.
  `identityProof` derives `Γ, A |- A` for any formula, and the quasiquoter
  splices it where a script closes a goal by `Id` or `assumption` on a
  `formula` metavariable, so `rule r (A : formula) (Γ : ctx) : A, Γ |- A by
  assumption` certifies, as does generalized induction under a `formula`
  metavariable.
- Unfolding lemmas: the equations a function was defined by are lemmas in
  scope wherever its signature is, one per clause, stated as the theorem
  `|- f p₁ … pₙ = e` with the pattern variables free and proved by `Defeq`,
  which the checker verifies against the definitions; nothing is trusted.
  `Language.Praxis.PRA.Tactic.Unfolding` states and certifies them. A lemma
  is named by its symbol and the shape of the patterns its clause matches
  on, `add_0`, `add_S`, `sub_S`, `ifte_0`, `h_SS`, or by the symbol alone
  for a clause matching on nothing, `lt`; a declaration of the same name
  shadows it, and two clauses which would be named alike are an error.
  `exact add_S`, `rewrite sub_S in H1` and `cong sub_S` use them as any
  lemma stating an equation. A `Symbol` records its clauses,
  `symbolEquations`, which `compileDefinitions` sets and a spliced signature
  keeps; the quasiquoter splices an appeal to one as the proof itself, a
  `LemmaEntry` now carrying a `LemmaSource`. `Language.Praxis.PRA.Syntax.Parser`
  exports `resolveTerm`, and `Language.Praxis.PRA.Tactic` `renderProofErrorReason`.
- Bounded quantifiers: `∀ i < t. A` and `∃ i < t. A`, or `forall` and
  `exists` spelt out, are atoms, the equations of
  `holdsBelow {λ i ys. c} t ss` with 1 and of `mu {λ i ys. c} t ss < t`, where
  `c` is the code of `A` and the lambda captures the maximal subterms of `c`
  not mentioning `i`, the `ss`; so a substitution in the formula is one in
  what it captures, and the printer shows it as it was written. Within a term,
  `∀ i < t. c` and `∃ i < t. c` quantify a code `c` directly, in the equation
  language as in the concrete syntax, where `⟦A⟧`, or `[[A]]`, is the code of
  `A`. The equation language gains `QuantET`, and `Syntax.capturedTerms`
  lists what a lambda captures.
  Any number of parentheses around a quantifier read it as the formula
  unless a term goes on after it, a wildcard in the body of a pattern is
  captured, and an abstract function of a rule may stand anywhere in the
  body.
- Codes of formulas, `Language.Praxis.PRA.Reflection`: `⟦s = t⟧ = s == t`,
  `⟦A /\ B⟧ = conj ⟦A⟧ ⟦B⟧`, likewise `disj` and `imp`, `⟦_|_⟧ = 0`, a
  comparison `<` or `<=`, or an instance of `holdsBelow`, equated with 1 is
  its own code, and `0 < c`, for any other `c`, has the code `c`.
  `encodeFormula` and `decodeFormula` are inverse on formulas without
  metavariables.
- `reflect` and `reify`, on the goal or on a hypothesis, `reflect H as K`:
  the truth of a code, `0 < c` or `c = 1`, becomes the formula it is the code
  of, and the converse. Both are built from the reflection lemmas of the
  library, found by name, `conjIntro`, `conjElim1`, …, `eqOne`, `belowOne`;
  `ReflectionLemma` names one which is missing or hidden by a premise or a
  hypothesis of its name, `NothingToReflect` and `NoCode` what cannot be done.
- The library of lemmas, `src-pra/lemmas.pra`, which
  `Language.Praxis.PRA.Library` embeds and certifies when first needed,
  splicing it being too slow to compile: order and arithmetic (`leTrans`,
  `leAntisym`, `ltTrichotomy`, `addComm`, `addCancelL`, `subAddCancel`,
  `addLtMonoL`, …), multiplication (`mulComm`, `mulAssoc`, `mulDistribL`,
  `mulLeMonoL`, `mulPos`, …), conditionals (`ifZero`, `ifPos`), the
  connectives and `==`, the reflection lemmas, `holdsBelow` (`belowIntro`,
  bounded course-of-values induction, `belowElim`, `belowUse`), `mu`
  (`muLe`, `muMin`, `muHit`, `muWitness`, `muBelow`, `muMiss`, `existsUse`,
  `muLeast`) and pairing (`projWChar`, `pi1Pair`, `pi2Pair`, `pairInjL`,
  `pairInjR`, `pairSurj`, `consSurj`, `lftLt`, `rgtLt`, `pi1Le`, …).
  `libraryScope` adds the unfolding lemmas of `builtin`; the quasiquoters do
  not see the library.
- `exact D` on a premise `D` whose hypotheses are among those of the goal
  uses it weakened, a `WeakenStep`, which the quasiquoter splices with
  `weakenProof`.

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
- `NotAnEquation` names the tactic which met it, `refl` or `cong`.
- A hypothesis selected by pattern, for `symmetry`, `rewrite` and `cong`, is
  written in parentheses, as an atom argument of a rule is; a bare name
  selects by name.
- The builtin conjunction of codes is `conj`, where it was `and`, which
  clashed with the Prelude; `disj` and `imp` join it, each 0 or 1 whatever
  its arguments.
- `forall` and `exists` are reserved words, of the equation language and of
  the concrete syntax.
- The bounded search `μ i < b. body` captures the maximal subterms of its
  body not mentioning `i`, numerals included, as the quantifiers do, and
  `Syntax.abstraction` abstracts by the same rule, a body `f i` for a
  function `f` which is not inlined being `f` itself; so an instance of `mu`
  or `holdsBelow` the engine builds reads back as the sugar it is shown as.
- `on` with a lemma tries every placing of the hypotheses named among those
  of the lemma, whose order is not the order they were written in, and a
  succedent the arguments do not determine is matched after the hypotheses.
- An appeal instantiating an eigenvariable of the lemma by a `var`
  metavariable `n` of the rule being proved needs the rule to declare `n` not
  free in every metavariable of the goal and of the other arguments, but one
  `n` parameterizes, as an induction on `n` does; `NotDeclaredFresh` says what
  to add.

## 0.1.0.0 - YYYY-MM-DD
