# Mathematical soundness and implementation review

Review date: 2026-09-22. This reviews the implementation at `f60e0a1` and
the repairs accompanying this report. It concerns inference, substitution,
interpretation of statements, conservativity over PRA, and implementation
uniformity. It is not a security review.

## Assessment

The review found an actual inconsistency in declaration certification and a
second invalid inference accepted through the direct certification API.
Both have been repaired. The primitive proof checker rejected the expanded
invalid derivations. This supports locating these defects in the wider
trusted certification layer; it does not establish consistency of the whole
implementation.

The primitive calculus has a straightforward interpretation in PRA. The
important remaining assurance obligation is that every accepted declaration
really has an expansion into that calculus, and that the translated
statement means what its source says. Standard-model truth, a conservative
proof translation, and correctness of the implementation of that
translation are three different claims. Passing tests establishes none of
them in full.

## Defects found and repaired

### P0: incomplete schematic substitution certified a contradiction

`Tactic.instantiateFormula` and `boundTerm` substituted direct applications
of a schematic function but missed occurrences inside compiled lambda
parameters. The quasiquoter had a separate implementation of this operation.
Thus an appeal could combine the old function inside a lambda with its new
instance outside it. That is not a legitimate substitution instance of the
proved sequent.

The complete [regression](../praxis-core/test/data/schematic-contradiction.pra)
first proves the valid schematic equation

```text
mu {λ i. p(i)} 1 = (if p(0) then 0 else 1).
```

The inconsistent appeal changes only its right-hand occurrence to `p := 1`.
A subsequent instance `p := 0` yields `1 = 0`, then `0 = 1`, then bottom.
Before the repair every declaration certified. The regression now rejects
the declaration `bad`, before either contradictory theorem is registered.

The repair puts simultaneous substitution in
`Signature.instantiateSchematicTerm`, used by both runtime certification and
generated proofs. It substitutes throughout compiled programs, reconstructs
captures when necessary, avoids variable capture, and does not recursively
substitute into replacements. Matching compiled closures also respects
explicitly supplied substitutions. Tests cover constants, renaming, nested
closures, captured values and primitive checking of instantiated proofs.

### P1: direct appeals bypassed induction's eigenvariable condition

`useLemmaWith` enforced eigenvariable freshness, but `certify` called
`instantiateLemma` without that check. This was more than an imprecise trust
description: an appeal to an honestly checked induction rule, with two
valid primitive premise proofs, certified

```text
(x = 0 → S x = 0) ⊢ 1 = 0.
```

Take the induction formula `A(x) := x = 0`, target `1`, and context
`Γ := {x = 0 → S x = 0}`. Its base premise is reflexivity; its step premise
follows by implication elimination. The conclusion is false at `x = 1`.
The primitive induction checker rejects it because `x` occurs freely in Γ.
The ordinary textual tactic path already rejected this appeal; the direct
certifier did not.

The check now lives in `instantiateLemma`, shared by tactic construction
and certification. The new regression first checks both premise proofs and
then requires `certify` to reject the appeal with `NotEigen`. It does not
depend on supplying a fabricated lemma or an unproved premise.

### P1: surface proof erasure discarded typing obligations

Statement elaboration accepted terms such as `(absurd rfl : Nat)` and
`f rfl` for `f : (0 ≡ 1) -> Nat`, then erased their nonexistent proofs.
Instance method elaboration also discarded obligations returned by the
ordinary clause elaborator. These were failures of the source language's
typing and adequacy contract. An accepted erased equation `0 = 0` alone is
not a proof of arithmetic inconsistency.

Function clauses and instance methods now retain their obligations.
Theorem applications and calculations include supplied proofs through the
existing core `Cut` rule, so erased arguments must still be proved.
Statements reject proof arguments until statement elaboration has an
equivalent checking path. This is an explicit restriction: valid proof
arguments in statements are also currently unsupported.

### P2: the index solver confused occurrence with impossibility

The occurs check classified `n = S (n - 1)` as a constructor clash, although
`n = 1` is a solution. Occurrence beneath an arbitrary function does not
make a value its own proper subterm. The repair reports such constraints as
`Stuck`; it reports a clash only for occurrence through constructors, as in
`n = S n`. This repairs an incorrect mathematical inference in elaboration;
the review did not exhibit an accepted primitive contradiction from this
defect alone.

## Remaining actionable findings

### P2: draft assumptions are indistinguishable from proved dependencies in the editor

In `praxis-lsp/src/Language/Praxis/LSP.hs`, `analysePra` inserts
`declLemma d` after `checkDecl` fails. The helper named `certified` does the
same. For example:

```text
theorem hole : |- 0 = 1
by sorry
theorem downstream : |- 0 = 1
by exact hole
```

The analysis reports the `sorry` as information, but does not report that
`downstream` depends on an unproved assumption. This behavior is deliberate
and covered by the existing LSP test; running the example above also returns
only that one information diagnostic. It is not a new discovery about
batch certification: the quasiquoter rejects `hole`, and the surface batch
checker does not register failed theorems. Nevertheless, editor diagnostics
do not constitute a certification verdict.

**Recommendation:** retain statements for navigation and exploratory
checking, but track unproved dependencies transitively and expose a distinct
conditional status. Keep the certified environment separate from the draft
environment; do not use the same `Map String Lemma` to imply both contracts.

### P2: adequacy tests can pass without testing an inhabited domain

In `praxis/test/Language/Praxis/Surface/AdequacyTest.hs`, both
`propFunction` and `propStatement` turn failure to generate arguments after
50 attempts into a successful property labelled “vacuous.” Failure of a
generator is not evidence that its domain is empty. A regression in index
generation or a sparsely inhabited type can therefore remove all useful
samples while the suite remains green.

**Recommendation:** require successful sample coverage for fixtures known
to be inhabited, seed them with concrete witnesses, and distinguish
deliberately empty fixtures from generator exhaustion. Exhaustion should
be reported as insufficient coverage, not mathematical vacuity.

There is a separate coverage limitation: `genAt` interprets every type
parameter as `Nat`, with the always-true membership predicate, and generates
small naturals. Those tests cannot establish behavior for arbitrary type
predicates or distinguish every missing membership premise. Add inhabited
and empty predicates, nontrivial data-type instances, and nested container
instances. These are testing gaps, not demonstrated new false theorems.

### Closed: runtime certification and exported proof generation now cover quantified premises

`Certificate` is an abstract checked entry retaining the `Free Step`
derivation and its lexical dependency certificates. The runtime library,
surface prelude and surface checker store these entries; statement maps are
projections for parsing and tactic search. A failed declaration cannot be
inserted through this API. Dependencies are retained by identity, so later
shadowing does not rewrite an earlier proof.

`replayCertificate` instantiates the retained derivation, substitutes actual
premise proofs, expands appeals recursively, and checks the resulting
primitive proof and its conclusion with `inferConclusionIn`. It uses the
statement instantiator for proof fields, including schematic closures.
Supplied premise proofs are checked against their instantiated sequents.
Replay is explicit: ordinary checking retains a certificate without eagerly
expanding its dependency DAG.

The quasiquoter now represents a universally quantified premise by a proof
function taking one term per local variable. Calls abstract the premise
proof by capture-avoiding substitution. Runtime replay and export share
premise alpha-renaming, substitution-template freshening, schematic term
substitution and primitive proof transformations. Haskell quotation remains
a specialized code-generation backend; independent kernel replay is the
check on its output, not an assumption that generation is correct.

## Conservativity over PRA

For an arithmetic statement in the original language, conservativity asks
for a translation from an accepted proof to a PRA proof of that statement.
Truth in the standard natural numbers would not suffice: true statements
need not be PRA-provable.

The implementation provides the following ingredients for such a translation:

1. `Rule/G3i.hs` specifies propositional sequent rules, equality, successor
   separation/injectivity and quantifier-free induction. Their instances
   are derivable in PRA. `Cut` composes derivations; it is not an additional
   arithmetic axiom. The induction eigenconditions are essential.
2. Closed primitive-recursive programs use zero, successor, projections,
   composition and primitive recursion. Named definitions are checked for
   arity, missing references and cycles. `eraseFunction` expands a fully
   instantiated, opaque-free program to bare `PRFCode`. Such definitions
   are definitional extensions. Abstract functions remain schematic
   parameters; one must not claim that unresolved opaque code has already
   been erased to a PRA definition.
3. Definitional equality uses finite reductions of those programs. Fuel
   exhaustion preserves residual expressions; it does not assert an
   unproved equality. Each successful finite computation has an equational
   justification in PRA. Term equality compares structure, including after
   interning; hash equality alone is not accepted as term equality.
4. Bounded searches and bounded quantifiers are primitive-recursive codes.
   Reflection appeals to proved lemmas. Data types are encoded by natural
   numbers; generated membership, unfolding and index lemmas are submitted
   for certification. No new unbounded induction rule is introduced by
   these surface constructions.
5. Reusing derived rules requires admissible substitution, weakening and
   substitution of premise proofs, respecting eigenvariables and local
   binders. The two certification defects above broke precisely this step.

These ingredients give a defensible conditional conservativity argument.
The missing implementation-wide result is a verified expansion of every
accepted certificate, including locally quantified premises and schematic
closures, and preservation of its conclusion. This review does not claim
that result. Nor does the informal standard-model adequacy argument in
`elaboration.md` by itself prove proof-theoretic conservativity.

The absence of a total primitive-recursive evaluator for all PRF codes must
not be confused with an obstruction to a uniform syntactic proof
translation. The latter would relate proof predicates,
`Prf_impl(p, A) -> Prf_PRA(T(p), tr(A))`, without asserting a uniform truth
predicate or PRA's own soundness. Constructing and verifying such a `T` is
the relevant conservativity task; it remains outstanding here.

For surface statements, an additional adequacy argument relates finite
values, their numeric encodings, type membership and statement translation.
An over-approximate membership predicate used only as an antecedent makes
the core obligation stronger and is not itself unsound. Erasing an
unproved precondition or strengthening an antecedent without justification
is a different matter and requires checking.

## Maintainability and uniformity

The rule table is a strong design choice: proof constructors, rule names,
primitive checking and primitive tactic application derive from one rule
description. Preserve that arrangement. Centralizing schematic substitution
and eigencondition validation follows the same principle and removes two
demonstrated sources of disagreement.

The remaining structural risks are concrete:

- `Lemma` remains publicly constructible for raw syntax and editor drafts.
  The production library and surface environment now use abstract
  `Certificate` entries; extending that distinction to editor dependency
  status is tracked above.
- Proof erasure is duplicated in `CoreText.termCT` and `Compile.bodyCT`.
  Both accept general `Expr` values and erase `ProofArg`; certification is
  enforced by their callers. Prefer an obligation-bearing elaboration
  result and one shared lowering traversal, with explicit hooks for
  recursive calls and dictionaries. Adding another caller should not
  silently create another way to drop obligations.
- The shared schematic substitution has a structural path for closed
  replacements and closure reconstruction for replacements with captures.
  This distinction is justified by representation and arity, not by
  particular lemma or schema names. Keep its laws under test: identity,
  simultaneous substitution, freshness, and agreement between an
  instantiated statement and an expanded proof's conclusion.

The appropriate next architectural step is a common certificate and
obligation representation, rather than additional special cases in each
frontend.

## Evidence and scope

The review inspected primitive rule specifications and checker generation,
definitional equality and program environments, proof substitution and
weakening, declaration certification and quasiquotation, surface statement
translation and proof erasure, index unification, adequacy tests, and LSP
handling of failed declarations. It is a targeted adversarial review, not
a formal verification or an exhaustive analysis of every compiler branch.

The contradiction fixture is retained in the repository. Regressions also
exercise primitive checking of instantiated closure proofs, the direct
certifier eigenvariable counterexample, rejected unchecked surface proof
arguments, valid theorem/calculation arguments, instance method obligations,
and the index constraint with a concrete solution.

Executed validation after the repairs:

- `cabal test praxis-core --offline`: 389 tests and 38 doctest examples pass.
- `cabal test praxis --offline`: 67 tests pass.
- `cabal test praxis-lsp --offline`: 19 tests pass.
- `cabal build all --offline`: passes.
- `cabal check` in `praxis-core`: exits successfully, with existing package
  metadata and version-bound warnings.
- Fourmolu and Cabal Gild checks pass for the changed source and package file.

Existing warnings and the unavailable HLS cradle do not count as successful
HLS verification; package builds and tests provide the executed compiler
checks.

## Follow-up stages

1. Certificate retention and quantified-premise replay are implemented in
   `Language.Praxis.PRA.Certificate`, the runtime library and the surface
   checker. Four focused regressions cover runtime replay, exported proof
   functions, incorrect supplied premises and lexical dependency retention.
   The core suite passes 393 tests and all 38 doctest examples. The initial
   doctest run lacked the local package in Cabal's environment; rebuilding
   the library restored it, and the complete rerun passed.
   The surface suite (67 tests), LSP suite (19 tests), formatting checks and
   core package check also pass after this change.
