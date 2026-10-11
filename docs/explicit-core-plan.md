# Explicit surface core migration

## Objective

Keep the PRA calculus unchanged. Elaborate the existing surface fragment into
an explicit core with typed values, explicit dictionary arguments and evidence;
lower that core to primitive-recursive definitions and checked PRA derivations.
Ordinary data declarations and indexed declarations use the same constructor
signature. Recovering an erased proof field means applying a certified
membership elimination lemma, never extracting a derivation from a number.

## Invariants

- Constructor signatures contain every value and evidence argument, in scope.
  Source visibility, computational relevance and storage are distinct.
- An ordinary datatype is a family with no value indices.
- The explicit boundary has no instance search or unchecked proof erasure.
- Value lowering preserves membership and index evidence. Pattern-bound proof
  fields require certified membership inversion; repacking requires introduction.
- A numerical encoding must retain every condition used by its eliminators.
  Missing conditions are errors, not silently omitted premises.
- Proof arguments are retained until a checked derivation discharges them.
  Bottom elimination occupies a value argument even when its evidence is erased.
- Kernel checking proves the translated statement. Source adequacy remains a
  separate obligation; this refactor does not claim a formal conservativity proof.

## Implementation sequence

1. Normalize all constructor declarations to one nonoptional telescope and result
   signature; share application, matching, encoding and adequacy generators.
2. Introduce context/type-indexed explicit values, fully instantiated application
   signatures and explicit evidence arguments. Integrate the boundary into the
   existing elaborator and compiler, rather than adding an unused alternative AST.
3. Separate elaborated evidence from source proof syntax and enforce the
   membership introduction/elimination contract during PRA lowering.
4. Make structured checked declarations the compilation boundary, retaining
   readable core dumps and independent primitive certificate replay.
5. Test constructor-syntax equivalence, proof forwarding and unpack/repack,
   function/container boundaries, invalid evidence and primitive replay. Run
   formatting, package builds and all affected package tests.

## Scope

Preserve the currently accepted first-order, primitive-recursive language and
its examples. This migration does not introduce arbitrary dependent type theory,
unrestricted higher-order computation or new arithmetic axioms. Existing source
syntax remains usable. No commits or pushes are part of this request.

## Progress

- Constructor normalization, the typed value boundary, certificate handoff,
  structured PRA admission, and end-to-end regressions are implemented.
- All three package suites, the kernel doctests, formatting, package checks,
  HLS checks and the surface-core CLI regression pass.

## Implemented architecture

`Env.ConstructorSignature` is mandatory for both declaration syntaxes. The
signature separates its logical telescope, result indices and proof premises
from `ctorFields`, the numerical storage layout. `constructorValueTypes` retains
the logical types of stored fields. Applications, patterns and generated index
functions consume that common representation. A proof premise may refer only to
values already in scope.

`Surface.Core` contains a private `Value evidence context type` GADT. Variables
are membership proofs in the heterogeneous context; applications pair an
instantiated signature with a heterogeneous list of arguments of those types.
Construction checks global declarations, argument counts, evidence counts and
resolved dictionary implementations. Dictionary closures contain no free value
variables. Signatures retain explicit type arguments and numbered index
arguments; static method dictionaries are resolved before this boundary.
Singleton reflection rejects unresolved value indices. An unconstrained erased
type argument, such as the element type in `length Nil`, is instantiated at Nat.

The existing bidirectional elaborator transports checked annotations in resolved
syntax, then constructs this core for every function clause, including generated
index functions and instance methods. `fcBody` lowers the typed value instead of
storing a second independently mutable term tree. Dictionary pruning is a
lowering optimization; it retains the original typed body and all evidence.
An impossible clause is an explicit empty branch, with no fabricated value of
its result type; its total numerical implementation is guarded by the certified
membership/index contradiction.

Evidence is staged explicitly:

1. A body contains scoped proof obligations with their propositions, local value
   types, dictionary slots and enclosing proof hypotheses.
2. The proof engine elaborates each obligation into a PRA declaration. The
   checker retains a `Certificate`, including its derivation and lexical
   dependencies, only after PRA checking succeeds.
3. `Core.traverseObligations` replaces every pending obligation by that
   certificate. `Check.coreBodies` exposes these checked typed bodies. A failed
   obligation prevents publication of the body's result contracts.

For a constructor pattern, evidence comes from the certified membership
inversion lemma. Repacking uses the constructor introduction lemma and the
obligation certificate. Passing a value through a function uses its certified
closure and index contracts; passing it through a container uses field
membership. Functions returning proof-bearing values, including values inside
containers, must establish a membership contract. The numerical value never
contains a serialized PRA derivation.

`validateEncoding` refuses missing proof conditions and unavailable field-index
conditions before a datatype's encoding is admitted. Existing deliberately weak
representations of some higher-kinded fields remain weak: they do not gain
additional elimination lemmas.

`Check.addEquations` and `Check.certifyDeclaration` are the structured PRA
admission APIs. Existing definition and tactic generators still have text
adapters, which parse into those APIs. This preserves the readable PRA dump and
the existing proof tactics; it does not replace every generator with native AST
construction. Source proof syntax is transient during checking and is absent
from the checked bodies.

Inspect both representations with:

```sh
cabal run praxis -- check --alone --dump-surface-core praxis/test/data/proof-flow.px
cabal run praxis -- check --alone --dump-core praxis/test/data/proof-flow.px
```

The PRA inference rules and kernel are unchanged. `replayCertificate` expands
named appeals and independently checks the resulting primitive-rule derivation.
The proof-flow regression exercises this for the theorem that projects an erased
proof from a GADT. These checks establish correctness of the generated PRA
statements; they are not a formal adequacy proof of the whole source language.

## Verification

- `cabal test praxis`: 89 tests passed, including constructor normalization,
  typed scope/signature/dictionary rejection, proof forwarding through functions
  and containers, rebuilding from a theorem application, impossible branches,
  invalid evidence, and independent replay of a GADT projection proof.
- `cabal test praxis-core`: 401 tests and 38 doctests passed.
- `cabal test praxis-lsp`: 25 tests passed.
- HLS: both the explicit core and downstream LSP module checked successfully.
- Fourmolu checks pass; `cabal-gild` refreshed the module lists.
- `cabal check` exits successfully for all three packages, with existing package
  metadata and dependency-bound warnings.
- `cabal run praxis -- check --alone --dump-surface-core
  praxis/test/data/proof-flow.px` succeeds. The dump retains explicit index
  arguments, proof counts, dictionary types and source result types of empty
  branches.

No kernel rules or axioms were added. No commits or pushes were made.
