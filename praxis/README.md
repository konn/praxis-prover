# praxis

The Surface Language compiler and checker for Praxis. Surface declarations
elaborate into Praxis Core, the explicit typed intermediate language, then
lower to CoPRA, the internal PRA kernel language provided by `praxis-copra`.
The PRA kernel checks the resulting definitions and proofs. The bundled
[`base` library](data/libraries/base/README.md) provides natural arithmetic
and order, finite ordinals, lists, and length-indexed vectors with checked
proofs.

From the repository root:

```sh
cabal run praxis -- check praxis/data/libraries/base
```

The [`logic` example](data/libraries/logic/README.md) proves Glivenko's
theorem for implication and bottom, with a verified proof transformation
and a shared-tree evaluator for running it on a classical Peirce proof:

```sh
cabal run praxis -- eval praxis/data/libraries/logic/src/Logic/Glivenko.px \
  --entry Logic.Glivenko.demo --nat 0 --nat 1
```

## Internal mode

`internal T where` selects an indexed datatype of derivations as the
calculus in which declarations construct proofs. Inside the block,
signatures state object conclusions and the constructors of `T` are in
scope. Leaving it gives ordinary proof-producing functions with generated,
PRA-checked membership and conclusion contracts.

For example, in the Glivenko module:

```text
module ClassicalExamples where
  internal Classical where
    peirce-law : {a b : Formula} -> Imp (Imp (Imp a b) a) a
    peirce-law {a} {b} = by
      exact peirce {a} {b}
```

This exports `ClassicalExamples.peirce-law` with result type
`Classical (Imp (Imp (Imp a b) a) a)`. The demo passes that proof to the
verified `glivenko` transformation. Internal blocks preserve enclosing
namespaces, support qualified theory names, and scope their constructor
selection locally. Formula parameters give uniform theorem schemata;
native function arrows retain their usual meaning.

The first implementation accepts checked first-order indexed proof
families with one explicit conclusion index and no type parameters. Proof
bodies may use construction terms or `by` blocks with `exact`, `apply`,
bare terms, and focused subproofs. See the
[`logic` example](data/libraries/logic/README.md#entering-and-leaving-a-theory)
for a complete internal proof. Object proofs remain data; internal mode
adds no reflection rule to PRA.

Construction tactics also work in ordinary value definitions, including
local function arguments and nested `by` expressions. For example,
`next n = by apply S; exact n` constructs a natural number when `next` has
type `Nat -> Nat`. An explicitly typed `Proof a` definition uses the same
construction elaborator as an internal declaration. Internal mode supplies
the selected proof family and its constructor scope; native proposition
goals continue to use the PRA proof engine. Values used syntactically as
dependent indices still require ordinary index expressions, rather than
nested `by` blocks.

The logic library also contains a first-order foundation with locally
nameless syntax, finite PA axiom witnesses including induction, and an
initial certified relation-definition interface. See
[the first-order examples](data/libraries/logic/README.md#first-order-theories-and-definitions)
for its current scope and limitations.

## Copyright

(c) Hiromi ISHII 2026- present
