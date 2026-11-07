# Glivenko's proof transformation in Praxis

[`Logic/Glivenko.px`](src/Logic/Glivenko.px) proves and implements Glivenko's
theorem for the propositional **implication/bottom fragment**:

```text
CPC proves A    iff    IPC proves ¬¬A
```

Here `¬A` abbreviates `A → ⊥`. Formulas have natural-numbered atoms, bottom,
and implication. IPC derivations use the Hilbert K, S, and explosion axiom
schemata and modus ponens. CPC adds double-negation elimination. There are
no hypotheses in these proof datatypes: the theorem is about theoremhood.
Conjunction and disjunction are not yet implemented as primitive connectives.

## Run the example

From the repository root:

```sh
cabal run praxis -- check praxis/data/libraries/logic
cabal run praxis -- eval praxis/data/libraries/logic/src/Logic/Glivenko.px \
  --entry Logic.Glivenko.demo --nat 0 --nat 1
```

The demo constructs a classical proof of Peirce's law
`P = ((p → q) → p) → p`, runs the verified transformation, and prints
`Result <output conclusion> <input proof size> <output proof size>`:

```text
Result (((((Atom 0 :=> Atom 1) :=> Atom 0) :=> Atom 0) :=> Bottom) :=> Bottom) 35 1273
```

The conclusion is `¬¬P`. Sizes count nodes of the unfolded Hilbert proof;
runtime allocation statistics count shared nodes instead.
The supplied example has 35 classical proof nodes and 1,273 intuitionistic
proof nodes after translation. Its input is supplied by the namespaced
internal theorem schema `ClassicalExamples.peirce-law`.

To inspect both proof objects, use `--entry Logic.Glivenko.demo-proofs` and a
small `--depth`, such as `3`. `--fuel` bounds evaluator steps. The current
`eval` command takes a standalone module, a qualified definition and optional
`--nat` arguments. Runtime arguments follow declaration order, with stored
implicit indices first. For `demo-proofs`, supply the same
`--nat 0 --nat 1` arguments. Other input datatypes are not yet accepted by
the command; the function itself may construct and transform their values.
It supports first-order functions, constructor patterns, naturals and a
small arithmetic builtin set. Imports, callbacks and dictionaries are not
yet supported by this command.

Values print as surface syntax. An operator constructor such as `:=>` or
`:@` is always written between its operands, parenthesised by its declared
fixity, leaving out the implicit arguments its code stores, as source text
leaves them to inference. A constructor goes by its bare name unless two
constructors printed in the same value share it: `demo-proofs` shows
`Classical.:@` and `Intuitionistic.:@`, since both calculi have modus
ponens.

Checking and evaluation are separate phases. The CLI checks the module on
each invocation; the demo takes a few seconds to certify and run on the
development machine, nearly all of it checker cost, not the running time
of the transformation. The evaluator API accepts an already checked module
and can reuse it for different inputs, as an interactive frontend would do.

The proof generator shares unchanged term subtrees between rewrite steps,
so retaining a calculation no longer copies the whole term at every step.
CI runs the complete Glivenko group separately with a 512 MiB heap limit,
including certification, independent Hilbert checking of the evaluated
translation, and rejection of malformed proofs. Run the same memory check
from the repository root with:

```sh
cabal test praxis --test-show-details=direct \
  --test-options='-p /Glivenko/ -j2 +RTS -N2 -M512m -s -RTS'
```

## The algorithm is a Praxis function

The main interface is:

```text
glivenko      : Classical A -> Intuitionistic (nn A)
embed         : Intuitionistic A -> Classical A
recover       : {A : Formula} -> Intuitionistic (nn A) -> Classical A
contradiction : Classical Bottom -> Intuitionistic Bottom
```

`glivenko` recurses on the input proof. It lifts each intuitionistic axiom
into its double negation, replaces a classical DNE axiom by its
intuitionistically provable double negation, and translates MP with a fixed
proof of `¬¬(A → B) → (¬¬A → ¬¬B)`. Only the two immediate premise proofs
are recursive arguments. The helper proof schemata are uniform functions
of formulas, not infinitely many separately registered declarations.

The four intuitionistic helper schemata are:

```text
A → ¬¬A
¬¬(A → B) → (¬¬A → ¬¬B)
¬¬(¬¬A → A)
¬¬⊥ → ⊥
```

Theorems about the transformations are ordinary Praxis theorems over these
proof values. `embed-size` proves by clauses that embedding preserves the
size of a proof, with a calculation for modus ponens:

```text
embed-size (f :@ x) = calc
  classical-size (embed (f :@ x))
  = classical-size (embed f :@ embed x)
  = S (classical-size (embed f) + classical-size (embed x))
  = S (intuitionistic-size f + classical-size (embed x))
      := cong (embed-size f)
  = S (intuitionistic-size f + intuitionistic-size x)
      := cong (embed-size x)
  = intuitionistic-size (f :@ x)
```

## Entering and leaving a theory

The same file constructs the identity schema with construction tactics in
an ordinary definition:

```text
identity : {a : Formula} -> Intuitionistic (a :=> a)
identity {a} = by
  apply (:@)
  {
    apply (:@)
    { exact Intuitionistic.S {a} {a :=> a} {a} }
    { exact Intuitionistic.K {a} {a :=> a} }
  }
  { exact Intuitionistic.K {a} {a} }
```

`apply` supplies a rule with the terms constructed for its remaining
explicit arguments; the ordinary indexed term checker validates every
premise. The `by` block, tactic words, and `{ ... }` focus blocks use
Praxis's existing tactic syntax and parser. Each focus block constructs
one argument. Formula parameters make `identity` a uniform theorem schema.
Modus ponens, `(:@)`, is found by the expected type. `K` and `S` are
qualified because both calculi have them,
and outside internal mode a bare `S` is the natural successor.

Internal mode states the same declaration by its object formula:

```text
internal Intuitionistic where
  identity : {a : Formula} -> a :=> a
  identity {a} = by
    apply (:@)
    {
      apply (:@)
      { exact S {a} {a :=> a} {a} }
      { exact K {a} {a :=> a} }
    }
    { exact K {a} {a} }
```

An internal signature states an object formula. Elaboration wraps its final
result in the selected proof family, so this declares the same ordinary
function `identity : {a : Formula} -> Intuitionistic (a :=> a)`. `K`, `S`,
and `(:@)` denote the selected family's constructors inside the block; in
particular, this `S` is its Hilbert axiom, even though the surface language
also has natural successor. Internal mode selects the proof family and
wraps result signatures; construction itself needs no internalization.
Native proposition goals retain their PRA proof tactics.

Internal mode also works inside ordinary namespaces:

```text
module ClassicalExamples where
  internal Classical where
    peirce-law : {a b : Formula} -> ((a :=> b) :=> a) :=> a
    peirce-law {a} {b} = by
      exact peirce {a} {b}
```

Here `peirce` is the Hilbert proof built by bracket abstraction. Leaving the block
retains `ClassicalExamples.peirce-law` as a normal exported function with a
`Classical` result. The demo passes its proof to `translation`, which calls
`glivenko`. Namespace qualification and the selected calculus are
independent: internal blocks introduce no namespace of their own, and their
constructor selection ends at the closing boundary. A theory can also be
selected by its qualified name, including through an import alias.
Private declarations and nested modules use the existing export rules.
Openings and import aliases restore on leaving the block; fixity discovery
and bare-constructor overload candidates retain their existing module-wide
behavior.

Only the result is wrapped. An input proof remains explicitly typed, for
example `Intuitionistic a -> b :=> a` inside an intuitionistic block means
`Intuitionistic a -> Intuitionistic (b :=> a)`. Native `->` describes the
Praxis function; `:=>` constructs the object implication. Internal mode
does not reinterpret native arithmetic propositions or quantifiers.

The initial implementation selects checked indexed datatypes with one
explicit conclusion index, no type parameters, and fully checked
first-order field memberships. It supports term bodies and `by` blocks
using `exact`, bare terms, `apply`, and focused subproofs. The proof-family
interface is generic: nothing in internal elaboration singles out CPC,
IPC, or this formula language. Declaring a datatype of derivations describes
its rules; it does not add those rules to PRA. Richer proof tactics, generic
language/theory registrations, and GL staging remain future work.

## First-order theories and definitions

The `Logic.FirstOrder` modules provide a concrete first-order foundation:

- `Syntax` separates free atoms (`Free n`) from bound indices (`Bound n`).
  It defines scope checks, free and simultaneous substitution, renaming,
  and opening/closing under quantifiers as certified primitive-recursive
  functions. The language has arithmetic terms, equality, numbered binary
  relations, implication, bottom, and universal quantification.
- `Proof` represents classical first-order derivations as finite data.
  Quantifier and equality constructors carry checked syntax side conditions,
  including equality with the actual opening/closing result. Examples prove
  universal reflexivity and instantiate beneath nested quantifiers.
- `Peano` uses a finite `Axiom` witness datatype for the arithmetic axioms
  and `Induction Formula`, with primitive-recursive formula and validity
  functions. Thus infinitely many induction instances need no infinite
  stored set. `PA` retains the witness and checks its conclusion; the
  `induction-schema` function constructs proofs uniformly from formula
  parameters and checked syntactic side conditions.
- `Definitions` introduces one fresh binary relation using a quantifier-free
  two-parameter template. A definition proof retains the template, original
  formula, and a base derivation of its expansion, with a checked scope
  condition in its membership predicate. The
  generated PRA contract of `erase` certifies extraction of that derivation
  uniformly. Base-language formulas expand to themselves.

For example, `Definitions.same` defines the fresh relation by equality.
Its `same-reflexive` schema works inside `internal DefinitionProof`, and
`base-reflexive` leaves that interface with an ordinary first-order proof
of `Equal t t`. `all-same-reflexive` uses the relation under a quantifier.
Template placeholders are distinct from variable names, so inserting both
arguments is simultaneous; a separate source scope check rejects escaping
indices even in arguments the definition ignores.

This definition interface elaborates proofs directly into base derivations.
It does not yet translate an independently represented extended calculus.
It supports one relation over `Proof`, not arbitrary theories or a sequence
of definitions. Quantified definition bodies, graph-defined functions
(including ZF pairing), ZF/ZFC axiom families, and portable proof bundles
remain unimplemented. General substitution laws and formal adequacy or
semantic soundness proofs of these first-order presentations remain to be
proved. The existing kernel checks all generated PRA contracts; it does
not adopt PA's axioms or infer object-level truth.

## Bracket abstraction in Praxis

The double-negation lemmas `glivenko` uses (`double-negation-intro`,
`-mp` and `-dne`) and `bottom-out`, which `contradiction` uses, are
ordinary finite K/S/explosion/MP proofs; the classical Peirce example adds
one DNE axiom. They are written as lambda terms and compiled by bracket
abstraction, which is itself a Praxis function over derivations, checked
like the rest:

```haskell
-- \f. \p. \nb. f (\g. p (\x. nb (g x)))
double-negation-mp {a} {b} = close (deduction (deduction (deduction (
  Hyp (There (There Here)) :@ deduction (
    Hyp (There (There Here)) :@ deduction (
      Hyp (There (There Here)) :@ (Hyp (There Here) :@ Hyp Here)))))))
```

`Open g a` is an intuitionistic derivation of `a` under a context `g` of
hypotheses, `Hyp m` one of them by its typed de Bruijn index `m : Member a
g`. `deduction : Open (g :> a) b -> Open g (a :=> b)` is the deduction
theorem: it discharges the newest hypothesis, `annotate` first marking each
node by whether it uses that hypothesis (`Use`, in the co-de Bruijn style),
and `abstract` then emitting K for an unused part, the identity for the
hypothesis, and eta or S for an application. `close : Open Empty a ->
Intuitionistic a` reads a derivation under no hypotheses as a closed one.
Their index contracts are certified, so each lemma's type follows from the
types of the lambda term's parts, and `eval` computes its Hilbert proof:
the same trees the earlier Python generator produced. Peirce's law is
classical; its abstraction over `f` applies `S (K DNE)` in the classical
calculus to the `embed`ding of an intuitionistic part built this way.

The lemmas are computed where they are used, not stored as trees: each
application in `glivenko` runs the abstraction at its own formulas. The
demo's evaluation therefore takes about 170,000 evaluator steps where the
stored trees took about 73,000, well within the default `--fuel` of
1,000,000; a larger input needs proportionally more.

## What PRA certifies

The indexed proof datatypes generate primitive-recursive membership and
conclusion functions. Their membership tests check the formulas and the
indices of both MP premises. A proof code cannot establish a formula merely
by claiming it as its final index.

Let `C(p)` and `I(p)` denote these membership predicates, `c(p)` and `i(p)`
their conclusion functions, and `G` the compiled `glivenko` function. Its
generated `#contract` certificate proves the quantifier-free sequent

```text
C(p) > 0  ⊢  I(G(p)) > 0 ∧ i(G(p)) = nn(c(p)).
```

Variables are implicitly universal at the metalevel. Equivalently, for
`Prf_T(p,A) := T(p) > 0 ∧ conclusion_T(p) = A`, this is the uniform
finite-witness form of Glivenko:

```text
Prf_CPC(p,A)  ⊢  Prf_IPC(G(p),nn(A)).
```

The compiler also retains separate `#closed` and `#index` certificates,
projected from the checked joint contract instead of repeating its induction.
`contradiction` composes `G` with the last helper to prove

```text
Prf_CPC(p,⊥)  ⊢  Prf_IPC(contradiction(p),⊥).
```

This is the finite proof transformation underlying
`Con(IPC) ⇒ Con(CPC)`. The implementation does not assert either theory's
consistency, or add an unbounded consistency formula to quantifier-free PRA.
`recover` gives the other direction of Glivenko's theoremhood equivalence.

Inspect the elaborated program or its arithmetic lowering with:

```sh
cabal run praxis -- check --alone --dump-core \
  praxis/data/libraries/logic/src/Logic/Glivenko.px
cabal run praxis -- check --alone --dump-pra \
  praxis/data/libraries/logic/src/Logic/Glivenko.px
```

The PRA dump uses the normal Praxis prelude; it is an inspection view of
the generated definitions and derivations, not a standalone serialized
proof bundle.

## Evaluation and trust

There is no separately handwritten executable Glivenko algorithm. The
evaluator executes the checked core bodies, after elaboration has recovered
implicit indices and certified erased proof arguments. It interns equal
constructor nodes and memoizes function calls. This avoids materializing
huge Gödel numbers or running course-of-values recursion up to those numbers.

The evaluator is currently an ordinary Haskell implementation, not a
PRA-certified interpreter or a verified compiler backend. Its results are
never accepted as proof evidence. The PRA certificates establish the
arithmetic program's correctness; the test suite separately checks the
evaluated classical and intuitionistic objects with an independent Hilbert
proof checker. Adequacy tests also compare the production evaluator with
the reference surface semantics and the symbolic generated-core semantics
on randomized inputs, including indexed constructors. These differential
tests check semantic preservation on samples; a universal formal proof for
this evaluator is future work. It does not change the kernel or metatheory.

Internal mode is a scoped surface notation for these indexed proof values.
Its declarations use the same membership and conclusion contracts as
ordinary functions, and their proof objects remain available for
metamathematical transformations. Leaving a block does not turn an object
proof of `A` into a native PRA proof of `A`. No kernel rule or stronger
metatheory is added.
