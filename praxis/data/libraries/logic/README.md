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
`P = ((p → q) → p) → p`, runs the verified transformation, and returns
`Result <output conclusion> <input proof size> <output proof size>`.
The conclusion is `¬¬P`. Sizes count nodes of the unfolded Hilbert proof;
runtime allocation statistics count shared nodes instead.
The supplied example has 35 classical proof nodes and 1,273 intuitionistic
proof nodes after translation.

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

Checking and evaluation are separate phases. The CLI checks the module on
each invocation; the full demo currently takes roughly half a minute to
certify on the development machine. This is checker cost, not the running
time of the transformation. The evaluator API accepts an already checked
module and can reuse it for different inputs, as an interactive frontend
would do. Improving certification of composed proof-producing functions
remains a performance task.

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

They are ordinary finite K/S/explosion/MP proofs. The authoring script
[`generate_templates.py`](tools/generate_templates.py) uses typed lambda
terms and bracket abstraction to generate these certificates and the
classical Peirce example. The script is untrusted: every generated
definition is checked by Praxis. It adds no axioms or inference rules.

The generator emits five named proofs and seven intermediate parts, grouping
MP steps and letting Praxis infer their intermediate formula indices.
It previously named every MP step, producing 86 declarations. The remaining
parts keep the two largest proofs within the current checker's
definitional-equality resources; inlining every step into one body does not
yet certify. This grouping preserves the actual Hilbert proof trees.

```sh
python3 praxis/data/libraries/logic/tools/generate_templates.py --check
```

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

The implementation needs indexed proof data, first-order primitive
recursion and their generated contracts. It does not need internal-mode
syntax, binders, generic theory presentations or GL staging. Those features
can later make the same proof more convenient to write.
