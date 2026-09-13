# The kernel: quantifier-free PRA in a sequent calculus

This document describes the trusted core of praxis, in `praxis-core`: the
terms, formulas and sequents of Primitive Recursive Arithmetic (PRA), the
inference rules, definitional equality, and the checker. Everything else —
the `prf` and `pra` languages, the tactic engine, the surface language — is
built on top of it and trusted only as far as the kernel re-checks it.

## Why PRA, and why this presentation

PRA is the arithmetic of finitism: quantifier-free statements about
primitive recursive functions, proved with induction on quantifier-free
formulas. praxis aims to be a *finitistic* prover whose trusted base is
small enough to be believed, and useful for mechanising relative
consistency proofs, whose meta-theory must itself be finitistic.

The kernel presents PRA as an intuitionistic sequent calculus (G3i, the
quantifier-free fragment) extended with cut, equality and the PRA axioms.
A free variable of a sequent is read universally: a theorem `Γ ⊢ C` with free
variables `x̄` is the Π₁ statement `∀x̄. Γ → C`.

## Terms

`Language.Praxis.PRA.Syntax.Term a` is a variable of type `a`, a numeral
`Lit n`, or a function applied to arguments: `App (Function n) (V n (Term a))`,
the argument vector's length fixed by the function's arity at the type level.

A `Function n` (`PrimitiveRecursion.Function`) is one of:

| constructor | meaning |
|---|---|
| `Primitive (PRFCode n)` | a bare code: `Zero`, `Succ`, `Proj i`, `Comp f gs`, `Rec b s` |
| `Defined (DefId n)` | a named definition, looked up in a `KernelEnv` |
| `Inline (Program n)` | residual code produced by partial evaluation or by instantiating a schema |
| `Abstract (DefId n)` | a function known by name only — the parameter of a derived rule — which never reduces |

`PRFCode` is the bare language of primitive recursion. `Rec b s` recurses on
its first argument: `Rec b s (0, x̄) = b x̄` and `Rec b s (y+1, x̄) = s (y, Rec b s (y, x̄), x̄)`.
A `Program` is the same with calls to named definitions and to abstract
functions. A `KernelEnv` maps definition names to programs; it is built
only by `extendKernelEnv`, which checks arities at every reference and
rejects every call cycle, so a named definition is primitive recursive by
construction.

**Invariant (canonical numerals).** A numeral has exactly one spelling:
`canonicalise` turns `Succ (Lit n)` into `Lit (n+1)` and `Zero` at any arity
into `Lit 0`, and `Eq`/`Hashable` on terms compare canonical forms. This is
*not* evaluation: `plus 2 3` is not `5` until definitional equality says so.

## Formulas and sequents

An atomic formula is an equation `s = t`. Formulas are built with `∧`, `∨`,
`→` and `⊥`; `¬A` is `A → ⊥`. There are no quantifiers in the kernel: a
bounded quantifier is a *term* (see [pra-and-prf.md](pra-and-prf.md)) whose
truth is an equation. A sequent is `Γ ⊢ C` with `Γ` a multiset of formulas.

Truth of a code — a term standing for a proposition — is `0 < c`, which
is itself the equation `lt 0 c = 1`.

## The rules

`Language.Praxis.PRA.Rule.G3i.allRules` is the single source of truth: each
rule is a `Rule` value in a small pattern language (`Rule.hs`), and Template
Haskell (`Rule/TH.hs`) generates from the list the `Proof` datatype, its
base functor `ProofF`, the enumeration of rule names and the checker. To
change the calculus, change that file; the order of the list fixes the order
of the generated constructors.

| rule | premises | conclusion | side condition |
|---|---|---|---|
| `Id` | — | `A, Γ ⊢ A` | `A` atomic |
| `ExFalso` | — | `⊥, Γ ⊢ A` | |
| `ConjL` | `A, B, Γ ⊢ C` | `A ∧ B, Γ ⊢ C` | |
| `ConjR` | `Γ ⊢ A`, `Γ ⊢ B` | `Γ ⊢ A ∧ B` | |
| `DisjL` | `A, Γ ⊢ C`, `B, Γ ⊢ C` | `A ∨ B, Γ ⊢ C` | |
| `DisjR1 A` | `Γ ⊢ B` | `Γ ⊢ A ∨ B` | names the disjunct *added*: it proves the right one |
| `DisjR2 A` | `Γ ⊢ B` | `Γ ⊢ B ∨ A` | proves the left one |
| `ImplL` | `A → B, Γ ⊢ A`, `B, Γ ⊢ C` | `A → B, Γ ⊢ C` | |
| `ImplR` | `A, Γ ⊢ B` | `Γ ⊢ A → B` | |
| `Defeq s t` | `s = t, Γ ⊢ C` | `Γ ⊢ C` | `s` and `t` definitionally equal |
| `Subst x t s P` | `t = s, P[t], P[s], Γ ⊢ C` | `t = s, P[t], Γ ⊢ C` | `P` an atomic template in `x` |
| `SuccNonZero` | — | `S t = 0, Γ ⊢ A` | |
| `SuccInj` | `S t = S s, t = s, Γ ⊢ A` | `S t = S s, Γ ⊢ A` | |
| `Ind x A t` | `Γ ⊢ A[0/x]`, `A, Γ ⊢ A[S x/x]` | `Γ ⊢ A[t/x]` | `x` not free in `t` nor in `Γ` |
| `Cut A` | `Γ ⊢ A`, `A, Γ ⊢ C` | `Γ ⊢ C` | |

`Cut` is primitive by design. It is admissible in pure G3i, but not
eliminable once `Ind` is present: a hypothesis about the induction term
enters the induction formula only as the antecedent of an implication, which
cut then discharges. The `induction` tactic relies on it.

## Definitional equality

`Language.Praxis.PRA.Equality.defEqIn` decides the side condition of
`Defeq`: syntactic equality first, else both sides are *partially
evaluated* and the results compared. Partial evaluation runs the ordinary
evaluator on terms: an application whose recursion argument is neither `0`
nor a successor is left as a residual term, so evaluation makes as much
progress as it can on open terms and stops.

**Soundness.** Equal normal forms denote equal numbers under every
assignment of the free variables. **Incompleteness.** No amount of
reduction proves `x + 1 = 1 + x`; that needs induction. **Budget.** Evaluation
is metered by `Fuel` (`defaultFuel` = 100 000 steps); running out can only make
the check fail, never succeed.

A caveat for code generators: fuel bounds steps, not term size. Residuals
share structure in memory but are compared as trees, so normalising a term
whose evaluation unrolls μ-searches or histories over a symbolic successor
can take unbounded time within the budget. The surface language therefore
never asks for `Defeq` on such terms (see [elaboration.md](elaboration.md)).

## Checking

`Proof.inferConclusionIn env p` infers the sequent a proof establishes, or
every reason it fails. Open proofs (`inferConclusionOpenIn`) have leaves
standing for assumed sequents: the premises of a derived rule.

Two transformations of proofs are admissible meta-theorems, implemented in
`Proof.Transform`:

- `substProof σ p` proves the instance `σ(Γ ⊢ C)`, renaming the variables a
  step binds (the eigenvariable of `Ind`, the placeholder of `Subst`) apart;
- `weakenProof Δ p` proves `Δ, Γ ⊢ C`.

They are what makes a certified lemma reusable: an appeal to a lemma is its
proof, instantiated and weakened.

## The trusted base

Trusted: `Rule/G3i.hs` and the generated checker; the evaluator of
`PRFCode`/`Program` and `Equality`; `extendKernelEnv`'s closure, arity and
acyclicity checks; `Proof.Transform`. Everything that *produces* proofs —
tactics, quasiquoters, the language server, the surface language — is
untrusted: its output is checked. The surface language produces statements
too, and the kernel certifies the core statement it is given; that this
statement means what the surface one says is argued in
[elaboration.md](elaboration.md), § Statements and their adequacy.

One point of the trust model deserves stating plainly. When a declaration is
certified by `checkDecl` (see [pra-and-prf.md](pra-and-prf.md)), an appeal to
a lemma is checked against the lemma's *statement*, instantiated; the
instantiated proof is not re-run. This rests on the admissibility of
substitution and weakening, which holds for the idealised calculus; a
re-check of an instantiated `Defeq` could fail on fuel, but never succeed
wrongly. The eigenvariable conditions of such appeals are checked by the
tactic engine (`useLemma`); a producer that bypasses the engine and builds
appeal steps by hand must not be trusted with them.
