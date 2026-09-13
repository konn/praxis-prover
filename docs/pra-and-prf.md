# The core languages: `prf` definitions and `pra` proofs

praxis-core has two concrete languages over the kernel of
[kernel.md](kernel.md): `prf`, in which primitive recursive functions are
*defined* by equations, and `pra`, in which theorems and derived rules are
*stated* as sequents and *proved* by a small tactic language. Both are
untrusted front ends: `prf` produces kernel definitions, which the kernel
environment checks for closure and acyclicity; `pra` produces proofs, which
the kernel checker checks.

## `prf`: functions by equations

```
environment builtin

add n 0 = n
add n (S m) = S (add n m)

mu {P} 0 $[xs] = 0
mu {P} (S n) $[xs] = if mu {P} n $[xs] < n then mu {P} n $[xs] else if P n $[xs] then n else S n
```

`PrimitiveRecursion.Elaboration.*` compiles a family of equations:

1. **Parsing** (`Elaboration.Parser`): applicative terms, infix operators
   resolved to symbols by name (`+` is `add`, `<` is `lt`, `==` is `eq`, …),
   `if … then … else` (`ifte`), layout or `;`-separated equations. Binders —
   lambdas `λ x y. e`, bounded search `μ i < b. e`, bounded quantifiers over
   codes `∀ i < b. e`, `∃ i < b. e` — are **locally nameless**
   (`BoundET depth position`, names kept as `IrrelevantName` hints, equal to
   one another).
2. **Variadic expansion** (`Elaboration.Variadic`): a schema with a variadic
   group `$[xs]` is a template, instantiated on demand at each arity it is
   applied at.
3. **Renaming and case trees** (`Rename`, `CaseTree`): patterns are
   variables, `0`, `S p`; clauses must be exhaustive and disjoint.
4. **Recursion reconstruction** (`Compile`): a self-recursive function must
   recurse on one argument, on its predecessor, with the other arguments
   unchanged; it becomes `Rec`. Other cycles are rejected.

A **schema** `f {P, Q} x̄` takes function parameters, each of the arity of
its first application in the clauses, and is applied as `f {p} {q} t̄`, a
symbol or a closed λ in each place; its instance is the code with them
substituted. A schema uses each of its parameters, and recurs with them
unchanged and in order. An instance at primitive recursive functions is
then a primitive recursive definition: schemas abbreviate families of
definitions and add nothing to PRA. A recursion changing a function
parameter, `iter {F} (S n) x = iter {λ y. F (F y)} n x`, is recursion of a
higher type, which defines Ackermann's function, and is refused. A
**variadic schema** takes one parameter and also passes extra arguments
through to it, which is how a closure captures variables: a λ must be
closed, and μ, ∀ and ∃ capture the maximal subterms of their body not
mentioning the bound variable (canonical closure conversion), so that
substituting into a captured term yields the same code again.

`Signature` (`PRA.Signature`) names the results: plain symbols (with the
Haskell binding their code lives in, for splicing, and the equations they were
defined by), schemas and variadic schemas, and the checked `KernelEnv`.
`builtin` (`PrimitiveRecursion`) is the arithmetic library: `add`, `mul`,
`sub` (monus), `prd`, `sgn`, `lt`, `le`, `eq`, `ifte`, `triangle`, the Cantor
pairing `pair` and `cons x y = S (pair x y)` with projections `lft`, `rgt`,
the schemas `mu` and `holdsBelow`, and the connectives on codes `conj`,
`disj`, `imp`.

**Unfolding lemmas.** Each clause of a definition is a lemma,
`add_0 : |- n + 0 = n`, `add_S : …` (`Tactic.Unfolding`). They are *not*
trusted: each is proved by `Defeq` and checked by the kernel.

## `pra`: statements and tactics

```
theorem zeroAdd : |- 0 + t = t
by induction t as n { refl } { calc 0 + S n = S (0 + n) = S n by cong H1 }

rule cvInduction (n : var) (t : term) (Γ : ctx) (p(n) : term)
  (step : holdsBelow {p} n = 1, Γ |- 0 < p(n))
  : Γ |- 0 < p(t)
  where n ∉ Γ, t
by …
```

A **theorem** is a sequent with free variables. A **rule** is schematic:
it binds metavariables of sorts `var`, `term`, `atom`, `formula` and `ctx`
(a formula or term metavariable may take `var` parameters, `P(n)`; a term one
with parameters is an *abstract function* `p(n)` and may stand as a schema
parameter, `holdsBelow {p} n`, in any of a schema's places, `mix {f} {g} n
x`), premises (named sequents, usable only at
exactly their stated shape), and eigenvariable conditions `where n ∉ Γ, t`.

**Tactics** (`Tactic.hs`, grammar in `Tactic/Parser.hs`) are deliberately
few. The primitive ones are the rule labels, applied backwards, with
arguments inferred from the goal when omitted. The derived ones are `refl`,
`symmetry`, `rewrite … in …`, `cong` (close `u = v` by a hypothesis or an
equational lemma under a context found by comparing the sides), `calc`,
`have`, `induction` (generalises hypotheses mentioning the term through
`Cut`), `assumption`, `exact` (a premise, a hypothesis, or a lemma),
`reflect`/`reify` (below), `skip`, `sorry`, and the combinators `;`, `|`,
`try`, `repeat`, `t { … } { … }`. Hypotheses are named `H1, H2, …` by the
engine, or as `as` says; `on` selects principal formulas.

**Lemma appeals.** `exact name` instantiates a certified `Lemma`
(statement, metavariables, premises, bound variables) to the goal by
matching; abstract functions are inferred by abstracting the goal. A lemma
with free object variables but no metavariables or premises is instantiated
by substitution; one with both is refused (`NotClosed`), and a rule's `var`
metavariables bound as eigenvariables must be instantiated apart from the
goal (`NotEigen`).

**Certification.** `Tactic.Quote.checkDecl env lemmas decl` runs a
declaration's tactic, and certifies the resulting partial proof against the
kernel (`certify`): rule steps by the kernel's checker, lemma appeals by
instantiating the lemma's statement. The engine is thus not trusted with
rule applications; see [kernel.md](kernel.md) for what it *is* trusted with
(eigenvariable conditions of appeals).

## Reflection and bounded quantifiers

`PRA.Reflection` maps formulas to their codes: `⟦s = t⟧ = s == t`,
`⟦A ∧ B⟧ = conj ⟦A⟧ ⟦B⟧`, `⟦A → B⟧ = imp ⟦A⟧ ⟦B⟧`, `⟦⊥⟧ = 0`, a comparison
`x < y` stands for itself, and anything else `c` is read as `0 < c`.
`decode ⟦A⟧ = A` for formulas without metavariables. The tactic `reflect`
turns the truth of a code into the formula it codes, `reify` the other way,
both by appealing to the reflection lemmas of the library. `⟦A⟧` may be
written in terms as `[[A]]`.

A bounded quantifier is an atom: `∀ i < t. A` is `holdsBelow {λ i ȳ. ⟦A⟧} t s̄ = 1`
and `∃ i < t. A` is `mu {λ i ȳ. ⟦A⟧} t s̄ < t`, the λ closed over the captured
subterms `s̄`. Course-of-values induction, `cvInduction`, is a derived rule
over an abstract function, proved once from `Ind`.

## Libraries and tooling

- `src-pra/lemmas.pra` is the lemma library: order and arithmetic,
  booleans and `eq`, the reflection lemmas, `holdsBelow` and `mu`, pairing
  (`lftCons`, `rgtCons`, `ltConsL`, `ltConsR`, `pairInjL`, …). `PRA.Library`
  embeds its text with Template Haskell and certifies it at run time
  (`certifiedLibrary`, `libraryScope`); splicing it as Haskell bindings would
  take the compiler very long.
- The quasiquoters `[prf| … |]` and `[pra| … |]` (`PrimitiveRecursion.Quote`,
  `Tactic.Quote`) check at compile time and splice definitions and proofs.
- `praxis-lsp` serves `.pra` and `.prf` files: diagnostics from the same
  checkers, hover by re-running a proof with `sorry` injected at the cursor.
