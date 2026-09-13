# Elaboration: from the surface language to the kernel

This document explains how a module of the surface language
([surface.md](surface.md)) becomes definitions and certified theorems of the
core ([kernel.md](kernel.md), [pra-and-prf.md](pra-and-prf.md)), and the
invariants that make the translation sound and fast. The code is in
`praxis/src/Language/Praxis/Surface/`.

## The trust architecture

The surface layer is an untrusted *producer*. It emits text in the concrete
syntax of praxis-core — `prf` equations for definitions and `pra`
declarations for lemmas and theorems — and hands it to the core's own parsers
and checker:

- definitions go through `PrimitiveRecursion.Environment.compileDefinitions`
  and `extendEnvironment`, which elaborate them to kernel programs and
  reject cycles, redefinitions and ill-formed recursion;
- every lemma and theorem goes through `Tactic.Quote.checkDecl` against the
  lemmas certified before it (`Check.certifyDecl`).

What must be trusted is therefore small:

1. the kernel and its certification of declarations;
2. **the translation of statements**: a surface theorem must mean what its
   core statement says (§ Statements), since the core certifies the latter;
3. the definitions of the prelude (`src-pra/prelude.prf`), which are ordinary
   primitive recursive definitions, and the membership predicates generated
   for data types, which appear in statements.

Everything else — the parser, the type checker, the encoder, the compiler,
the proof engine — can only cause a rejection when it is wrong. A declaration
which fails is reported and **never becomes a lemma**: later declarations are
checked without it (unlike the language server of `.pra` files, which keeps
failed declarations as lemmas for convenience). A theorem is not in scope in
its own proof.

## Names in the core

The surface names things the core syntax cannot spell (`Data.List.(<>)`,
`append-nil`), and the core parser reads a name the signature defines as that
symbol before any variable. `Mangle` therefore maps every surface name into a
namespace of its own: globals to `u_…`, variables to `v_…`, with an injective
escape (`_s` separates segments, `_d` is a dash, `_x<hex>_` any other
character). Nothing in praxis-core or the prelude starts with `u_` or `v_`, so
a surface variable called `at` or `add` is never taken for a symbol.
`demangle` turns core messages back into surface names.

`CoreText` builds that text from a small term type, parenthesising every
application, so the text means exactly the term whatever the core's fixities.
`praxis check --dump-core` prints it.

## The prelude

`src-pra/prelude.prf` extends `builtin` with:

```
hd 0 = 0            hd (S p) = godelPi1 p       -- stuck at once on a non-successor
tl 0 = 0            tl (S p) = godelPi2 p
drop 0 l = l        drop (S k) l = tl (drop k l)
at h k j = hd (drop (k - S j) h)                -- the value at j < k in the history of k
hist {F} 0 $[xs] = 0
hist {F} (S n) $[xs] = cons (F n (hist {F} n $[xs]) $[xs]) (hist {F} n $[xs])
cvrec {F} n $[xs] = F n (hist {F} n $[xs]) $[xs]
```

`src-pra/prelude.pra` proves, once, over abstract functions: `hdCons`,
`tlCons`, `dropTl`, `dropConsSucc`, `subSuccPos`, `cvrecUnfold` and above all

```
rule histAt (k h : var) (t j : term) (Γ : ctx) (f(k, h) : term)
  : j < t, Γ |- at (hist {f} t) t j = cvrec {f} j
```

`Surface.Prelude` embeds both files and certifies them at run time, over the
library of praxis-core.

## Data types

`data T p̄ = C₀ … | C₁ …` (`Encode`):

- **Codes.** Constructor `Cᵢ` with fields `x₁ … xₖ` is the prf definition
  `T.Cᵢ x₁ … xₖ = cons i (cons x₁ … (cons xₖ 0))`, a tagged finite sequence.
  Its tag is `hd c`, its field `j` is `hd (tl^(j+1) c)`.
- **Constructor lemmas**, certified at the declaration:
  `C.#def : |- C x̄ = cons i …` (by `refl`, over variables),
  `C.#tag : |- hd (C x̄) = i`, `C.#field-j : |- hd (tl^(j+1) (C x̄)) = x_j`,
  `C.#lt-j : |- x_j < C x̄` (from `ltConsL`, `ltConsR`, `ltTrans`).
- **Membership** `T.is n = cvrec {λ k h. dispatch} n`: the dispatch on the tag
  checks, in the branch of `Cᵢ`, that the code is *exactly* `Cᵢ` applied to its
  fields (no junk) and the membership of the fields of `T` itself (by the
  history, `at h k field`) and of data types encoded before. It is *shape*
  membership: fields of a type parameter, of `Nat` or of a later type are
  unconstrained.
- **`T.#is-def`, `T.#is-beta`** unfold the predicate at a variable, and
  `T.#collapse-i` collapses a dispatch at tag `i` over variables.
- **Inversion** `T.#inversion : 0 < T.is t |- ⋁ᵢ (t = Cᵢ (fields t) ∧
  memberships)`, proved by case analysis on the tag with `eqBool`,
  `collapseT/F`, `conjElim1/2`, `eqElim`, and `histAt` with `C.#lt-j` for the
  recursive fields.

Which fields contribute a membership conjunct is recorded
(`encodedMembers`) and is the single source both the inversion and the proof
engine read: they cannot disagree.

## Functions

`Compile` turns clauses into one prf definition. Functions are type-erased
PRFs on codes. The clauses must split one argument, the scrutinee, on each
constructor exactly once (nested patterns, several matched arguments and
overlap are refused for now). A split is `if hd c == 0 then b₀ else if hd c
== 1 then b₁ … else 0`; a code outside the type falls to `0`.

A function whose clauses call it is recursive on the scrutinee, and every
recursive call must pass a field of the matched constructor there and the
other arguments unchanged — primitive recursion with parameters, which the
compiler checks. It is then

```
f a₀ … = cvrec {λ k h ȳ. dispatch on k, recursive calls at h k field} a_c ȳ
```

**Unfolding lemmas.** Each clause is `f.unfold-C : |- f … (C x̄) … = body`
(and `f.eq_i`), an equation for *all* codes, since the dispatch reads only the
tag and the fields. Its generated proof is the chain

```
f … (C x̄) …  = cvrec {B} (C x̄) ȳ            by exact f.#def
             = dispatch[k := C x̄, …]         by exact f.#beta
             = dispatch[hd (C x̄) := i]       by cong C.#tag
             = branchᵢ                        by exact T.#collapse-i
             = … fields replaced by x_j       by cong C.#field-j   (each field)
             = … at H (C x̄) x_j := cvrec … x_j by cong Eⱼ  (Eⱼ from histAt, C.#lt-j)
             = body                           by cong f.#def       (each recursive call)
```

## The definitional-equality discipline

Measured while designing this: `refl` on `app (C x xs) m = <its unfolding>`
does not finish in minutes. Normalising a term in which a symbolic
constructor code sits under a projection or a history unrolls the μ-searches
of `lft`/`rgt` and the history once per successor layer, and the kernel
compares the exponentially shared residuals as trees. Hence two invariants:

1. **Projections are the prelude's `hd`/`tl`**, never the core's `lft`/`rgt`:
   `hd` is a case on its argument, so on a non-successor it is stuck at once
   and stays small.
2. **`Defeq` is only ever used on statements over variables** (`#def`,
   `#beta`, `#collapse-i`, `#is-def`, `#is-beta`), certified once, and
   instantiated at codes by `exact` and `cong`. `checkDecl` checks an appeal
   against the lemma's statement and does not re-normalise the instance.

With both, every generated lemma of the examples certifies in milliseconds.

## Statements

A theorem `{ā} → (x₁ : T₁) → … → A` (`Engine.proveTheorem`) becomes the core
sequent

```
0 < T₁.is x₁, …, H₁, …, Hₘ |- C
```

where `A = H₁ → … → Hₘ → C`: the values are free variables (the Π₁ reading
of a PRA theorem), each of a data type with its membership hypothesis (none
for `Nat`), and top-level implications become hypotheses. Type parameters are
erased. This is the trusted translation, and its soundness argument is simple:
shape membership is implied by the intended typing, so the core statement has
*weaker* hypotheses than the intended one — it is at least as strong, and
proving it proves what the user wrote. Propositions translate connective by
connective (`CoreText.propText`); bounded quantifiers become the core's
bounded quantifier atoms.

## Proofs

The engine translates a proof into one core tactic per declaration, plus
auxiliary theorems certified before it. Goals are tracked statically — the
hypotheses in the order the core numbers them `H1, H2, …`, the conclusion,
the variables by surface name with their core names and types, and the surface
names of hypotheses. User hypothesis names never reach the core.

**Structural induction** on `x : T`, from a tactic or from clauses:

1. Revert the hypotheses mentioning `x` into the goal: the motive `P(x)`.
2. For each constructor `C`, an auxiliary theorem
   `memberships of the fields, P(recursive fields) (the IHs), the other
   hypotheses |- P(C x̄)`, its fields free variables, proved by the user's
   case — named `thm.#case-L<line>C<col>-i`, unique by source position.
3. The theorem's own script:
   ```
   have C: (0 < imp (T.is x) [[P(x)]]) { exact cvInduction m x {
     have Q: (0 < T.is m ==> 0 < [[P(m)]]) { ImplR as M;
       have I: (…) { exact T.#inversion };  DisjL … per constructor {
         (ConjL: Km : m = C (fields m), memberships K…)
         (per recursive field: its lt, belowElim, impElim, reflect → the IH)
         have A: (P(C (fields m))) { exact case-i };  reify A as A1;
         calc (0 < [[P(m)]]) = (0 < [[P(C (fields m))]]) by cong Km = 1 by exact A1 } };
     exact impIntro } };
   have R: (0 < [[P(x)]]) { exact impElim on C Hmember };  reflect R as R1;  (ImplL for the reverted)
   ```
   The case is transported to `m` as an *atom*, the truth of the motive's
   code, which is what `cong` can rewrite whatever the shape of `P`.

**`rfl`** rewrites the sides by the unfolding lemmas, outermost first,
wherever a function meets a constructor, and closes with the core's
definitional equality only on what remains (functions applied to variables).
**`calc`** is the core's `calc`, each step's justification translated in the
step's goal. A recursive call in a proof term names the induction hypothesis
at its argument; a lemma name is `exact`, `cong e` is `cong`.

## Invariants, collected

1. Every name the surface hands to the core is mangled into `u_…`/`v_…`.
2. Projections of codes are `hd`/`tl`; `Defeq` is used on statements over
   variables only.
3. Membership predicates only ever weaken the hypotheses of a statement.
4. Unfolding lemmas hold for all codes.
5. The inversion lemma and the engine read the same record of which fields
   carry memberships.
6. Declarations are certified in order; a failure is never a lemma; a theorem
   is not in scope in its own proof.
7. The engine builds text, never proof terms: the core certifies it.
8. Auxiliary theorems have names unique by the source position of their
   induction.
