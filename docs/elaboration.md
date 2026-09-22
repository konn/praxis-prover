# Elaboration: from the surface language to the kernel

This document explains how a module of the surface language
([surface.md](surface.md)) becomes definitions and certified theorems of the
core ([kernel.md](kernel.md), [pra-and-prf.md](pra-and-prf.md)), why a
certified theorem means what the user wrote, and the invariants that keep
the translation sound and fast. The code is in
`praxis/src/Language/Praxis/Surface/`.

## The trust architecture

The surface layer produces proofs and statements. It emits text in the concrete
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
2. **the translation of statements** (`Engine.statementGoal`, with
   `CoreText.termCT` and `CoreText.propText`): the kernel certifies a core
   statement, so the core statement must mean what the surface statement
   says. Its adequacy is argued once, in § Statements and their adequacy,
   from facts about the generated definitions which the kernel certifies;
   that argument is the one piece of trusted reasoning, and differential
   tests check the implementation against it.

The definitions themselves — the prelude's, the codes of constructors, the
membership predicates, the compiled functions — are not trusted: adding a
primitive recursive definition is always sound, and what the argument needs
of them is certified. Generated proofs are checked independently of the
surface proof engine. The parser, elaborator and statement translation also
determine which proposition is submitted; their correctness is part of the
source-to-core adequacy obligation, not established by checking that core
proposition's proof. A declaration which fails is reported and **never becomes a
lemma**: later declarations are checked without it (unlike the language
server of `.pra` files, which keeps failed declarations as lemmas for
convenience). A theorem is not in scope in its own proof.

What no machine checks is the reading of the source: that the parser, the
fixities and the resolution of names give a statement the meaning its author
intended. Every proof assistant shares this last step; `praxis check
--dump-core` prints each core statement that was certified, for inspection.

## Names in the core

The surface names things the core syntax cannot spell (`Data.List.(<>)`,
`append-nil`), and the core parser reads a name the signature defines as that
symbol before any variable. `Mangle` therefore maps every surface name into a
namespace of its own: globals to `u_…`, variables to `v_…`, with an injective
escape (`_s` separates segments, `_d` is a dash, `_x<hex>_` any other
character). Nothing in praxis-core or the prelude starts with `u_` or `v_`, so
a surface variable called `at` or `add` is never taken for a symbol.
`demangle` turns core messages back into surface names.

A global's qualified name starts with the library its module belongs to,
when it belongs to one, `lists/Data.List.foo` as the tables render it, so
that two libraries exposing modules of one name are two families of globals,
`u_lists_sData_sList_sfoo` and `u_other_sData_sList_sfoo` in the core. The
renamer ("Rename", [packages.md](packages.md) § Names) writes every
reference in that canonical form before elaboration, which looks names up
in one table without any scope.

The value binders of a theorem must have distinct names. Elaboration rejects
duplicates, and statement translation checks this invariant again: merging
two values into one core variable would conjoin their membership predicates
on the same code and could turn an inhabited surface context into an
impossible numeric context. Induction uses a fresh eigenvariable apart from
the values already in scope.

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
- **Membership** `T.is {p̄} n = cvrec {λ k h. dispatch} n`, over the
  predicates `p̄` of the type's parameters its fields use. In the branch of
  `Cᵢ` the dispatch on the tag checks that the code is *exactly* `Cᵢ` applied
  to its fields (no junk). It also checks the fields:
  - a field of a parameter satisfies the parameter's predicate, `pᵢ field`;
  - a field of `T` itself is a member, through the history, `at h k field`;
  - a field of a data type encoded before is a member of it at the
    predicates of its arguments, `U.is {λ y. V.is {p} y} field`;
  - in a data type in the GADT style, each index of an entry of an indexed
    type is the one the constructor's signature gives it,
    `eq (U.#idx-j entry) index` (see Indexed data types below).

  Fields of `Nat`, of a higher-kinded parameter, of a later type, or of `T` at
  other arguments are unconstrained. When the predicate takes parameters,
  the lemmas below are rules over them.
- **`T.#is-def`, `T.#is-beta`** unfold the predicate at a variable, and
  `T.#collapse-i` collapses a dispatch at tag `i` over variables.
- **Introduction** `C.#intro : 0 < U₁.is x_{j₁}, …, U.#idx-j e = i, … |- 0 < T.is (C x̄)`,
  a hypothesis for each field whose membership the branch of `C` checks and
  one for each equation of indices it checks: the predicate unfolds at the
  code (`#is-def`, `#is-beta`), the tag selects the branch (`C.#tag`,
  `T.#collapse-i`), the shape conjunct is `eqRefl` once the fields are
  rewritten to the variables (`C.#field-j`), the conjunct of a field of `T`
  itself is its hypothesis through the history (`histAt` with `C.#lt-j`), an
  equation's conjunct is its hypothesis by `eqIntro` once the fields are
  rewritten, and `conjIntro` joins them. By induction on a value, the code of
  every value of `T` is a member — premise (M) of § Adequacy.
- **Inversion** `T.#inversion : 0 < T.is t |- ⋁ᵢ (t = Cᵢ (fields t) ∧
  memberships ∧ equations of indices)`, proved by case analysis on the tag
  with `eqBool`, `collapseT/F`, `conjElim1/2`, `eqElim`, and `histAt` with
  `C.#lt-j` for the recursive fields. Induction rests on it.

Which fields contribute a membership conjunct, and by which predicate, is
recorded (`encodedMembers`, a `FieldPred` over the type's parameters), and
so are the equations of indices each constructor's branch checks
(`encodedIndexEquations`, over the positions of its code). They are the
single source both the inversion and the proof engine read: they cannot
disagree.

**Predicates capturing terms.** A membership predicate of one parameter is a
variadic template, `T.is {p0} n $[ys]`, when two conditions hold: some field
is of the parameter, and every other field passes the parameter's predicate
on only to a variadic predicate of one parameter in turn. The parameter may
then be any predicate on the element's code: a closure over the terms it
captures, in the canonical form the core abstracts a term to
(`CoreText.predicateOver`). The elements below `b` are `{λ x y_1. lt x y_1}`
capturing `b`, and the lists of them are `List.is {λ x y_1. lt x y_1} xs b`,
the captured terms after the arguments. The template passes them to its
step, `cvrec {λ k h. … p0 field $[ys] …} n`, whose λ the core closes over
them. With nothing captured it is the plain predicate. So its lemmas, rules
over the parameter, hold at every closure: the kernel instantiates them at
the closure's code and appends what it captures. A predicate of several
parameters stays a plain schema, since the kernel's variadic schemas take
one parameter.

**Indexed data types.** A data type in the GADT style is encoded as the data
type its indices erased: its constructors' codes store their fields and the
implicit arguments no field determines. An implicit argument which is an
index of a field's type — `n` of `(:-) : {n : nat} -> a -> Vec a n -> Vec a (S n)`,
the index of its tail — is not stored. For each index the declaration
generates an index function, `Vec.#idx` (`T.#idx-j` for several), a function
by clauses as any other: at each constructor the index of its result, its
fields and its stored arguments as they are, the arguments not stored
recovered by the index functions of the fields' types:
`Vec.#idx (x :- xs) = S (Vec.#idx xs)`. So each value has exactly one index,
a primitive recursive function of its code — which keeps induction on a
value of an indexed type the core's induction on one variable, whatever the
indices of the value's fields.

Its membership predicate is the erased type's, and it checks indices too
(`Encode.ctorIndexEquations`): a constructor makes a value of its type only of
entries at the indices its signature gives them. For each entry of the
constructor's telescope of an indexed type `U`, and each index of `U`, the
branch of the constructor has the conjunct `eq (U.#idx-j e) i`: `e` the entry
— the field at its position, or an implicit argument not stored, the index it
is recovered by — and `i` the index the entry's type states, over the entries
likewise. An equation which recovery makes so is left out: `Vec` checks none,
its tail's index being the `n` recovered from it, but
`Detach : {b : Fm} -> Pf (Imp Top b) -> Pf b` checks `Pf.#idx p = Imp Top b`
of its premise `p`. So `Pf c` stands for the codes of the derivations of `c`,
not of every code whose last step claims `c`. Since the predicate calls the
index functions, these are defined after the codes of the constructors,
whose lemmas their unfolding lemmas need, and before the predicate; their
closure lemmas, which need the predicate, come after it (`Check`). An index of
a type encoded later is not checked, as a field of such a type is no member.

The inversion gives the equations as hypotheses of each case of an induction,
which the engine uses as it does the indices a theorem states of its binders:
to prove the indices an appeal needs, and to rewrite by where a hypothesis or
the induction hypothesis proves the goal once unfolded
(`Engine.bridgeChain`). Where a constructor is introduced, the engine proves
the equations its introduction takes as it proves the indices of an
application's arguments (`Engine.indexEquation`).

The head is a telescope: the type of an index may mention the type
parameters and the indices before it, `(l : Vec a n)`. An implicit parameter
of the head, `{n}`, is a type parameter or an index like any other, in the
types and in the codes; only a use of the type does not write it, and it is
found by matching the kind of each index written against the index's type,
one-sided, as an application's implicit arguments are. An index function's
result is of its index's type erased, `SameVec.#idx-2 : SameVec a → Vec a`,
the indices of that type being other index functions' results.

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
tag and the fields. Its sides are the clause's patterns and body translated
by `termCT`, as a statement is — premise (U) of § Adequacy. Its generated
proof is the chain

```
f … (C x̄) …  = cvrec {B} (C x̄) ȳ            by exact f.#def
             = dispatch[k := C x̄, …]         by exact f.#beta
             = dispatch[hd (C x̄) := i]       by cong C.#tag
             = branchᵢ                        by exact T.#collapse-i
             = … fields replaced by x_j       by cong C.#field-j   (each field)
             = … at H (C x̄) x_j := cvrec … x_j by cong Eⱼ  (Eⱼ from histAt, C.#lt-j)
             = body                           by cong f.#def       (each recursive call)
```

**Closure lemmas.** A function whose result is of a data type or of a type
parameter has `f.#closed : 0 < A₁.is {p̄} x₁, … |- 0 < T.is {p̄} (f x̄)`, a
hypothesis for each argument with a predicate. It is a rule over the
predicates of the function's type parameters: its results are members. The
engine proves it (`Engine.proveClosure`) by induction on the argument the
clauses match on, each case the membership of the clause's body once
`f.unfold-C` rewrites the application. That membership is a hypothesis, the
induction hypothesis at a recursive call, `C.#intro` at a constructor, or
`g.#closed` at another function, each after the memberships of what it is
applied to (`Engine.membershipProof`). Under constraints with laws, the
closures of the dictionary's methods are premises, and an appeal discharges
them as it does a theorem's. A body whose membership is not established that
way leaves the function without a closure lemma.

**Specifications.** The closure lemma is one specification (`Engine.Spec`)
among others, all proved by one generator (`Engine.proveSpec`). A
specification states a postcondition at the application under the
memberships of the arguments and preconditions over them. The generator
proves it by induction on the argument the clauses match on, or outright,
and hands each case to the specification's own prover, with the
implications of its conclusion introduced. The closure lemma's
postcondition is the membership of the result, and its prover resolves the
membership of the body (`Engine.membershipCase`). An equational
postcondition is proved by unfolding both sides and closing by `refl`, or
by congruence from a hypothesis such as the induction hypothesis
(`Engine.equationCase`). `Check.checkSourceWith` proves the specifications
given of each function after its closure lemma, and certifies each as
`f.#name`.

Clauses matching on several values of `Nat` at once are proved by
course-of-values induction on the code of their tuple, `pair x₀ (pair x₁ …)`
(`Engine.tupleInduction`). Every code is such a pair (`pairSurj`), so the
motive needs no guard: the goal at the components of the code, `godelPi1 n`,
…, with the hypotheses mentioning the values reverted into it. In the step
each component is `0` or a successor (`zeroOrSucc`), and each combination is a
case, an auxiliary theorem, with an induction hypothesis at each tuple the
case's unfolding lemma recurses to: that tuple's code is below the case's
(`pairLtL`, `pairLtR`), and `belowElim` looks it up. The core codes `0 < u` as
`u`, so the code of the motive at a tuple with `0` in it is not the instance
of its code: two helper lemmas, stated at variables and instantiated at each
case, pass between the motive and its code. An induction hypothesis under
preconditions is specialized where these are established — by a hypothesis,
an obligation, or a hypothesis once unfolded — and its conjuncts are taken
apart (`Engine.specializeIHs`), for the case's prover.

**Indices.** A function whose signature's types have indices gets from them
(`Engine.indexSpecOf`) the equations its arguments' indices satisfy — each an
index function at an argument, and an index over the function's value
parameters — and those of its result. A value parameter which is, bare, the
first index of an argument is eliminated, that index standing for it. Its
closure lemma takes the arguments' equations as hypotheses, and a case whose
hypotheses clash is refuted (`Engine.refute`): the equations are unfolded, a
successor against a successor taken apart by `SuccInj`, and zero against a
successor closed by `SuccNonZero`. That is how an omitted clause is
justified. When its result has indices, its lemma `f.#index` states them
(`Engine.indexSpec`), each case refuted or proved by `Engine.indexCase`: both
sides unfolded, and what is left an equation at hand, a rewriting by one, or
the index another function's `#index` gives its application, the indices its
arguments must have found the same way and matched against those it asks.
The resolver finds the indices of the arguments so where a closure lemma with
such hypotheses is appealed to. A failure of either lemma refuses the
function.

**Matching and coverage.** The elaborator (`Elab.elabPattern`) unifies the
indices of a constructor's result with those expected, the signature's value
parameters and the constructor's implicit arguments the variables to solve
(`Index.unifyIx`): a clash refuses the clause, and so does an index a function
computes, which unification cannot see into. A constructor the clauses omit
must clash there; `FunDef.fdImpossible` records it, and `Compile` gives its
branch of the dispatch `0`, and it no unfolding lemma. An absurd pattern,
`()`, is checked alike: every constructor must clash there. Its clause has
no right side and is the only one, so the function compiles to the constant
`0`, never reached, while its lemmas, and a theorem, split on that argument
and refute every case. None of this is trusted: the closure and index lemmas
certify what the elaborator concluded.

## The definitional-equality discipline

Measured while designing this: `refl` on `app (C x xs) m = <its unfolding>`
did not finish in minutes. Normalising a term in which a symbolic
constructor code sits under a projection or a history unrolls the μ-searches
of `lft`/`rgt` and the history once per successor layer, and the kernel then
compared the exponentially shared residuals as trees. It now interns them,
at a cost linear in the DAGs, which took the lemmas of a function matching on
two values of `Nat` from seconds to milliseconds; the unrolling itself
remains. Hence two invariants:

1. **Projections are the prelude's `hd`/`tl`**, never the core's `lft`/`rgt`:
   `hd` is a case on its argument, so on a non-successor it is stuck at once
   and stays small.
2. **`Defeq` is only ever used on statements over variables** (`#def`,
   `#beta`, `#collapse-i`, `#is-def`, `#is-beta`), certified once, and
   instantiated at codes by `exact` and `cong`. `checkDecl` checks an appeal
   against the lemma's statement and does not re-normalise the instance.

With both, every generated lemma of the examples certifies in milliseconds.

## Statements and their adequacy

### The translation

Proof arguments may be erased only after their obligations are collected for
certification. Function bodies, including instance methods, retain these
obligations. Theorem applications and calculations include each supplied
proof as a premise of a core `Cut`, so it is checked even when computation
erases the argument. Statements currently reject proof arguments because
statement elaboration does not yet support certifying their obligations. In
particular, `absurd rfl` cannot become a numeral in a theorem's statement.

A theorem `{ā} → (x₁ : T₁) → … → A` becomes, by `Engine.statementGoal`, the
core sequent

```
0 < T₁.is {p̄₁} x₁, …, H₁, …, Hₘ |- C
```

where `A = H₁ → … → Hₘ → C`, and top-level implications become hypotheses.
The values are free variables (the Π₁ reading of a PRA theorem), each with
the membership hypothesis of its type's predicate. A data type's predicate
is at the predicates of its arguments, `0 < List.is {w_1} xs`. A type
parameter's is its own, `0 < w_1 x`. A value of `Nat` has none: its
predicate, the prelude's `anyIs n = 1`, holds of every code. A type
parameter's predicate is a parameter of the theorem's rule, so a theorem over
a type parameter is a rule over its predicate. An appeal instantiates it at
the predicate of the type the parameter stands for. Type parameters are
otherwise erased. Propositions translate connective by
connective (`CoreText.propText`):

| surface | core |
|---|---|
| `s ≡ t`, `s ≠ t` | `s = t`, `~ (s = t)` |
| `s < t`, `s ≤ t` | `lt s t = 1`, `le s t = 1` |
| `s > t`, `s ≥ t` | `lt t s = 1`, `le t s = 1` |
| `A ∧ B`, `A ∨ B`, `A → B`, `¬ A` | `A /\ B`, `A \/ B`, `A ==> B`, `~ A` |
| `A ↔ B` | `(A ==> B) /\ (B ==> A)` |
| `⊤`, `⊥` | `0 = 0`, `_|_` |
| `∀ i < t, A`, `∀ i ≤ t, A` (and `∃`) | `∀ i < t. A`, `∀ i < S t. A` |

and terms by `CoreText.termCT`: a variable, a numeral, a constructor or a
function applied to its arguments, and `S`, `+`, `-`, `*`, `^` as the
builtins `S`, `add`, `sub`, `mul`, `pow`. The sides of `≡` and `≠` are of one
type up to its indices, which the encoding erases: codes are compared, and
(I) is of the erased type.

A binder of an indexed type, `x : T τ̄ ī`, has besides its membership the
equation of each index, `T.#idx x = i` (`T.#idx-j x = iⱼ` for several), the
index a term. The theorem's value parameters, the variables its binders'
indices mention, are free variables as its binders are, with the
memberships of their types; but one which is the whole index of a binder is
replaced by that binder's index, `T.#idx x`, and has no equation. So
`(v : Vec a n) → length v ≡ n` becomes `0 < Vec.is {w_1} v |- length v =
Vec.#idx v`, whose induction is on `v` alone, while `(v : Vec a (S n)) → …`
keeps `n`, and the hypothesis `Vec.#idx v = S n`. Induction introduces the
equations of indices it reverts in each case, and a case whose equations
clash, once unfolded, is refuted; an appeal proves the equations the
theorem's hypotheses need of its arguments, as an application of a function
does its index premises.

### First-order values

The encoding gives a meaning to values of first-order types only: `Nat`,
data types applied to first-order types, and type parameters. The elaborator
keeps every value first-order — a field of a data type, a value a theorem
quantifies over, and a function's arguments and result have types without
arrows, and every function and constructor is applied to all its arguments
(`Types.firstOrder`, `Elab.checkTerm`). So no term of a statement denotes a
function, and a type parameter only ever stands for a first-order type.
`statementGoal` checks the values once more: the translation refuses what it
could not give a meaning to.

### What a statement means

- A data type denotes the finite trees its constructors build, at
  first-order types for its parameters; `Nat` denotes ℕ.
- A function denotes the unique function on those trees satisfying its
  clauses — structural recursion has exactly one solution. The arithmetic of
  `Nat` is the usual one, subtraction truncated.
- A theorem `(x̄ : T̄) → H₁ → … → Hₘ → C` means: for every assignment ρ of
  values to x̄, if every `Hᵢ` holds then `C` does.

The **encoding** of a value is `e(n) = n` on `Nat` and
`e(Cᵢ v₁ … vₖ) = cons i (cons e(v₁) … (cons e(vₖ) 0))`. It is the same at every
instance of the type parameters: nothing in the translation depends on a
type.

### Adequacy

**Theorem.** If the kernel certifies the core sequent of a theorem, the
theorem holds.

It rests on three premises about the generated definitions, each certified
per declaration:

- **(U)** each function `f̂` satisfies each of its clauses at all codes: the
  unfolding lemmas `f.unfold-C`;
- **(I)** codes are injective with distinct tags: `C.#tag` gives a code's
  tag, `C.#field-j` each field;
- **(M)** the code of every value of `T τ̄` is a member by `T.is` at the
  predicates of `τ̄`: `C.#intro`, by induction on the value.

The proof is three inductions over finite objects.

1. *Terms.* For a term `t` and an assignment ρ, `⟦tr t⟧(e∘ρ) = e(⟦t⟧ρ)`. By
   induction on `t`, and at an application of a function by induction on the
   order of definitions and on the value of its scrutinee: `f̂∘e` and `e∘f`
   satisfy the same clauses — the first by (U) — and structural recursion has
   one solution.
2. *Propositions.* `⟦tr A⟧(e∘ρ) ⇔ ⟦A⟧ρ`. By induction on `A`: `≡` and `≠` by
   (I), since `e` is injective at each type; comparisons and bounded
   quantifiers range over ℕ on both sides; the connectives are the same. It
   is an equivalence, so it holds under `¬` and `→` at any depth.
3. *The sequent.* The kernel's soundness gives the numeric instance at `e∘ρ`,
   the rule's predicates at those of the types its type parameters stand
   for. Its membership hypotheses hold there by (M), its equations of
   indices by (M) and (U) as below, its other hypotheses by 2 exactly when
   the surface ones do. So its conclusion holds, and by 2 the surface
   conclusion.

For a binder of an indexed type, (M) says more: the code of every value of
`T τ̄ ī` has the indices `ī` by the index functions, since these satisfy
their clauses (U), each the index of a constructor's result at the indices
its entries have. This and membership are proved together, by one induction
on the value: the entries of a value `C v̄` are of the types the signature of
`C` gives them, so by the induction hypothesis they have the indices those
types state — the equations of indices `C.#intro` takes — and the code of
`C v̄` is a member, with the indices of the result of `C`. So the equations of
indices hold at `e∘ρ`. A value parameter replaced by the index of its binder
quantifies over nothing less: every value has exactly one index, so a
statement for all values and all the indices they have is one for each value
at its own.

Each step is an induction on syntax or on finite trees, and a free-variable
theorem is read as its numeric instances: the argument is finitary, the kind
of reasoning Hilbert's metamathematics allows. It could be formalised in PRA
module by module, but not uniformly — surface functions reach every
primitive recursive function, and no primitive recursive function evaluates
them all, so a uniform statement would need evaluators indexed by fuel — and
nothing would be gained: a formal proof would rest on a semantics written
down by hand, as this one does.

Membership checks the fields of a type parameter by the parameter's
predicate, and, at an indexed type, the indices of the constructors'
entries. It does not check the fields of a higher-kinded parameter, of
`Nat`, of a later type, or of the type itself at other arguments, nor the
indices of a later type, so it may be wider than the codes of a type. It
appears only as a hypothesis on a theorem's values, where a wider predicate
gives the core statement more instances, not fewer: sound, and incomplete
where a statement needs the finer typing.

### Testing the translation

The argument is proved once; its implementation is tested.
`praxis/test/Language/Praxis/Surface/AdequacyTest.hs` runs two interpreters
on random values. One is a reference semantics of the elaborated surface
syntax: trees, functions run by their clauses, no codes. The other evaluates
the core text generated — the statement `Engine.theoremStatement` produces,
and the sides of the unfolding lemmas — as the certified lemmas describe its
symbols: constructors as free symbols (I), functions by their unfolding
lemmas (U), membership by a code's constructor, its fields and the equations
of indices of its entries (M and the inversion), and the builtins by the
kernel's own evaluator. It checks lemma 1
for every function, and lemma 2 and the membership hypotheses for every
statement of `test/data/adequacy.px` — statements true and false, over every
relation, connective and bounded quantifier — and of `list.px`, `gadt.px`
and `nat.px`: indexed types and their index functions, constructors with
named fields their indices mention, value parameters, implicit values taken
at runtime, proofs as arguments, and functions matching on values of `Nat`. A value of an indexed type is generated well typed at its
indices, entry by entry of a telescope — a statement's value parameters then
its values, a function's value parameters then its arguments, a
constructor's implicit arguments then its fields, at entries its
preconditions hold of — and an entry which is, bare, an index of a later
one's type is taken from that one. So a function
omitting a constructor impossible at its indices is applied only where it is
defined, and each equation of indices of a statement is checked to hold of
the codes of its values, as its memberships are: (M) for indices. The core side
evaluates symbolically because numerals are out of reach: the membership of
a code unrolls a history one level for every number below the code.

Generator exhaustion is a test failure, not a proof of emptiness. Deliberately
empty domains are recognized by constructor-index disjointness or an
explicitly empty type-parameter predicate. Equality preconditions can supply
unfixed natural-number witnesses when no field type depends on the entry;
all preconditions are still checked after generation.

Parameter predicates are also instantiated at concrete finite sets of
numerals, constructor values, nested containers and the empty set. The core
reference evaluator follows these arguments through membership predicates.
Negative examples evaluate translated membership premises on explicit
nonmembers, including nonmembers nested inside containers, to detect lost
constraints.

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

A hypothesis whose equation is not the goal's, but reduces to the same
equation, proves it by a `calc` (`Engine.hypothesisBridge`): the goal's left
side rewritten down to its normal form, the hypothesis's left side up from
it, the hypothesis, its right side down, and the goal's right side up, each
step an unfolding lemma. Ahead of the definitions' unfolding lemmas, the
engine rewrites by two equations of the library, from left to right:
`succSubSucc`, `S m - S n = m - n`, and `zeroMinus`, `0 - n = 0`
(`Prelude.preludeUnfoldings`), which is what the arithmetic of a comparison
needs, `lt (S n) (S m)` being `lt n m`.

A name no declaration of the module has, which names a lemma the core has
certified — of the library or of the prelude, whose names are not mangled —
is cited as it is, `exact ltTrans on H1 H2`, the hypotheses it is applied to
given in order (`Knowledge.knowLibrary`). A lemma whose conclusion at its
arguments mentions the index an index function gives a function's result is
appealed to as a hypothesis, `IxH`, when rewriting those indices by the
function's index specification (`indexOf`, a conjunct of it for a type of
several indices) makes it the goal; a calculation takes the goal's sides to
its (`Engine.indexedAppeal`). The conclusion is the theorem's proposition at
its arguments and at the value parameters they give (`TheoremInfo.thmProp`).

A lemma applied to arguments, `app-nil (rev xs)`, is appealed to the same
way, and the core finds its instance. Before the appeal, the engine proves
each membership the lemma's statement needs at those arguments that no
hypothesis states, by `membershipProof`, and adds it as a hypothesis. The
core's `cong` takes a lemma under hypotheses too, and discharges them where
it appeals to the instance.

A motive which is the truth of a term, `0 < u` — the membership of a closure
lemma — is its own code, `[[0 < u]] = u`, so the induction script neither
reflects nor reifies it.

## Classes

Classes are resolved before anything reaches the core, at each use of a
method. Type checking has no unification variables. An application takes the
parameters of its head's type from the type expected of it, then from its
arguments, by one-sided matching (`Types.matchTy`). What nothing fixes is a
hole, which the translation erases.

A method is resolved at the application, at the type its class's parameter is
then at (`Elab.methodAt`). At a known type, it is the instance of its class
for the head of that type, applied after its arguments to the dictionary the
instance's context takes at the type's arguments (`Elab.dictionaryAt`). At a
type variable a constraint gives it for, it is a place of the enclosing
dictionary. An argument whose method is not resolved for want of its type,
like `mempty` in `mempty <> xs`, is checked again once the other arguments
have fixed its domain; a side of an equation is checked again once the other
side has. A method at a type nothing determines, or at a type variable no
constraint gives it for, is refused.

An instance's methods are ordinary functions, compiled as any function is,
with their unfolding lemmas. The instance comes into scope before its
clauses, so a method may recur through itself, or use another method of the
instance.

A function under constraints takes a dictionary: the methods it uses of the
classes constraining its type variables and of their superclasses. The
elaborator keeps only the places its clauses refer to, because an instance
of a schema is recognised by the calls of its parameters, so a schema must
use each. A method taking arguments is a parameter of the function's prf
schema, `w_1`; a method taking none, a value, is an argument after the
function's own. So `mconcat xs` at `List Nat` is `mconcat
{Semigroup-List.(<>)} xs Monoid-List.mempty` in the core, and in `mconcat`'s
own clauses `x <> mconcat xs` is `w_1 x (mconcat {w_1} xs d0)`. A recursive
call passes the dictionary on unchanged, which the compiler checks:
primitive recursion keeps the parameters of a schema. The unfolding lemmas of
such a function are rules over the parameters of its schema, their variables
term metavariables, proved once by the same chain as any function's. An
appeal, by `exact`, `cong` or `rfl`, instantiates them at the methods of
instances.

For adequacy, a function under constraints at a known type denotes the
function its clauses define with the instances' methods in place of the
classes'. Premise (U) holds for its core term, an instance of its schema, as
its rules instantiated at those methods state.

A theorem under constraints is a rule of the core over the parameters of its
dictionary, the methods its statement uses taking arguments. Its values and
the values of its dictionary are term metavariables, and the auxiliary
theorems of its inductions are rules the same way. An appeal instantiates it
at the methods of an instance, which the core infers by matching. For
adequacy, the rule states its sequent at every instantiation of its abstract
functions by primitive recursive functions, among them the methods of each
instance. There the argument of § Statements and their adequacy applies: a
theorem under constraints holds at every instance of its classes.

The translation of statements therefore never meets a method. A certified
statement mentions the functions of the instances chosen, which
`praxis check --dump-core` shows, and § Statements and their adequacy
applies unchanged. That an instance is the only one of its class for its type
is what makes the choice the one the reader of the source predicts; soundness
does not depend on it.

**Instances under a context.** The functions of `instance Semigroup a =>
Semigroup (Pair a)` are functions under the context's constraints. Each
takes the places of the context's dictionary it uses, itself or through the
other methods of the instance it calls, found as a fixpoint, since a schema
must use each of its parameters. A use at a known type passes the
dictionary the context takes at the type's arguments, each place resolved in
turn (`Elab.methodAt`, `dictionaryAt`). Passed on as the parameter of a
schema, such a function is the closed λ applying it to its dictionary:
`mconcat {λ y_1 y_2. (Semigroup-Pair.(<>) {Semigroup-Nat.(<>)} y_1 y_2)} …`.
The instance's laws are elaborated at its type under the context, as a
theorem under constraints is. For adequacy, a function of an instance under
a context at a known type denotes the function its clauses define with the
context's instances' methods in place, as a function under constraints does.

**Resolution.** Instances and the obligations of proofs are found by one
search (`Resolve.solve`). It takes a goal and a database of Horn clauses
keyed by the goal's head symbol, and searches recursively, with a depth
bound. A clause does not apply to a goal, refuses it with a reason, or
reduces it to subgoals, the goal's result built from theirs. What a result
is, and how the clauses that apply are taken, belongs to the back end:

- **Methods** (`Elab.methodDatabase`) are coherent. The only clause at the
  head of a type is its instance, whose context's methods are the subgoals,
  and two clauses applying would be refused as an overlap.
- **Obligations of proofs** (`Engine.obligations`) are the membership of a
  term, a law at a type, and the closure of a method at a type. They take
  the first clause whose subgoals succeed, backtracking, since which proof
  is found does not matter. The clauses are a hypothesis, `anyIsMember`,
  the goal's premise, a constructor's `intro`, a function's closure lemma,
  and an instance's theorem of a law.

**Laws.** A law of a class is a statement over the class's dictionary at its
parameter. An instance proves it as a theorem at its type, the dictionary's
places its functions: `Pointed-List.plus-zero : 0 < List.is x |-
Pointed-List.plus x Pointed-List.zero = x`, a statement of § Statements.

A type variable a theorem's values mention has a place of its own in the
theorem's dictionary: `#is`, the membership predicate of the type it stands
for, a parameter of the theorem's rule of one argument, say `w_2`
(§ Statements). Where a class with laws constrains the variable, the rule
has premises over variables of their own (see [pra-and-prf.md](pra-and-prf.md)):

- each law of the classes constraining the variable whose methods its
  statement uses, `(law_1 ∀ l_0 : 0 < w_2 l_0 |- w_1 l_0 d0 = l_0)`;
- the closure of each method it uses returning the variable's type,
  `(closed_3 ∀ l_0 l_1 : 0 < w_2 l_0, 0 < w_2 l_1 |- 0 < w_2 (w_1 l_0 l_1))`,
  or `(closed_2 : |- 0 < w_2 d0)` for a value.

In the proof, a law applied at values of the variable is its premise,
`exact law_1`, and the membership of a method's result the closure premise
(`Engine.membershipProof`). A law about a method the statement does not use
is no premise: an appeal could not tell which function it is at. An appeal
at an instance, `plus-zero-twice xs` at `List Nat`, instantiates the
membership predicate by `List.is`, or by the prelude's `anyIs n = 1` at
`Nat`, and discharges the premises. It uses the instance's proofs of the
laws, the closure lemmas of its functions, and `anyIsMember : |- 0 < anyIs
n` at `Nat`. An appeal at a type variable of a caller under the same class
uses the caller's own premises. The engine states the instance of an appeal
by `cong`, `have (eq) { exact … }; cong (eq)`, so that its membership
hypotheses are the arguments'.

For adequacy: the rule states its sequent at every instantiation of its
abstract functions, the membership predicate among them, under its
premises. At an instance, the premises are the instance's laws and the
closure of its methods, each certified. So the theorem's sequent holds
there, its values members as § Statements reads them; at `Nat`, `anyIs`
takes every value. An instance's laws are statements of § Statements, whose
values have memberships, and the premises state them so: a law is only ever
asked of members.

## Invariants, collected

1. Every name the surface hands to the core is mangled into `u_…`/`v_…`.
2. Projections of codes are `hd`/`tl`; `Defeq` is used on statements over
   variables only.
3. Values are first-order: no field, theorem value, argument or result of
   function type, and every application complete.
4. The code of every value of a data type is a member at the predicates of
   its type's arguments (`C.#intro`), and membership hypotheses stand only on
   a theorem's values, where a wider predicate only strengthens the
   statement. At an indexed type membership checks the indices of the
   constructors' entries, so the index functions are defined before the
   predicate.
5. Unfolding lemmas hold for all codes.
6. The inversion lemma and the engine read the same record of which fields
   carry memberships, and of which equations of indices each constructor's
   branch checks.
7. Declarations are certified in order; a failure is never a lemma; a theorem
   is not in scope in its own proof.
8. The engine builds text, never proof terms: the core certifies it.
9. Auxiliary theorems have names unique by the source position of their
   induction.
10. Methods never reach the core: each use is the function of the instance
    of its class for the type it is used at, the only instance of its class
    for that type, or a place of a dictionary, a parameter of a schema or a
    rule. A law is likewise the theorem proving it at an instance, or a
    premise of a rule.
