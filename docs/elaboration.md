# Elaboration: from the surface language to the kernel

This document explains how a module of the surface language
([surface.md](surface.md)) becomes definitions and certified theorems of the
core ([kernel.md](kernel.md), [pra-and-prf.md](pra-and-prf.md)), why a
certified theorem means what the user wrote, and the invariants that keep
the translation sound and fast. The code is in
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
of them is certified. Everything else — the parser, the type checker, the
encoder, the compiler, the proof engine — can only cause a rejection when it
is wrong. A declaration which fails is reported and **never becomes a
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
- **Membership** `T.is n = cvrec {λ k h. dispatch} n`: the dispatch on the tag
  checks, in the branch of `Cᵢ`, that the code is *exactly* `Cᵢ` applied to its
  fields (no junk) and the membership of the fields of `T` itself (by the
  history, `at h k field`) and of data types encoded before. It is *shape*
  membership: fields of a type parameter, of `Nat` or of a later type are
  unconstrained.
- **`T.#is-def`, `T.#is-beta`** unfold the predicate at a variable, and
  `T.#collapse-i` collapses a dispatch at tag `i` over variables.
- **Introduction** `C.#intro : 0 < U₁.is x_{j₁}, … |- 0 < T.is (C x̄)`, a
  hypothesis for each field whose membership the branch of `C` checks: the
  predicate unfolds at the code (`#is-def`, `#is-beta`), the tag selects the
  branch (`C.#tag`, `T.#collapse-i`), the shape conjunct is `eqRefl` once the
  fields are rewritten to the variables (`C.#field-j`), the conjunct of a
  field of `T` itself is its hypothesis through the history (`histAt` with
  `C.#lt-j`), and `conjIntro` joins them. By induction on a value, the code of
  every value of `T` is a member — premise (M) of § Adequacy.
- **Inversion** `T.#inversion : 0 < T.is t |- ⋁ᵢ (t = Cᵢ (fields t) ∧
  memberships)`, proved by case analysis on the tag with `eqBool`,
  `collapseT/F`, `conjElim1/2`, `eqElim`, and `histAt` with `C.#lt-j` for the
  recursive fields. Induction rests on it.

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

**Closure lemmas.** A function whose result is of a data type has
`f.#closed : 0 < A₁.is x₁, … |- 0 < T.is (f x̄)`, a hypothesis for each
argument of a data type: its results are members. The engine proves it
(`Engine.proveClosure`) by induction on the argument the clauses match on,
each case the membership of the clause's body once `f.unfold-C` rewrites the
application. That membership is a hypothesis, the induction hypothesis at a
recursive call, `C.#intro` at a constructor, or `g.#closed` at another
function, each after the memberships of what it is applied to
(`Engine.membershipProof`). A body whose membership is not established that
way leaves the function without a closure lemma: say, a field of a type
parameter, which shape membership does not check, returned where a data type
is expected.

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

## Statements and their adequacy

### The translation

A theorem `{ā} → (x₁ : T₁) → … → A` becomes, by `Engine.statementGoal`, the
core sequent

```
0 < T₁.is x₁, …, H₁, …, Hₘ |- C
```

where `A = H₁ → … → Hₘ → C`: the values are free variables (the Π₁ reading
of a PRA theorem), each of a data type with its membership hypothesis (none
for `Nat` or a type parameter), and top-level implications become
hypotheses. Type parameters are erased. Propositions translate connective by
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
builtins `S`, `add`, `sub`, `mul`, `pow`.

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
- **(M)** the code of every value is a member: `C.#intro`, by induction on the
  value.

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
3. *The sequent.* The kernel's soundness gives the numeric instance at `e∘ρ`.
   Its membership hypotheses hold there by (M), its other hypotheses by 2
   exactly when the surface ones do, so its conclusion holds, and by 2 the
   surface conclusion.

Each step is an induction on syntax or on finite trees, and a free-variable
theorem is read as its numeric instances: the argument is finitary, the kind
of reasoning Hilbert's metamathematics allows. It could be formalised in PRA
module by module, but not uniformly — surface functions reach every
primitive recursive function, and no primitive recursive function evaluates
them all, so a uniform statement would need evaluators indexed by fuel — and
nothing would be gained: a formal proof would rest on a semantics written
down by hand, as this one does.

Membership is *shape* membership, which may be wider than the codes of a
type (a field of a type parameter is unconstrained). It appears only as a
hypothesis on a theorem's values, where a wider predicate gives the core
statement more instances, not fewer: sound, and incomplete where a statement
needs the finer typing. Full membership predicates are planned.

### Testing the translation

The argument is proved once; its implementation is tested.
`praxis/test/Language/Praxis/Surface/AdequacyTest.hs` runs two interpreters
on random values. One is a reference semantics of the elaborated surface
syntax: trees, functions run by their clauses, no codes. The other evaluates
the core text generated — the statement `Engine.theoremStatement` produces,
and the sides of the unfolding lemmas — as the certified lemmas describe its
symbols: constructors as free symbols (I), functions by their unfolding
lemmas (U), membership by a code's constructor and fields (M and the
inversion), and the builtins by the kernel's own evaluator. It checks lemma 1
for every function, and lemma 2 and the membership hypotheses for every
statement of `test/data/adequacy.px` — statements true and false, over every
relation, connective and bounded quantifier — and of `list.px`. The core side
evaluates symbolically because numerals are out of reach: the membership of
a code unrolls a history one level for every number below the code.

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

Classes are resolved before anything reaches the core. A use of a method
stands for a placeholder, and records a constraint: the type its class is at
there. Once the declaration's types are unified, each constraint is solved by
the instance of its class for the head of that type, and the placeholder
replaced by the instance's function (`Elab.resolveMethods`). A method at a
type not known, or at a type variable, is refused.

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

**Laws.** A law of a class is a statement over the class's dictionary at its
parameter. An instance proves it as a theorem at its type, the dictionary's
places its functions: `Pointed-List.plus-zero : 0 < List.is x |-
Pointed-List.plus x Pointed-List.zero = x`, a statement of § Statements.

A type variable which a class with laws constrains has a place of its own in
a theorem's dictionary: `#is`, the membership predicate of the type it stands
for, a parameter of the theorem's rule of one argument, say `w_2`. The
theorem's values of that type have the hypothesis `0 < w_2 x`, as the values
of a data type have theirs. Its rule has premises over variables of their
own (see [pra-and-prf.md](pra-and-prf.md)):

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
4. The code of every value of a data type is a member (`C.#intro`), and
   membership hypotheses stand only on a theorem's values, where a wider
   predicate only strengthens the statement.
5. Unfolding lemmas hold for all codes.
6. The inversion lemma and the engine read the same record of which fields
   carry memberships.
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
