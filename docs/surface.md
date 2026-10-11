# The surface language, `.px`

The surface language is what a user of praxis writes: modules of data types,
functions defined by pattern matching, and theorems proved by clauses, by
calculations or by tactics, in a syntax close to Agda and Haskell. It lives in
the `praxis` package. It elaborates into Praxis Core, the explicit typed
intermediate language, then lowers to Copra, the internal PRA kernel language
in `praxis-copra`. Every definition becomes a primitive recursive `prf`
definition, and every proof a `pra` declaration checked by its declaration
certifier and the PRA kernel. That the resulting arithmetic statement
preserves the surface statement's meaning is a separate
adequacy obligation — see [elaboration.md](elaboration.md) for how, and
[kernel.md](kernel.md) for what
the kernel checks.

```
module Data.List where

data List a = Nil | a : List a

(<>) : List a -> List a -> List a
(<>) Nil      ys = ys
(<>) (x : xs) ys = x : (xs <> ys)

infixr 4 <>

append-nil : {a : Type} -> (xs : List a) -> xs <> Nil ≡ xs
append-nil {a} Nil = (<>).unfold-Nil
append-nil {a} (x : xs) = calc
  (x : xs) <> Nil
  = x : (xs <> Nil)
  = x : xs  := by cong (append-nil xs)

append-nil-tactically : {a : Type} -> (xs : List a) -> xs <> Nil ≡ xs
append-nil-tactically {a} xs = by
  induction xs
  { refl }
  { intros x xs
    calc (x : xs) <> Nil = x : (xs <> Nil)
                         = x : xs := by IH }
```

## The pipeline

```
source ──Lexer/Parser──▶ raw syntax (named, operators unassociated)
       ──Fixity─────────▶ operators associated by the module's fixities, and the imports'
       ──Rename─────────▶ scope resolved: imports, openings, nested modules, privacy; every global by its canonical name
       ──Elab───────────▶ resolved syntax and Praxis Core (explicit typed intermediate language)
       ──Encode/Compile─▶ prf equations + generated lemmas (Copra)
       ──Engine─────────▶ theorem proofs as pra declarations (Copra)
       ──Check──────────▶ Copra definitions and proofs certified by the PRA kernel, in order
```

Each stage is a module of `Language.Praxis.Surface`: `Lexer`, `Parser` and
`Syntax.Raw`; `Fixity`; `Rename`, the scope checker; `Syntax`, `Types`, `Env`, `Elab` and `Core`; `Encode`,
`Compile`, `CoreText` and `Mangle`; `Engine`; `Check`, the driver, with
`Prelude`, the definitions and lemmas every module is compiled against.

## Lexical structure

- **Comments** are `-- …` to the end of the line, and `{- … -}`, nestable.
- **Identifiers** are alphanumeric segments joined by single dashes, as in
  Agda: `append-nil`, `unfold-Nil`. Binary minus therefore needs spaces:
  `x-y` is one identifier, `x - y` a subtraction.
- **Qualified names** join segments with a dot and no whitespace:
  `List.Nil`, `Term.App`, `(<>).unfold-Nil`, `List.(:)`. A segment may be an
  operator in parentheses, and the last segment of a qualified member may end
  in operator segments, `(<>).unfold-:`.
- **Operators** are runs of symbol characters (ASCII and Unicode). The
  grammar reserves `->`, `→`, `|`, `\`, `=>`, `<-`, `←`, `.`, `<;>`, `¬`, `⊤`,
  `⊥`; `=`, `:` and `:=` are ordinary operators the grammar reads specially
  where it needs them, so `:` and `:=` can still name constructors.
- **Keywords** are `module where open import private public using hiding renaming data class instance
  infixl infixr infix case of if then else let in by calc Type forall exists
  fun with`; `as` and `to` are words only in imports and renamings. Tactic
  names are words only in tactic position.

## Layout

Layout is the offside rule, checked token by token (`Lexer.block`). A block
opened without a brace — after `where`, `by`, `of`, and for a `calc`'s steps —
takes the column of its first token; a line starting at that column starts
the next item, and within an item every later token must stand to the right
of the column. Brackets `( ) [ ] { } ⟨ ⟩` suspend the layout of the enclosing
block, and a closing bracket is never offside. Inside explicit braces, items
are separated by `;` or by newlines at the column of the first item; a
trailing `;` is ignored. There is no other scoping rule: mixing tactics,
calculations and terms is resolved by this one.

A `calc` whose first term follows it on the same line has its further steps
on lines deeper than the item it belongs to; one with nothing after it on its
line is a block whose first item is the first term. A step is
`= term [:= proof]`, and Lean's `_ = term := proof` is accepted.

## Declarations

| declaration | example |
|---|---|
| module header | `module Logic.FOL where`, optional: a file is the module its path names |
| nested module | `module Length where` and its declarations, laid out deeper or in braces |
| import | `import Data.List`, `import "pkg" Data.List as L using (a) hiding (b) renaming (c to d)` |
| namespace opening | `open List`, `open Data.List using (…) public`, `open import Data.List` |
| private block | `private` and its declarations, which the module does not export |
| data type | `data Term r f v = FVar v \| BVar nat \| App (f (Formula r f v) (Term r f v))` |
| fixity | `infixr 4 <>`, `infixl 6.5 +++`, `infix 9/2 ~~` |
| signature | `name : type` |
| clause | `lhs = rhs`, or `lhs` alone where a pattern is absurd, `()` |
| class | `class Semigroup a => Monoid a where`, and the signatures of its methods |
| instance | `instance Monoid Nat where`, and the clauses of its methods |

A constructor is a name applied to the types of its fields, `Neg t`, or two
types around a constructor operator, `t :+ t`; as in Haskell, a constructor
operator starts with `:`.

A signature whose type ends in a proposition declares a **theorem**; any other
declares a **function**. The clauses following it define it; a clause's left
side may be prefix, `(<>) Nil ys`, or infix, `Nil <> ys`.

## Modules, namespaces and names

A file is one top-level module, named by its path within its library;
modules nest, `module N where`, each a namespace of what it exports, which
is what it declares outside `private` and what it opens `public`. `import
M` brings the exports of `M` into scope qualified, `open N` brings the
members of a namespace into unqualified scope, both with `using`, `hiding`
and `renaming`, as in Agda. Modules are grouped into libraries, packages and
projects, with dependencies and versions: [packages.md](packages.md) has the
whole of it, and the manifests.

Namespaces follow Rust: `data T` opens the namespace `T`, holding its
constructors; a function `f` opens the namespace `f`, holding the lemmas
generated for it, `f.unfold-C` and Lean's `f.eq_i`; a class holds its
methods and laws, an instance its functions.

Names are resolved by the renamer, before elaboration, into canonical
names. An unqualified name resolves, in order, as a local variable, a name
declared by the module or by one enclosing it, a member of an opened
namespace, and then a constructor — of the type expected there, which is
how `Nil` means `List.Nil` in the example without any `open`, or the only
constructor of that name among the modules in scope. Anything else is an
ambiguity error listing the candidates, or, once typed, not in scope. A
qualified name is resolved through its first segments — a namespace in
scope, an imported module, the module's own name — the rest navigating
namespaces.

## Classes and instances

```
class Semigroup a where
  (<>) : a -> a -> a

class Semigroup a => Monoid a where
  mempty : a

instance Semigroup (List a) where
  (<>) Nil      ys = ys
  (<>) (x : xs) ys = x : (xs <> ys)

instance Monoid (List a) where
  mempty = Nil
```

A class has one parameter, methods and laws. Its methods have first-order
signatures; methods taking arguments must mention the parameter. Its laws are statements over
values of the parameter and of types over it:

```
class Pointed a where
  zero : a
  plus : a -> a -> a
  plus-zero : (x : a) -> plus x zero ≡ x
```

Method signatures may depend on preceding nullary members of the same
dictionary. For example, given an indexed vector type:

```haskell
class Sized a where
  card : Nat
  enumeration : Vec card a
```

`enumeration` carries the cardinality supplied by that same `Sized a`
dictionary. Forward references in method signatures are rejected. A nullary
member such as `card` need not mention `a` in its result type; its use must
still select a unique dictionary. With two possible `Sized` dictionaries,
an unqualified `card` is ambiguous; `card {a}` explicitly selects the
dictionary for `a`. Inside an instance, an otherwise undetermined class
type defaults to that instance's head. Dictionary pruning retains the values
needed by dependent signatures, and Praxis Core checks these indices against
the actual dictionary arguments.

Its superclasses constrain the same parameter. A method or a law is a
top-level name, as in Haskell, and a member of its class's namespace.

An instance is for a data type applied to distinct type and index variables,
or for `Nat`. For example, `instance Sized (Fin n)` covers every `n`; a
specialized head such as `Fin 0` is rejected. Index variables retain their
declared types and are available in the method and law clauses, including
through explicit implicit patterns such as `card {n} = n`.
Unused runtime indices are pruned. Passing a method with arguments as a
dictionary requires its runtime captures to be closed; passing a nullary
member as a value has no such restriction.
It is the only instance of its class for that type; it comes after an
instance of each superclass for it; it defines every method by clauses, as a
function is defined; and it proves every law by clauses, as a theorem is
proved. Each method of an instance is a function of the instance,
`Semigroup-List.(<>)` — `lists.(<>)` for `instance lists : Monoid (List a)
where …` — with its unfolding lemmas, `Semigroup-List.(<>).unfold-Nil`. Each
law is a theorem at the instance's type, its methods the instance's
functions, `Pointed-List.plus-zero`:

```
instance Pointed (List a) where
  zero = Nil
  plus xs ys = app xs ys
  plus-zero Nil = rfl
  plus-zero (x : xs) = calc
    plus (x : xs) zero
    = x : plus xs zero
    = x : xs := by cong (plus-zero xs)
```

An instance may constrain the variables of its type:

```
instance Semigroup a => Semigroup (Pair a) where
  (<>) (MkPair x y) q = MkPair (x <> first q) (y <> second q)
```

Its functions are then functions under the constraints, each taking the
methods of the context it uses, itself or through the instance's other
methods. A use at `Pair Nat` is `Semigroup-Pair.(<>)` with
`Semigroup-Nat.(<>)` passed. At `Pair (Pair Nat)` it is passed the
instance's own function for `Pair Nat`, with that function's methods in
turn. Its laws are theorems under the context. A value of `Pair a` is a
member by the predicate of `a` at its fields, so a law's proof has the
context's laws there:

```
instance Pointed a => Pointed (Pair a) where
  zero = MkPair zero zero
  plus (MkPair x y) q = MkPair (plus x (first q)) (plus y (second q))
  plus-zero (MkPair x y) = calc
    plus (MkPair x y) zero
    = MkPair (plus x zero) (plus y zero)
    = MkPair x (plus y zero) := by cong (plus-zero x)
    = MkPair x y := by cong (plus-zero y)
```

A use of a method is resolved where it is applied, as soon as the type it is
used at is known there: it is the function of the instance of its class for
that type. `2 <> 3` is `Semigroup-Nat.(<>) 2 3`, and `mempty <> xs`, at
`List Nat`, is `Semigroup-List.(<>) Monoid-List.mempty xs`.

The type of an application comes from the type expected of it first, then
from its arguments. An argument that cannot determine its own type, like
`mempty` here, takes it from the others, and a side of an equation takes it
from the other side, as in `mempty ≡ 0`. A use at a type nothing determines
is refused as ambiguous.

A function may constrain its type variables, `mconcat : Monoid a => List a
-> a` (or `(C a, D b) => …`, in front of the signature or after its
implicit binders). In its clauses, a method at a constrained variable is the
one the caller's instance provides:

```
mconcat : Monoid a => List a -> a
mconcat Nil      = mempty
mconcat (x : xs) = x <> mconcat xs
```

A call at a known type passes the instances' methods; a call at a
constrained variable passes on the caller's own. A method at a type not
known, or at a variable no constraint is on, is refused.

A theorem may constrain its type variables too. It is proved once, for
every instance:

```
mconcat-single : Monoid a => (x : a) -> mconcat (x : Nil) ≡ x <> mempty
mconcat-single x = rfl

single-five : mconcat (5 : Nil) ≡ 5 <> mempty
single-five = mconcat-single 5
```

Its proof may use what holds at every instance: the clauses of the
functions, and the laws of the classes.

```
plus-zero-twice : Pointed a => (x : a) -> plus (plus x zero) zero ≡ x
plus-zero-twice x = calc
  plus (plus x zero) zero
  = plus x zero := plus-zero (plus x zero)
  = x := plus-zero x

twice-list : (xs : List Nat) -> plus (plus xs zero) zero ≡ xs
twice-list xs = plus-zero-twice xs
```

A law applied to values of a constrained type variable holds at every
instance; applied to values of a known type, it is the instance's proof of
it. Under a class with laws, a theorem's values of the constrained variable
are members of the type it stands for, and so is every result of a method
applied to members: what a law applied at them needs. An appeal at an
instance holds by the instance's proofs of the laws. A law applies to
arguments, whose type gives the instance; and a proof may use the laws
about the methods its statement uses, which fix the functions they are at.

## Builtin registrations

`{-# BUILTIN ROLE name #-}` connects a compiler role to an ordinary,
previously declared definition. It introduces no axiom. The checker validates
the exact signature and the role's earlier registrations, and activates the
binding only after the target completes checking. A compiled body with a
failed proof obligation or generated contract is insufficient. A role cannot
be registered twice or rebound, including across imported modules.

The builtin roles include the following:

| Role | Required declaration |
| --- | --- |
| `FIN` | An inductive type with one `Nat` index |
| `VEC` | An inductive type with a `Nat` index followed by one type parameter |
| `FIN_FROM_NAT` | Conversion from `k`, given `k < n`, to `Fin n` |
| `FIN_TO_NAT` | Conversion from `Fin n` to `Nat` |
| `FIN_TO_NAT_BOUND` | A certified theorem that the conversion is less than `n` |
| `FIN_FROM_TO_NAT` | A certified theorem that converting an ordinal to `Nat` and back returns it |
| `FIN_TO_FROM_NAT` | A certified theorem that converting a bounded numeral to an ordinal and back returns it |
| `VEC_LOOKUP` | `Fin n -> Vec n a -> a` |
| `FINITE` | The finite class |
| `FINITE_CARD` | Its `card : Nat` method |
| `FINITE_CODE` | Its `code : a -> Fin card` method |
| `FINITE_DECODE` | Its `decode : Fin card -> a` method |
| `FINITE_DECODE_CODE` | Its law `decode (code x) = x` |

The dependent member signatures and retraction law must use the same registered
class and cardinality. The bridge theorems must have exactly the required
statements, without extra assumptions. Names alone do not establish these
properties: the PRA kernel checks the ordinary proofs. A role declaration is
surface elaboration metadata; it creates no special Praxis Core expression.

The finite interface requires only the round trip from an element through
its code and back. Different ordinals may decode to the same element, so
`card` is an upper bound on the number of elements. A vector enumeration and
lookup are not prerequisites of the finite roles. When useful, an enumeration
can be built separately by tabulating `decode`.

## Types

Types are `Nat` (also `nat`), data types applied to types, type parameters
(possibly higher-kinded, `f` in `Term r f v` has kind `Type -> Type -> Type`,
inferred from use) and function types. Polymorphism is rank 1, as in
Hindley–Milner: a signature's free type variables are its implicit
parameters, in order, and implicit binders `{a : Type}` may also be written in
front.

Values are first-order. Data fields, type arguments and function results
cannot contain function values. An explicit function argument or theorem
binder may instead be a **fixed function schema** whose own arguments and
result are first-order. A schema is applied to all of its arguments and
cannot be stored or compared as a value. The encoding gives a meaning to
first-order values and separately checked schemas (see
[elaboration.md](elaboration.md), § Statements and their adequacy). A theorem
over a type parameter holds at every first-order type it stands for.

## Fixed function schemas

```
apply : (Nat -> Nat) -> Nat -> Nat
apply f x = f x

iterate : (Nat -> Nat) -> Nat -> Nat -> Nat
iterate f 0 x = x
iterate f (S n) x = f (iterate f n x)

apply-law : (f : Nat -> Nat) -> (x : Nat) -> apply f x = f x
apply-law f x = rfl
```

A schema parameter is bound by a name or `_`, with no constructor matching
or induction on the function. Recursive calls keep the same function
parameter. Function names and lambdas are accepted where a schema argument
is expected, including lambdas that capture ordinary values:

```
captured : (n : Nat) -> apply (\x -> x + n) 2 = 2 + n
captured n = rfl
```

The expected domain determines a lambda's argument types. Functions still
cannot be returned, placed in data constructors, or passed through a
polymorphic value parameter. Write a pointwise law such as `f x = g x`
instead of `f = g`. Proof arguments inside lambdas are currently rejected;
their obligations would need to be checked in the lambda's bound scope.

## Type synonyms

Transparent type synonyms abbreviate types, including indexed types:

```
type Board n a = Vec n (Vec n a)
type AnnotatedBoard (n : nat) a = Vec n (Vec n a)
```

Here `Vec` has its length before its element type. The use of `n` at its
length index infers `n : nat`; `a` is a type parameter. Synonyms expand
during elaboration, so a `Board n a` and a `Vec n (Vec n a)` are the same
type, with no wrapping constructor or extra runtime representation.
Parameters may interleave, and annotations must respect dependency order.
Synonyms can refer to other synonyms, including ones declared later, but
cycles are rejected. They participate in imports, openings and renaming.
`--dump-core` shows their expanded types. An alias for a function type can
abbreviate a function signature; it does not permit function-valued fields.

## Indexed data types

A data type may be indexed by values, in the GADT style: its constructors
are given by their signatures after `where`, each ending in the data type at
its parameters and at indices.

```
data Vec a n where
  nil : Vec a 0
  (:-) : {n : nat} -> a -> Vec a n -> Vec a (S n)

tail : Vec a (S n) -> Vec a n
tail (_ :- tl) = tl
```

A parameter of the head is a type parameter or an index, as its kind says:
`Type` (also `type`), or an arrow of such kinds, for a type; a value kind for
an index, `nat` or a data type. Type parameters and indices may interleave;
each binder's type may mention only binders before it. Applications follow
declaration order. For example:

```
data VecByLength (n : Nat) (a : Type) where
  Nil : VecByLength 0 a
  Cons : {n : Nat} -> a -> VecByLength n a -> VecByLength (S n) a
```

An equality hypothesis can transport a value between different indices of the
same data type. For example:

```
cast : {n m : Nat} -> n = m -> VecByLength n a -> VecByLength m a
cast {n} {m} h xs = xs
```

When a value's indices differ from its expected type, the elaborator tries to
prove the required equalities by congruence from the proof hypotheses in
scope. It records explicit transport evidence, which the core checks before
erasing the transport from computation. The data type and element types must
still agree. To use a theorem such as commutativity, pass its proof to `cast`;
the `base` library uses this to give vector append the result index `n + m`.

An implicit argument's slot follows the same declaration order among implicit
binders. Explicitly supplied implicit arguments still go in braces before the
ordinary arguments. A header such as `(xs : VecByLength n a) (n : Nat)
(a : Type)` is rejected because `n` and `a` are not yet in scope.

The kind is given
with the parameter, `data Vec a (n : nat) where`; after the parameters,
`data Vec : type -> nat -> type where`; or in a kind signature before the
declaration, `type Vec : type -> nat -> type`. Without one, a parameter is an
index where a constructor's result has a numeral, a successor, arithmetic,
or a variable of a value type there, and a type parameter otherwise. Type
parameters come first, and are the same distinct variables in every
constructor's result: a type is no index.

An implicit parameter of the head, `{n}`, is not written where the type is
used: the kind of a parameter after it mentions it, and the index written
there determines it. Its kind is written with it, `{n : nat}`, or found where
the kinds after it mention it — a type where they have a type, the type of
the index they have it at otherwise.

```
data SameVec {a} {n} {m} (l : Vec a n) (r : Vec a m) where
  BothNil : SameVec nil nil
  BothCons : {x : a} -> {xs : Vec a n} -> {ys : Vec a m} -> SameVec xs ys -> SameVec (x :- xs) (x :- ys)
```

`SameVec xs ys` is at the type of the elements of `xs` and at the lengths of
both, found from their types. A constructor's signature has the head's
implicit type parameters by their names. A variable standing at an index
whose type mentions the head's parameters has its type written, `{xs : Vec a
n}`, in a constructor's signature as in a function's or a theorem's.

A constructor's implicit arguments, `{n : nat}`, come before its fields, and
a variable its indices mention which nothing binds is one too. A field may be
named, `(m : nat) ->`, and is then in scope after it, for the types of the
fields after it and the indices of the result: `Zero : (m : nat) -> PLt 0 (S
m)` takes `m` as an argument its type depends on, where an implicit one,
`{m : nat} -> PLt 0 (S m)`, is found from the type expected. Such an argument
is an index — a variable, a numeral, `S`, a constructor or a function applied
— and matching `Zero k` learns the index from `k`, or `k` from an index which
is a variable; against a numeral, `k` is refused, as nothing solves it. A
proposition among a constructor's arguments, `Exists : (k : nat) -> n + S k =
m -> ELt n m`, is a precondition: a proof its code does not store, over the
implicit arguments and the named fields, an equation or a comparison for now.
Constructor preconditions do not admit quantified propositions; the finite
quantifier syntax applies to theorem propositions and function preconditions.
Building with the constructor gives a proof of it, checked as an obligation
as a function's precondition is; the membership of a code checks it as it
checks an equation of indices, so a pattern names it, `Exists k h`, and `h`
is a hypothesis of the case, `n + S k = m` at the fields. The indices of its
result are patterns — variables, numerals, `S` and constructors — so that
matching on the constructor can solve them; indices elsewhere may apply
functions and the arithmetic of `Nat`.

A signature's free variables at indices are its implicit value parameters,
as its free type variables are its type parameters: `n : Nat` in `tail`, and
`{n : Nat}` may be written in front. They are found where the function is
applied, from the type expected and the types of the arguments, by matching;
an argument whose type's index does not match the one expected is refused
there, as `tail xs` at `xs : Vec a 0` is. Indices are compared in normal
form, the arithmetic of `Nat` evaluated as the core's definitional equality
does: `n + 1` is `S n`, but `0 + n` is not `n`.

An implicit argument may also be given, in braces before the explicit ones,
where nothing else determines it or to say which: `replicate-vec {3} x`, a
function's implicit values in the order its signature has them; `fzero {2}`,
a constructor's implicit arguments in the order of its signature; and in a
type, `SameVec {Nat} nil nil`, a data type's implicit parameters, its types
then its indices. Each is of its parameter's type, and must agree with what
the type expected and the arguments say of it.

An implicit value a function's clauses bind, `{n}`, is taken at runtime: the
function's code has it as an argument before its own, and an application
passes the value found for it, which must then be a term of what is in scope
there. A clause may match on it as on an argument, and what it matches holds
of the indices of the other arguments and of the result:

```
replicate-vec : {n : nat} -> a -> Vec a n
replicate-vec {0} x = nil
replicate-vec {S k} x = x :- replicate-vec x
```

An implicit value no clause binds stays out of the code, found for the types
alone, as `n` in `tail`.

A function may take a proof: a proposition among its domains, `(0 < n) ->`,
is a precondition, which its code does not take. A clause names the proof,
`h`, or matches it by `_`, a proposition having no constructors. Every
application gives a proof of the precondition there, a proof term as a
theorem's clause has; it is checked as a theorem of its own, an obligation,
over the clause's variables and under the clause's own preconditions, by the
names the clause gives them. The function's lemmas, the membership of its
results and their indices, are under its preconditions; where a lemma is
appealed to at a call, the call's precondition holds by a hypothesis stating
it, or by the call's obligation, the indices at hand rewritten. An obligation
is of the clause's variables as codes: no membership is among its
hypotheses. `absurd p`, `p` a proof of `⊥`, is a value of any
type, for a case the preconditions exclude; a hypothesis whose equation
clashes once unfolded, as `0 < 0` does, is such a proof.

```
head-safe : {n : nat} -> (0 < n) -> Vec a n -> a
head-safe h (x :- _) = x
head-safe h nil = absurd h

head-of-two : Vec a 2 -> a
head-of-two v = head-safe rfl v
```

Clauses may match on several values of `Nat` at once, implicit values among
them, each combination of `0` and a successor covered once; a recursive call
passes each value or its predecessor, and at least one predecessor. The
function's lemmas are then proved by induction on the code of the tuple of
the values:

```
data PLt (n : nat) (m : nat) where
  ZeroSucc : {m : nat} -> PLt 0 (S m)
  SuccSucc : {n m : nat} -> PLt n m -> PLt (S n) (S m)

plt-of-lt : {n m : nat} -> (n < m) -> PLt n m
plt-of-lt {0} {S m} h = ZeroSucc
plt-of-lt {S n} {S m} h = SuccSucc (plt-of-lt h)
plt-of-lt {n} {0} h = absurd h
```

The recursive call's precondition, `n < m`, is its obligation, proved from
`h : S n < S m` once unfolded; `h : n < 0` clashes, so `absurd h` there.

Matching a constructor refines what a clause knows: `(_ :- tl)` against
`Vec a (S n)` gives `tl` the type `Vec a n`. A constructor whose result's
indices clash with those of the argument's type — `nil`, of length 0, at
`S n` — can never match there: its clause may be omitted, and a clause for it
is refused. Every other constructor must have its clause.

Where no constructor can match an argument, the absurd pattern `()` stands
for it, and its clause has no right side, since nothing matches it:

```
plt-not-zero : {n : nat} -> PLt n 0 -> ⊥
plt-not-zero ()

absurd-plt : {n : nat} -> PLt n 0 -> a
absurd-plt ()
```

Each constructor's result must clash with the indices there; one which may
match makes the pattern not absurd. An absurd clause is its function's or
theorem's only clause, for now, and stands for a whole argument, not a field
of one. The function's lemmas, and the theorem, refute each case.

A type may be ascribed to a term, `(e : T)`, `T` a type in the scope of the
enclosing signature; a variable at an index of it which nothing binds stands
for any value, so that `(Vec.nil : Vec a n)` is refused. A parenthesized `:`
whose right side is no type is the operator `:`, a constructor.

What a function says of indices is certified, or the function refused: its
lemma `f.#index` states the indices of its result under those of its
arguments; and a function omitting a constructor has its closure lemma,
`f.#closed`, under the indices of its arguments, which is how the omission is
justified.

A constructor makes a value of its type only of entries at the indices its
signature gives them, and a statement over the type means those values: a
derivation below is one, not any code whose last step claims what it proves.

```
data Pf (c : Fm) where
  Ax : Pf Top
  Weak : {b : Fm} -> Pf b -> Pf (Imp Top b)
  Detach : {b : Fm} -> Pf (Imp Top b) -> Pf b

sound : (p : Pf c) -> holds c ≡ T
sound Ax = rfl
sound (Weak p) = sound p
sound (Detach p) = sound p
```

In the case of `Detach`, that `p` proves `Imp Top b` is a hypothesis of the
case, and the induction hypothesis at `p` proves the goal once rewritten by
it and unfolded. Where a constructor is applied, the indices of its entries
are proved as those of an application's arguments are.

A theorem over values of an indexed type states the indices of its binders:
`(v : Vec a (S n)) -> v ≡ head v :- tail v` is of the lists whose length is a
successor, `n` its implicit value parameter, as in a function's signature,
and in the scope of its proposition. Its proof by clauses on `v` omits the
constructors the indices exclude — `nil` here, whose case is refuted — and
an appeal to it proves the indices it needs of its arguments from what is
known of theirs, as an application of a function does. A value parameter
which is the whole index of a binder, `n` of `(v : Vec a n) -> length v ≡ n`,
stands for that binder's index, so that induction on `v` needs nothing of
`n`.

```
length-index : (v : Vec a n) -> length v ≡ n
length-index nil = rfl
length-index (x :- xs) = cong (length-index xs)

head-tail : (v : Vec a (S n)) -> v ≡ head v :- tail v
head-tail (x :- xs) = rfl
```

Equality compares codes, so its sides may be of one type at different
indices:

```
same-eq : {xs : Vec a n} -> {ys : Vec a m} -> (p : SameVec xs ys) -> xs ≡ ys
same-eq BothNil = rfl
same-eq (BothCons q) = cong (same-eq q)
```

## Propositions

`s ≡ t` (also `=`), `s ≠ t`, `s < t`, `s ≤ t`, `s > t`, `s ≥ t` (on `Nat`),
`⊤`, `⊥`, `¬ A`, `A ∧ B`, `A ∨ B`, `A → B`, `A ↔ B`, and the bounded
quantifiers `∀ i < t, A` and `∃ i < t, A` (also `≤ t`; `.` followed by a
space may replace the comma).

Relations bind looser than every term operator, whatever its declared
precedence, so `xs <> Nil ≡ xs` needs no parentheses; connectives take
Lean's precedences, `¬` 40, `∧` 35 and `∨` 30 to the right, `↔` 20; the
arrow binds loosest.

Numeric bounded quantifiers may occur anywhere in a proposition: under
negation, in either side of an implication, or nested with other quantifiers.
They do not require prenex form. If a numeric binder has a written type,
that type must be `Nat`: `∀ (i : Nat) < n, P` checks the annotation.

A typed quantifier without a numeric bound ranges over a finite type:
`∀ (x : T), P` or `∃ (x : T), P`. The same rule applies at the beginning
of a theorem and inside a proposition. For example, with the finite protocol
registered:

```haskell
all-indices : ∀ (i : Fin n), i = i
nested : (∃ (i : Fin 3), i = i) -> ∀ (j : Fin 2), j = j
under-negation : ¬ (∃ (i : Fin 0), i = i)
generic : Finite a => ∀ (x : a), x = x
```

Applying a finite universal theorem can infer its domain from the supplied
value. For example, `all-indices i` infers `n` from `i : Fin n`, and
`generic True` selects the finite instance for the type of `True`. Each
argument is checked against the instantiated domain; a proved index equality
can supply the usual transport between indexed types.

Each typed binder needs an explicit first-order type. Later binder groups
may depend on earlier values, as in `∀ n < 3, ∀ (i : Fin n), P`.
Names in one group share the type as it was before that group: in
`(n : Nat) -> ∀ (n m : Fin n), P`, both finite bounds refer to the
outer `n`, even though the first finite binder shadows its name.

The leading arrow binder `(xs : List a) -> P` still quantifies over an
arbitrary value of `List a`, with the Π₁ reading of a PRA theorem. Use this
form for types which need not be finite. Explicit `∀ (xs : List a), P`
is no longer a synonym for that binder: it requires a finite-domain
instance, just as it would inside `P`. Unbounded numeric existential
statements `∃ y, P` remain unsupported.

### Finite domains

The registered `Fin n` type has a direct translation using its certified
conversions to and from a number below `n`. It does not require a `Finite`
instance. Other finite types use this ordinary class and its ordinary law:

```haskell
class Finite a where
  card : Nat
  code : a -> Fin card
  decode : Fin card -> a
  decode-code : (x : a) -> decode (code x) = x
```

The `BUILTIN` registrations above select these declarations. Both dependent
method types use the `card` of the same dictionary. `code` chooses a bounded
ordinal for each element, and the law proves that decoding this ordinal
returns the original element. This makes `a` a retract of `Fin card`.
No law `code (decode i) = i` is required: several ordinals may decode to the
same element, and `card` need not be the number of distinct elements.

Write `c = card` and `d = decode` for the selected dictionary. Both
quantifiers range over the numbers below `c` and replace the source variable
by the corresponding decoded value:

```text
∀ (x : T), P x   ↦   ∀ j < c, P (d (from-nat j))
∃ (x : T), P x   ↦   ∃ j < c, P (d (from-nat j))
```

For `Fin n`, the bound is `n` and the replacement is just `from-nat j`.
The bound supplies that conversion's required inequality. At a zero bound,
the universal proposition is true and the existential is false; no element
of the empty domain is constructed. Checked type contracts and the
`decode-code` law justify this translation equally under negation and
implication. The translation inserts neither a vector nor a search; a
library may implement `decode` using a vector if that is convenient.

An instance must supply primitive recursive `code` and `decode` functions.
Finiteness is not inferred from the presence of an inductive declaration:
`List Bool`, for example, has lists of unbounded length. Indexed families
such as `Fin n` can be finite for each index without having one finite
bound for all indices. Quantification bounded by a subterm or subtree relation remains separate
from this finite-type protocol.

Generic use of an indexed finite instance currently requires its non-nullary
dictionary methods to have no open runtime captures. The `Fin n` instance
meets this restriction because its identity methods need no captured `n`.
An instance whose coding or decoding method must capture a local index is
rejected; closed-index uses can still be supported.

Registrations must already be available where the proposition is written,
including in a local `have` or a function precondition. Later pragmas cannot
change earlier proof syntax. A failed roundtrip proof, method body or
required generated contract prevents the finite domain from being used,
even when the resulting proposition is a tautology or an unused local fact.
The [checked finite examples](../praxis/test/data/base/src/FiniteExamples.px)
cover `Fin 0`, generic domains and duplicate decoded values.
These obligations are retained before proof erasure; the full details are
in [elaboration.md](elaboration.md#finite-quantifier-desugaring).

### Proof arguments in propositions

The final relation in a theorem statement may call a function that needs
evidence. Leading implication antecedents provide the hypotheses for that
evidence; for example, `k < n -> bounded {k} {n} (by assumption) = k`.
The checker certifies every supplied proof before erasing it from the
statement. Proof arguments inside an antecedent, a quantifier or another
logical connective are not supported yet.

A theorem means what it says of the values it quantifies over: a data type
denotes the finite trees its constructors build, a function the unique
solution of its clauses, and the arithmetic of `Nat` the usual one, `m - n`
being `0` when `n` exceeds `m`. The core statement a theorem becomes means
the same; [elaboration.md](elaboration.md), § Statements and their adequacy,
argues why.

## Proofs

A theorem's right side is a proof in one of three styles, which nest freely.

**By clauses** (Agda style). Clauses matching on a value of a data type
prove the statement by structural induction on it, one clause per
constructor; a recursive call of the theorem at a field of the matched
constructor is the induction hypothesis there. Clauses matching on a value of
`Nat`, one on `0` and one on `S n`, prove it by the core's induction, the
recursive call at `n` the hypothesis; a numeral other than `0` is written as
the successor. A value the statement quantifies over need not be named: in
`PLt n m -> n < m` the type before the arrow to a proposition is that of a
value, which a clause matches on as on any other. A clause gives, in braces,
patterns for the theorem's implicit parameters, in the order its signature
has them: an implicit value is a value the statement quantifies over, and is
matched on as any other — `zero-add {0} = rfl` and `zero-add {S n} = cong
(zero-add {n})` prove `{n : nat} -> 0 + n ≡ n` by induction on `n` — while an
implicit type takes a name, which does not matter. An implicit value which
is, bare, an index of a value the theorem quantifies over is that index, and
not a variable of the statement: it is not matched on, only the value is. After
the patterns of its values, a clause names its hypotheses, each by a variable
or `_`: `lt-of-succ-lt {n} {m} h = h` names the hypothesis `S n < S m` `h`. A
hypothesis mentioning the value matched on, which the induction reverts, is
introduced by that name in each case. A right side is a proof term
— a lemma or a hypothesis, `cong e`, `rfl` — a `calc`, or `by` tactics.
Where the heads of the sides of an equation differ, `cong e` first unfolds
them, outermost first, until their heads agree, so that the congruence is
under what their definitions share: `length (x :- xs) ≡ Vec.#idx (x :- xs)` is
`S (length xs) ≡ S (Vec.#idx xs)`.

**By calculation.** `calc t₀ = t₁ := p₁ … = tₙ := pₙ` proves `t₀ = tₙ`, which
must be the goal's equation, its sides as written; an omitted justification
is `rfl`.

**By tactics** (Lean 4 style, with Rocq's spellings accepted). A tactic acts
on the first goal; newlines and `;` sequence; `{ … }` and `· …` focus the first
goal and must close it, so `induction xs { … } { … }` solves the cases in
turn. The engine translates, so far: `rfl` (`refl`, `reflexivity`), `exact`,
`cong` (`congr`), `calc`, `induction x`, `intro`/`intros` (naming what a case
introduces: the constructor's fields, then the induction hypotheses, `IH` by
default, `IH1 …` when there are several, then any implications reverted into
the goal), `have h : P := proof`, `assumption`, `sorry` (`admit`),
focused blocks, and a bare proof term, `by IH`, which closes the goal by the
term or else by congruence. A goal reported — by `sorry`, when unsolved, or
when a `calc` does not prove it — is over the names the clause and `intro`
gave its variables, not the eigenvariables the core introduces for them, `e_0`.
`constructor` splits a conjunction, while `left` and `right` select a
disjunction branch. `contradiction` handles impossible index equalities.
For finite quantifiers, `intro` names a decoded source element, `exists`
(`use`) takes a source element as witness, and `obtain` extracts a source
element and its property. A numeric `exists` additionally requires a proof
that its witness satisfies the bound. Universal hypotheses and theorems can
be applied to a source element with `exact h x`.

The grammar also accepts `apply`, `rw [e, ← e'] at
h`, `unfold`, `simp only`, `exfalso`, `cases`, `show`, `revert`,
`clear`, `by_cases`, `try`, `repeat`, `first`, `all_goals`, `any_goals`, `<;>`
and `case`; their translations are the next step of the engine.

`have` checks its proof before making the proposition available to subsequent
tactics. Its annotation can be omitted when a theorem application or named
hypothesis determines the proposition: `have bound := lt-of-plt p`. This is
particularly useful for facts about GADT indices. The proof remains checked
even when the following tactics do not use the local fact.

`rfl` is *surface* definitional equality: the sides are rewritten by the
unfolding lemmas wherever a function meets a constructor — a module's
functions', and those of the core's arithmetic and of the prelude, `add x (S y)`
to `S (add x y)` — then compared, the core's definitional equality taking only
what is left. A comparison is its equation in the core, `s < t` the equation
`lt s t = 1`, so `rfl` proves `0 < S m`, and `cong` rewrites in it. The
arithmetic of a comparison is rewritten by the library's equations too,
`S m - S n` to `m - n` and `0 - n` to `0`, so that `S n < S m` is `n < m` once
unfolded, and `n < 0` a clash. A hypothesis, or the induction hypothesis a
recursive call names, proves a goal it is once both are unfolded:
```
lt-of-plt : {n m : nat} -> PLt n m -> (n < m)
lt-of-plt ZeroSucc = rfl
lt-of-plt (SuccSucc p) = lt-of-plt p
```

A lemma of the library praxis-copra certifies, or of the prelude, is cited by
its name, applied to hypotheses, which it takes in order: `ltTrans nltm mltk`
proves `n < k` from `nltm : n < m` and `mltk : m < k`. A name of the module
comes first.

Where a lemma's conclusion, at its arguments, is the goal once the indices it
gives their terms are rewritten, the indices each function's lemma states of
its result rewrite it: `lt-of-plt (plt-trans {n} {m} {k} nltm mltk)` concludes
the indices of `plt-trans n m k` in order, which are `n` and `k`, so it proves
`n < k`.

A lemma applies at any arguments of its types: `app-nil (rev xs)` proves
`app (rev xs) Nil ≡ rev xs`. A value of a data type the lemma quantifies over
must be a member of that type. For an argument built from constructors and
functions this follows from their introduction and closure lemmas, generated
for every constructor and for every function whose result is of a data type.

## Tooling

- `praxis check [--dump-core] [--dump-pra] [--alone] [TARGET…]` checks a project, a
  package, a directory holding one, or `.px` files — each as a module of the
  package enclosing it, its imports first, or on its own — and prints every
  report. `--dump-core` prints datatype declarations with constructor signatures,
  and elaborated function signatures and clauses
  in surface-like notation, with explicit type arguments (`@T`), named index
  instantiations (`{n = value}`), dictionaries (`[dict …]`) and certified proof
  references (`[proof …]`). It includes imported declarations. This inspection
  notation is not yet accepted as source by the parser.
  `--dump-pra` prints the numerical definitions and every declaration handed
  to the PRA kernel. Both options can be used together.
- `praxis-lsp` serves `.px` documents with the driver's diagnostics, each as a
  module of the package enclosing it; with semantic tokens, every name
  coloured by what the renamer and the environment say it is — a data type,
  a constructor, a function, a theorem, a class, a method, a module, a
  variable, a word of the tactic language; and with go to definition, in
  the document or in the module it imports. `Check.checkedRenamed` and
  `Rename.rnResolved` and `rnHeaders` are what it reads.
- `editors/vscode` highlights `.px` and starts the server.

## Scope of the current implementation

Implemented: the whole grammar above; data types, including higher-kinded
parameters and nested and mutually referring types; functions matching on one
argument, each constructor once or `0` and `S n`, structurally recursive with unchanged other
arguments, or on several values of `Nat` at once, each case of `0` and `S`
once, recursive at predecessors through the code of their tuple, their closure
and index lemmas by induction on that code; classes with superclasses, and their instances for data types and
`Nat`, each use of a method resolved at the type it is used at; functions
and theorems under constraints, schemas and rules over the methods they use;
laws of classes, proved by each instance and premises of the theorems under
the class; theorems by clauses on one value, of a data type or of `Nat`, by
`calc`, and by the tactics
listed, a lemma applying at any arguments through the closure lemmas of
functions; instances under contexts; membership predicates taking those of
a type's parameters; data types in the GADT style indexed by values of `Nat`
and of data types, their kinds given or inferred, with their index
functions, their membership checking the indices of their constructors'
entries; implicit value parameters of signatures; matching which refines
indices, and clauses omitted where their constructor is impossible, justified
by certified index and closure lemmas; theorems over their values, the
indices of their binders as hypotheses and the cases these exclude refuted;
implicit parameters of data types, found from the indices written, and
indices whose types mention the parameters and the indices before them;
implicit values a function's clauses bind, taken at runtime; proofs as
arguments, each application's checked as an obligation, and `absurd`;
implicit arguments given in braces, `C {n}`; type ascriptions; modules,
imports, openings, nested modules and privacy, resolved by the renamer, and
libraries, packages and projects ([packages.md](packages.md)); `.px`
diagnostics.
Planned, in order: goal display in hover, the
remaining tactic translations, Σ₁ statements with witness terms, `case` and
`if` in terms, nested patterns and matching on several arguments not all of `Nat`, overlapping first-match clauses, mutual recursion and
accumulating parameters, membership checking the fields of nested
and higher-kinded parameters, and list-literal sugar. For indexed data types:
the types of variables at indices of dependent types inferred rather than
written; and explicit value binders in
the signatures of functions.
