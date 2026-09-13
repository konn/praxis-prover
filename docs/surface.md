# The surface language, `.px`

The surface language is what a user of praxis writes: modules of data types,
functions defined by pattern matching, and theorems proved by clauses, by
calculations or by tactics, in a syntax close to Agda and Haskell. It lives in
the `praxis` package. Nothing in it is trusted: every definition becomes a
primitive recursive definition of the core, and every proof a declaration of
the core's `pra` language, certified by the kernel — see
[elaboration.md](elaboration.md) for how, and [kernel.md](kernel.md) for what
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
       ──Fixity─────────▶ operators associated by the module's fixities
       ──Elab───────────▶ resolved syntax (bound scopes), types checked, items
       ──Encode/Compile─▶ prf equations + generated lemmas (core text)
       ──Engine─────────▶ theorem proofs as pra declarations (core text)
       ──Check──────────▶ the core compiles and certifies, in order
```

Each stage is a module of `Language.Praxis.Surface`: `Lexer`, `Parser` and
`Syntax.Raw`; `Fixity`; `Syntax`, `Types`, `Env` and `Elab`; `Encode`,
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
- **Keywords** are `module where open using hiding data class instance
  infixl infixr infix case of if then else let in by calc Type forall exists
  fun with`. Tactic
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
| module header | `module Logic.FOL where` |
| namespace opening | `open List` (the `using (…)` and `hiding (…)` forms parse, and are not enforced yet) |
| data type | `data Term r f v = FVar v \| BVar nat \| App (f (Formula r f v) (Term r f v))` |
| fixity | `infixr 4 <>`, `infixl 6.5 +++`, `infix 9/2 ~~` |
| signature | `name : type` |
| clause | `lhs = rhs` |
| class | `class Semigroup a => Monoid a where`, and the signatures of its methods |
| instance | `instance Monoid Nat where`, and the clauses of its methods |

A constructor is a name applied to the types of its fields, `Neg t`, or two
types around a constructor operator, `t :+ t`; as in Haskell, a constructor
operator starts with `:`.

A signature whose type ends in a proposition declares a **theorem**; any other
declares a **function**. The clauses following it define it; a clause's left
side may be prefix, `(<>) Nil ys`, or infix, `Nil <> ys`.

## Namespaces and names

Namespaces follow Rust: `data T` opens the namespace `T`, holding its
constructors; a function `f` opens the namespace `f`, holding the lemmas
generated for it, `f.unfold-C` and Lean's `f.eq_i`. `open T` brings a
namespace's members into unqualified scope, as in Agda.

An unqualified name resolves, in order, as a local variable, a top-level name
of the module, a member of an opened namespace, and then a constructor — of
the type expected there, which is how `Nil` means `List.Nil` in the example
without any `open`, or the only constructor of that name. Anything else is an
ambiguity error listing the candidates.

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

A class has one parameter, methods and laws. Its methods are first-order
signatures, each mentioning the parameter. Its laws are statements over
values of the parameter and of types over it:

```
class Pointed a where
  zero : a
  plus : a -> a -> a
  plus-zero : (x : a) -> plus x zero ≡ x
```

Its superclasses constrain the same parameter. A method or a law is a
top-level name, as in Haskell, and a member of its class's namespace.

An instance is for a data type applied to distinct type variables, or for
`Nat`. It is the only instance of its class for that type; it comes after an
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

A use of a method is resolved once the types of its declaration are known:
it is the function of the instance of its class for the type it is used at.
`2 <> 3` is `Semigroup-Nat.(<>) 2 3`, and `mempty <> xs`, at `List Nat`,
is `Semigroup-List.(<>) Monoid-List.mempty xs`.

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

## Types

Types are `Nat` (also `nat`), data types applied to types, type parameters
(possibly higher-kinded, `f` in `Term r f v` has kind `Type -> Type -> Type`,
inferred from use) and function types. Polymorphism is rank 1, as in
Hindley–Milner: a signature's free type variables are its implicit
parameters, in order, and implicit binders `{a : Type}` may also be written in
front.

Values are first-order. A field of a data type, a value a theorem quantifies
over, and a function's arguments and result have types without arrows, and a
function or a constructor is always applied to all its arguments; an arrow
stands only at the top of a function's signature. The encoding gives a
meaning to first-order values only (see [elaboration.md](elaboration.md),
§ Statements and their adequacy). Types guide elaboration only: the core
never sees them, except through the membership predicates of data types.

## Propositions

`s ≡ t` (also `=`), `s ≠ t`, `s < t`, `s ≤ t`, `s > t`, `s ≥ t` (on `Nat`),
`⊤`, `⊥`, `¬ A`, `A ∧ B`, `A ∨ B`, `A → B`, `A ↔ B`, and the bounded
quantifiers `∀ i < t, A` and `∃ i < t, A` (also `≤ t`; `.` followed by a
space may replace the comma).

Relations bind looser than every term operator, whatever its declared
precedence, so `xs <> Nil ≡ xs` needs no parentheses; connectives take
Lean's precedences, `¬` 40, `∧` 35 and `∨` 30 to the right, `↔` 20; the
arrow binds loosest.

A theorem may quantify over values only in front, `(xs : List a) -> …` or
`∀ (xs : List a), …`: its statement is Π₁, as PRA's theorems are. A
quantifier elsewhere must be bounded. Σ₁ statements, `∃ y, A` at the top,
proved by a witness term, are planned (see below).

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
constructor is the induction hypothesis there. A right side is a proof term
— a lemma or a hypothesis, `cong e`, `rfl` — a `calc`, or `by` tactics.

**By calculation.** `calc t₀ = t₁ := p₁ … = tₙ := pₙ` proves `t₀ = tₙ`; an
omitted justification is `rfl`.

**By tactics** (Lean 4 style, with Rocq's spellings accepted). A tactic acts
on the first goal; newlines and `;` sequence; `{ … }` and `· …` focus the first
goal and must close it, so `induction xs { … } { … }` solves the cases in
turn. The engine translates, so far: `rfl` (`refl`, `reflexivity`), `exact`,
`cong` (`congr`), `calc`, `induction x`, `intro`/`intros` (naming what a case
introduces: the constructor's fields, then the induction hypotheses, `IH` by
default, `IH1 …` when there are several), `assumption`, `sorry` (`admit`),
focused blocks, and a bare proof term, `by IH`, which closes the goal by the
term or else by congruence. The grammar also accepts `apply`, `rw [e, ← e'] at
h`, `unfold`, `simp only`, `constructor`, `left`, `right`, `exfalso`,
`contradiction`, `cases`, `obtain`, `exists`/`use`, `have`, `show`, `revert`,
`clear`, `by_cases`, `try`, `repeat`, `first`, `all_goals`, `any_goals`, `<;>`
and `case`; their translations are the next step of the engine.

`rfl` is *surface* definitional equality: the sides are rewritten by the
unfolding lemmas wherever a function meets a constructor, then compared,
the core's definitional equality taking only what is left.

A lemma applies at any arguments of its types: `app-nil (rev xs)` proves
`app (rev xs) Nil ≡ rev xs`. A value of a data type the lemma quantifies over
must be a member of that type. For an argument built from constructors and
functions this follows from their introduction and closure lemmas, generated
for every constructor and for every function whose result is of a data type.

## Tooling

- `praxis check [--dump-core] FILE.px…` checks modules and prints every
  report; `--dump-core` prints the core text generated — the definitions,
  and every declaration handed to the kernel — for inspection.
- `praxis-lsp` serves `.px` documents with the driver's diagnostics.
- `editors/vscode` highlights `.px` and starts the server.

## Scope of the current implementation

Implemented: the whole grammar above; data types, including higher-kinded
parameters and nested and mutually referring types; functions matching on one
argument, each constructor once, structurally recursive with unchanged other
arguments; classes with superclasses, and their instances for data types and
`Nat`, each use of a method resolved at the type it is used at; functions
and theorems under constraints, schemas and rules over the methods they use;
laws of classes, proved by each instance and premises of the theorems under
the class; theorems by clauses on one value, by `calc`, and by the tactics
listed, a lemma applying at any arguments through the closure lemmas of
functions; `.px` diagnostics. Planned, in order: instances with contexts;
goal display in hover, the
remaining tactic translations, Σ₁ statements with witness terms, `case` and
`if` in terms, nested patterns and matching on several arguments, matching
and recursion on `Nat`, overlapping first-match clauses, mutual recursion and
accumulating parameters, full (not only shape) membership predicates for
nested and higher-kinded types, and list-literal sugar.
