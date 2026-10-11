# Praxis Prover - A Finitistic Theorem Prover Based on Primitive Recursive Arithmetic

Praxis aims to put [Primitive Recursive Arithmetic][PRA] (*PRA*) into practice through a proof assistant with a familiar Agda-style surface language, with applications to metamathematics or mathematical logic in mind.
PRA is widely regarded as formalising finitistic mathematics in the sense of Hilbert’s finitary standpoint, and is considered a suitable metatheory for metamathematics and mathematical logic.
The goal of Praxis is *NOT* to provide a proof assistant for finitist mathematicians; rather, it is meant to help formalise and mechanise metamathematics, especially relative consistency proofs, more safely and conveniently.
There are many powerful and elegant proof assistants, but most of them are based on powerful type systems with consistency strengths far above $\mathrm{PA}$—some lie between $\mathrm{PA}$ and second-order arithmetic, and some even lie above $\mathrm{ZFC} + \exists \text{inaccessible(s)}$. Such systems are too strong to serve as metatheories for metamathematics[^1].
Proof manipulation (in ordinary FOL or HOL, not infinitary logic, of course!) should be intrinsically finitistic.
And if you want to establish translations, conservativity results, or relative consistency between theories, those reductions *should* also be finitistic.
For example, a relative consistency proof $\mathrm{Con}(S) \implies \mathrm{Con}(T)$ should actually establish $T \vdash \bot \implies S \vdash \bot$ by providing a concrete transformation algorithm.
To keep these finitistic manipulations explicit, we insist on a finitistic metatheory; otherwise, the finitistic content may be lost[^2].

[PRA]: https://en.wikipedia.org/wiki/Primitive_recursive_arithmetic

## Key Features

One downside of PRA is that, well, as the name suggests, it is too *primitive* to work in directly: there are only natural numbers and primitive recursive functions, and every mathematical object must be encoded using them!
Encoding every mathematical object this way is already torture for a logician—hence Praxis provides a richly typed language that ultimately compiles down to a PRA kernel.

So Praxis provides the following powerful and rich features:

1. Editor support through the Language Server Protocol.
2. Inductive datatypes, possibly indexed by values of other types (GADTs), allowing proofs or witnesses to be encoded structurally.
3. Equational definitions of primitive recursive functions and proofs over natural numbers and these inductive types.
4. Implicit arguments and typeclasses with laws.
5. $\Pi_1$ propositions and rank-1 polymorphism.
6. Arbitrarily nested bounded and finite-domain quantifiers.
7. Proof-irrelevant proof objects.
8. A tactic language and a calculational proof command to make proofs easier to write.
   - You can still write proofs recursively in an equational form, as in Agda.

To remain within a first-order framework, all values in Praxis must be first-order.
Still, you can define higher-order functions (or function schemas) equationally, provided that function parameters remain fixed during recursion and are not themselves recursed on.
Furthermore, if a function's domain is finite, you can encode it as a finite sequence and pass it around freely.

Values are compared for equality by their codes; any proof objects in a datatype are ignored during computation and equality testing.
These proof objects are treated as side conditions, and the Praxis compiler automatically generates lemmas relating a function's input and output values.

## Showcase

### List operations

```haskell
data List a = Nil | a :: List a

infixr 5 ::
open List public

singleton : a -> List a
singleton x = (x :: Nil)

map : (a -> b) -> List a -> List b
map f Nil = Nil
map f (x :: xs) = f x :: map f xs

(<>) : List a -> List a -> List a
Nil <> ys = ys
(x :: xs) <> ys = x :: (xs <> ys)

map-id : (xs : List a) -> map (\x -> x) xs = xs
map-id Nil = rfl
map-id (x :: xs) = cong (map-id xs)

map-compose : (f : a -> b) -> (g : b -> c) -> (xs : List a) -> map g (map f xs) = map (\x -> g (f x)) xs
map-compose f g Nil = rfl
map-compose f g (x :: xs) = calc
  map g (map f (x :: xs))
  = g (f x) :: map g (map f xs)
  = g (f x) :: map (\y -> g (f y)) xs := cong (map-compose f g xs)
  = map (\y -> g (f y)) (x :: xs)

append-nil : (xs : List a) -> (xs <> Nil) = xs
append-nil Nil = rfl
append-nil (x :: xs) = cong (append-nil xs)

append-assoc : (xs ys zs : List a) -> ((xs <> ys) <> zs) = (xs <> (ys <> zs))
append-assoc Nil ys zs = rfl
append-assoc (x :: xs) ys zs = calc
  (((x :: xs) <> ys) <> zs)
  = (x :: ((xs <> ys) <> zs))
  = (x :: (xs <> (ys <> zs))) := cong (append-assoc xs ys zs)
  = ((x :: xs) <> (ys <> zs))
```

### GADT-based order relations with witnesses

```haskell
-- Inductive (Peano) witnesses for strict order.
data PLt (n : nat) (m : nat) where
  ZeroSucc : {m : nat} -> PLt 0 (S m)
  SuccSucc : {n m : nat} -> PLt n m -> PLt (S n) (S m)

plt-of-lt : {n m : nat} -> n < m -> PLt n m
plt-of-lt {0} {S m} h = ZeroSucc
plt-of-lt {S n} {S m} h = SuccSucc (plt-of-lt h)
plt-of-lt {n} {0} h = absurd h

lt-of-plt : {n m : nat} -> PLt n m -> n < m
lt-of-plt ZeroSucc = rfl
lt-of-plt (SuccSucc p) = lt-of-plt p

-- Existential witnesses store the gap; the equality is a checked premise.
data ELt (n : nat) (m : nat) where
  Gap : (k : nat) -> n + S k = m -> ELt n m

lt-of-elt : {n m : nat} -> ELt n m -> n < m
lt-of-elt (Gap {n} {m} k h) = by
  have bound : n < m := by exact ltOfAdd
  bound

elt-of-lt : {n m : nat} -> n < m -> ELt n m
elt-of-lt {n} {m} h = Gap (m - S n) (calc
  n + S (m - S n)
  = S (n + (m - S n))
  = S n + (m - S n) := by cong succAdd
  = m := by exact ltAddSub)
```

## Packages

- `praxis-copra`: CoPRA, the internal PRA kernel language (`prf` definitions and `pra` proofs), its quasiquoters, and the trusted PRA kernel.
- `praxis`: Praxis Surface, `.px` — Agda/Haskell-like modules of data types, functions defined by pattern matching, and theorems proved by clauses, calculations or tactics — and its explicit typed intermediate language, Praxis Core. Declarations are lowered to CoPRA and certified by the PRA kernel. The package also supports packages and projects of modules through `package.toml` and `project.toml`, and provides the `praxis check` command.
- `praxis-lsp`: a language server for `.px`, `.pra` and `.prf` files. It checks files as they are edited, highlights names by their roles, supports navigation to definitions, and shows the goal under the cursor in `.pra` files. `editors/vscode` contains the VS Code extension that runs it.

The design is documented in [`docs/`](docs/README.md): Praxis Surface, Praxis Core, CoPRA, and the elaboration and compilation between them.

CoPRA is an internal codename; the user-facing system is Praxis. Praxis Core names the separate typed intermediate language. CoPRA keeps the `.prf` and `.pra` file extensions and the `Language.Praxis.PRA` Haskell namespace.

## Design Goals

- Praxis Surface: a rich finitistic interactive theorem prover with inductive types and primitive recursion.
- Praxis Core: an explicit typed intermediate language after elaboration and desugaring, before arithmetic encoding.
- CoPRA: the PRA kernel language of primitive-recursive definitions and arithmetic proofs, checked by the trusted PRA kernel. It formalises PRA over G3i + Cut.

```text
Praxis Surface -[elaborate]-> Praxis Core -[compile]-> CoPRA <- checked by the kernel
```

## Copyright

(c) Hiromi ISHII 2026–present

[^1]: DISCLAIMER: The author himself believes that at least one supercompact cardinal should exist, though.

[^2]: FAQ: "Then, why not System T, HA, or PA?" Well, I would like to explore by hand how weak the metatheory can be, so I chose one at the weak end of the spectrum ;-). FAQ 2: "Why not IΣ₁?" Well, it doesn't offer as many naming puns as PRA does :-). I love ZFC.
