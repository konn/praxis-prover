# Praxis base

`base` is the Surface Language standard library. Its source declarations and
proofs are checked by the same PRA kernel as client modules; it adds no axioms.
The package is distributed with the Haskell `praxis` package as data files.

From the repository root, certify every module with:

```sh
cabal run praxis -- check praxis/data/libraries/base
```

CI runs that command explicitly. The Haskell package tests also certify a
separate client package importing all the modules and using their operations
and proofs (`praxis/test/data/base`).

## Using the library

Include this directory and your package in a Surface project:

```toml
[project]
packages = ["path/to/praxis/data/libraries/base", "my-package"]
```

In your package's `package.toml`, declare the dependency:

```toml
[package]
name = "my-package"
version = "0.1.0.0"

[lib]
source-dir = "src"
dependencies = ["base ^>= 0.1"]
```

Import the modules you need. Qualified imports avoid collisions among names
such as `length`, `replicate`, and `reverse`:

```text
module Example where
import "base" Data.Nat as N
import "base" Data.List as L
open N using ((/), (%), (^^))

reverse-twice : (xs : L.List a) -> L.reverse (L.reverse xs) = xs
reverse-twice xs = L.reverse-reverse xs
```

## Modules

| Module | Contents |
| --- | --- |
| `Data.Nat` | Builtin natural arithmetic laws; exponentiation `^^`; total quotient `/` and remainder `%`, with division algorithm and remainder bound |
| `Data.Nat.Order` | Builtin linear ordering laws; addition and multiplication monotonicity; inductive `PLt`/`PLeq` and gap-based `ELt`/`ELeq`, with both round-trip laws and conversions to and from builtin comparisons |
| `Data.Fin` | Inductive `Fin n` and bounded-natural `EFin n`, conversions and both inverse laws, bounds, weakening and ordinal reversal |
| `Data.List` | `Nil`, `(::)`, `(<>)`, map, length, replication, reversal, take/drop, concatenation, sum/product, class-schema fold and algebraic proofs |
| `Data.Vec` | Length-indexed `Vec n a`, head/tail, map, bounded take, replication, lookup/tabulate with inverse laws, reversal, append and list conversions |

Natural subtraction is truncated: `n - m = 0` when `m` exceeds `n`.
Division is total, with `n / 0 = 0` and `n % 0 = n`. For every divisor,
`d * (n / d) + n % d = n`; for positive divisors, `n % d < d`.
Exponentiation is right associative, with `n ^^ 0 = 1`, including `0 ^^ 0`.
Addition, multiplication, subtraction, `<`, and `<=` use the builtin natural
operations; the library provides their Surface proofs.

`Fin` uses `FZero` and `FSucc`. `EFin` uses `Mk : (k : Nat) -> k < n -> EFin n`.
`to-efin` and `from-efin` preserve the ordinal; `from-to-efin` and
`to-from-efin` prove equality after both round trips. The proofs compare the
values themselves, not just their projections to natural numbers.

`Vec` puts the length first: `Vec n a`. Its `append` returns `Vec (n + m) a`
for arguments of lengths `n` and `m`. The implementation uses `cast` with a
checked commutativity proof to transport its length index; transport preserves
the entries and is erased at runtime. `length-append` proves the corresponding
length equation. `SomeVec a` packs a vector with its length, and the list
conversions have inverse laws.

`Data.List.fold` uses the fixed methods of `Folding a`; the `Monoid a`
subclass supplies checked identity and associativity laws. Lists have an
instance, with `fold-concat` proving that folding a list of lists is `concat`.

Both `Data.List.map` and `Data.Vec.map` take a fixed function argument. Their
identity and composition laws are proved; list mapping also preserves
concatenation, length, and flattening.

`Data.Vec.tabulate : {n : Nat} -> (Fin n -> a) -> Vec n a` constructs the vector
of a function's values in ordinal order. Together with `lookup`, it gives the
finite function/vector isomorphism: `lookup-tabulate` proves
`lookup i (tabulate f) = f i`, and `tabulate-lookup` proves
`tabulate (\i -> lookup i xs) = xs`. The function-side inverse is pointwise,
so no function-extensionality axiom is needed. The empty case constructs `Nil`
without calling the function or requiring a default element of `a`.

Function arguments compile to fixed PRA schemas. Recursion can apply the
callback and pass it unchanged; it cannot recurse on the callback or change
it at a recursive call. Lambdas may capture values in scope, as the vector
round-trip example does. Callbacks take and return ordinary values; they
are not stored in data fields or passed to other callbacks.

Every declared callback must be used somewhere in its function's definition.
Base cases need not apply it; empty lists and zero-length vectors use no
callback results.
