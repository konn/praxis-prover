# praxis-core

## Defining primitive-recursive functions

Enable `QuasiQuotes` and import
`Language.Praxis.PRA.PrimitiveRecursion.Quote`:

```haskell
[prf|
  environment arithmetic

  add n 0 = n
  add n (S m) = S (add n m)

  mul n 0 = 0
  mul n (S m) =
    add n
        (mul n m)
|]
```

This generates `add, mul :: Function 2` and `arithmetic :: Signature`.
The functions are references with identities qualified by package and module.
The signature holds the precompiled definition table. Parsing, arity checking,
coverage, overlap, and primitive-recursion checking happen at compile time.
The table's closure and acyclicity are also validated when first demanded;
there is no runtime equation parsing or elaboration.

The header is optional. A headerless block generates `addSignature` and
`mulSignature`, both aliases of one shared signature for the complete block.

The existing `parseEquations` accepts the same equation layout. The first
equation establishes the block indentation: aligned lines start equations and
deeper lines continue them. Blank lines and comments are ignored; parentheses
suspend layout. Explicit semicolons are supported, and `{ ... }` blocks require
semicolons and ignore indentation. This is an applicative PRF language, not a
full Haskell parser: overlapping equations, partial applications, and arbitrary
Haskell expressions are unsupported. Self recursion must use the immediate
predecessor in one argument and keep all other parameters unchanged.

## Shared calls and evaluation

`PrimitiveRecursion.Code` contains the unchanged bare `PRFCode` language.
`PrimitiveRecursion.Function` adds `Function n`, `Program n`, and `KernelEnv`.
A function is a raw `Primitive code`, a `Defined (DefId ...)` reference, or an
`Inline program` residual produced during partial evaluation. Programs retain
named calls under composition and primitive recursion. Neither constructing a
term nor evaluating one expands the complete dependency tree.

```haskell
import Data.Sized (pattern Nil, pattern (:<))
import Language.Praxis.PRA.Equality
import Language.Praxis.PRA.PrimitiveRecursion.Function
import Language.Praxis.PRA.Signature
import Language.Praxis.PRA.Syntax
import Numeric.Natural (Natural)

example :: Either KernelError Natural
example = do
  env <- signatureKernelEnv arithmetic
  evalTermIn env (const 0) (App mul (Lit 3 :< Lit 4 :< Nil))
-- Right 12
```

`App` is the general application node. The existing `code :$ args` spelling
remains a pattern synonym for `App (Primitive code) args`. Parsing a named term
through a signature constructs `App (Defined ...) args`, not a copy of its body.
Term equality and hashing compare definition identities without evaluating them.

Use `evalFunction env`, `evalTermIn env`, `normalizeIn env fuel`, and
`defEqIn env fuel` for named definitions. Partial evaluation retains references
when it runs out of fuel; missing references and wrong arities report errors.
The older environment-free operations remain available for bare-code clients.
`eraseFunction env` explicitly converts a shared function into bare `PRFCode`
when an expanded representation is wanted.

`KernelEnv` has a private constructor. `extendKernelEnv` checks duplicates,
reference arities, missing definitions, and the entire call graph. All call
cycles are rejected, including self calls: valid source self recursion becomes
the finite `Rec` constructor. This validation inspects references without
following them into another body. Merging signatures with conflicting identities
is reported by `signatureKernelEnv`, rather than silently changing meanings.

Proof conversion uses only the PRA evaluator and its checked definition table.
`inferConclusionIn env`, `inferConclusionOpenIn env`, and `proveOpenIn env`
support shared definitions. `praQuoter` automatically uses its signature's
environment. There is no native executable backend in the proof-checking path.

## Growing an environment

Successive declaration quotes can explicitly extend earlier snapshots in the
same Haskell module:

```haskell
[prf|
  environment basic
  add n 0 = n
  add n (S m) = S (add n m)
|]

[prf|
  environment arithmetic extends basic
  mul n 0 = 0
  mul n (S m) = add n (mul n m)
|]
```

The parent remains unchanged. A block adds complete definitions; it cannot add
clauses to a previously compiled function. Forward references are allowed
within a block, but references to later blocks and mutual recursion are rejected.
The private Template Haskell registry stores completed snapshots and is local
to the module. No intervening declaration splice is required.

For another module, export the generated signature and define configured
quoters in a support module:

```haskell
module ArithmeticQuotes (arithmeticPRF, arithmeticProof) where

import ArithmeticDefinitions (arithmetic)
import Language.Praxis.PRA.PrimitiveRecursion.Quote (prfQuoter)
import Language.Praxis.PRA.Tactic.Quote (praQuoter)

arithmeticPRF = prfQuoter arithmetic
arithmeticProof = praQuoter arithmetic
```

Import these quoters into their consumer module, respecting Template Haskell's
staging restriction. They can use the exported functions without reconstructing
their definitions from Haskell types. Generated function references record
qualified Haskell names, so consumer imports need not be unqualified.

The library's own signature is `builtin`, exported by
`Language.Praxis.PRA.PrimitiveRecursion` together with `add`, `mul`, `pow`,
`sub`, `lt`, `le`, `ifte`, the bounded search `mu` and the rest of its arithmetic.
`Language.Praxis.PRA.Tactic.Quote` exports `pra = praQuoter builtin`, so proofs
over that arithmetic need no support module of their own.

A declaration is a lemma for the declarations after it, in the same quote or
in a later quote of the same module: `exact name` appeals to it, with its
metavariables inferred from the goal or given as arguments, its free variables
instantiated, the hypotheses it does not mention weakened in, and its premises
left as goals for the blocks which follow.

To appeal to them from another module, open a quote with `library name`: the
quasiquoter then also binds `name :: Library`, the lemmas in scope at the end
of the quote, and a support module defines a quasiquoter over it, as for a
signature:

```haskell
module Arithmetic.Lemmas (basics, plusZeroRight, …) where
[pra|
library basics
theorem plusZeroRight : |- y + 0 = y
by …
|]

module Arithmetic.Quotes (arithmeticProof) where
import Arithmetic.Lemmas (basics)
arithmeticProof = praQuoterIn basics
```

The bindings a library refers to must be exported. A quote of
`arithmeticProof` may open a library of its own, which extends `basics`. A
file of declarations is spliced the same way with `praFile "Lemmas.pra"`,
`prfFile "Definitions.prf"` or `quoteFile arithmeticProof "More.pra"`; the
path is relative to the package directory, and the module is recompiled when
the file changes.

The hypotheses of a goal are named, `H1`, `H2`, … in the order written and a
context metavariable by its own name, and a `sorry` report lists them so. A
step which introduces hypotheses numbers them on, or names them as told:
`Cut (a = 0) as H`, `ConjL as HA HB`, `induction t as n IH H'`. `symmetry H1`,
`rewrite H1 in H2` and `exact H2` refer to hypotheses by name, and `ImplL on
H2` picks the hypothesis a rule acts on where several have the right shape.

`cong H2` closes an equation whose right side is the left with one side of
`H2` replaced by the other, under any function symbols; `cong` alone tries
every hypothesis.

`have H: (A) { … }` proves `A` in its block and goes on with `A` as the
hypothesis `H`, a `Cut` whose second branch is the rest of the script; with
no name given, the hypothesis is `H`, or the next `H<n>` when `H` is taken.

An equation may be proved as a calculation, one step per line, each by its
own tactic or by `refl` when definitional:

```haskell
[pra|
theorem twiceZero : |- (y + 0) + 0 = y
by calc (y + 0) + 0
     = y + 0 by exact plusZeroRight
     = y by exact plusZeroRight
|]
```

```haskell
[pra|
theorem succSubSucc : |- S n - S m = n - m
by induction m
   { Defeq (S n - 1) (n - 0); Id }
   { Defeq (S n - S (S m')) (prd (S n - S m'))
   ; rewrite (S n - S m' = n - m') in (S n - S (S m') = prd (S n - S m'))
   ; Defeq (prd (n - m')) (n - S m')
   ; rewrite (prd (n - m') = n - S m') in (S n - S (S m') = prd (n - m'))
   ; Id }

theorem succSubSuccAt : x = 0 |- S 3 - S x = 3 - x
by exact succSubSucc
|]
```

A comparison may stand alone as an atom: `t < S t` is `(t < S t) = 1`, as
are `x <= y` and `x == y` with their symbols, and a goal or a hypothesis of
that shape is shown so.

A lemma cut in serves a congruence step of a calculation:

```haskell
[pra|
theorem ltSucc : |- t < S t
by induction t as n
   { refl }
   { Cut (S (S n) - S n = S n - n)
     { exact succSubSucc }
     { calc (S n < S (S n))
         = sgn (S (S n) - S n)
         = sgn (S n - n) by cong H2
         = (n < S n)
         = 1 by exact H1 }
   }
|]
```

For non-TH use, `PrimitiveRecursion.Environment` provides `compileDefinitions`,
`compileDefinitionsWith` (qualified identities), and `extendEnvironment`.
Compiled blocks retain equation rows, case trees, and the recursion argument
alongside the shared programs for subsequent unfolding-lemma work. This is
compilation evidence, not a generated proof of the defining equations.

## Copyright

2026-present (c) Hiromi ISHII
