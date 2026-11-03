# praxis

The Surface Language compiler and checker for Praxis. Surface declarations
elaborate into Praxis Core, the explicit typed intermediate language, then
lower to CoPRA, the internal PRA kernel language provided by `praxis-copra`.
The PRA kernel checks the resulting definitions and proofs. The bundled
[`base` library](data/libraries/base/README.md) provides natural arithmetic
and order, finite ordinals, lists, and length-indexed vectors with checked
proofs.

From the repository root:

```sh
cabal run praxis -- check praxis/data/libraries/base
```

The [`logic` example](data/libraries/logic/README.md) proves Glivenko's
theorem for implication and bottom, with a verified proof transformation
and a shared-tree evaluator for running it on a classical Peirce proof:

```sh
cabal run praxis -- eval praxis/data/libraries/logic/src/Logic/Glivenko.px \
  --entry Logic.Glivenko.demo --nat 0 --nat 1
```

## Copyright

(c) Hiromi ISHII 2026- present
