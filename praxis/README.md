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

## Copyright

(c) Hiromi ISHII 2026- present
