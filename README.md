# Praxis Prover - Finitistic Theorem Prover based on Primitive Recursive Arithmetic

This is my personal experiment of implementing a finitistic (interactive) theorem prover based on Primitive Recursive Arithmetic (*PRA*).
The usage includes, well, development of finitistic mathematics, but the main motivation is to provide a convenient tool for mechanising relative consistency proofs with small finitistic core.

## Packages

- `praxis-core`: the PRA kernel, the primitive-recursive definition language `prf`, the proof language `pra` and their quasiquoters.
- `praxis`: Praxis Surface, `.px` — Agda/Haskell-like modules of data types, functions by pattern matching and theorems proved by clauses, calculations or tactics — and its explicit typed intermediate language, Praxis Core. Declarations are lowered to the PRA kernel language and certified by the PRA kernel. The package also provides packages and projects of modules, `package.toml` and `project.toml`, and its checker, `praxis check`.
- `praxis-lsp`: a language server for `.px`, `.pra` and `.prf` files, checking them as they are edited, highlighting their names by what they are, going to definitions, and showing the goal under the cursor in `.pra` files; `editors/vscode` is the VS Code extension which runs it.

The design is documented in [`docs/`](docs/README.md): Praxis Surface, Praxis Core, the PRA kernel language, and the elaboration and compilation between them.

## Design Goal

- Praxis Surface: a rich finitistic interactive theorem prover with inductive types and primitive recursion.
- Praxis Core: an explicit typed intermediate language after elaboration and desugaring, before arithmetic encoding.
- PRA kernel language: primitive-recursive definitions and arithmetic proofs, checked by the trusted PRA kernel.

## Copyright

(c) Hiromi ISHII 2026- present
