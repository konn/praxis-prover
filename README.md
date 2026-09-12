# Praxis Prover - Finitistic Theorem Prover based on Primitive Recursive Arithmetic

This is my personal experiment of implementing a finitistic (interactive) theorem prover based on Primitive Recursive Arithmetic (*PRA*).
The usage includes, well, development of finitistic mathematics, but the main motivation is to provide a convenient tool for mechanising relative consistency proofs with small finitistic core.

## Packages

- `praxis-core`: the calculus, the primitive-recursive function language `prf`, the tactic language `pra` and their quasiquoters.
- `praxis-lsp`: a language server for `.pra` and `.prf` files, checking them as they are edited and showing the goal under the cursor; `editors/vscode` is the VS Code extension which runs it.
- `praxis`: the user-facing layer, to come.

## Design Goal

- Surface Language: finitistic, but a rich interactive theorem prover with inductive types and primitive recursion.
- Core Language: Bare Primitive Recursive Arithmetic.
  + We are considering sequent calclus and/or optimised Hilbert-style combinator calculus as a deduction system.

## Copyright

(c) Hiromi ISHII 2026- present
