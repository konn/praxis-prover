# Design documents

praxis is a finitistic prover: its trusted core is Primitive Recursive
Arithmetic, and everything a user writes is translated into it and checked
by it. These documents describe the design, from the bottom up.

| document | what it covers |
|---|---|
| [kernel.md](kernel.md) | the trusted core: terms, formulas and sequents of quantifier-free PRA, the inference rules, definitional equality, the checker, and exactly what is trusted |
| [logical-review.md](logical-review.md) | adversarial mathematical review: repaired defects, remaining findings, the conservativity argument and its limits, and implementation uniformity |
| [pra-and-prf.md](pra-and-prf.md) | the core's two languages: `prf` definitions by equations (schemas, variadic schemas, closure conversion) and `pra` statements and tactics (derived rules, lemma appeals, certification, reflection, the lemma library) |
| [surface.md](surface.md) | the surface language `.px`: syntax, layout, namespaces, types, propositions, the three proof styles, tooling, and the scope of the implementation |
| [packages.md](packages.md) | packages, projects and modules: `package.toml` and `project.toml`, libraries and sublibraries, versions and constraints, files and nested modules, imports and openings, the renamer and canonical names, `praxis check` over projects |
| [elaboration.md](elaboration.md) | how the surface language becomes core definitions and certified theorems: the encoding of data types, the compilation of functions, the generated lemmas, the translation of statements and the argument that it is adequate, the translation of proofs, and the invariants that keep it sound and fast |

The packages map onto the layers:

- `praxis-core` — the kernel, `prf`, `pra`, the tactic engine, the lemma
  library, and their quasiquoters;
- `praxis` — the surface language, its packages and projects, and its checker,
  `praxis check`;
- `praxis-lsp` — a language server for `.px`, `.pra` and `.prf` files:
  diagnostics, semantic highlighting and go to definition, with the VS Code
  extension in `editors/vscode`.

A reader new to the code base might read [kernel.md](kernel.md) for the
calculus and its trust model, skim [pra-and-prf.md](pra-and-prf.md), and then
read [surface.md](surface.md) and [elaboration.md](elaboration.md) together
with `praxis/test/data/list.px` and its generated core text,
`praxis check --dump-core praxis/test/data/list.px`.
