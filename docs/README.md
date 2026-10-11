# Design documents

Praxis is a finitistic prover. Praxis Surface elaborates into Praxis Core,
an explicit typed intermediate language. Compilation then produces CoPRA, the PRA
kernel language: primitive-recursive definitions and arithmetic proofs checked
by the trusted PRA kernel. CoPRA is an internal codename; Praxis remains the
user-facing name. These documents describe the design, from the bottom up.

```text
Praxis Surface --elaboration/desugaring--> Praxis Core
              --arithmetic encoding/proof generation--> CoPRA
              --PRA kernel checking--> verdict
```

`BUILTIN` pragmas configure surface elaboration. Syntax that depends on them
must be desugared before the Praxis Core boundary; the intermediate language
does not perform builtin lookup or instance search. The PRA kernel validates
the generated proofs independently of those surface registrations.

| document | what it covers |
|---|---|
| [kernel.md](kernel.md) | the PRA kernel: terms, formulas and sequents of quantifier-free PRA, the inference rules, definitional equality, the checker, and exactly what is trusted |
| [logical-review.md](logical-review.md) | adversarial mathematical review: repaired defects, remaining findings, the conservativity argument and its limits, and implementation uniformity |
| [pra-and-prf.md](pra-and-prf.md) | CoPRA, the PRA kernel language, and its frontends: `prf` definitions by equations (schemas, variadic schemas, closure conversion) and `pra` statements and tactics (derived rules, lemma appeals, certification, reflection, the lemma library) |
| [surface.md](surface.md) | the surface language `.px`: syntax, layout, namespaces, types, propositions, the three proof styles, tooling, and the scope of the implementation |
| [packages.md](packages.md) | packages, projects and modules: `package.toml` and `project.toml`, libraries and sublibraries, versions and constraints, files and nested modules, imports and openings, the renamer and canonical names, `praxis check` over projects |
| [explicit-core-plan.md](explicit-core-plan.md) | Praxis Core: the explicit typed intermediate language, its evidence boundary and implemented migration |
| [elaboration.md](elaboration.md) | how Praxis Surface elaborates into Praxis Core and compiles to CoPRA definitions and certified theorems: the encoding of data types, the compilation of functions, the generated lemmas, the translation of statements and the argument that it is adequate, the translation of proofs, and the invariants that keep it sound and fast |

The packages map onto the layers:

- `praxis-copra` — CoPRA (`prf` and `pra`), the PRA kernel, the tactic engine, the lemma
  library, and their quasiquoters;
- `praxis` — Praxis Surface, Praxis Core, their packages and projects, and the checker,
  `praxis check`;
- `praxis-lsp` — a language server for `.px`, `.pra` and `.prf` files:
  diagnostics, semantic highlighting and go to definition, with the VS Code
  extension in `editors/vscode`.

A reader new to the code base might read [kernel.md](kernel.md) for the
calculus and its trust model, skim [pra-and-prf.md](pra-and-prf.md), and then
read [surface.md](surface.md) and [elaboration.md](elaboration.md) together
with `praxis/test/data/list.px` and its generated CoPRA text,
`praxis check --dump-pra praxis/test/data/list.px`.
