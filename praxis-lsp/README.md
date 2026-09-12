# praxis-lsp

A language server for the files of praxis: `.pra` files of theorems and
rules, as `praFile` splices them, and `.prf` files of definitions, as
`prfFile` does.

It speaks the Language Server Protocol over standard input and output:

```bash
cabal run praxis-lsp
```

A `.pra` document is read over the `builtin` signature, with the unfolding
lemmas of `builtin` in scope and each declaration a lemma for those after it,
as the quasiquoter reads it. Every declaration is checked as it is edited: a
tactic which fails is an error at its position,
and a `sorry` an information diagnostic listing the goal it stopped at, with
the hypotheses by name. Hovering over a tactic shows the goal it faces, found
by running the proof with that tactic replaced by `sorry`. A `.prf` document
is checked as the quasiquoter checks it, over the empty signature.

## Editors

The server is not tied to an editor. Point a generic client at the built
executable for the two extensions; for example, in Neovim:

```lua
vim.filetype.add { extension = { pra = "praxis-pra", prf = "praxis-prf" } }
vim.api.nvim_create_autocmd("FileType", {
  pattern = { "praxis-pra", "praxis-prf" },
  callback = function()
    vim.lsp.start { name = "praxis", cmd = { "praxis-lsp" }, root_dir = vim.fs.root(0, { "cabal.project" }) }
  end,
})
```

In VS Code, the extension in `editors/vscode` of the repository highlights
both kinds of file and starts the server for them:

```bash
cabal install praxis-lsp
cd editors/vscode && npm install && npx @vscode/vsce package
code --install-extension praxis-0.1.0.vsix
```

Its setting `praxis.server.path` names the server when it is not on the
path, such as the executable `cabal list-bin praxis-lsp` prints.
