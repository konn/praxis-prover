# Changelog for `praxis-lsp`

All notable changes to this project will be documented in this file.

## Unreleased

### Added

- Semantic tokens (`textDocument/semanticTokens/full`): in a `.px` document
  every name is a token of what it is — a data type, a constructor, a
  function or theorem, a class, a method, a module or instance, a type
  variable, a value parameter, a variable, a builtin or a lemma of the
  library — and the words of the tactic language are keywords in tactic
  position only; in `.pra` and `.prf` documents, the theorems, rules and
  definitions declared, and the names appealing to them.
- Go to definition (`textDocument/definition`): from a name of a `.px`
  document to its declaration, in the document or in the file of the module
  it imports, an import or an opening to the module's header, and a lemma
  generated for a function to the function; from an appeal in a `.pra` or
  `.prf` document to the declaration it names. `analyseDocument`,
  `definitionsAt` and `semanticTokensOf` are the API.
- Positions are converted between the checkers' columns, which expand tabs,
  and the protocol's UTF-16 units.
- A `.px` document is checked as a module of the package enclosing it, its
  imports resolved and the modules it imports checked first (`analyseIn`).

- The language server.
- A VS Code extension, in `editors/vscode` of the repository, which
  highlights `.pra` and `.prf` files and runs the server for them.
- The unfolding lemmas of `builtin` are in scope in a `.pra` document:
  `exact add_S`, `rewrite sub_S in H1`, `cong sub_S`.
- The lemmas of the library of praxis-core, `src-pra/lemmas.pra` as
  `Language.Praxis.PRA.Library` certifies it, are in scope in a `.pra`
  document, so it appeals to them, `exact belowIntro`, and `reflect` and
  `reify` find the reflection lemmas; a declaration of a name the library
  also declares is the document's own: the library's lemma of that name is
  out of scope throughout the document.

### Changed

- A declaration whose proof fails, or ends in `sorry`, is still a lemma for
  the declarations after it, by its statement, so an appeal to it is checked
  rather than reported as unknown.

### Fixed

- The notifications `workspace/didChangeConfiguration`, `$/setTrace` and
  `workspace/didChangeWatchedFiles`, which VS Code sends, are accepted
  rather than reported as unhandled.
