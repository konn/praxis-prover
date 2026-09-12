# Changelog for `praxis-lsp`

All notable changes to this project will be documented in this file.

## Unreleased

### Added

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
