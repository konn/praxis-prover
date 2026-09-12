# Changelog for `praxis-lsp`

All notable changes to this project will be documented in this file.

## Unreleased

### Added

- The language server.
- A VS Code extension, in `editors/vscode` of the repository, which
  highlights `.pra` and `.prf` files and runs the server for them.

### Changed

- A declaration whose proof fails, or ends in `sorry`, is still a lemma for
  the declarations after it, by its statement, so an appeal to it is checked
  rather than reported as unknown.

### Fixed

- The notifications `workspace/didChangeConfiguration`, `$/setTrace` and
  `workspace/didChangeWatchedFiles`, which VS Code sends, are accepted
  rather than reported as unhandled.
