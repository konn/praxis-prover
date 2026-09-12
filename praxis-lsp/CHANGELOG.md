# Changelog for `praxis-lsp`

All notable changes to this project will be documented in this file.

## Unreleased

### Added

- The language server.

### Changed

- A declaration whose proof fails, or ends in `sorry`, is still a lemma for
  the declarations after it, by its statement, so an appeal to it is checked
  rather than reported as unknown.
