# Changelog for `praxis`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## Unreleased

### Added

- A kernel-certified `base` Surface package with natural arithmetic and
  ordering, inductive and bounded finite ordinals, lists and length-indexed
  vectors. CI certifies the library and a separate importing package.
- Checked local `have` facts, congruence using multiple equalities, and erased
  GADT index transport justified by equality proofs. Vector append exposes
  the conventional result length `n + m` using a commutativity proof.
- A hierarchical module system in the Agda style: one top-level module per
  file named by its path, nested `module N where`, `import ["lib"] M [as N]`
  with `using`, `hiding` and `renaming`, `open N [public]`, `open import`,
  and `private` blocks; a renamer pass, `Language.Praxis.Surface.Rename`,
  resolves scope before elaboration and writes every global by its canonical
  name, headed by its library.
- Packages and projects: `package.toml` with a `[package]` header and
  `[[lib]]` sections (the main library unnamed, sublibraries named, component
  paths `pkg:lib:name`), PVP versions and Cabal-syntax ranges; `project.toml`
  listing packages and the project-wide constraints on versions;
  `Language.Praxis.Package.{Version,Manifest,Build}`.
- `praxis check` over projects, packages, directories and files, the latter
  as modules of the package enclosing them, or `--alone`.

## 0.1.0.0 - YYYY-MM-DD
