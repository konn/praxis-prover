# Repository Guidelines

## Project Structure & Module Organization

Praxis is a Cabal multi-package Haskell project. `praxis-core/` contains primitive-recursive arithmetic syntax, proofs, and utilities under `src/Language/Praxis/PRA/` and `src/Data/`. The higher-level `praxis/` package is the user-facing layer. Each package keeps executables in `app/` and tests in `test/`; `praxis-core/doctest/` runs documentation examples. Shared build configuration lives in `cabal.project`, while CI support is under `.github/workflows/` and `ci/scripts/`. Do not commit generated `dist-newstyle/` content.

## Build, Test, and Development Commands

- `cabal build praxis-core` and `cabal build praxis` build each package.
- `cabal test praxis-core` and `cabal test praxis` run package tests, including core doctests.
- `cabal run praxis` or `cabal run praxis-core` launches an executable.
- `fourmolu --mode inplace <file.hs>` formats changed Haskell files using `fourmolu.yaml`.
- `bash ci/scripts/cabal-check-packages.sh` performs the package checks used by CI.

Use the root `cabal.project`; CI currently exercises GHC 9.10.3 with Cabal 3.10.x.

## Coding Style & Naming Conventions

Follow GHC2024 and the warnings configured in each `.cabal` file. Fourmolu uses two-space indentation, leading commas, and spaced record braces. Name modules in `Upper.Camel.Case`, types and constructors in `UpperCamelCase`, and functions and values in `lowerCamelCase`. Keep exports explicit and place modules beneath a directory matching their namespace. Prefer `(<>)` over `(++)`, including for lists and strings.

## Testing Guidelines

Add focused tests to the owning package's `test/` tree and Haddock examples where they clarify public APIs. Test entry points are named `Test.hs`; give supporting modules descriptive names. The conventional test suites are currently placeholders, so new behavior should arrive with meaningful assertions. No coverage threshold is configured. Run both package tests before opening a pull request.

## Commit & Pull Request Guidelines

Use Conventional Commits with a short, imperative description, such as `feat(core): add induction rules` or `fix(parser): reject empty terms`. Keep commits focused and append an appropriate `Co-authored-by: Name <email>` trailer. Never add a `Codex-Session:` trailer, session URL, or other internal metadata. Pull requests should explain the motivation and implementation, identify affected packages, link relevant issues, and report build, test, and formatting results.

## Agent-Specific Instructions

Use the `/haskell` skill from [`konn/haskell-claude-marketplace`](https://github.com/konn/haskell-claude-marketplace) for Haskell source, Cabal, build, and test work. Keep its `/haskell-format` and `/haskell-cabal-gild` on-save hooks enabled; consult HLS before package-scoped builds and local Haddock or Hoogle for APIs. Do not run `git add`, `git commit`, or `git push` unless explicitly requested. If `package.yaml` is introduced or changed, run `hpack` to regenerate the Cabal file.
