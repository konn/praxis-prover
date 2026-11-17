#!/usr/bin/env bash
set -euo pipefail

# Match Hometrics: ghc-wasm-meta supplies SDK tools; ghcup owns the compiler.
version=9.12.4.20260402
if command -v "wasm32-wasi-ghc-$version" >/dev/null 2>&1; then
  "wasm32-wasi-ghc-$version" --version
  exit 0
fi

curl --proto '=https' --tlsv1.2 --silent --show-error --fail \
  https://gitlab.haskell.org/haskell-wasm/ghc-wasm-meta/-/raw/master/bootstrap.sh \
  | SKIP_GHC=1 sh
# shellcheck source=/dev/null
source "$HOME/.ghc-wasm/env"
ghcup config add-release-channel \
  https://gitlab.haskell.org/haskell-wasm/ghc-wasm-meta/-/raw/master/ghcup-wasm-0.0.9.yaml
# CONFIGURE_ARGS is intentionally word-split, as specified by ghc-wasm-meta.
# shellcheck disable=SC2086
ghcup install ghc "wasm32-wasi-$version" -- ${CONFIGURE_ARGS:-}
