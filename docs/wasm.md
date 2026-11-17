# Surface evaluation in WebAssembly

Praxis can extract a checked Surface function to a Haskell module, compile it
with GHC's `wasm32-wasi` backend, and call it from JavaScript using JSON. The
included single-page application plays Black against the White strategy in
`Game.Othello.FourSolved.white-wins`.

## Build and play

From the repository root, with native GHC 9.12.4, Cabal, ghcup, and Node.js:

```sh
cabal run shake-praxis -- toolchain
cabal run shake-praxis -- browser
python3 -m http.server 8080 --directory _build/browser
```

Open `http://localhost:8080`. The HTTP server only serves static files; game
evaluation happens in a browser Web Worker. The page supports legal-move
markers, automatic White responses, forced passes, undoing a round, restarting,
and terminal scores. Black's placement and flips appear first; after a pause,
White's reply appears. An animation toggle enables immediate updates, and the
flip effects respect the system's reduced-motion preference. No Python program
participates in the game or extraction.

The first browser build checks the complete certificate and can take around
20 minutes and several GiB of memory. Shake records source dependencies so the
checked extraction is reused until its inputs change. Generated Haskell,
compiler outputs, the browser bundle, and npm dependencies are ignored by Git.

The toolchain setup follows [Hometrics](https://github.com/konn/hometrics):
`ghc-wasm-meta` supplies SDK utilities and **ghcup manages the compiler**.
`cabal-wasm.project` pins GHC `9.12.4.20260402`, while its freeze file pins the
cross-compiler dependency plan. An existing compiler with that version is
reused. The browser uses GHC's generated JS FFI glue and a pinned, locally
bundled `@bjorn3/browser_wasi_shim`; there is no Cloudflare dependency.

## Export another function

```sh
cabal run praxis -- extract path/to/Module.px \
  --entry package.Module.function \
  --output praxis-wasm/generated/Extracted.hs
cabal run shake-praxis -- wasm
```

For a standalone module, omit the package prefix from the entry name.
Extraction resolves package imports and requires successful checking before
writing the Haskell module. `extract` never consumes a hand-parsed certificate,
an unchecked source AST, or a separately generated strategy table.

The generic bundle is written to `_build/wasm`. Import `loadPraxis` from its
`runtime.js` and await the returned function:

```js
import { loadPraxis } from "./runtime.js";
const evaluate = await loadPraxis();
const result = await evaluate({ value: ["2", "3"] });
// For an exported addition function: { value: "5" }
```

`praxis-wasm` is disabled in the ordinary native project until its `extracted`
flag is enabled, so a fresh native checkout does not need generated code.
After extraction, the same target can be built natively for comparison:

```sh
cabal build praxis-wasm -fextracted --disable-documentation
```

The native executable reads one JSON request per line and prints one response.
The WASM project enables this flag itself.

## JSON protocol and membership

A request has exactly one field: `{"value": [argument, ...]}`. The positional
array follows runtime argument order, including stored implicit value
parameters before explicit arguments. A nullary function takes `{"value":[]}`.

* Naturals are decimal strings. Safe nonnegative JSON integers are accepted
  as a convenience; results always use strings so large naturals remain exact.
* A datatype value is `["fully.qualified.Constructor", field, ...]`.
  Fields follow the checked physical layout: stored implicit fields are
  included; recovered indices and erased proof arguments are omitted.
* A successful response is `{"value": result}`.
* An error is `{"error":{"message":"description"}}`.

Before invoking the entry point, Haskell checks argument count, natural
domains, constructor ownership and arity, every nested field, GADT index
equations, and executable constructor proof preconditions. It reconstructs
recovered indices from their carrying fields. Callers supply neither type
claims nor proof tokens. Invalid inputs never reach the entry function.
Fuel, input-depth, request-size, and unfolded-output limits report JSON errors.

Exported entry points currently require monomorphic first-order input domains,
concrete dictionaries, and discharged function proof preconditions. Export a
Praxis wrapper when specialization or proof discharge is needed. Ordinary
callbacks, including captured lambdas, execute inside the program; callbacks
cannot be supplied through JSON. Runtime dictionary machinery and packed
membership predicates are rejected during extraction. Constructor guards
outside the executable quantifier-free fragment are rejected at the input
boundary, rather than treating erased evidence as valid.

## Implementation

1. `Language.Praxis.Surface.Extract` reads checked `Core.computation` bodies,
   runtime patterns, function signatures, and constructor telescopes. It emits
   `Extracted.hs`, a Haskell value containing the portable Surface program and
   datatype descriptors. Proof obligations have already been checked before
   their computational erasure.
2. `praxis-runtime` owns the portable representation, evaluator, membership
   checks, and JSON codec. Its constructor nodes are hash-consed and calls are
   memoized. `praxis eval` delegates to this same runtime; its existing pretty
   printer remains in the Surface package. Package imports now work in `eval`.
3. `praxis-wasm` compiles the generated module together with that runtime. A
   Haskell `foreign export javascript "praxis_eval"` exposes an asynchronous
   JSON-string function. CoPRA and the proof checker are **not dependencies** of
   the WASM target. This is a separate Surface compilation target, not an
   implementation of PRA evaluation in the browser.
4. Shake runs checking/extraction, Cabal cross-compilation, GHC's `post-link.mjs`,
   and static bundling. The generated module contains Surface code interpreted
   by the shared Haskell runtime; it does not generate a different handwritten
   Haskell implementation of each Praxis function.
5. `Game.Othello.Interactive` is a Praxis eliminator of `Derivation`. It turns
   the checked witness into a playable plan, follows a history of Black moves,
   automatically follows White choices, and produces a compact `View` with
   the intermediate boards before White moves. These observations let the
   renderer show discs that flip on both turns even when their final color
   matches their original color. All animation timing and effects are JavaScript.
   `Game.Othello.Browser.play` supplies `FourSolved.white-wins` to that code.
   JavaScript encodes the move history and renders the returned view. It
   contains no capture rules, move generator, search algorithm, or strategy
   extractor.

The original certificate establishes the White-score bound. The Haskell
extraction/runtime and GHC/WASM toolchain are part of the execution trust
boundary; this change does not claim a formal compiler-correctness theorem.

## Validation

The Surface tests exercise checked-source extraction, nested datatype
membership, recovered GADT indices, erased constructor proof preconditions,
callback captures, failed checking, and bounded JSON expansion. Existing
evaluator tests also exercise sharing and rendering.

For a small, real WASM/native comparison:

```sh
cabal run praxis -- extract praxis/test/data/wasm-api.px \
  --entry WasmAPI.run --output praxis-wasm/generated/Extracted.hs
cabal run shake-praxis -- wasm
cabal build praxis-wasm -fextracted --disable-documentation
node web/othello/test-wasm.mjs _build/wasm "$(cabal list-bin praxis-wasm -fextracted)"
```

After building `browser`, the complete game traversal calls the actual WASM
function for every Black reply, checks terminal White wins and the certified
score bound, exercises forced passes, rejects illegal histories, and checks
restart behavior:

```sh
node web/othello/test-game.mjs _build/browser
```
