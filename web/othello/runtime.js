import ghcWasmJsffi from "./ghc_wasm_jsffi.js";
import { WASI, File, OpenFile, ConsoleStdout } from "./vendor/dist/index.js";

/** Load the Haskell reactor. No Praxis or game semantics are implemented here. */
export async function loadPraxis(bytes) {
  const wasi = new WASI([], [], [
    new OpenFile(new File([])),
    ConsoleStdout.lineBuffered(console.log),
    ConsoleStdout.lineBuffered(console.error),
  ]);
  const exports = {};
  const imports = {
    wasi_snapshot_preview1: wasi.wasiImport,
    ghc_wasm_jsffi: ghcWasmJsffi(exports),
  };
  const module = bytes ?? await (await fetch(new URL("./praxis.wasm", import.meta.url))).arrayBuffer();
  const { instance } = await WebAssembly.instantiate(module, imports);
  Object.assign(exports, instance.exports);
  wasi.initialize(instance);
  return async function evaluate(request) {
    return JSON.parse(await exports.praxis_eval(JSON.stringify(request)));
  };
}
