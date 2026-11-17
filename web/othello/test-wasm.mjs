import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { execFileSync } from "node:child_process";

const directory = resolve(process.argv[2] ?? "_build/wasm");
const { loadPraxis } = await import(pathToFileURL(resolve(directory, "runtime.js")));
const evaluate = await loadPraxis(await readFile(resolve(directory, "praxis.wasm")));
const nil = ["WasmAPI.Vec.Nil"];
const cons = (n, xs) => ["WasmAPI.Vec.Cons", String(n), xs];
const cases = [
  [{ value: [["WasmAPI.Request.Add", "2", "3"]] }, "5"],
  [{ value: [["WasmAPI.Request.Add", "9007199254740993", "8"]] }, "9007199254741001"],
  [{ value: [["WasmAPI.Request.CheckVector", cons(4, cons(5, nil))]] }, "2"],
  [{ value: [["WasmAPI.Request.CheckBound", ["WasmAPI.Bounded.Mk", "3"]]] }, "3"],
  [{ value: [["WasmAPI.Request.CheckVector", nil]] }, null],
  [{ value: [["WasmAPI.Request.CheckBound", ["WasmAPI.Bounded.Mk", "4"]]] }, null],
  [{ value: [["WasmAPI.Request.Add", -1, 3]] }, null],
  [{ value: [["WasmAPI.Request.Add", 1.5, 3]] }, null],
  [{ value: [["WasmAPI.Request.Add", 9007199254740992, 3]] }, null],
  [{ value: [], type: "Request" }, null],
  [{ value: [["NoSuchConstructor"]] }, null],
];
const actual = [];
for (const [request, expected] of cases) {
  const response = await evaluate(request);
  if (expected === null) assert.equal(typeof response.error?.message, "string");
  else assert.deepEqual(response, { value: expected });
  actual.push(response);
}
if (process.argv[3]) {
  const output = execFileSync(resolve(process.argv[3]), [], {
    input: cases.map(([request]) => JSON.stringify(request)).join("\n") + "\n",
    encoding: "utf8",
  });
  assert.deepEqual(output.trim().split("\n").map(JSON.parse), actual);
  console.log("Native and WASM results match for every case.");
}
console.log(`${cases.length} real GHC WASM JSON/domain tests passed.`);
