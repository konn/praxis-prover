import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";

const directory = resolve(process.argv[2] ?? "_build/browser");
const { loadPraxis } = await import(pathToFileURL(resolve(directory, "runtime.js")));
const evaluate = await loadPraxis(await readFile(resolve(directory, "praxis.wasm")));
const listPrefix = "base.Data.List.List.";
const viewPrefix = "othello.Game.Othello.Interactive.View.";
const encode = (xs) => xs.reduceRight((tail, n) => [listPrefix + "::", String(n), tail], [listPrefix + "Nil"]);
function decodeValues(xs) {
  const result = [];
  while (xs[0] === listPrefix + "::") { result.push(xs[1]); xs = xs[2]; }
  assert.deepEqual(xs, [listPrefix + "Nil"]);
  return result;
}
const decode = (xs) => decodeValues(xs).map(Number);
async function observe(history) {
  const result = await evaluate({ value: [encode(history)] });
  assert.equal(result.error, undefined, JSON.stringify(result.error));
  const playback = result.value;
  assert.equal(playback[0], "othello.Game.Othello.Interactive.Playback.WithFrames");
  for (const frame of decodeValues(playback[1])) {
    assert.equal(frame[0], "othello.Game.Othello.Interactive.Frame.BeforeWhite");
    const cells = decode(frame[1]);
    assert.equal(cells.length, 16);
    assert.equal(cells.filter((n) => n === 1).length, Number(frame[2]));
    assert.equal(cells.filter((n) => n === 2).length, Number(frame[3]));
    const move = Number(frame[4]);
    assert.ok(move >= 0 && move <= 16);
    if (move !== 16) assert.equal(cells[move], 0);
  }
  return playback;
}
const play = async (history) => (await observe(history))[2];
let positions = 0, terminals = 0, passes = 0;
async function visit(history) {
  assert.ok(history.length <= 32, "the strategy failed to terminate");
  const view = await play(history);
  positions++;
  const cells = decode(view[1]);
  assert.equal(cells.length, 16);
  assert.ok(cells.every((n) => [0, 1, 2].includes(n)));
  if (view[0] === viewPrefix + "Finished") {
    terminals++;
    const black = Number(view[2]), white = Number(view[3]);
    assert.equal(cells.filter((n) => n === 1).length, black);
    assert.equal(cells.filter((n) => n === 2).length, white);
    assert.ok(white > black);
    assert.ok(16 - black >= Number(view[4]));
    assert.equal(Number(view[4]), 9);
  } else {
    assert.equal(view[0], viewPrefix + "Playing");
    const legal = decode(view[2]);
    assert.ok(legal.length > 0);
    assert.equal(new Set(legal).size, legal.length);
    if (legal.includes(16)) { assert.deepEqual(legal, [16]); passes++; }
    for (const move of legal) await visit([...history, move]);
    assert.deepEqual(await play([...history, 99]), [viewPrefix + "Invalid"]);
  }
}
const opening = await play([]);
assert.deepEqual(decode(opening[2]), [1, 4, 11, 14]);
// B2 flips once on each turn: identical old/final cells must not hide either.
const firstRound = await observe([1]);
const firstFrames = decodeValues(firstRound[1]);
assert.equal(firstFrames.length, 1);
assert.deepEqual(firstFrames[0].slice(2), ["4", "1", "0"]);
assert.equal(decode(firstFrames[0][1])[5], 1);
assert.equal(decode(firstRound[2][1])[5], 2);
await visit([]);
assert.deepEqual(await play([]), opening, "new game must restore the initial state");
assert.ok((await evaluate({ value: ["0"] })).error, "a raw number must not pass list membership");
assert.deepEqual(await play([]), opening, "rejected inputs must not corrupt subsequent games");
assert.ok(terminals > 0);
console.log(`Traversed ${positions} playable histories, ${terminals} White wins, ${passes} forced Black passes through real WASM.`);
