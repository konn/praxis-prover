const $ = (id) => document.getElementById(id);
const worker = new Worker(new URL("./worker.js", import.meta.url), { type: "module" });
let history = [], legal = [], cells = Array(16).fill(0), busy = true, sequence = 0, pendingMove = null;
const listPrefix = "base.Data.List.List.";
const interactivePrefix = "othello.Game.Othello.Interactive.";
const viewPrefix = interactivePrefix + "View.";

// Codecs for the exported datatypes; game rules and intermediate boards come
// exclusively from the checked Praxis computation in the WASM worker.
function encodeList(xs) {
  return xs.reduceRight((tail, x) => [listPrefix + "::", String(x), tail], [listPrefix + "Nil"]);
}
function decodeValues(value) {
  const xs = [];
  while (value?.[0] === listPrefix + "::") { xs.push(value[1]); value = value[2]; }
  if (value?.[0] !== listPrefix + "Nil") throw new Error("Unexpected list returned by Praxis.");
  return xs;
}
const decodeList = (value) => decodeValues(value).map(Number);
const coordinate = (n) => n === 16 ? "pass" : "ABCD"[n % 4] + (Math.floor(n / 4) + 1);
const delay = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
const moveDescription = ({ player, move }) => move === 16 ? `${player} ${player === "You" ? "pass" : "passes"}.` : `${player} ${player === "You" ? "play" : "plays"} ${coordinate(move)}.`;

function discElement(cell, extra = "") {
  const disc = document.createElement("span");
  disc.className = `disc ${cell === 1 ? "black" : "white"} ${extra}`;
  return disc;
}
function renderBoard(previous = null, highlight = null) {
  $("board").replaceChildren(...cells.map((cell, n) => {
    const square = document.createElement("button");
    square.className = "square" + (legal.includes(n) ? " legal" : "") + (n === highlight ? " last-move" : "");
    square.disabled = busy || !legal.includes(n);
    square.setAttribute("aria-label", `${coordinate(n)}: ${["empty", "Black", "White"][cell]}${legal.includes(n) ? ", legal move" : ""}`);
    if (cell) {
      if (previous?.[n] && previous[n] !== cell) {
        const flip = document.createElement("span");
        flip.className = "flip-disc";
        flip.append(discElement(previous[n], "front"), discElement(cell, "back"));
        square.append(flip);
      } else square.append(discElement(cell, previous && !previous[n] ? "placed" : ""));
    }
    square.addEventListener("click", () => move(n));
    return square;
  }));
  $("undo").disabled = busy || history.length === 0;
  $("restart").disabled = busy;
  $("pass").hidden = !legal.includes(16);
  $("pass").disabled = busy;
  $("animate").disabled = busy;
  $("history").textContent = history.length ? history.map(coordinate).join("  ·  ") : "A fresh board.";
}
function request(move = null) {
  busy = true; pendingMove = move;
  $("error").hidden = true;
  $("status").textContent = sequence === 0 ? "Loading the strategy…" : move === null ? "Restoring the board…" : "Your move…";
  renderBoard();
  worker.postMessage({ id: ++sequence, request: { value: [encodeList(history)] } });
}
function move(n) { if (!busy && legal.includes(n)) { history.push(n); request(n); } }
function fail(error) {
  busy = false; legal = [];
  $("error").textContent = String(error);
  $("error").hidden = false;
  $("status").textContent = "The game could not be evaluated.";
  renderBoard();
}
function readView(view) {
  if (view?.[0] === viewPrefix + "Playing") {
    const nextLegal = decodeList(view[2]);
    return {
      cells: decodeList(view[1]), legal: nextLegal, black: view[3], white: view[4],
      status: nextLegal.includes(16) ? "No placement is available. Pass your turn." : "Your turn. Choose a marked square.",
    };
  }
  if (view?.[0] === viewPrefix + "Finished") return {
    cells: decodeList(view[1]), legal: [], black: view[2], white: view[3],
    status: `Game over. White wins · certified score ≥ ${view[4]}.`,
  };
  throw new Error("Praxis rejected this move history.");
}
async function showTurn(board, black, white, action) {
  if (board.length !== 16) throw new Error("Unexpected board size returned by Praxis.");
  const previous = cells;
  cells = board; legal = [];
  $("black-count").textContent = black; $("white-count").textContent = white;
  $("status").textContent = moveDescription(action);
  renderBoard(previous, action.move);
  await delay(500);
}
worker.addEventListener("message", async ({ data }) => {
  if (data.id !== sequence) return;
  try {
    if (data.response.error) throw new Error(data.response.error.message);
    const playback = data.response.value;
    if (playback?.[0] !== interactivePrefix + "Playback.WithFrames") throw new Error("Unexpected playback returned by Praxis.");
    const frames = decodeValues(playback[1]);
    const final = readView(playback[2]);
    if (final.cells.length !== 16) throw new Error("Unexpected board size returned by Praxis.");
    if (pendingMove !== null && $("animate").checked) {
      let action = { player: "You", move: pendingMove };
      for (const frame of frames) {
        if (frame?.[0] !== interactivePrefix + "Frame.BeforeWhite") throw new Error("Unexpected animation frame returned by Praxis.");
        await showTurn(decodeList(frame[1]), frame[2], frame[3], action);
        action = { player: "White", move: Number(frame[4]) };
        $("status").textContent = action.move === 16 ? "White has no legal placement…" : "White to move…";
        await delay(750);
      }
      await showTurn(final.cells, final.black, final.white, action);
    }
    cells = final.cells; legal = final.legal;
    $("black-count").textContent = final.black; $("white-count").textContent = final.white;
    $("status").textContent = final.status;
    busy = false; pendingMove = null;
    renderBoard();
  } catch (error) { fail(error); }
});
worker.addEventListener("error", (event) => fail(event.message || "The WebAssembly worker could not start."));
$("pass").addEventListener("click", () => move(16));
$("undo").addEventListener("click", () => { history.pop(); request(); });
$("restart").addEventListener("click", () => { history = []; request(); });
request();
