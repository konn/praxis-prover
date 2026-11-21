# Othello in Praxis

## Play the checked 4×4 strategy

From the repository root, run `cabal run shake-praxis -- browser`, then serve
`_build/browser` over HTTP with the `praxis-web` Servant and Warp executable:
`cabal run praxis-web` serves it at `http://localhost:8080` (pass
`-- --port PORT` or `-- --directory DIR` to customize).

`Game.Othello.Interactive` eliminates the checked strategy witness in Praxis;
`Game.Othello.Browser.play` follows the user's move history through that
witness. A shared Haskell Surface evaluator is compiled with GHC WASM and
called by the single-page application. JavaScript only renders views and
encodes user input. See [the build, JSON protocol, and design overview](../../../../docs/wasm.md).

## Formalisation and certificates

A separate Surface library for the 4×4 and 6×6 Othello tasks in the
[TPP 2026 problem collection](https://auto-res.github.io/tpp2026/ja/tpp2026mark/).
It depends on the bundled `base` library and adds no axioms.

The first problem now has a checked strategy certificate: White can force a
tournament score of at least 9 from the standard 4×4 opening. The optimal
20–16 result on 6×6 is **not yet certified**.

- `Game.Othello.Board` and `Game.Othello.Rules` implement a checked reference
  model: eight capture directions, simultaneous flips, forced passes, and
  termination when neither colour can move. The reference model checks its
  flat storage length at game entry points.
- `Game.Othello.Initial` defines the standard 4×4 and 6×6 openings.
- `Game.Othello.Four` provides a dedicated 4×4 board representation (`Board4`)
  with constant-time cell access and three-ray capture evaluation, proved
  equivalent to `Game.Othello.Board`, `Game.Othello.Rules`,
  `Game.Othello.Initial`, and `Game.Othello.Certificate`, together with
  certified reflection constructors (`mk-leaf`, `mk-choice`, `mk-replies`,
  `mk-no-moves`, `mk-reply`) and a boolean-indexed witness container
  (`Check4 j ok`, `extract4`).
- `Game.Othello.FourSolved.white-wins` is the checked 4×4 strategy certificate,
  constructed and certified entirely in Praxis with no external code generator.
  At White turns it applies a zero-lookahead square-priority policy
  (`white-place`, selecting between a top-corner priority order for the
  `(0, 1)`/`(1, 0)` Black openings and its $180^\circ$-rotated counterpart for
  `(3, 2)`/`(2, 3)`), checks all seven Black–White rounds purely on `Board4`
  booleans via `by decide`, and reflects the result into
  `K.Derivation (K.AtBound K.Lower I.four-opening 9)` in a single top-down pass.
- `Game.Othello.Sized` supplies the intended board representation,
  `Vec n (Vec n Cell)`, with finite row and column indices. Cell writes use
  `Vec.modify` and `Vec.update`; `read-write` proves the selected cell changes.
  `Square n` pairs two finite indices. `to-reference` flattens a typed board,
  and `to-reference-well-formed` proves that its storage has the required size.
  Moving the complete game rules onto this representation remains unfinished.
- `Game.Othello.Certificate` defines checked lower/upper strategy bounds as
  indexed proof objects. At the defending player's turns, the
  rule requires the complete legal move list. `ExactScore` requires both bounds. Its score
  credits remaining empty squares to the winner, following the tournament
  convention used in the historical 6×6 solution; raw disc counts are separate.

From the repository root:

```sh
cabal run praxis -- check praxis/data/libraries/othello +RTS -N1 -M12G -RTS
```

The 4×4 certificate (`Game.Othello.Four` and `Game.Othello.FourSolved`) is
written and checked entirely in Praxis, with no external code generator.

## Search-method survey

The survey found useful exact reductions, but no ready-made short mathematical
strategy proof for the two requested openings.

- [Takeshita et al. (2017)](https://pdfs.semanticscholar.org/cc22/09cf7e551d183cdac08f4d335fd345a52b0a.pdf)
  use alpha–beta pruning, learned move ordering, and a transposition table for
  6×6. They report nine billion terminal positions; adding the table reduced
  search by 40%. Ordering guides an exact search and does not justify discarding
  an opponent's reply from a certificate.
- [Sakuta and Iida (2001)](https://citeseerx.ist.psu.edu/document?doi=db6ce86eea0106dc6ae75349a2cacb212b91884e&repid=rep1&type=pdf)
  compare PN*, PDS, and proof-number search on 6×6 Othello and Tsume-Shogi.
  Depth-first variants avoid retaining a whole best-first search tree. They
  motivate a proof-directed search, but are not a demonstrated shortcut to
  this library's exact-score certificate.
- [Van Dijk (2019)](https://theses.liacs.nl/pdf/2018-2019-DijkStefvan.pdf)
  applies symbolic retrograde analysis with BDDs, solving boards up to 4×5.
  This is evidence for compressed sets of positions, not an existing 6×6
  solution we can directly import.
- [Egaroucid's implementation notes](https://www.egaroucid.nyanyan.dev/en/technology/explanation/)
  describe sound stability cutoffs as well as heuristic search techniques.
  A stable-disc bound could replace an entire subtree after its stability and
  score implications are proved in Praxis. Heuristic pruning is not evidence.
- [Kodama's compact solver](https://github.com/yaskodama/othello6x6)
  supplies an inspectable modern implementation. Its two-slot replacement
  policy and omission of table access in small endgames motivated the native
  search improvements here; this implementation retains full-board comparisons
  for every table hit. The external solver optimizes raw disc difference, so
  its numerical results are not directly substituted for tournament scores.
- [Takizawa (2026 revision)](https://arxiv.org/html/2411.01029v2)
  distinguishes a playable solution artifact from the additional evidence
  needed to verify it. The released [6×6 tablebase](https://zenodo.org/records/18843225)
  is 138.4 GB, so importing it does not meet our lightweight-source objective.
- [Considine (2024)](https://arxiv.org/abs/2411.07273)
  proposes compressed set operations for game solving, with experimental
  results on Breakthrough. Applicability to Othello remains to be established.

For 6×6, the intended search target is two threshold certificates at score 20,
with exact transposition reuse, good move ordering, and separately proved
symmetry/stability reductions where worthwhile. Computing every position's
exact minimax value or a semi-strong tablebase is unnecessary for these bounds.
The score convention must remain explicit: the historical result credits
empty squares to the winner, as stated by
[Feinstein](https://www.maths.nottingham.ac.uk/plp/pmzjff/Othello/Amenor.html).

The pure-Praxis 4×4 certificate (`Game.Othello.Four` + `Game.Othello.FourSolved`)
passes with `+RTS -N1 -M4G -s` in ~54 seconds (~307 MiB maximum live
residency, ~916 MiB total heap memory in use, ~246 GB cumulative allocation),
and the full `othello` package checks in ~56 seconds (~290 MiB maximum live
residency) — down from 1,157 seconds and 3.61 TB cumulative allocation for
the earlier Python-generated 128-position DAG. All derivations and lexical
dependencies remain available for replay; `--dump-pra` still retains the
complete generated text.
