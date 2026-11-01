# Othello in Praxis

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
- `Game.Othello.FourSolved.white-wins` is the checked 4×4 strategy certificate.
  It shares 128 positions in 77,651 bytes of Surface source, including all
  opponent replies, move legality, terminal bounds and the opening equality.
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

`tools/generate_four.py` is an **untrusted** search and candidate-certificate
generator targeting the certificate API. Running it is not a proof.
The generated output must pass the Praxis checker before
it can support a solution claim. The shipped `FourSolved.px` is the exact
candidate that passed the complete check; this generator does not search 6×6.

The generator caches search positions modulo the eight square symmetries and
selects winning White moves with minimum unfolded proof-tree size. The emitted
DAG shares only identical boards: each rotated or reflected board still has
its own checked move obligations, so this optimization adds no symmetry axiom.
This reduces the current candidate from 277 positions / 158,845 bytes to
128 positions / 77,651 bytes (including move-coverage proofs and explicit
transport to the standard opening). The cost calculation explores 5,131 canonical
positions; it minimizes tree size, not globally shared DAG size. This exhaustive
cost optimization is restricted to 4×4. Run its untrusted-tool checks with:

```sh
python3 -m unittest discover -s praxis/data/libraries/othello/tools -v
```

`tools/search_exact.cpp` prepares an untrusted exact search for both board
sizes. It uses bitboards, alpha–beta bounds, full-key transposition entries,
and mobility ordering with positional tie breakers. Each table bucket preserves
an earlier position with more empty squares and a recent position; the last
four empty squares are searched without table access. Opening positions with
at most twelve discs are canonicalized under square symmetries. Hash collisions
cannot establish a bound.
It respects node/time budgets and reports `certified: false` even on success;
its persistent query mode supplies untrusted bounds to the strategy extractor.
Its differential tests compare
the 4×4 opening, all positions in the candidate strategy, forced passes, and
small 6×6 endgames with an independent exhaustive coordinate-based evaluator.
`--stability 1` additionally computes conservative stable-disc bounds, using
full lines, board edges and previously established stable neighbours. It is
optional: a 24-position endgame sample reduced nodes from 256,484 to 186,992,
but increased search time from 37 to 49 ms. These bounds are not yet proved in
Praxis and cannot replace a subtree in a formal certificate.

`tools/generate_strategy.py` extracts either bound on either board size, sharing
only identical positions. It checks every defender's reply and every terminal
score with its coordinate model, then emits all obligations for Praxis. Partial
checkpoints preserve the candidate DAG and untrusted oracle answers; they do
not assert the root result. The output file is written only after the complete
root candidate has been extracted. For example, a bounded 6×6 attempt is:

```sh
python3 praxis/data/libraries/othello/tools/generate_strategy.py \
  --solver /tmp/othello-search --size 6 --bound lower --score 20 \
  --positions 10000 --nodes 100000000 --seconds 60 \
  --output /tmp/SixLower.px --checkpoint /tmp/six-lower.json
```

Repeating the command resumes its checkpoint. Both the checkpoint and the
emitted source remain untrusted until the source passes Praxis. The 4×4
integration run extracted 145 positions for the lower bound 9 and 231 for the
upper bound 13; the separate proof-size optimizer still gives the smaller
128-position candidate for the first problem.

```sh
clang++ -std=c++20 -O3 -Wall -Wextra -Wpedantic \
  praxis/data/libraries/othello/tools/search_exact.cpp -o /tmp/othello-search
OTHELLO_SEARCH_BIN=/tmp/othello-search python3 -m unittest discover \
  -s praxis/data/libraries/othello/tools -v
```

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

The 4×4 bottleneck was proof checking rather than search. Reusing
`cvrecUnfold` fixes GADT admission; `by decide` emits shared, checked computation
lemmas, and constructor checking reuses already certified proof arguments.
Terminal leaves, both standard opening definitions, and a three-position
branch containing a forced pass now pass. On this branch, peak live heap fell
from 944 MiB to 697 MiB with term interning, then 226 MiB with strict step
reconstruction, and 142 MiB with identifier sharing and omission of inspection
text. All derivations and lexical dependencies remain available for replay;
`--dump-pra` still retains the complete generated text. Earlier full attempts
exhausted their heap caps. The corrected full 4×4 certificate now passes with
`+RTS -N1 -M12G -s`: 1,157 seconds, 2,342,874,184 bytes maximum live residency
(2.18 GiB), and 6,110 MiB total heap memory in use. This includes the explicit
equality transport to the standard opening. The check still allocates heavily
(3.61 TB cumulatively); source size, live memory and cumulative allocation are
different measurements.

The native 6×6 benchmark exhausted a 100-million-node budget in about 20
seconds without finishing; a one-billion-node attempt without symmetry took
about 177 seconds and also did not finish. Neither establishes the opening
value or a formal certificate. `--guess-white 20` selects the first search
window but never assumes that score as a bound.

The lower-bound strategy extraction at score 20 has also exhausted a
one-million-position certificate budget without completing the opening.
Its resumable, untrusted checkpoint occupies 81,283,815 bytes; 850,348 of
those positions have at most six empty squares. No 6×6 proof source has been
emitted or certified. This is a concrete limit of the current explicit
strategy representation even with exact-position sharing. A proved
endgame or stability reduction is the next compression target; merely
raising the extraction cap would work against the lightweight-proof goal.
