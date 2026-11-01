# Othello in Praxis

A separate Surface library for the 4×4 and 6×6 Othello tasks in the
[TPP 2026 problem collection](https://auto-res.github.io/tpp2026/ja/tpp2026mark/).
It depends on the bundled `base` library and adds no axioms.

This is work in progress. It does **not** yet certify either winning-strategy
claim: White winning 4×4, or the optimal 20–16 result on 6×6.

- `Game.Othello.Board` and `Game.Othello.Rules` implement a checked reference
  model: eight capture directions, simultaneous flips, forced passes, and
  termination when neither colour can move. The reference model checks its
  flat storage length at game entry points.
- `Game.Othello.Initial` defines the standard 4×4 and 6×6 openings.
- `Game.Othello.Sized` supplies the intended board representation,
  `Vec n (Vec n Cell)`, with finite row and column indices. Cell writes use
  `Vec.modify` and `Vec.update`; `read-write` proves the selected cell changes.
  Moving the complete game rules onto this representation remains unfinished.
- `design/Certificate.px` sketches lower/upper strategy bounds as indexed
  proof objects. It is **not admitted by the checker**: the generated membership
  beta lemma for `Derivation` currently fails kernel checking, so it is outside
  the package's source directory. At the defending player's turns, the proposed
  rule requires the complete legal move list. `ExactScore` requires both bounds. Its score
  credits remaining empty squares to the winner, following the tournament
  convention used in the historical 6×6 solution; raw disc counts are separate.

From the repository root:

```sh
cabal run praxis -- check praxis/data/libraries/othello
```

`tools/generate_four.py` is an **untrusted** search and candidate-certificate
generator targeting that draft certificate API. Running it is not a proof.
The draft API and generated output must both pass the Praxis checker before
they can support a solution claim. No checked root strategy
certificate is currently shipped, and the tool does not search 6×6.
