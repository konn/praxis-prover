"""Checks for the untrusted search tool; these are not Praxis certificates."""

import unittest

import generate_four as g


class SearchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.nodes, cls.root = g.strategy()

    def test_strategy_covers_all_replies_and_terminates(self):
        by_id = {ident: (b, p) for (b, p), (ident, _) in self.nodes.items()}
        self.assertEqual(by_id[self.root], (g.initial(), g.BLACK))
        for (b, p), (ident, children) in self.nodes.items():
            moves = g.moves(b, p)
            if not moves:
                self.assertFalse(children)
                self.assertGreater(b.count(g.WHITE), b.count(g.BLACK))
            elif p == g.BLACK:
                self.assertEqual(tuple(m for m, _ in children), moves)
            else:
                self.assertEqual(len(children), 1)
                self.assertIn(children[0][0], moves)
            for move, child in children:
                self.assertLess(child, ident)
                self.assertEqual(by_id[child], (g.play(b, p, move), 3 - p))

    def test_symmetry_commutes_with_legal_moves_and_play(self):
        for b, p in self.nodes:
            for permutation in g.SYMMETRIES:
                transformed = tuple(b[i] for i in permutation)
                inverse = {old: new for new, old in enumerate(permutation)}
                mapped_move = lambda move: None if move is None else inverse[move]
                self.assertEqual(
                    set(g.moves(transformed, p)),
                    {mapped_move(m) for m in g.moves(b, p)},
                )
                for move in g.moves(b, p):
                    after = g.play(b, p, move)
                    self.assertEqual(
                        g.play(transformed, p, mapped_move(move)),
                        tuple(after[i] for i in permutation),
                    )
                self.assertEqual(g.canonical(transformed), g.canonical(b))

    def test_cost_search_agrees_with_independent_boolean_search(self):
        # Include off-strategy alternatives, not just the extracted proof.
        frontier = {(g.initial(), g.BLACK)}
        for _ in range(6):
            following = set()
            for b, p in frontier:
                self.assertEqual(
                    g.proof_cost(g.canonical(b), p) is not None,
                    g.white_wins(b, p),
                )
                following.update((g.play(b, p, m), 3 - p) for m in g.moves(b, p))
            frontier = following

    def test_draw_and_losing_leaves_are_not_wins(self):
        for b in ((g.BLACK,) * 16, (g.BLACK, g.WHITE) * 8):
            for p in (g.BLACK, g.WHITE):
                self.assertIsNone(g.proof_cost(g.canonical(b), p))
                self.assertFalse(g.white_wins(b, p))


if __name__ == '__main__':
    unittest.main()
