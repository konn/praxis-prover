"""Checks for untrusted strategy extraction; Praxis must check the output."""

from pathlib import Path
import tempfile
import unittest

import generate_four as four
from generate_strategy import BLACK, WHITE, Extractor, Game, Incomplete, Unattainable
from test_search_exact import reference


class ExtractionTests(unittest.TestCase):
    def extractor(self, bound='lower', score=9, **kwargs):
        def ask(board, player):
            value = reference(board, player, 4)
            return value >= score if bound == 'lower' else value <= score
        return Extractor(Game(4), bound, score, ask, **kwargs)

    def test_both_bounds_extract_complete_shared_strategies(self):
        for bound, score in (('lower', 9), ('lower', 13), ('upper', 13)):
            with self.subTest(bound=bound, score=score):
                extractor = self.extractor(bound, score)
                root = extractor.visit(extractor.game.initial(), BLACK)
                extractor.validate()
                self.assertEqual(extractor.nodes[root][:2], (four.initial(), BLACK))
                self.assertEqual(root, len(extractor.nodes) - 1)

    def test_wrong_bounds_and_poisoned_oracles_cannot_make_valid_graphs(self):
        for bound, score in (('lower', 16), ('upper', 12)):
            extractor = self.extractor(bound, score)
            with self.assertRaises(Unattainable):
                extractor.visit(extractor.game.initial(), BLACK)
        poisoned = Extractor(Game(4), 'lower', 16, lambda _board, _player: True)
        with self.assertRaises(Unattainable):
            poisoned.visit(poisoned.game.initial(), BLACK)

    def test_checkpoint_resume_reuses_answers_and_checks_reply_coverage(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'candidate.json'
            partial = self.extractor(limit=8, checkpoint=path)
            with self.assertRaises(Incomplete):
                partial.visit(partial.game.initial(), BLACK)
            partial.save()
            resumed = self.extractor(checkpoint=path)
            resumed.resume()
            cached = set(resumed.answers)
            original = resumed.ask

            def fresh_only(board, player):
                self.assertNotIn((board, player), cached)
                return original(board, player)

            resumed.ask = fresh_only
            root = resumed.visit(resumed.game.initial(), BLACK)
            resumed.validate()
            board, player, children = resumed.nodes[root]
            self.assertGreater(len(children), 1)
            resumed.nodes[root] = board, player, children[:-1]
            with self.assertRaisesRegex(ValueError, 'incomplete reply'):
                resumed.validate()

    def test_coordinates_agree_with_four_generator_and_six_opening(self):
        game = Game(4)
        nodes, _ = four.strategy()
        for board, player in nodes:
            self.assertEqual(game.moves(board, player), four.moves(board, player))
            for move in game.moves(board, player):
                self.assertEqual(game.play(board, player, move), four.play(board, player, move))
        six = Game(6)
        self.assertEqual(six.placements(six.initial(), BLACK), (8, 13, 22, 27))
        self.assertEqual(six.initial().count(BLACK), 2)
        self.assertEqual(six.initial().count(WHITE), 2)


if __name__ == '__main__':
    unittest.main()
