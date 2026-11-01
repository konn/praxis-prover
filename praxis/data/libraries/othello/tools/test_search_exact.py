"""Differential checks for the untrusted native search, not proof certificates.

Set OTHELLO_SEARCH_BIN to a compiled search_exact.cpp executable to run these.
The reference uses coordinates and exhaustive minimax, without bitboards or
alpha-beta bounds. Small transposition tables deliberately exercise collisions.
"""

from functools import cache
import json
import os
import random
import subprocess
import unittest

import generate_four as g

EXECUTABLE = os.environ.get('OTHELLO_SEARCH_BIN')


def captures(board, player, square, side):
    if board[square]:
        return ()
    result = []
    r, c = divmod(square, side)
    for dr, dc in g.DIRECTIONS:
        rr, cc, line = r + dr, c + dc, []
        while 0 <= rr < side and 0 <= cc < side and board[rr * side + cc] == 3 - player:
            line.append(rr * side + cc)
            rr, cc = rr + dr, cc + dc
        if line and 0 <= rr < side and 0 <= cc < side and board[rr * side + cc] == player:
            result.extend(line)
    return tuple(result)


def successors(board, player, side):
    result = []
    for square in range(side * side):
        flips = captures(board, player, square, side)
        if flips:
            child = list(board)
            for i in (square,) + flips:
                child[i] = player
            result.append(tuple(child))
    return result


@cache
def reference(board, player, side):
    children = successors(board, player, side)
    if children:
        choose = min if player == g.BLACK else max
        return choose(reference(child, 3 - player, side) for child in children)
    if successors(board, 3 - player, side):
        return reference(board, 3 - player, side)
    black, white = board.count(g.BLACK), board.count(g.WHITE)
    return side * side - black if white > black else white if black > white else side * side // 2


@unittest.skipUnless(EXECUTABLE, 'set OTHELLO_SEARCH_BIN to run native search checks')
class ExactSearchTests(unittest.TestCase):
    def invoke(self, *arguments):
        return subprocess.run([EXECUTABLE, *arguments], text=True, capture_output=True, timeout=30)

    def assert_score(self, board, player, side, table_bits=8, stability=True):
        result = self.invoke('--size', str(side), '--table-bits', str(table_bits),
                             '--board', ''.join('.BW'[cell] for cell in board),
                             '--player', '.BW'[player], '--stability', str(int(stability)))
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        output = json.loads(result.stdout)
        self.assertTrue(output['solved'])
        self.assertFalse(output['certified'])
        self.assertEqual(output['white_score'], reference(board, player, side))
        return output

    def test_four_opening_and_transpositions(self):
        for player in (g.BLACK, g.WHITE):
            for bits in (8, 12):
                with self.subTest(player=player, bits=bits):
                    self.assertGreater(self.assert_score(g.initial(), player, 4, bits)['tt_hits'], 0)

    def test_four_strategy_and_forced_passes(self):
        nodes, _ = g.strategy()
        passes = 0
        for board, player in nodes:
            passes += g.moves(board, player) == (None,)
            self.assert_score(board, player, 4)
        self.assertGreater(passes, 0)

    def test_six_small_endgames(self):
        # Only short endgames are searched here, not the unsolved opening proof.
        rng = random.Random(4626)
        for _ in range(16):
            board = [0] * 36
            board[14], board[15], board[20], board[21] = 2, 1, 1, 2
            board, player = tuple(board), g.BLACK
            while board.count(0) > 5:
                children = successors(board, player, 6)
                if children:
                    board = rng.choice(children)
                elif not successors(board, 3 - player, 6):
                    break
                player = 3 - player
            for player in (g.BLACK, g.WHITE):
                self.assert_score(board, player, 6)
                self.assert_score(board, player, 6, stability=False)

    def test_terminal_empty_square_credit_and_draws(self):
        for side in (4, 6):
            for player in (g.BLACK, g.WHITE):
                for board in ((0,) * (side * side),
                              (g.BLACK,) + (0,) * (side * side - 1),
                              (g.WHITE,) + (0,) * (side * side - 1),
                              (g.BLACK, g.WHITE) * (side * side // 2)):
                    self.assert_score(board, player, side)

    def test_budget_exhaustion_is_not_a_solution(self):
        result = self.invoke('--nodes', '1')
        self.assertEqual(result.returncode, 2)
        output = json.loads(result.stdout)
        self.assertFalse(output['solved'])
        self.assertFalse(output['certified'])
        self.assertNotIn('white_score', output)

    def test_initial_guess_is_not_trusted(self):
        expected = reference(g.initial(), g.BLACK, 4)
        for guess in (0, 8, expected, 16):
            result = self.invoke('--guess-white', str(guess), '--table-bits', '8')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout)['white_score'], expected)

    def test_persistent_bound_queries_share_only_valid_bounds(self):
        board = ''.join('.BW'[cell] for cell in g.initial())
        queries, expected = [], []
        for player in (g.BLACK, g.WHITE):
            value = reference(g.initial(), player, 4)
            for score in (0, 8, 13, 16):
                for bound in ('lower', 'upper'):
                    queries.append(f'{bound} {".BW"[player]} {board} {score}')
                    expected.append(value >= score if bound == 'lower' else value <= score)
        result = subprocess.run([EXECUTABLE, '--serve', '--table-bits', '8'],
                                input='\n'.join(queries) + '\n', text=True,
                                capture_output=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        answers = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual([answer['bound'] for answer in answers], expected)
        self.assertTrue(all(answer['complete'] and not answer['certified'] for answer in answers))
        counts = [answer['nodes'] for answer in answers]
        self.assertEqual(counts, sorted(counts))

    def test_persistent_query_budget_does_not_answer_false(self):
        board = ''.join('.BW'[cell] for cell in g.initial())
        result = subprocess.run([EXECUTABLE, '--serve', '--nodes', '1'],
                                input=f'lower B {board} 9\n', text=True,
                                capture_output=True, timeout=30)
        self.assertEqual(result.returncode, 2)
        answer = json.loads(result.stdout)
        self.assertNotIn('bound', answer)
        self.assertFalse(answer['solved'])

    def test_rejects_malformed_input(self):
        for args in (('--size', '5'), ('--size', '4bad'), ('--nodes', '-1'),
                     ('--table-bits', '999999999999'), ('--seconds', 'nan'),
                     ('--seconds', 'inf'), ('--seconds', '0junk'),
                     ('--board', 'x' * 16), ('--board', '.'),
                     ('--player', 'X'), ('--guess-white', '17'),
                     ('--stability', '2'), ('--unknown', '1'), ('--size',)):
            with self.subTest(args=args):
                result = self.invoke(*args)
                self.assertEqual(result.returncode, 1)
                self.assertEqual(result.stdout, '')


if __name__ == '__main__':
    unittest.main()
