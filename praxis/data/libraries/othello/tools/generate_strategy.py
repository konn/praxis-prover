#!/usr/bin/env python3
"""Extract a bounded, shared strategy candidate using an untrusted native oracle.

Neither the oracle nor the checkpoint is trusted. Every emitted move, terminal
score and complete reply list must subsequently pass the Praxis checker.
"""

import argparse
import json
import math
from pathlib import Path
import subprocess
import sys
import time

BLACK, WHITE = 1, 2
DIRECTIONS = tuple((r, c) for r in (-1, 0, 1) for c in (-1, 0, 1) if r or c)


class Incomplete(Exception):
    pass


class Unattainable(Exception):
    pass


class Game:
    def __init__(self, side):
        if side not in (4, 6):
            raise ValueError('expected board size 4 or 6')
        self.side = side

    def initial(self):
        n, b = self.side, [0] * (self.side * self.side)
        lo, hi = n // 2 - 1, n // 2
        b[lo * n + lo] = b[hi * n + hi] = WHITE
        b[lo * n + hi] = b[hi * n + lo] = BLACK
        return tuple(b)

    def captures(self, board, player, square):
        if board[square]:
            return ()
        n, result = self.side, []
        r, c = divmod(square, n)
        for dr, dc in DIRECTIONS:
            rr, cc, run = r + dr, c + dc, []
            while 0 <= rr < n and 0 <= cc < n and board[rr * n + cc] == 3 - player:
                run.append(rr * n + cc)
                rr, cc = rr + dr, cc + dc
            if run and 0 <= rr < n and 0 <= cc < n and board[rr * n + cc] == player:
                result.extend(run)
        return tuple(result)

    def placements(self, board, player):
        return tuple(i for i in range(self.side * self.side) if self.captures(board, player, i))

    def moves(self, board, player):
        return self.placements(board, player) or ((None,) if self.placements(board, 3 - player) else ())

    def play(self, board, player, move):
        if move is None:
            return board
        result = list(board)
        for i in (move,) + self.captures(board, player, move):
            result[i] = player
        return tuple(result)

    def score(self, board):
        black, white = board.count(BLACK), board.count(WHITE)
        return self.side ** 2 - black if white > black else white if black > white else self.side ** 2 // 2

    def choice_order(self, board, player, moves):
        n = self.side
        corners = (0, n - 1, n * (n - 1), n * n - 1)
        return sorted(moves, key=lambda m: (
            len(self.placements(self.play(board, player, m), 3 - player)),
            m not in corners, -1 if m is None else m))


def board_string(board):
    return ''.join('.BW'[cell] for cell in board)


def parse_board(text, side):
    if len(text) != side * side or any(c not in '.BW' for c in text):
        raise ValueError('invalid checkpoint board')
    return tuple('.BW'.index(c) for c in text)


class Extractor:
    def __init__(self, game, bound, score, ask, limit=10000, checkpoint=None):
        if bound not in ('lower', 'upper') or not 0 <= score <= game.side ** 2:
            raise ValueError('invalid bound')
        self.game, self.bound, self.score, self.ask = game, bound, score, ask
        self.limit, self.checkpoint = limit, checkpoint
        self.nodes, self.ids, self.answers = [], {}, {}
        self.last_save = time.monotonic()

    def choosing(self, player):
        return (self.bound == 'lower') == (player == WHITE)

    def holds(self, score):
        return score >= self.score if self.bound == 'lower' else score <= self.score

    def query(self, board, player):
        key = (board, player)
        if key not in self.answers:
            self.answers[key] = self.ask(board, player)
            self.save_if_due()
        return self.answers[key]

    def visit(self, board, player):
        key = (board, player)
        if key in self.ids:
            return self.ids[key]
        if len(self.nodes) >= self.limit:
            raise Incomplete(f'certificate position budget ({self.limit}) exhausted')
        moves = self.game.moves(board, player)
        if not moves:
            if not self.holds(self.game.score(board)):
                raise Unattainable('a terminal position violates the requested bound')
            children = []
        elif self.choosing(player):
            for move in self.game.choice_order(board, player, moves):
                child = self.game.play(board, player, move)
                if (child, 3 - player) in self.ids or self.query(child, 3 - player):
                    children = [(move, self.visit(child, 3 - player))]
                    break
            else:
                raise Unattainable('no legal choice establishes the requested bound')
        else:
            children = [(move, self.visit(self.game.play(board, player, move), 3 - player)) for move in moves]
        if len(self.nodes) >= self.limit:
            raise Incomplete(f'certificate position budget ({self.limit}) exhausted')
        ident = len(self.nodes)
        self.nodes.append((board, player, children))
        self.ids[key] = ident
        if len(self.nodes) % 128 == 0:
            print(f'{len(self.nodes)} candidate positions; {len(self.answers)} oracle answers', file=sys.stderr)
            self.save_if_due()
        return ident

    def validate(self):
        for ident, (board, player, children) in enumerate(self.nodes):
            moves = self.game.moves(board, player)
            if not moves:
                if children or not self.holds(self.game.score(board)):
                    raise ValueError('invalid terminal checkpoint node')
            elif self.choosing(player):
                if len(children) != 1 or children[0][0] not in moves:
                    raise ValueError('invalid chosen move')
            elif tuple(move for move, _ in children) != moves:
                raise ValueError('incomplete reply list')
            for move, child in children:
                if not isinstance(child, int) or not 0 <= child < ident:
                    raise ValueError('checkpoint is not a backward-pointing DAG')
                wanted = self.game.play(board, player, move), 3 - player
                if self.nodes[child][:2] != wanted:
                    raise ValueError('checkpoint successor mismatch')

    def save_if_due(self):
        if time.monotonic() - self.last_save >= 5:
            self.save()

    def save(self):
        if self.checkpoint is None:
            return
        payload = {'side': self.game.side, 'bound': self.bound, 'score': self.score,
                   'certified': False,
                   'nodes': [[board_string(b), p, children] for b, p, children in self.nodes],
                   'answers': [[board_string(b), p, answer] for (b, p), answer in self.answers.items()]}
        temporary = self.checkpoint.with_suffix(self.checkpoint.suffix + '.tmp')
        temporary.write_text(json.dumps(payload, separators=(',', ':')))
        temporary.replace(self.checkpoint)
        self.last_save = time.monotonic()

    def resume(self):
        data = json.loads(self.checkpoint.read_text())
        if (data['side'], data['bound'], data['score']) != (self.game.side, self.bound, self.score):
            raise ValueError('checkpoint belongs to a different problem')
        self.nodes = [(parse_board(b, self.game.side), p, children) for b, p, children in data['nodes']]
        if any(p not in (BLACK, WHITE) for _, p, _ in self.nodes):
            raise ValueError('invalid checkpoint player')
        self.validate()
        self.ids = {(b, p): ident for ident, (b, p, _) in enumerate(self.nodes)}
        if len(self.ids) != len(self.nodes):
            raise ValueError('duplicate checkpoint positions')
        for b, p, answer in data['answers']:
            if p not in (BLACK, WHITE) or not isinstance(answer, bool):
                raise ValueError('invalid checkpoint oracle answer')
            self.answers[parse_board(b, self.game.side), p] = answer

    def emit(self, root):
        self.validate()
        if self.nodes[root][:2] != (self.game.initial(), BLACK):
            raise ValueError('the root is not the standard opening')
        size_name = 'Four' if self.game.side == 4 else 'Six'
        kind, value = self.bound.title(), self.score
        lines = [f'module Game.Othello.{size_name}{kind} where', '',
                 '-- Untrusted generated candidate: check every premise with Praxis.',
                 'import "base" Data.List as L', 'open L using (Nil, (::))',
                 'import Game.Othello.Board as C', 'import Game.Othello.Rules as R',
                 'import Game.Othello.Initial as I', 'import Game.Othello.Certificate as K', '']
        cells = ('C.Empty', '(C.Disc C.Black)', '(C.Disc C.White)')

        def move_text(move):
            return 'R.Pass' if move is None else f'(R.Place (C.At {move // self.game.side} {move % self.game.side}))'

        for ident, (board, player, children) in enumerate(self.nodes):
            colour = 'C.Black' if player == BLACK else 'C.White'
            other = 'C.White' if player == BLACK else 'C.Black'
            pos = f'(R.Turn {colour} b{ident})'
            lines += [f'b{ident} : C.Board',
                      f'b{ident} = C.Grid {self.game.side} (' + ' :: '.join(cells[c] for c in board) + ' :: Nil)',
                      f'd{ident} : K.Derivation (K.AtBound K.{kind} {pos} {value})']
            if not children:
                body = f'K.Derivation.Leaf{kind} (by decide) (by decide)'
            elif self.choosing(player):
                move, child = children[0]
                body = f'K.Derivation.Choice {{K.{kind}}} {{{colour}}} {{b{ident}}} {{{value}}} {{{move_text(move)}}} {{R.Turn {other} b{child}}} (by decide) (by decide) (by decide) d{child}'
            else:
                body = f'K.Derivation.NoMoves {{K.{kind}}} {{{pos}}} {{{value}}} {{Nil}} (by decide)'
                for offset in reversed(range(len(children))):
                    move, child = children[offset]
                    tail = ''.join(move_text(m) + ' :: ' for m, _ in children[offset + 1:]) + 'Nil'
                    body = f'K.Derivation.Reply {{K.{kind}}} {{{pos}}} {{{value}}} {{{move_text(move)}}} {{{tail}}} {{R.Turn {other} b{child}}} (by decide) d{child} ({body})'
                all_moves = ''.join(move_text(m) + ' :: ' for m, _ in children) + 'Nil'
                body = f'K.Derivation.Replies {{K.{kind}}} {{{colour}}} {{b{ident}}} {{{value}}} {{{all_moves}}} (by decide) (by decide) (by decide) (by decide) ({body})'
            lines += [f'd{ident} = {body}', '']
        opening = f'I.{size_name.lower()}-opening'
        lines += [f'bound : K.Derivation (K.AtBound K.{kind} {opening} {value})',
                  f'bound = K.cast {{K.AtBound K.{kind} (R.Turn C.Black b{root}) {value}}} {{K.AtBound K.{kind} {opening} {value}}} (by decide) d{root}', '']
        return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solver', required=True, type=Path)
    parser.add_argument('--size', type=int, choices=(4, 6), required=True)
    parser.add_argument('--bound', choices=('lower', 'upper'), required=True)
    parser.add_argument('--score', type=int, required=True)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--checkpoint', type=Path)
    parser.add_argument('--positions', type=int, default=10000)
    parser.add_argument('--nodes', type=int, default=100000000)
    parser.add_argument('--seconds', type=float, default=60)
    parser.add_argument('--table-bits', type=int, default=22)
    args = parser.parse_args()
    if args.positions < 1:
        parser.error('--positions must be positive')
    if not 0 <= args.score <= args.size ** 2 or args.nodes < 0 or not 8 <= args.table_bits <= 25:
        parser.error('score, node budget or table size is out of range')
    if not math.isfinite(args.seconds) or args.seconds < 0:
        parser.error('--seconds must be finite and nonnegative')
    game = Game(args.size)
    process = subprocess.Popen([str(args.solver.resolve()), '--serve', '--size', str(args.size),
                                '--nodes', str(args.nodes), '--seconds', str(args.seconds),
                                '--table-bits', str(args.table_bits)],
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)

    def ask(board, player):
        process.stdin.write(f'{args.bound} {".BW"[player]} {board_string(board)} {args.score}\n')
        process.stdin.flush()
        line = process.stdout.readline()
        if not line:
            raise Incomplete('native oracle stopped without answering')
        answer = json.loads(line)
        if not answer.get('complete') or not isinstance(answer.get('bound'), bool):
            raise Incomplete(f'native search budget exhausted: {answer}')
        return answer['bound']

    extractor = Extractor(game, args.bound, args.score, ask, args.positions, args.checkpoint)
    ready = False
    try:
        if args.checkpoint and args.checkpoint.exists():
            extractor.resume()
        ready = True
        root = extractor.visit(game.initial(), BLACK)
        source = extractor.emit(root)
        args.output.write_text(source)
        print(json.dumps({'candidate_complete': True, 'certified': False,
                          'positions': len(extractor.nodes), 'bytes': len(source.encode())}))
    except (Incomplete, Unattainable) as error:
        print(str(error), file=sys.stderr)
        return 2
    finally:
        if ready:
            extractor.save()
        process.stdin.close()
        try:
            process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            process.terminate()
            process.wait()
    return 0


if __name__ == '__main__':
    sys.exit(main())
