// Untrusted exact search for 4x4 and 6x6 Othello. This is not a Praxis proof.
// Alpha-beta, full-key transpositions, and move ordering; no heuristic pruning.
#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <functional>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Bits = std::uint64_t;
using Clock = std::chrono::steady_clock;

struct Limit {};

static unsigned long long natural(const std::string &value) {
  if (value.empty() || value.find_first_not_of("0123456789") != std::string::npos)
    throw std::runtime_error("expected a nonnegative integer");
  return std::stoull(value);
}

static double duration(const std::string &value) {
  std::size_t used;
  double result = std::stod(value, &used);
  if (used != value.size() || !std::isfinite(result) || result < 0)
    throw std::runtime_error("expected finite nonnegative seconds");
  return result;
}

static std::pair<Bits, Bits> parse_board(const std::string &board, int side) {
  if (board.size() != std::size_t(side * side))
    throw std::runtime_error("wrong board length");
  Bits black = 0, white = 0;
  for (std::size_t i = 0; i < board.size(); ++i) {
    if (board[i] == 'B') black |= Bits{1} << i;
    else if (board[i] == 'W') white |= Bits{1} << i;
    else if (board[i] != '.') throw std::runtime_error("board cells must be . B W");
  }
  return {black, white};
}

class Search {
  struct Entry {
    Bits player = 0, opponent = 0;
    std::int8_t lower = -37, upper = 37;
    std::uint8_t best = 255, empties = 0;
    bool occupied = false;
  };
  struct Bucket { Entry deep, recent; };
  struct Move {
    Bits player, opponent;
    int square, order;
  };
  int side, area;
  Bits mask, first_column = 0, last_column = 0, corners;
  std::array<std::array<int, 36>, 8> symmetries{};
  struct Axis {
    Bits line = 0, neighbours = 0;
    bool boundary = false;
  };
  std::array<std::array<Axis, 4>, 36> axes{};
  bool stability;
  std::vector<Bucket> table;
  std::uint64_t node_limit;
  double seconds;
  Clock::time_point started = Clock::now();

  static Bits mix(Bits x) {
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
  }

  static bool matches(const Entry &entry, Bits p, Bits o) {
    return entry.occupied && entry.player == p && entry.opponent == o;
  }

  void save(std::size_t slot, const Entry &entry) {
    auto &bucket = table[slot];
    if (matches(bucket.deep, entry.player, entry.opponent)) bucket.deep = entry;
    else if (matches(bucket.recent, entry.player, entry.opponent)) bucket.recent = entry;
    else if (!bucket.deep.occupied || entry.empties >= bucket.deep.empties) bucket.deep = entry;
    else bucket.recent = entry;
  }

  int position_order(int square, Bits occupied) const {
    Bits bit = Bits{1} << square;
    if (corners & bit) return 64;
    int r = square / side, c = square % side;
    int near_r = r < side / 2 ? 0 : side - 1;
    int near_c = c < side / 2 ? 0 : side - 1;
    if (std::abs(r - near_r) <= 1 && std::abs(c - near_c) <= 1 &&
        !(occupied & (Bits{1} << (near_r * side + near_c)))) return -32;
    return (r == near_r || c == near_c) ? 8 : 0;
  }

  Bits shift(Bits b, int dr, int dc) const {
    if (dc < 0) b &= ~first_column;
    if (dc > 0) b &= ~last_column;
    int distance = dr * side + dc;
    return (distance > 0 ? b << distance : b >> -distance) & mask;
  }

  Bits legal(Bits p, Bits o) const {
    Bits result = 0, empty = mask & ~(p | o);
    if (!empty) return 0;
    for (int dr = -1; dr <= 1; ++dr) {
      for (int dc = -1; dc <= 1; ++dc) {
        if (!dr && !dc) continue;
        Bits run = shift(p, dr, dc) & o;
        for (int i = 0; i < side - 2; ++i)
          run |= shift(run, dr, dc) & o;
        result |= shift(run, dr, dc) & empty;
      }
    }
    return result;
  }

  Bits flipped(Bits p, Bits o, Bits square) const {
    Bits result = 0;
    for (int dr = -1; dr <= 1; ++dr) {
      for (int dc = -1; dc <= 1; ++dc) {
        if (!dr && !dc) continue;
        Bits current = shift(square, dr, dc), run = 0;
        while (current & o) {
          run |= current;
          current = shift(current, dr, dc);
        }
        if (current & p) result |= run;
      }
    }
    return result;
  }

  int terminal(Bits p, Bits o) const {
    int difference = std::popcount(p) - std::popcount(o);
    int empty = area - std::popcount(p | o);
    // Tournament scoring: unplayed empty squares go to the winner.
    return difference > 0 ? difference + empty
                         : difference < 0 ? difference - empty : 0;
  }

  Bits stable(Bits colour, Bits occupied) const {
    // Sufficient stability only. A full line admits no future placement on
    // that axis. Otherwise a boundary or an adjacent stable friendly disc
    // prevents bracketing from that side. Requiring this on all four axes
    // makes the least fixed point stable under every subsequent legal move.
    Bits result = colour & corners, previous;
    do {
      previous = result;
      Bits remaining = colour & ~result;
      while (remaining) {
        int square = std::countr_zero(remaining);
        remaining &= remaining - 1;
        bool fixed = true;
        for (const auto &axis : axes[square]) {
          if (!axis.boundary && !(axis.neighbours & result) &&
              (axis.line & occupied) != axis.line) {
            fixed = false;
            break;
          }
        }
        if (fixed) result |= Bits{1} << square;
      }
    } while (result != previous);
    return result;
  }

  void canonicalize(Bits &p, Bits &o) const {
    // Spend symmetry work near the root, where equivalent opening branches
    // would otherwise outlive the bounded transposition table. Subsequent
    // moves are searched on the transformed board, so stored move indices
    // stay in the same orientation as their complete position keys.
    if (std::popcount(p | o) > 12) return;
    std::pair<Bits, Bits> best{p, o};
    for (const auto &permutation : symmetries) {
      Bits pp = 0, oo = 0, remaining = p | o;
      while (remaining) {
        int square = std::countr_zero(remaining);
        Bits bit = Bits{1} << permutation[square];
        if (p & (Bits{1} << square)) pp |= bit;
        else oo |= bit;
        remaining &= remaining - 1;
      }
      best = std::min(best, std::pair<Bits, Bits>{pp, oo});
    }
    p = best.first;
    o = best.second;
  }

  int search(Bits p, Bits o, int alpha, int beta) {
    if (node_limit && ++nodes > node_limit) throw Limit{};
    if (!node_limit) ++nodes;
    if ((nodes & ((1ULL << 18) - 1)) == 0 &&
        seconds > 0 && elapsed() >= seconds)
      throw Limit{};
    if ((p | o) == mask) return terminal(p, o);
    int empties = area - std::popcount(p | o);
    if (empties <= 4) return small(p, o, alpha, beta);
    canonicalize(p, o);
    std::size_t slot = mix(p ^ std::rotl(mix(o), 23)) & (table.size() - 1);
    Entry entry = matches(table[slot].deep, p, o) ? table[slot].deep : table[slot].recent;
    // Hash collisions replace an entry; they never establish a bound.
    if (matches(entry, p, o)) {
      ++hits;
      if (entry.lower >= beta) return entry.lower;
      if (entry.upper <= alpha) return entry.upper;
      if (entry.lower == entry.upper) return entry.lower;
      alpha = std::max(alpha, int(entry.lower));
      beta = std::min(beta, int(entry.upper));
    } else {
      entry = Entry{};
      entry.player = p;
      entry.opponent = o;
      entry.empties = empties;
      entry.occupied = true;
    }
    if (stability && area - std::popcount(p | o) <= 10) {
      // A colour cannot have more stable discs than discs. In a null window
      // at most one colour's count can possibly produce a cutoff; avoid the
      // fixed-point calculation for the other colour (often for both).
      if (2 * std::popcount(p) - area >= beta)
        entry.lower = std::max(int(entry.lower), 2 * std::popcount(stable(p, p | o)) - area);
      if (area - 2 * std::popcount(o) <= alpha)
        entry.upper = std::min(int(entry.upper), area - 2 * std::popcount(stable(o, p | o)));
      if (entry.lower >= beta || entry.lower == entry.upper) {
        save(slot, entry);
        return entry.lower;
      }
      if (entry.upper <= alpha) {
        save(slot, entry);
        return entry.upper;
      }
      alpha = std::max(alpha, int(entry.lower));
      beta = std::min(beta, int(entry.upper));
    }
    const int start_alpha = alpha, start_beta = beta;
    Bits moves = legal(p, o);
    int value = -area - 1;
    if (!moves) {
      if (!legal(o, p)) {
        value = terminal(p, o);
        entry.lower = entry.upper = value;
        save(slot, entry);
        return value;
      }
      value = -search(o, p, -beta, -alpha);
    } else {
      std::array<Move, 36> choices;
      int count = 0;
      while (moves) {
        int square = std::countr_zero(moves);
        Bits bit = Bits{1} << square;
        moves &= moves - 1;
        Bits flips = flipped(p, o, bit);
        Bits next_p = p | bit | flips, next_o = o & ~flips;
        int order = (square == entry.best ? 100000 : 0) +
                    position_order(square, p | o) -
                    256 * std::popcount(legal(next_o, next_p));
        choices[count++] = {next_p, next_o, square, order};
      }
      std::sort(choices.begin(), choices.begin() + count,
                [](const Move &a, const Move &b) {
                  return a.order != b.order ? a.order > b.order
                                            : a.square < b.square;
                });
      for (int i = 0; i < count; ++i) {
        const auto &move = choices[i];
        int score = -search(move.opponent, move.player, -beta, -alpha);
        if (score > value) {
          value = score;
          entry.best = move.square;
        }
        alpha = std::max(alpha, value);
        if (alpha >= beta) break;
      }
    }
    if (value <= start_alpha) entry.upper = std::min(int(entry.upper), value);
    else if (value >= start_beta) entry.lower = std::max(int(entry.lower), value);
    else entry.lower = entry.upper = value;
    // Children may have overwritten this slot; restore our complete key.
    save(slot, entry);
    return value;
  }

  int small(Bits p, Bits o, int alpha, int beta) {
    // The caller counted this node and checked its budget. At most four
    // placements remain; avoid hashing and sorting by successor mobility.
    Bits moves = legal(p, o);
    if (!moves) {
      if (!legal(o, p)) return terminal(p, o);
      return -search(o, p, -beta, -alpha);
    }
    std::array<std::pair<int, int>, 4> choices;
    int count = 0;
    while (moves) {
      int square = std::countr_zero(moves);
      moves &= moves - 1;
      choices[count++] = {position_order(square, p | o), square};
    }
    std::sort(choices.begin(), choices.begin() + count, std::greater<>());
    int best = -area - 1;
    for (int i = 0; i < count; ++i) {
      Bits bit = Bits{1} << choices[i].second;
      Bits flips = flipped(p, o, bit);
      best = std::max(best, -search(o & ~flips, p | bit | flips, -beta, -alpha));
      alpha = std::max(alpha, best);
      if (alpha >= beta) break;
    }
    return best;
  }

public:
  std::uint64_t nodes = 0, hits = 0;

  Search(int n, int table_bits, std::uint64_t limit, double time_limit, bool use_stability)
      : side(n), area(n * n), mask((Bits{1} << area) - 1),
        corners(1 | (Bits{1} << (n - 1)) | (Bits{1} << (n * (n - 1))) |
                (Bits{1} << (area - 1))),
        stability(use_stability), table(std::size_t{1} << table_bits), node_limit(limit), seconds(time_limit) {
    for (int r = 0; r < side; ++r) {
      first_column |= Bits{1} << (r * side);
      last_column |= Bits{1} << (r * side + side - 1);
    }
    for (int reflection = 0; reflection < 2; ++reflection) {
      for (int turns = 0; turns < 4; ++turns) {
        for (int square = 0; square < area; ++square) {
          int r = square / side, c = square % side;
          if (reflection) c = side - 1 - c;
          for (int i = 0; i < turns; ++i) {
            int old_r = r;
            r = c;
            c = side - 1 - old_r;
          }
          symmetries[4 * reflection + turns][square] = r * side + c;
        }
      }
    }
    const std::array<std::pair<int, int>, 4> directions{{{1, 0}, {0, 1}, {1, 1}, {1, -1}}};
    for (int square = 0; square < area; ++square) {
      int r = square / side, c = square % side;
      for (int a = 0; a < 4; ++a) {
        auto [dr, dc] = directions[a];
        auto &axis = axes[square][a];
        axis.line = Bits{1} << square;
        for (int sign : {-1, 1}) {
          int rr = r + sign * dr, cc = c + sign * dc;
          if (rr < 0 || rr >= side || cc < 0 || cc >= side) axis.boundary = true;
          else axis.neighbours |= Bits{1} << (rr * side + cc);
          while (rr >= 0 && rr < side && cc >= 0 && cc < side) {
            axis.line |= Bits{1} << (rr * side + cc);
            rr += sign * dr;
            cc += sign * dc;
          }
        }
      }
    }
  }

  double elapsed() const {
    return std::chrono::duration<double>(Clock::now() - started).count();
  }

  int solve(Bits p, Bits o, int guess) {
    // Repeated null-window probes establish matching lower and upper bounds.
    // The initial guess chooses the first probe; it is never a trusted bound.
    int lower = -area, upper = area;
    while (lower < upper) {
      int beta = guess == lower ? guess + 1 : guess;
      guess = search(p, o, beta - 1, beta);
      if (guess < beta) upper = guess;
      else lower = guess;
    }
    return guess;
  }

  bool has_bound(Bits black, Bits white, bool white_to_move, bool lower, int score) {
    Bits p = white_to_move ? white : black, o = white_to_move ? black : white;
    int target = (2 * score - area) * (white_to_move ? 1 : -1);
    if (lower == white_to_move) return search(p, o, target - 1, target) >= target;
    return search(p, o, target, target + 1) <= target;
  }
};

int main(int argc, char **argv) {
  try {
    int side = 4, table_bits = 20, guess_white = -1;
    bool stability = false;
    bool serve = false;
    std::uint64_t limit = 100000000;
    double seconds = 60;
    std::string board, player = "B";
    for (int i = 1; i < argc; ++i) {
      std::string option = argv[i];
      if (option == "--serve") { serve = true; continue; }
      if (i + 1 == argc) throw std::runtime_error("missing option value");
      std::string value = argv[++i];
      if (option == "--size") {
        auto n = natural(value);
        if (n != 4 && n != 6) throw std::runtime_error("expected size 4 or 6");
        side = int(n);
      } else if (option == "--table-bits") {
        auto n = natural(value);
        if (n < 8 || n > 25) throw std::runtime_error("expected table bits 8..25");
        table_bits = int(n);
      } else if (option == "--nodes") limit = natural(value);
      else if (option == "--stability") {
        auto enabled = natural(value);
        if (enabled > 1) throw std::runtime_error("stability must be 0 or 1");
        stability = enabled;
      }
      else if (option == "--guess-white") {
        auto n = natural(value);
        if (n > 36) throw std::runtime_error("guess exceeds largest board");
        guess_white = int(n);
      }
      else if (option == "--seconds") seconds = duration(value);
      else if (option == "--board") board = value;
      else if (option == "--player") player = value;
      else throw std::runtime_error("unknown option: " + option);
    }
    if ((side != 4 && side != 6) || table_bits < 8 || table_bits > 25 ||
        seconds < 0 || guess_white > side * side || (player != "B" && player != "W"))
      throw std::runtime_error("expected size 4/6, table bits 8..25, and player B/W");
    if (board.empty()) {
      board.assign(side * side, '.');
      int low = side / 2 - 1, high = side / 2;
      board[low * side + low] = board[high * side + high] = 'W';
      board[low * side + high] = board[high * side + low] = 'B';
    }
    auto [black, white] = parse_board(board, side);
    Search solver(side, table_bits, limit, seconds, stability);
    try {
      if (serve) {
        // A persistent untrusted oracle for certificate extraction. One line
        // is: lower|upper B|W .BW-board white-score. The table and budgets
        // persist across queries; no answer is a certificate or an axiom.
        std::string line;
        while (std::getline(std::cin, line)) {
          std::istringstream input(line);
          std::string bound, turn, position, target, extra;
          if (!(input >> bound >> turn >> position >> target) || (input >> extra) ||
              (bound != "lower" && bound != "upper") || (turn != "B" && turn != "W"))
            throw std::runtime_error("expected: lower|upper B|W board score");
          auto score = natural(target);
          if (score > std::size_t(side * side)) throw std::runtime_error("score exceeds board area");
          auto [query_black, query_white] = parse_board(position, side);
          bool answer = solver.has_bound(query_black, query_white, turn == "W", bound == "lower", int(score));
          std::cout << "{\"complete\":true,\"certified\":false,\"bound\":"
                    << (answer ? "true" : "false") << ",\"nodes\":" << solver.nodes
                    << ",\"seconds\":" << solver.elapsed() << "}\n" << std::flush;
        }
        return 0;
      }
      int guess = guess_white < 0 ? 0 : (2 * guess_white - side * side) * (player == "W" ? 1 : -1);
      int relative = solver.solve(player == "B" ? black : white,
                                  player == "B" ? white : black, guess);
      int white_score = (side * side + (player == "W" ? relative : -relative)) / 2;
      std::cout << "{\"solved\":true,\"certified\":false,\"white_score\":"
                << white_score << ",\"nodes\":" << solver.nodes
                << ",\"tt_hits\":" << solver.hits
                << ",\"seconds\":" << solver.elapsed() << "}\n";
      return 0;
    } catch (const Limit &) {
      std::cout << "{\"solved\":false,\"certified\":false,\"nodes\":"
                << solver.nodes << ",\"tt_hits\":" << solver.hits
                << ",\"seconds\":" << solver.elapsed() << "}\n";
      return 2;
    }
  } catch (const std::exception &error) {
    std::cerr << error.what() << '\n';
    return 1;
  }
}
