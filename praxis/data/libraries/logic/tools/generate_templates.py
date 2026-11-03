#!/usr/bin/env python3
"""Generate finite Hilbert proof templates; Praxis checks every generated node.

The typed lambda notation here is only an untrusted authoring convenience.
Bracket abstraction emits K/S/Explosion/MP (and DNE for the classical example),
not a new object inference rule. Run with --check to check reproducibility.
"""

from dataclasses import dataclass
from pathlib import Path
import argparse


@dataclass(frozen=True)
class Formula:
    name: str
    args: tuple = ()

    def px(self):
        if not self.args:
            return self.name
        return "(" + self.name + " " + " ".join(x.px() for x in self.args) + ")"


def arrow(a, b):
    return Formula("Imp", (a, b))


BOT = Formula("Bottom")
A, B = Formula("a"), Formula("b")


def neg(a):
    return arrow(a, BOT)


def nn(a):
    return neg(neg(a))


@dataclass(frozen=True)
class Proof:
    tag: str
    typ: Formula
    args: tuple = ()
    params: tuple = ()


def var(name, typ):
    return Proof(name, typ)


def k(a, b):
    return Proof("K", arrow(a, arrow(b, a)), params=(a, b))


def s(a, b, c):
    return Proof("S", arrow(arrow(a, arrow(b, c)), arrow(arrow(a, b), arrow(a, c))), params=(a, b, c))


def explosion(a):
    return Proof("Explosion", arrow(BOT, a), params=(a,))


def dne(a):
    return Proof("DNE", arrow(nn(a), a), params=(a,))


def app(f, x):
    assert f.typ.name == "Imp" and f.typ.args[0] == x.typ, (f.typ, x.typ)
    return Proof("MP", f.typ.args[1], (f, x))


def free(p, x):
    return p == x or any(free(child, x) for child in p.args)


def abstract(x, p):
    if p == x:
        return app(app(s(x.typ, arrow(x.typ, x.typ), x.typ), k(x.typ, arrow(x.typ, x.typ))), k(x.typ, x.typ))
    if not free(p, x):
        return app(k(p.typ, x.typ), p)
    assert p.tag == "MP", p
    f, a = p.args
    if a == x and not free(f, x):
        return f
    return app(app(s(x.typ, a.typ, p.typ), abstract(x, f)), abstract(x, a))


def lambdas(xs, p):
    for x in reversed(xs):
        p = abstract(x, p)
    return p


def templates():
    x, na = var("x", A), var("na", neg(A))
    yield "double-negation-intro", "Intuitionistic", ("a",), lambdas([x, na], app(na, x))

    f, a, nb = var("f", nn(arrow(A, B))), var("aProof", nn(A)), var("nb", neg(B))
    ab, x = var("ab", arrow(A, B)), var("x", A)
    body = app(f, abstract(ab, app(a, abstract(x, app(nb, app(ab, x))))))
    yield "double-negation-mp", "Intuitionistic", ("a", "b"), lambdas([f, a, nb], body)

    h = var("h", neg(arrow(nn(A), A)))
    n, x, ignored = var("n", nn(A)), var("x", A), var("ignored", nn(A))
    body = app(h, abstract(n, app(explosion(A), app(n, abstract(x, app(h, abstract(ignored, x)))))))
    yield "double-negation-dne", "Intuitionistic", ("a",), abstract(h, body)

    n, z = var("n", nn(BOT)), var("z", BOT)
    yield "bottom-out", "Intuitionistic", (), abstract(n, app(n, abstract(z, z)))

    f, na, x = var("f", arrow(arrow(A, B), A)), var("na", neg(A)), var("x", A)
    body = app(dne(A), abstract(na, app(na, app(f, abstract(x, app(explosion(B), app(na, x)))))))
    yield "peirce", "Classical", ("a", "b"), abstract(f, body)


@dataclass(frozen=True)
class Expression:
    head: str
    args: tuple = ()

    def flat(self):
        return "(" + " ".join([self.head, *(arg.flat() for arg in self.args)]) + ")"

    def render(self, indent=0):
        flat = self.flat()
        if not self.args or indent + len(flat) <= 100:
            return flat
        return "(" + self.head + "\n" + "\n".join(
            " " * (indent + 2) + arg.render(indent + 2) for arg in self.args
        ) + ")"


# Group MP steps rather than declaring one helper per node. Whole-template
# inlining exceeds the current checker's definitional-equality resources for
# the two largest templates. Six is a practical block size, not a logic rule.
# A block can finish above this threshold when its two children are joined.
INLINE_MPS = 6


def emit(name, calculus, params, root):
    nodes = {}
    parts = []
    lines = []
    binders = "".join("{" + x + " : Formula} -> " for x in params)
    captures = "".join(" {" + x + "}" for x in params)

    def declare(node, proof, expression):
        lines.extend([
            f"{node} : {binders}{calculus} {proof.typ.px()}",
            f"{node}{captures} =",
            "  " + expression.render(2),
            "",
        ])

    def visit(p):
        if p in nodes:
            return nodes[p]
        if p.tag != "MP":
            assert p.tag in {"K", "S", "Explosion", "DNE"}
            assert p.tag != "DNE" or calculus == "Classical"
            return Expression(calculus + "." + p.tag + "".join(" {" + a.px() + "}" for a in p.params)), 0
        f, fcost = visit(p.args[0])
        x, xcost = visit(p.args[1])
        # Praxis infers the antecedent and conclusion from these proof terms.
        expression, cost = Expression(calculus + ".MP", (f, x)), 1 + fcost + xcost
        if cost >= INLINE_MPS and p != root:
            node = f"{name}-part-{len(parts) + 1}"
            parts.append(node)
            declare(node, p, expression)
            expression, cost = Expression(node + captures), 0
        nodes[p] = expression, cost
        return nodes[p]

    result, _ = visit(root)
    declare(name, root, result)
    return "\n".join(lines)


START = "-- BEGIN GENERATED HILBERT TEMPLATES"
END = "-- END GENERATED HILBERT TEMPLATES"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    path = Path(__file__).resolve().parents[1] / "src/Logic/Glivenko.px"
    source = path.read_text()
    before, rest = source.split(START, 1)
    _, after = rest.split(END, 1)
    body = "\n\n".join(emit(*t) for t in templates())
    generated = before + START + "\n-- Generated by tools/generate_templates.py; all nodes are checked by Praxis.\n\n" + body + END + after
    if args.check:
        if source != generated:
            raise SystemExit("Hilbert templates need regeneration")
    else:
        path.write_text(generated)


if __name__ == "__main__":
    main()
