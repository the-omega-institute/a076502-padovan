#!/usr/bin/env python3
"""Exact finite-state verification for Cloitre's A076502 candidate.

An integer carry invariant proves soundness independently of the chosen box.
Completeness must be established by language inclusion, never inferred from
stabilization of the box or from a numerical prefix.
"""

import argparse
import ast
from collections import deque
from dataclasses import dataclass
from itertools import product
import json
from pathlib import Path
import time


@dataclass
class DFA:
    names: tuple
    rows: list
    final: set
    start: int = 0

    @property
    def width(self):
        return 1 << len(self.names)

    def stats(self):
        return {"states": len(self.rows), "accepting": len(self.final)}


def bits(symbol, count):
    return tuple((symbol >> (count - i - 1)) & 1 for i in range(count))


def encode(values):
    n = 0
    for b in values:
        n = 2 * n + b
    return n


def reachable(names, start, step, accept, cap=1000000):
    states = [start]
    ids = {start: 0}
    rows = []
    final = set()
    alphabet = list(product((0, 1), repeat=len(names)))
    for s in states:
        if accept(s):
            final.add(ids[s])
        row = []
        for letter in alphabet:
            t = step(s, letter)
            if t is None:
                row.append(-1)
                continue
            if t not in ids:
                if len(states) >= cap:
                    raise RuntimeError(f"state cap {cap}: {names}")
                ids[t] = len(states)
                states.append(t)
            row.append(ids[t])
        rows.append(row)
    return DFA(tuple(names), rows, final), states


def trim(dfa):
    rev = [[] for _ in dfa.rows]
    for s, row in enumerate(dfa.rows):
        for t in set(row):
            if t >= 0:
                rev[t].append(s)
    live = set(dfa.final)
    todo = list(live)
    for s in todo:
        for t in rev[s]:
            if t not in live:
                live.add(t)
                todo.append(t)
    if dfa.start not in live:
        return DFA(dfa.names, [[-1] * dfa.width], set())
    order = [dfa.start] + sorted(live - {dfa.start})
    ids = {s: i for i, s in enumerate(order)}
    return DFA(dfa.names, [[ids.get(t, -1) for t in dfa.rows[s]] for s in order],
               {ids[s] for s in dfa.final})


def minimize(dfa):
    dfa = trim(dfa)
    classes = [int(s in dfa.final) for s in range(len(dfa.rows))]
    while True:
        signatures = {}
        new = []
        for s, row in enumerate(dfa.rows):
            key = (s in dfa.final, tuple(classes[t] if t >= 0 else -1 for t in row))
            new.append(signatures.setdefault(key, len(signatures)))
        if new == classes:
            break
        classes = new
    reps = {}
    for s, c in enumerate(classes):
        reps.setdefault(c, s)
    rows = [[classes[t] if t >= 0 else -1 for t in dfa.rows[reps[c]]]
            for c in range(len(reps))]
    return DFA(dfa.names, rows, {classes[s] for s in dfa.final}, classes[dfa.start])


def rename(dfa, names):
    assert len(set(names)) == len(names) == len(dfa.names)
    return DFA(tuple(names), dfa.rows, dfa.final, dfa.start)


def intersect(*dfas):
    names = tuple(dict.fromkeys(n for d in dfas for n in d.names))
    maps = [tuple(names.index(n) for n in d.names) for d in dfas]

    def step(states, letter):
        nxt = tuple(d.rows[s][encode(letter[i] for i in inds)]
                    for d, s, inds in zip(dfas, states, maps))
        return None if -1 in nxt else nxt

    out, _ = reachable(names, tuple(d.start for d in dfas), step,
                       lambda ss: all(s in d.final for d, s in zip(dfas, ss)))
    return minimize(out)


def project(dfa, names):
    inds = tuple(dfa.names.index(n) for n in names)
    groups = [[] for _ in range(1 << len(names))]
    for i in range(dfa.width):
        letter = bits(i, len(dfa.names))
        groups[encode(letter[j] for j in inds)].append(i)

    def step(states, letter):
        nxt = frozenset(dfa.rows[s][i] for s in states
                        for i in groups[encode(letter)] if dfa.rows[s][i] >= 0)
        return nxt if nxt else None

    out, _ = reachable(tuple(names), frozenset([dfa.start]), step,
                       lambda ss: bool(ss & dfa.final))
    return minimize(out)


def inclusion(left, right):
    """Return shortest counterexample, or None after exhausting the product."""
    assert left.names == right.names
    start = (left.start, right.start)
    previous = {start: None}
    todo = deque([start])
    while todo:
        u, v = todo.popleft()
        if u in left.final and v not in right.final:
            word = []
            at = (u, v)
            while previous[at] is not None:
                at, letter = previous[at]
                word.append(bits(letter, len(left.names)))
            return list(reversed(word))
        for letter, un in enumerate(left.rows[u]):
            if un < 0:
                continue
            vn = right.rows[v][letter] if v >= 0 else -1
            at = (un, vn)
            if at not in previous:
                previous[at] = ((u, v), letter)
                todo.append(at)
    return None


def greedy(name):
    # q=0..4 counts trailing zeros, capped at 4; q=5 is the exceptional
    # terminal 10001, allowed only as the very end of the word.
    def step(q, letter):
        b = letter[0]
        if q == 5:
            return None
        if not b:
            return min(4, q + 1)
        if q == 4:
            return 0
        return 5 if q == 3 else None

    out, _ = reachable((name,), 4, step, lambda q: True)
    return out


def prefixed_zero_domain(names, count):
    gs = [greedy(n) for n in names]
    core = intersect(*gs)
    # All tracks have count leading zero digits, then arbitrary legal words.
    rows = [[-1] * core.width for _ in range(count)]
    rows.extend([[t + count if t >= 0 else -1 for t in row] for row in core.rows])
    for i in range(count):
        rows[i][0] = i + 1 if i + 1 < count else count + core.start
    return DFA(tuple(names), rows, {s + count for s in core.final})


def carry_step(r, digit):
    a, b, c = r
    return c + digit, a + c, b


def value(r):
    return 2 * r[0] + 2 * r[1] + 3 * r[2]


def adder(bound=12):
    # Reduce digit polynomial modulo X^3-X-1. The actual weights have
    # U_0=1, while the homogeneous sequence W has W_0=2, W_1=2,W_2=3.
    # Therefore sum z_p U_p = 2r0+2r1+3r2-z_0 exactly.
    def step(state, letter):
        r, last = state
        z = letter[0] + letter[1] - letter[2]
        nr = carry_step(r, z)
        return (nr, z) if max(map(abs, nr)) <= bound else None

    out, _ = reachable(("x", "y", "z"), ((0, 0, 0), 0), step,
                       lambda s: value(s[0]) == s[1])
    print("raw adder", out.stats(), flush=True)
    return intersect(minimize(out), greedy("x"), greedy("y"), greedy("z"))


def dump(dfa, path):
    path.write_text(json.dumps({"names": dfa.names, "start": dfa.start,
                               "rows": dfa.rows, "final": sorted(dfa.final)},
                              separators=(",", ":")) + "\n")


def author_table(name):
    source = Path(__file__).parent.parent / "correspondence/attachments/a076502_morphic_check.py"
    tree = ast.parse(source.read_text())
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == name
                                               for t in node.targets):
            return ast.literal_eval(node.value)
    raise ValueError(name)


def candidate_graph(bound=8):
    e = author_table("E_DFAO")
    g = greedy("_")

    def step(state, letter):
        q, gx, gy, older, recent, r, last = state
        x, y = letter
        qn = e[q][x]
        gxn, gyn = g.rows[gx][x], g.rows[gy][y]
        if min(qn, gxn, gyn) < 0:
            return None
        z = older - y
        nr = carry_step(r, z)
        if max(map(abs, nr)) > bound:
            return None
        return qn, gxn, gyn, recent, x, nr, z

    out, _ = reachable(("n", "b"), (0, g.start, g.start, 0, 0, (0, 0, 0), 0),
                       step, lambda s: value(s[-2]) - s[-1] + e[s[0]][2] == 0)
    print("raw candidate graph", out.stats(), flush=True)
    return minimize(out)


def constant(name, n):
    if n == 0:
        return DFA((name,), [[0, -1]], {0})
    if n == 1:
        return DFA((name,), [[0, 1], [-1, -1]], {1})
    raise ValueError(n)


def at_least_two(name):
    # Canonical representations of 0 and 1 are exactly 0* and 0*1.
    seen = DFA((name,), [[0, 1], [2, 2], [2, 2]], {2})
    return intersect(greedy(name), seen)


def difference_graph():
    table, g = author_table("D_DFAO"), greedy("n")

    def step(state, letter):
        q, r, d = state
        x, y = letter
        if d == 1:
            return None
        qn, rn = table[q][x], g.rows[r][x]
        return None if min(qn, rn) < 0 else (qn, rn, y)

    out, _ = reachable(("n", "d"), (0, g.start, 0), step,
                       lambda s: table[s[0]][2] == s[2])
    return minimize(out)


def recurrence_check(add, graph, directory):
    result = {}

    def save(label, dfa):
        result[label] = dfa.stats()
        dump(dfa, directory / f"{label}.json")
        print(label, dfa.stats(), flush=True)
        return dfa

    def compose(left, right, keep):
        return project(intersect(left, right), keep)

    bounded = save("bounded", project(intersect(graph, rename(add, ("b", "r", "n"))), ("n",)))
    result["bounded_counterexample"] = inclusion(prefixed_zero_domain(("n",), 3), bounded)
    zeros = project(intersect(graph, constant("b", 0)), ("n",))
    result["positive_counterexample"] = inclusion(zeros, constant("n", 0))
    succ = save("successor", project(intersect(rename(add, ("m", "one", "n")),
                                              constant("one", 1)), ("n", "m")))
    pred_b = save("b_of_predecessor", compose(succ, rename(graph, ("m", "p")), ("n", "p")))
    h = save("h", compose(pred_b, rename(add, ("h", "p", "n")), ("n", "h")))
    bh = save("b_of_h", compose(h, rename(graph, ("h", "v")), ("n", "v")))
    k = save("k", compose(bh, rename(add, ("k", "v", "n")), ("n", "k")))
    bk = save("b_of_k", compose(k, rename(graph, ("k", "w")), ("n", "w")))
    good = save("recurrence", project(intersect(graph, bk, rename(add, ("b", "w", "n"))), ("n",)))
    domain = intersect(prefixed_zero_domain(("n",), 3), at_least_two("n"))
    result["recurrence_counterexample"] = inclusion(domain, good)
    next_b = compose(rename(succ, ("np", "n")), rename(graph, ("np", "bp")), ("n", "bp"))
    diff_good = save("first_difference", project(intersect(graph, next_b, difference_graph(),
                                    rename(add, ("b", "d", "bp"))), ("n",)))
    result["difference_counterexample"] = inclusion(prefixed_zero_domain(("n",), 3), diff_good)
    e = author_table("E_DFAO")
    assert e[0][2] == 0 and e[e[0][1]][2] == 1
    result["base_values"] = {"b(0)": 0, "b(1)": 1}
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--bound", type=int, default=12)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("automata-results"))
    args = parser.parse_args()
    args.output.mkdir(exist_ok=True)
    t = time.monotonic()
    add = adder(args.bound)
    print("trimmed canonical adder", add.stats(), flush=True)
    dump(add, args.output / "adder.json")
    dom = project(add, ("x", "y"))
    print("adder domain", dom.stats(), flush=True)
    witness = inclusion(prefixed_zero_domain(("x", "y"), 3), dom)
    report = {"bound": args.bound, "adder": add.stats(), "domain": dom.stats(),
              "totality_counterexample": witness,
              "seconds": time.monotonic() - t}
    if witness is not None:
        raise RuntimeError(f"adder totality failed: {witness}")
    graph = candidate_graph(args.bound)
    dump(graph, args.output / "candidate-graph.json")
    print("candidate graph", graph.stats(), flush=True)
    graphdom = project(graph, ("n",))
    report["graph"] = graph.stats()
    report["graph_totality_counterexample"] = inclusion(prefixed_zero_domain(("n",), 3), graphdom)
    if report["graph_totality_counterexample"] is not None:
        raise RuntimeError("graph totality failed")
    report["identification"] = recurrence_check(add, graph, args.output)
    report["seconds"] = time.monotonic() - t
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report), flush=True)
    if any(v is not None for k, v in report["identification"].items()
           if k.endswith("counterexample")):
        raise RuntimeError("identification failed; see report counterexample")


if __name__ == "__main__":
    main()
