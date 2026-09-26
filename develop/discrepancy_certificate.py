#!/usr/bin/env python3
"""Exact rational bound for Cloitre's Padovan candidate, not a Lean proof.

Finite weighted-path extrema bound the last L digits, while the proven
quadratic-energy estimate bounds every possible higher-position tail.
"""

from fractions import Fraction as F
import json
from pathlib import Path

from automata_proof import author_table, greedy


def cubic(x):
    return x**3 - x**2 + 2*x - 1


def certificate(length=20):
    lower, upper = F(569840290998, 10**12), F(569840290999, 10**12)
    assert cubic(lower) < 0 < cubic(upper)
    weights = [1, 2, 3, 4, 5]
    while len(weights) < length:
        weights.append(weights[-2] + weights[-3])
    deltas = []
    for p, weight in enumerate(weights):
        shifted = weights[p-2] if p >= 2 else 0
        deltas.append((shifted - upper*weight, shifted - lower*weight))

    e, g = author_table("E_DFAO"), greedy("n")
    start = (0, g.start)
    reachable = {start}
    queue = [start]
    for q, r in queue:
        for b in (0, 1):
            nxt = (e[q][b], g.rows[r][b])
            if min(nxt) >= 0 and nxt not in reachable:
                reachable.add(nxt)
                queue.append(nxt)

    # Every admissible higher prefix ends in one of these states. Prefixes
    # and suffixes are deliberately decoupled for a conservative bound.
    ranges = {state: (F(0), F(0)) for state in reachable}
    for position in reversed(range(length)):
        nxt_ranges = {}
        for (q, r), (lo, hi) in ranges.items():
            for b in (0, 1):
                nxt = (e[q][b], g.rows[r][b])
                if min(nxt) < 0:
                    continue
                new = (lo + b*deltas[position][0], hi + b*deltas[position][1])
                if nxt in nxt_ranges:
                    old = nxt_ranges[nxt]
                    new = min(old[0], new[0]), max(old[1], new[1])
                nxt_ranges[nxt] = new
        ranges = nxt_ranges
    lo = min(v[0] + e[q][2] for (q, _), v in ranges.items())
    hi = max(v[1] + e[q][2] for (q, _), v in ranges.items())
    tail = F(5, 16) * F(7, 8)**(length-3) / (1-F(7, 8)**5)
    assert lo-tail > -F(11, 10) and hi+tail < F(6, 5)
    return {"suffix_length": length, "prefix_states": len(reachable),
            "c_interval": [str(lower), str(upper)],
            "suffix_lower": str(lo), "suffix_upper": str(hi),
            "tail_bound": str(tail), "lower": str(lo-tail), "upper": str(hi+tail),
            "decimal_bounds_display_only": [float(lo-tail), float(hi+tail)],
            "simple_strict_bounds": ["-11/10", "6/5"],
            "sharp_floor_offsets_contained_in": [-1, 0, 1, 2],
            "assumptions": ["Exact greedy-language lemma", "Quadratic-energy tail lemma",
                            "b(n)=shift2(n)+E(greedy(n))", "c=rho^-2"]}


if __name__ == "__main__":
    report = certificate()
    target = Path(__file__).with_name("automata-results") / "discrepancy.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
