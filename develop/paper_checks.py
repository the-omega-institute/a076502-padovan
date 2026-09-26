#!/usr/bin/env python3
"""Differential checks for the manuscript additions and author attachment."""

import ast
from fractions import Fraction as F
import hashlib
from itertools import product
import json
from pathlib import Path
import subprocess
import sys

from automata_proof import author_table, greedy
from extrema_certificate import certificate

ROOT = Path(__file__).parent
RESULTS = ROOT / "automata-results"


def brute_suffix(length):
    result = certificate(length)
    c_lo, c_hi = map(F, result["c_interval"])
    e, g = author_table("E_DFAO"), greedy("n")
    states = {(0, g.start)}
    while True:
        more = {(e[q][b], g.rows[r][b]) for q, r in states for b in (0, 1)
                if e[q][b] >= 0 and g.rows[r][b] >= 0}
        if more <= states:
            break
        states |= more
    weights = [1, 2, 3, 4, 5]
    while len(weights) < length:
        weights.append(weights[-2] + weights[-3])
    lower, upper, paths = None, None, 0
    for word in product((0, 1), repeat=length):
        value = sum(b * weights[p] for p, b in enumerate(reversed(word)))
        shifted = sum(b * weights[p-2] for p, b in enumerate(reversed(word)) if p >= 2)
        for q, r in states:
            for bit in word:
                q, r = e[q][bit], g.rows[r][bit]
                if min(q, r) < 0:
                    break
            else:
                paths += 1
                a, b = shifted + e[q][2] - c_hi * value, shifted + e[q][2] - c_lo * value
                lower = a if lower is None else min(lower, a)
                upper = b if upper is None else max(upper, b)
    tail = F(result["tail_bound"])
    assert (lower-tail, upper+tail) == tuple(map(F, result["global_strict_bounds"]))
    return {"suffix_length": length, "enumerated_accepted_paths": paths, "DP_matches_enumeration": True}


def witness_checks():
    reports = json.loads((RESULTS / "extrema.json").read_text())["certificates"]
    graph = json.loads((RESULTS / "candidate-graph.json").read_text())
    weights = [1, 2, 3, 4, 5]

    def representation(value):
        while weights[-1] <= value:
            weights.append(weights[-2] + weights[-3])
        bits = []
        for weight in reversed(weights):
            b = int(value >= weight)
            value -= b * weight
            bits.append(str(b))
        assert value == 0
        return "".join(bits).lstrip("0")

    checked = 0
    for report in reports:
        for key in ("lower_witness", "upper_witness"):
            witness = report[key]
            x, y = representation(witness["n"]), representation(witness["a_n_from_proved_identification"])
            assert x == witness["representation"]
            size = max(len(x), len(y)) + 3
            state = graph["start"]
            for u, v in zip(x.zfill(size), y.zfill(size)):
                state = graph["rows"][state][2*int(u)+int(v)]
                assert state >= 0
            assert state in graph["final"]
            checked += 1
    small = reports[0]
    bound = max(small[key]["n"] for key in ("lower_witness", "upper_witness"))
    a = [0, 1]
    for n in range(2, bound+1):
        a.append(n - a[n-a[n-a[n-1]]])
    for key in ("lower_witness", "upper_witness"):
        assert a[small[key]["n"]] == small[key]["a_n_from_proved_identification"]
    return {"witnesses_accepted_by_saved_graph": checked,
            "small_witnesses_match_literal_recurrence": 2}


def replay_author():
    source = ROOT.parent / "correspondence/attachments/a076502_independent_reverification.py"
    tree = ast.parse(source.read_text())
    table = next(ast.literal_eval(node.value) for node in tree.body if isinstance(node, ast.Assign)
                 and any(isinstance(t, ast.Name) and t.id == "E" for t in node.targets))
    assert table == author_table("E_DFAO")
    results = []
    for bound in (8, 10):
        run = subprocess.run([sys.executable, str(source), str(bound)], capture_output=True,
                             text=True, check=True, timeout=60)
        # The author's script prints failed checks; an exit code alone is insufficient.
        required = ["adder: 411 states", "graph (n,b(n)): 72 states", "Good(n): 7 states",
                    "adder totality, 000(GxG) included in exists z: OK",
                    "graph totality on 000G: OK",
                    "recurrence for all n>=2, (000G, value>=2) included in Good: OK",
                    "b(n) <= n for all n: OK", "b(n) = 0 only for n = 0: OK",
                    "b(0) = 0 ; b(1) = 1"]
        assert all(line in run.stdout.splitlines() for line in required)
        assert "COUNTEREXAMPLE" not in run.stdout and "False" not in run.stdout
        (RESULTS / f"author-reverification-box-{bound}.txt").write_text(run.stdout)
        results.append({"carry_box": bound, "required_checks_pass": True})
    return {"sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "bytes": source.stat().st_size, "E_table_matches_original_attachment": True,
            "replays": results}


if __name__ == "__main__":
    report = {"author": replay_author(), "suffix_DP": [brute_suffix(k) for k in (5, 8, 12)],
              "witness_checks": witness_checks()}
    (RESULTS / "paper-checks.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
