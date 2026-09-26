#!/usr/bin/env python3
"""Independent numerical diagnostics for the exact automata proof.

Does not import the proof generator or execute the author's script. The tables
are read as data. These tests are finite checks, not the universal proof.
"""

import ast
from array import array
import argparse
from fractions import Fraction
import json
from pathlib import Path
import random


HERE = Path(__file__).parent


def data():
    path = HERE.parent / "correspondence/attachments/a076502_morphic_check.py"
    out = {}
    for node in ast.parse(path.read_text()).body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id in ("E_DFAO", "D_DFAO", "TAU", "PI"):
                    out[target.id] = ast.literal_eval(node.value)
    return out


def weights(limit):
    ws = [1, 2, 3, 4]
    while ws[-1] <= limit:
        i = len(ws)
        ws.append(ws[i-2] + ws[i-3])
    return ws


def expansion(n, ws):
    selected = []
    for i in range(len(ws)-1, -1, -1):
        if n >= ws[i]:
            n -= ws[i]
            selected.append(i)
    assert n == 0
    return selected


def table_output(table, selected):
    if not selected:
        return table[0][2]
    occupied = set(selected)
    state = 0
    for i in range(selected[0], -1, -1):
        state = table[state][int(i in occupied)]
        assert state >= 0
    return table[state][2]


def candidate(n, ws, tables):
    selected = expansion(n, ws)
    shift = sum(ws[i-2] for i in selected if i >= 2)
    return shift + table_output(tables["E_DFAO"], selected)


def accepts(dfa, values, ws):
    positions = [set(expansion(n, ws)) for n in values]
    width = max((max(s, default=-1) for s in positions), default=-1)+4
    state = dfa["start"]
    for i in range(width-1, -1, -1):
        symbol = 0
        for selected in positions:
            symbol = 2*symbol + int(i in selected)
        state = dfa["rows"][state][symbol]
        if state < 0:
            return False
    return state in dfa["final"]


def floor_c_times(n):
    lo, hi = 0, n+1
    while hi-lo > 1:
        mid = (lo+hi)//2
        sign = mid**3-mid**2*n+2*mid*n*n-n**3
        if sign < 0:
            lo = mid
        else:
            hi = mid
    return lo


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=1000000)
    args = parser.parse_args()
    nmax = args.limit
    tables, ws = data(), weights(nmax+1)
    values = array("I", [0, 1])
    for n in range(2, nmax+2):
        i = n-values[n-1]
        j = n-values[i]
        assert 0 < i < n and 0 < j < n
        values.append(n-values[j])

    # Expand the morphism by a lazy depth-first traversal, rather than the
    # author's repeated whole-word concatenation.
    depth, wordlen = 0, {ch: len(out) for ch, out in tables["PI"].items()}
    while wordlen["S"] < nmax:
        wordlen = {ch: sum(wordlen[t] for t in out) for ch, out in tables["TAU"].items()}
        depth += 1
    stack, morph = [("S", depth)], bytearray()
    while stack and len(morph) < nmax:
        letter, d = stack.pop()
        if d:
            stack.extend((ch, d-1) for ch in reversed(tables["TAU"][letter]))
        else:
            morph.extend(int(b) for b in tables["PI"][letter])
    witnesses = {}
    for n in range(nmax+1):
        selected = expansion(n, ws)
        assert all(i-j >= 5 or (i,j) == (4,0) for i,j in zip(selected,selected[1:]))
        shift = sum(ws[i-2] for i in selected if i >= 2)
        assert values[n] == shift + table_output(tables["E_DFAO"], selected), n
        assert values[n+1]-values[n] == table_output(tables["D_DFAO"], selected), n
        if n:
            assert morph[n-1] == values[n+1]-values[n], n
        if n and len(witnesses) < 4:
            offset = values[n]-floor_c_times(n)
            witnesses.setdefault(offset, {"n": n, "a": values[n], "floor_cn": values[n]-offset})

    add = json.loads((HERE/"automata-results/adder.json").read_text())
    graph = json.loads((HERE/"automata-results/candidate-graph.json").read_text())
    rng = random.Random(760502)
    bigchecks = 0
    for bitlength in (32, 128, 512, 1024):
        bws = weights(1 << (bitlength+2))
        for _ in range(25):
            n, m = rng.getrandbits(bitlength), rng.getrandbits(bitlength)
            b = candidate(n, bws, tables)
            assert accepts(add, (n, m, n+m), bws)
            assert not accepts(add, (n, m, n+m+1), bws)
            assert accepts(graph, (n,b), bws)
            assert not accepts(graph, (n,b+1), bws)
            if n >= 2:
                i = n-candidate(n-1,bws,tables)
                j = n-candidate(i,bws,tables)
                assert b == n-candidate(j,bws,tables)
            bigchecks += 1
    report = {"independent_recurrence_prefix": nmax, "morphism_and_two_dfaos": "all matched",
              "all_four_offsets_witnessed": witnesses, "large_integer_cases": bigchecks,
              "largest_random_input_bits": 1024, "seed": 760502,
              "scope": "Finite diagnostics; universal proof is the separate finite-state inclusion argument."}
    (HERE/"automata-results/independent-checks.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
