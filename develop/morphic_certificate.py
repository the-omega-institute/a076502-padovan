#!/usr/bin/env python3
"""Construct a non-erasing morphic presentation from the verified D-DFAO.

The all-index argument is in morphic-and-extrema.md. Prefix comparisons below
are independent diagnostics, not a substitute for that argument.
"""

from collections import deque
import json
from pathlib import Path

from automata_proof import author_table, greedy


def construct():
    d, g = author_table("D_DFAO"), greedy("n")
    # The marker represents epsilon. Its only canonical child starts with 1.
    root = (d[0][1], g.rows[g.start][1])
    states, seen = [root], {root}
    children = {}
    for state in states:
        q, r = state
        row = []
        for bit in (0, 1):
            nxt = (d[q][bit], g.rows[r][bit])
            if min(nxt) >= 0:
                row.append(nxt)
                if nxt not in seen:
                    seen.add(nxt)
                    states.append(nxt)
            elif g.rows[r][bit] >= 0:
                raise AssertionError("D is undefined on a legal continuation")
        children[state] = row
    mortal = {state for state in states if not children[state]}
    immortal = [state for state in states if state not in mortal]
    assert all(any(t not in mortal for t in children[s]) for s in immortal)
    # Here each reachable D state determines the corresponding language state.
    assert len({q for q, _ in states}) == len(states)
    name = {state: f"q{state[0]}" for state in states}
    substitution = {"S": ["S", name[root]]}
    output = {"S": str(d[0][2]) + str(d[root[0]][2])}
    for state in immortal:
        substitution[name[state]] = [name[t] for t in children[state] if t not in mortal]
        output[name[state]] = "".join(str(d[t[0]][2]) for t in children[state])
    assert all(substitution.values()) and all(output.values())
    return substitution, output, states, mortal


def verify_prefix(substitution, output, limit=100000):
    word = ["S"]
    while sum(len(output[q]) for q in word) < limit:
        word = [t for q in word for t in substitution[q]]
    sequence = "".join(output[q] for q in word)[:limit]
    a = [0, 1]
    for n in range(2, limit + 1):
        a.append(n - a[n - a[n - a[n - 1]]])
    assert sequence == "".join(str(a[n + 1] - a[n]) for n in range(limit))

    # Check the distinct representation-order obligation independently.
    g = greedy("n")
    weights = [1, 2, 3, 4, 5]
    queue = deque([("", g.start)])
    for expected in range(limit):
        bits, state = queue.popleft()
        while len(weights) < len(bits):
            weights.append(weights[-2] + weights[-3])
        value = sum(weights[p] for p, bit in enumerate(reversed(bits)) if bit == "1")
        assert value == expected, (bits, value, expected)
        for bit in ((1,) if not bits else (0, 1)):
            nxt = g.rows[state][bit]
            if nxt >= 0:
                queue.append((bits + str(bit), nxt))
    return {"terms_compared_with_literal_recurrence": limit,
            "canonical_words_checked_in_genealogical_order": limit,
            "difference_prefix_from_n_zero": sequence[:81]}


if __name__ == "__main__":
    substitution, output, states, mortal = construct()
    report = {"status": "constructive_morphism_with_written_all_index_proof_not_Lean",
              "alphabet_size": len(substitution),
              "reachable_positive_representation_states": len(states),
              "removed_terminal_D_states": sorted(q for q, _ in mortal),
              "seed": "S", "substitution": substitution, "output_morphism": output,
              "indexing": "output(n) = a(n+1)-a(n), n>=0; first output is 1",
              "non_erasing_substitution": True, "non_erasing_output": True,
              "original_six_letter_identity": "not established",
              "diagnostics": verify_prefix(substitution, output)}
    target = Path(__file__).with_name("automata-results") / "morphic-presentation.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
