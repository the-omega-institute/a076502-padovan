#!/usr/bin/env python3
"""Exact global discrepancy enclosures with realizable near-extremal witnesses.

Root precision scales with suffix length. See morphic-and-extrema.md for the
proof of enclosure, realization, and convergence to the global inf/sup.
"""

from fractions import Fraction as F
import json
from pathlib import Path

from automata_proof import author_table, greedy


def root_bracket(bits):
    lo, hi = F(0), F(1)
    for _ in range(bits):
        mid = (lo + hi) / 2
        if mid**3 - mid**2 + 2 * mid - 1 < 0:
            lo = mid
        else:
            hi = mid
    assert lo**3 - lo**2 + 2 * lo - 1 < 0 < hi**3 - hi**2 + 2 * hi - 1
    return lo, hi


def certificate(length):
    assert length >= 5
    precision = 4 * length + 64
    c_lo, c_hi = root_bracket(precision)
    e, g = author_table("E_DFAO"), greedy("n")
    start = (0, g.start)
    prefixes = {start: ""}
    queue = [start]
    for state in queue:
        q, r = state
        for bit in (0, 1):
            nxt = e[q][bit], g.rows[r][bit]
            if min(nxt) >= 0 and nxt not in prefixes:
                prefixes[nxt] = prefixes[state] + str(bit)
                queue.append(nxt)
    weights = [1, 2, 3, 4, 5]
    while len(weights) <= length + max(map(len, prefixes.values())):
        weights.append(weights[-2] + weights[-3])

    # Each endpoint carries its own attaining path and starting prefix state.
    lo_paths = {s: (F(0), "", s) for s in queue}
    hi_paths = dict(lo_paths)
    for p in reversed(range(length)):
        shifted = weights[p-2] if p >= 2 else 0
        dl, du = shifted - c_hi * weights[p], shifted - c_lo * weights[p]
        new_lo, new_hi = {}, {}
        for state in lo_paths:
            q, r = state
            for bit in (0, 1):
                nxt = e[q][bit], g.rows[r][bit]
                if min(nxt) < 0:
                    continue
                a, word, origin = lo_paths[state]
                entry = a + bit * dl, word + str(bit), origin
                if nxt not in new_lo or entry[0] < new_lo[nxt][0]:
                    new_lo[nxt] = entry
                a, word, origin = hi_paths[state]
                entry = a + bit * du, word + str(bit), origin
                if nxt not in new_hi or entry[0] > new_hi[nxt][0]:
                    new_hi[nxt] = entry
        lo_paths, hi_paths = new_lo, new_hi
    low_state = min(lo_paths, key=lambda s: lo_paths[s][0] + e[s[0]][2])
    high_state = max(hi_paths, key=lambda s: hi_paths[s][0] + e[s[0]][2])
    suffix_lo = lo_paths[low_state][0] + e[low_state[0]][2]
    suffix_hi = hi_paths[high_state][0] + e[high_state[0]][2]
    tail = F(5, 16) * F(7, 8)**(length - 3) / (1 - F(7, 8)**5)

    def witness(paths, final):
        _, suffix, origin = paths[final]
        word = prefixes[origin] + suffix
        q, r = start
        for char in word:
            bit = int(char)
            q, r = e[q][bit], g.rows[r][bit]
            assert min(q, r) >= 0
        assert (q, r) == final
        n = sum(weights[p] for p, ch in enumerate(reversed(word)) if ch == "1")
        a = e[q][2] + sum(weights[p-2] for p, ch in enumerate(reversed(word))
                          if ch == "1" and p >= 2)
        lo, hi = a - c_hi * n, a - c_lo * n
        return {"n": n, "a_n_from_proved_identification": a,
                "representation": word.lstrip("0") or "",
                "discrepancy_interval": [str(lo), str(hi)],
                "decimal_display_only": [float(lo), float(hi)]}, lo, hi

    low_witness, _, low_hi = witness(lo_paths, low_state)
    high_witness, high_lo, _ = witness(hi_paths, high_state)
    inf_interval, sup_interval = (suffix_lo-tail, low_hi), (high_lo, suffix_hi+tail)
    assert inf_interval[0] <= inf_interval[1] and sup_interval[0] <= sup_interval[1]
    if length >= 70:
        assert suffix_lo - tail > -F(10493, 10000)
        assert suffix_hi + tail < F(1444, 1250)
    # Every chosen prefix has bounded length H. This bounds both the DP root
    # error and the error when enclosing the realized witness's discrepancy.
    h = max(map(len, prefixes.values()))
    convergence_bound = 2 * tail + (c_hi - c_lo) * (weights[length] + weights[length+h])
    assert all(b-a <= convergence_bound for a, b in (inf_interval, sup_interval))

    def outward_decimal(interval, digits=12):
        scale = 10**digits
        a, b = (x * scale for x in interval)
        integers = a.numerator // a.denominator, -((-b.numerator) // b.denominator)
        assert F(integers[0], scale) <= interval[0] <= interval[1] <= F(integers[1], scale)
        return [("-" if n < 0 else "") + str(abs(n)//scale) + "." +
                str(abs(n) % scale).zfill(digits) for n in integers]

    if length >= 200:
        assert suffix_lo-tail > -F(1049234, 1000000)
        assert suffix_hi+tail < F(1155081, 1000000)
    return {"suffix_length": length, "root_bisection_bits": precision,
            "prefix_states": len(prefixes), "maximum_witness_prefix_length": h,
            "tail_bound": str(tail), "c_interval": [str(c_lo), str(c_hi)],
            "global_strict_bounds": [str(suffix_lo-tail), str(suffix_hi+tail)],
            "global_bounds_decimal_display_only": [float(suffix_lo-tail), float(suffix_hi+tail)],
            "infimum_enclosure": [str(x) for x in inf_interval],
            "supremum_enclosure": [str(x) for x in sup_interval],
            "infimum_outward_decimal_enclosure": outward_decimal(inf_interval),
            "supremum_outward_decimal_enclosure": outward_decimal(sup_interval),
            "extrema_enclosure_widths_display_only": [float(b-a) for a,b in (inf_interval,sup_interval)],
            "proven_convergence_width_bound": str(convergence_bound),
            "lower_witness": low_witness, "upper_witness": high_witness,
            "scope": "global infimum/supremum over n>=0; no claim about attainment or liminf/limsup"}


if __name__ == "__main__":
    reports = [certificate(k) for k in (20, 70, 120, 200)]
    report = {"status": "exact_rational_computer_assisted_not_Lean",
              "certificates": reports}
    target = Path(__file__).with_name("automata-results") / "extrema.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    for r in reports:
        print(json.dumps({k:r[k] for k in ("suffix_length", "global_bounds_decimal_display_only",
                                          "extrema_enclosure_widths_display_only")}))
        print("witnesses:", r["lower_witness"]["n"], r["upper_witness"]["n"])
