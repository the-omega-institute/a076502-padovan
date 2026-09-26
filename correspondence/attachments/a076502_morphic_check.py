#!/usr/bin/env python3
"""
A076502:  a(1) = 1,  a(n) = n - a(n - a(n - a(n-1)))  for n >= 2.

Conjectural morphic description of the first-difference word
    d(n) = a(n+1) - a(n),   n >= 1      (so a(n) = 1 + d(1) + ... + d(n-1)).

Data
----
Alphabet {S, a, b, c, d, e, f}  (S is a start symbol that occurs only once).

Substitution tau (S is prolongable, the infinite word is X = tau^omega(S)):
    S -> S a b c d e c f
    a -> a d
    b -> a b e c b c f
    c -> a d c d
    d -> a b e c d e c b c f
    e -> a d e c f
    f -> a b e c f

Output morphism pi (non-erasing, not a coding):
    S -> 0101100111        (exceptional prefix, d(1)..d(10))
    a -> 010
    b -> 010111011
    c -> 0100110
    d -> 01011100111011
    e -> 0100111
    f -> 010111

Claim (empirical):  d(1) d(2) d(3) ... = pi(X).

Equivalent form without S: with sigma = tau restricted to {a,...,f} and
p = abcdecf, the word x = p sigma(p) sigma^2(p) ... satisfies x = p sigma(x),
and d = 0101100111 . pi(x).

Padovan numeration (second conjectural description)
---------------------------------------------------
U_0, U_1, ... = 1, 2, 3, 4, 5, 7, 9, 12, 16, 21, ...  with U_p = U_(p-2) + U_(p-3)
for p >= 4.  Every n >= 0 has a greedy expansion n = sum of U_p, p in D(n).
Read most significant digit first, without leading zeros (n = 0 is the empty
word).  The greedy words are exactly the binary words in which two consecutive
1s are at distance >= 5, except that positions 4 and 0 may both carry a 1
(6 = 5 + 1).

    shift2(n) = sum of U_(p-2) over the p >= 2 in D(n).

Claim (empirical):  a(n) = shift2(n) + e(n)  for all n >= 0 (with a(0) = 0),
where e(n) in {-1, 0, 1, 2} is the output of the 28-state DFAO E_DFAO below.
The DFAO D_DFAO outputs d(n) = a(n+1) - a(n) (with d(0) = 1).
Each row is (next state on 0, next state on 1, output), -1 = undefined
(the word is not a greedy expansion).  The initial state is q0.
Both automata were checked against the recurrence for all n <= 2*10^8.

Usage:  python3 a076502_morphic_check.py [N]      (default N = 10^6)
"""
import sys

TAU = {
    "S": "Sabcdecf",
    "a": "ad",
    "b": "abecbcf",
    "c": "adcd",
    "d": "abecdecbcf",
    "e": "adecf",
    "f": "abecf",
}
PI = {
    "S": "0101100111",
    "a": "010",
    "b": "010111011",
    "c": "0100110",
    "d": "01011100111011",
    "e": "0100111",
    "f": "010111",
}

D_DFAO = [
    (0, 1, 1), (2, -1, 0), (3, -1, 1), (4, -1, 0), (5, 6, 1), (7, 8, 1), (-1, -1, 0),
    (9, 10, 0), (11, -1, 1), (5, 12, 1), (13, -1, 1), (14, -1, 0), (15, -1, 0), (16, -1, 0),
    (17, -1, 1), (18, -1, 1), (19, -1, 1), (20, 21, 0), (22, -1, 1), (23, 21, 0), (24, 1, 0),
    (-1, -1, 1), (9, 21, 0), (25, 10, 1), (26, 1, 1), (20, 27, 0), (23, 8, 0), (15, -1, 1),
]
E_DFAO = [
    (0, 1, 0), (2, -1, 1), (3, -1, 1), (4, -1, 1), (5, 6, 0), (7, 8, 0), (-1, -1, 1),
    (9, 10, 0), (11, -1, 0), (5, 12, 0), (13, -1, 1), (14, -1, 2), (15, -1, 1), (16, -1, 1),
    (17, -1, 0), (18, -1, 1), (19, -1, 1), (20, 21, 1), (22, -1, 1), (23, 21, 1), (24, 1, 0),
    (-1, -1, 0), (9, 6, 0), (25, 10, -1), (26, 1, 0), (20, 27, 1), (23, 8, 1), (15, -1, 0),
]


def greedy_bits(n, U):
    """msd-first greedy Padovan expansion of n, no leading zeros."""
    bits = []
    for p in range(len(U) - 1, -1, -1):
        if U[p] <= n:
            n -= U[p]
            bits.append(1)
        elif bits:
            bits.append(0)
    return bits


def run(dfao, bits):
    q = 0
    for b in bits:
        q = dfao[q][b]
        if q < 0:
            return None
    return dfao[q][2]


def nested(N):
    """a[1..N] from the literal recurrence (a[0] unused)."""
    a = [0] * (N + 1)
    a[1] = 1
    for n in range(2, N + 1):
        a[n] = n - a[n - a[n - a[n - 1]]]
    return a


def morphic_bits(N):
    """First N letters of pi(tau^omega(S)) as a list of 0/1."""
    X = "S"
    # |pi(letter)| >= 3, so len(X) >= N/3 + 1 is more than enough
    while len(X) < N // 3 + 2:
        X = "".join(TAU[ch] for ch in X)
    out = []
    for ch in X:
        out.extend(1 if t == "1" else 0 for t in PI[ch])
        if len(out) >= N:
            break
    return out[:N]


def padovan(limit):
    U = [1, 2, 3, 4, 5]  # U_0..U_4, then U_p = U_(p-2) + U_(p-3)
    while U[-1] <= limit:
        U.append(U[-2] + U[-3])
    return U


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6
    a = nested(N + 1)
    d = morphic_bits(N)

    # 1. morphic description of the first differences
    bad = next((n for n in range(1, N + 1) if a[n + 1] - a[n] != d[n - 1]), None)
    print(f"[1] d(n) = pi(X)(n) for 1 <= n <= {N}:", "OK" if bad is None else f"FAILS at n={bad}")

    # 2. reconstruction of a from the morphic word
    s, ok = 1, True
    for n in range(1, N + 1):
        if s != a[n]:
            ok = False
            break
        s += d[n - 1]
    print(f"[2] a(n) = 1 + sum_(k<n) pi(X)(k) for n <= {N}:", "OK" if ok else "FAILS")

    # 3. Padovan numeration: U_0.. = 1,2,3,4,5,7,9,12,...
    U = padovan(N)
    ok3 = all(a[U[p]] == U[p - 2] for p in range(3, len(U)) if U[p] <= N)
    print("[3] a(U_p) = U_(p-2) for p >= 3:", "OK" if ok3 else "FAILS")

    # 4. a(n) minus the right shift by two positions of the greedy expansion
    seen = set()
    for n in range(1, N + 1):
        m, sh = n, 0
        for p in range(len(U) - 1, -1, -1):
            if U[p] <= m:
                m -= U[p]
                if p >= 2:
                    sh += U[p - 2]
        seen.add(a[n] - sh)
    print("[4] values of a(n) - shift2(n):", sorted(seen))

    # 5. offsets a(n) - floor(c n), c = positive root of x^3 - x^2 + 2x - 1,
    #    floor computed exactly from the sign of k^3 - k^2 n + 2 k n^2 - n^3
    offs = set()
    for n in range(1, N + 1):
        k = (5698 * n) // 10000 - 2
        while (k + 1) ** 3 - (k + 1) ** 2 * n + 2 * (k + 1) * n * n - n**3 < 0:
            k += 1
        offs.add(a[n] - k)
    print("[5] values of a(n) - floor(c n):", sorted(offs))

    # 6. the two Padovan DFAOs (a(0) = 0 by convention)
    a[0] = 0
    bad_d = bad_e = 0
    for n in range(0, N + 1):
        bits = greedy_bits(n, U)
        sh = sum(U[len(bits) - 1 - i - 2] for i, b in enumerate(bits) if b and len(bits) - 1 - i >= 2)
        if run(D_DFAO, bits) != a[n + 1] - a[n]:
            bad_d += 1
        if run(E_DFAO, bits) != a[n] - sh:
            bad_e += 1
    print(f"[6] DFAO for d(n): {bad_d} errors ; DFAO for e(n) = a(n) - shift2(n): {bad_e} errors (0 <= n <= {N})")


if __name__ == "__main__":
    main()
