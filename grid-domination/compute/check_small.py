#!/usr/bin/env python3
"""Independent checks of the column automaton against brute force.

    python3 check_small.py

1. For every grid with at most 14 vertices (heights 1 to 4), compute the {2}-domination number by
   trying all assignments of weights 0, 1, 2 directly from the definition (no automaton), and
   compare with the dynamic programme over columns.
2. Transposing a grid does not change the number: compare gamma(m, n) with gamma(n, m) for
   m, n <= 5, each computed by the dynamic programme of the other height.
3. Compare with the theorems and the table of Lee and Liu (arXiv:2502.00134): heights 1 and 2
   for n <= 60, and the list of values for the 4 x n grid, n <= 100 (their Theorem 3.6).
4. Compare the saved outputs of fast.c (results/out_M.txt, heights 1 to 10) with this script's
   own values for heights up to 5, with each other through gamma(m, n) = gamma(n, m), and with
   the formulas stated in the README.
"""
import os
from itertools import product

from strip import Strip


def brute(m, n):
    cells = [(i, j) for i in range(m) for j in range(n)]
    nbrs = []
    for (i, j) in cells:
        nb = [(i, j)] + [(a, b) for a, b in ((i - 1, j), (i + 1, j), (i, j - 1), (i, j + 1))
                         if 0 <= a < m and 0 <= b < n]
        nbrs.append([a * n + b for a, b in nb])
    best = 2 * m * n
    for f in product(range(3), repeat=m * n):
        s = sum(f)
        if s < best and all(sum(f[k] for k in nb) >= 2 for nb in nbrs):
            best = s
    return best


def dp_values(m, nmax):
    S = Strip(m)
    hist = S.forward(nmax)
    return [None] + [min(hist[n][k] for k in S.final) for n in range(1, nmax + 1)]


def lee_liu_table(n):
    """Theorem 3.6 of Lee and Liu: gamma(4, n) - 2n for n <= 100."""
    rows = [(2, [1]), (1, [2, 3, 5, 6]), (0, [4] + list(range(7, 15)) + [16, 17]),
            (-1, [15] + list(range(18, 26)) + [27, 28]), (-2, [26] + list(range(29, 37)) + [38]),
            (-3, [37] + list(range(39, 48))), (-4, range(48, 59)), (-5, range(59, 69)),
            (-6, range(69, 79)), (-7, range(79, 89)), (-8, range(89, 99)), (-9, [99, 100])]
    for c, ns in rows:
        if n in ns:
            return 2 * n + c
    raise ValueError(n)


if __name__ == "__main__":
    vals = {m: dp_values(m, 100) for m in range(1, 6)}

    count = 0
    for m in range(1, 5):
        for n in range(1, 15):
            if m * n <= 14:
                assert brute(m, n) == vals[m][n], (m, n)
                count += 1
    print(f"brute force agrees with the dynamic programme on all {count} grids with <= 14 vertices")

    for m in range(1, 6):
        for n in range(1, 6):
            assert vals[m][n] == vals[n][m], (m, n)
    print("gamma(m, n) = gamma(n, m) for m, n <= 5")

    assert all(vals[1][n] == 2 * -(-n // 3) for n in range(1, 61))
    assert all(vals[2][n] == n + 1 for n in range(1, 61))
    assert all(vals[4][n] == lee_liu_table(n) for n in range(1, 101))
    print("agrees with Lee-Liu Theorems 2.1, 2.3 (n <= 60) and with their table for 4 x n (n <= 100)")

    # ---- the saved outputs of fast.c
    here = os.path.dirname(os.path.abspath(__file__))
    fast = {}
    for m in range(1, 11):
        path = os.path.join(here, "results", f"out_{m}.txt")
        if os.path.exists(path):
            for line in open(path):
                if line.startswith("gamma:"):
                    fast[m] = [None] + [int(x) for x in line.split()[1:]]
    if fast:
        for m in fast:
            if m in vals:
                k = min(len(fast[m]), len(vals[m]))
                assert fast[m][1:k] == vals[m][1:k], m
        for m in fast:
            for n in fast:
                if n < len(fast[m]) and m < len(fast[n]):
                    assert fast[m][n] == fast[n][m], (m, n)

        def ceil(a, b):
            return -((-a) // b)

        stated = {
            1: lambda n: 2 * ceil(n, 3),
            2: lambda n: n + 1,
            3: lambda n: 3 * n // 2 + 1,
            4: lambda n: ceil(19 * n + 9, 10) + (n == 1) - (n in (4, 7, 8, 15, 18, 26, 37, 48)),
            5: lambda n: min((7 * n + 5) // 3, ceil(23 * n + 17, 10)),
            6: lambda n: ceil(41 * n + 18, 15) + (n == 16),
            7: lambda n: 3 * n + 3 + n // 11 + (n % 11 in (8, 10)) - (n in (2, 3, 4, 8)),
            8: lambda n: ceil(46 * n + 32, 13) - (n in (2, 3, 4, 5, 7, 9, 16, 18)),
            9: lambda n: 4 * n + 2,
            10: lambda n: (ceil(57 * n + 28, 13) - (n % 26 in (1, 5, 21)) + (n % 26 == 2)
                           + (n in (5, 7, 10, 17, 21, 25, 31, 33, 36, 51)) + 2 * (n == 1) - (n == 2)),
        }
        for m in fast:
            assert all(fast[m][n] == stated[m](n) for n in range(1, len(fast[m]))), m
        print(f"saved outputs of fast.c for heights {sorted(fast)}: agree with this script for "
              "heights <= 5, are symmetric in (m, n), and match the stated formulas for every "
              "computed n")
