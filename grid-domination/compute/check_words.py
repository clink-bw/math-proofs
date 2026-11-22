#!/usr/bin/env python3
"""Check upper bounds directly from the definition, without any dynamic programme.

    ./fast M NMAX THREADS WMAX > out_M.txt
    python3 check_words.py out_M.txt [more files ...] [--pictures]

The input is the output of fast.c with word output switched on.  For each height this script

1. rebuilds every listed pattern as an m x n table of weights and checks, square by square, that
   each square together with its neighbours has total weight at least 2, and that the total
   weight is the value gamma(n) that fast.c claims;
2. finds, in patterns with n >= N, a block of columns that can be repeated (the pair of columns
   before the block equals the pair at its end, so every window of three consecutive columns in
   the lengthened pattern already occurs in the original), checks that the block has the right
   weight, and checks several lengthened patterns directly as well;
3. confirms that the patterns and their lengthenings together cover every n >= 1 (it finds a
   block length ell such that every residue class modulo ell contains the length of a pattern
   with a repeatable block of ell columns).

So for every n there is a valid pattern of weight g(n), where g is fast.c's value for n < N + p
and is continued by g(n + p) = g(n) + q.  This is the upper bound for all n; only the lower
bound relies on the dynamic programme (or, for heights up to 5, on the Lean proof).
"""
import sys


def dg(c, i):
    return c // 3 ** i % 3


def valid(m, cols):
    n = len(cols)
    f = [[dg(c, i) for c in cols] for i in range(m)]
    for i in range(m):
        for j in range(n):
            s = f[i][j]
            if i > 0:
                s += f[i - 1][j]
            if i + 1 < m:
                s += f[i + 1][j]
            if j > 0:
                s += f[i][j - 1]
            if j + 1 < n:
                s += f[i][j + 1]
            if s < 2:
                return False
    return all(0 <= c < 3 ** m for c in cols)


def weight(m, cols):
    return sum(dg(c, i) for c in cols for i in range(m))


def picture(m, cols):
    return "\n".join(" ".join(".12"[dg(c, i)] for c in cols) for i in range(m))


def parse(path):
    m = N = p = q = None
    gam, words = [None], {}
    for line in open(path):
        t = line.split()
        if line.startswith("m="):
            m = int(t[0][2:])
        elif line.startswith("gamma:"):
            gam += [int(x) for x in t[1:]]
        elif line.startswith("word "):
            words[int(t[1])] = (int(t[2].rstrip(":")), [int(x) for x in t[3:]])
        elif line.startswith("periodicity:"):
            N, p, q = (int(x.split("=")[1]) for x in t[1:4])
    return m, gam, words, N, p, q


def check(path, pictures):
    m, gam, words, N, p, q = parse(path)
    wmax = max(words)
    assert set(words) == set(range(1, wmax + 1)) and wmax >= N + p

    assert len(gam) > N + p

    def g(n):                                   # fast.c's value, continued periodically
        k = 0
        while n >= len(gam):
            n -= p
            k += 1
        return gam[n] + k * q

    for n, (w, cols) in words.items():
        assert len(cols) == n and valid(m, cols) and weight(m, cols) == w == gam[n], (m, n)

    # repeatable blocks: fam[ell] = the lengths n whose pattern contains a block of ell columns
    # that can be repeated, of weight q * ell / p
    fam, shown = {}, None
    for n in range(N, wmax + 1):
        w, cols = words[n]
        for ell in range(1, n):
            found = None
            for i in range(0, n - ell - 1):
                if cols[i] == cols[i + ell] and cols[i + 1] == cols[i + ell + 1]:
                    block = cols[i + 1:i + ell + 1]
                    if weight(m, block) * p == q * ell:
                        found = (i, block)
                        break
            if not found:
                continue
            i, block = found
            # k extra copies add k * q * ell / p to the weight; g(n + k * ell) - k * q * ell / p
            # is periodic in k with period p, so checking k = 1..p settles all k.
            for k in range(1, max(3, p) + 1):
                longer = cols[:i + 1] + block * (k + 1) + cols[i + ell + 1:]
                assert len(longer) == n + k * ell and valid(m, longer)
                assert weight(m, longer) == g(n + k * ell), (m, n, k)
            fam.setdefault(ell, set()).add(n)
    # If, for some ell, every residue class modulo ell contains a length n0 whose pattern has a
    # repeatable block of ell columns, then every n beyond the listed patterns is n0 + k * ell
    # for such an n0, so every n >= 1 is covered.
    cover = None
    for ell in sorted(fam):
        first = {}
        for n0 in sorted(fam[ell]):
            first.setdefault(n0 % ell, n0)
        if len(first) == ell:
            cover = (ell, first)
            break
    if cover is None:
        best = max(fam, key=lambda e: len({n0 % e for n0 in fam[e]}) / e) if fam else None
        missing = sorted(set(range(best)) - {n0 % best for n0 in fam[best]}) if best else []
        print(f"m={m}: {len(words)} patterns valid with the claimed weights (n <= {wmax}); "
              f"repeatable blocks of {best} columns found, but not yet for the residues "
              f"{missing} modulo {best}: longer patterns are needed to cover every n")
        return
    ell, first = cover
    a = max(first.values())
    cols = words[a][1]
    for i in range(0, a - ell - 1):
        if cols[i] == cols[i + ell] and cols[i + 1] == cols[i + ell + 1]:
            if weight(m, cols[i + 1:i + ell + 1]) * p == q * ell:
                shown = cols[i + 1:i + ell + 1]
                break
    print(f"m={m}: {len(words)} patterns valid with the claimed weights; every residue modulo "
          f"{ell} has a pattern of length at most {a} with a repeatable block of {ell} columns, "
          f"so every n >= 1 is covered: gamma(n) <= g(n) for all n, with g(n+{p}) = g(n)+{q} "
          f"beyond n = {N}")
    if pictures:
        print(f"  a repeatable block ({len(shown)} columns, weight {weight(m, shown)}):")
        print("    " + picture(m, shown).replace("\n", "\n    "))


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    for path in args:
        check(path, "--pictures" in sys.argv)
