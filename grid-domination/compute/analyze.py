#!/usr/bin/env python3
"""Exact values for many n, and a proof by exact computation that they continue for ever.

    python3 analyze.py M NMAX        (M = height 1..4; NMAX = 2000 is plenty)

Prints gamma_{2}(P_M x P_n) for n <= NMAX, compares it with the formula, and looks for
N, p, q with  v_{N+p} = v_N + q  entrywise, where v_n is the vector of the dynamic programme
(one entry per state of the column automaton; v_n[s] is the least weight of n columns that
lead to state s).

Why that settles every n.  One step of the dynamic programme is
    v_{n+1}[t] = min over transitions s -> t of (v_n[s] + weight of the new column),
so adding a constant q to every entry of v_n adds q to every entry of v_{n+1}.  Hence
v_{N+p} = v_N + q implies v_{n+p} = v_n + q for every n >= N, and therefore
gamma(n + p) = gamma(n) + q for every n >= N.  The formula has the same property, so checking it
for n < N + p proves it for all n.

This script uses its own construction of the automaton (states found by search from the start
state), independent of strip.py which the Lean generator uses.
"""
import sys
from itertools import product

def automaton(m):
    cols = list(product(range(3), repeat=m))
    def need(b, d):
        return tuple(max(0, 2 - b[i] - d[i] - (d[i-1] if i > 0 else 0) - (d[i+1] if i < m-1 else 0))
                     for i in range(m))
    zero = (0,) * m
    start = (zero, zero)
    index = {start: 0}
    states = [start]
    trans = []                     # (src, dst, weight, column)
    k = 0
    while k < len(states):
        b, nu = states[k]
        for d in cols:
            if all(d[i] >= nu[i] for i in range(m)):
                t = (d, need(b, d))
                if t not in index:
                    index[t] = len(states); states.append(t)
                trans.append((k, index[t], sum(d), d))
        k += 1
    final = [i for i, (b, nu) in enumerate(states) if nu == zero]
    return states, trans, final

def formula(m, n):
    if m == 1:
        return 2 * -(-n // 3)              # Lee-Liu Theorem 2.1
    if m == 2:
        return n + 1                       # Lee-Liu Theorem 2.3
    if m == 3:
        return 3 * n // 2 + 1              # Lee-Liu Conjecture 2.5
    if m == 4:
        return 2 * n - (n - 9) // 10       # Lee-Liu Conjecture 3.7, stated for n >= 49
    raise ValueError

if __name__ == "__main__":
    m = int(sys.argv[1]); nmax = int(sys.argv[2])
    states, trans, final = automaton(m)
    S = len(states)
    print(f"m={m}: {S} states, {len(trans)} transitions, {len(final)} final states")
    preds = [[] for _ in range(S)]          # preds[t] = list of (source, weight)
    for a, t, w, _ in trans:
        preds[t].append((a, w))
    preds = [sorted(set(p)) for p in preds]
    INF = 1 << 50
    v = [INF] * S; v[0] = 0
    hist = [v]
    gam = [None]
    for n in range(1, nmax + 1):
        v = [min(min(v[a] + w for a, w in p), INF) for p in preds]
        hist.append(v)
        gam.append(min(v[i] for i in final))
    bad = [n for n in range(1, nmax + 1) if gam[n] != formula(m, n)]
    print("n where gamma(n) != formula(n):", bad)
    print("first values:", gam[1:61])
    # vector periodicity
    found = None
    for p in range(1, 61):
        for N in range(0, nmax - p + 1):
            a, b = hist[N], hist[N + p]
            if max(a) < INF and len({y - x for x, y in zip(a, b)}) == 1:
                found = (N, p, b[0] - a[0]); break
        if found: break
    print("vector periodicity (N, p, q):", found)
    if found:
        N, p, q = found
        ok = all(hist[n + p] == [x + q for x in hist[n]] for n in range(N, nmax - p + 1))
        print("  holds for all computed n >= N:", ok)
        first_ok = min(n for n in range(1, N + p)
                       if all(gam[k] == formula(m, k) for k in range(n, N + p)))
        print(f"  formula holds for all n in [{first_ok}, {N + p}), hence for all n >= {first_ok}")
