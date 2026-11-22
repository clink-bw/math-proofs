#!/usr/bin/env python3
"""Exact {2}-domination numbers of the m x n grid by dynamic programming over columns.

    python3 dp.py M NMAX

State after reading columns 1..j: (last column b, need vector nu), where nu_i is how much
weight the next column must still put in row i so that vertex (i, j) is dominated.
A column is a tuple in {0,1,2}^m.  Reading column d from state (b, nu) is allowed iff
d >= nu componentwise; the new state is (d, need(b, d)) with
    need(b, d)_i = max(0, 2 - b_i - d_i - d_{i-1} - d_{i+1}).
The grid is dominated iff the walk ends in a state with nu = 0.
"""
import sys
from itertools import product

def build(m):
    cols = list(product(range(3), repeat=m))
    def need(b, d):
        return tuple(max(0, 2 - b[i] - d[i] - (d[i-1] if i > 0 else 0) - (d[i+1] if i < m-1 else 0))
                     for i in range(m))
    return cols, need

def gamma_values(m, nmax):
    cols, need = build(m)
    zero = (0,) * m
    cur = {(zero, zero): 0}
    out = []
    for n in range(1, nmax + 1):
        nxt = {}
        for (b, nu), w in cur.items():
            for d in cols:
                if all(d[i] >= nu[i] for i in range(m)):
                    t = (d, need(b, d))
                    v = w + sum(d)
                    if v < nxt.get(t, 1 << 60):
                        nxt[t] = v
        cur = nxt
        out.append(min(w for (b, nu), w in cur.items() if nu == zero))
    return out, len(cur)

if __name__ == "__main__":
    m = int(sys.argv[1]); nmax = int(sys.argv[2])
    vals, nstates = gamma_values(m, nmax)
    print("states:", nstates)
    print(vals)
