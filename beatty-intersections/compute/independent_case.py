"""Gap sets of B(alpha) ∩ B(beta) when 1, 1/alpha, 1/beta are linearly independent over Q.

Write x = 1/alpha, y = 1/beta.  For an integer m,
    m in B(alpha)  <=>  floor((m+1) x) > floor(m x),
so the indicator of B(alpha) is the Sturmian word s(i) = floor((i+1)x) - floor(i x).

The points (m x, m y) mod 1 equidistribute on the 2-torus (Weyl), so the set of
gaps is the set of first common return times over ALL pairs of shifts:
    cut the x-circle at the points -k x (k = 0..G+1) and the y-circle at -l y;
    on the cell starting at (-k x, -l y) the pattern seen for j = 0..G is
    s(j - k) and t(j - l).
A gap g occurs iff some cell with s(-k) = t(-l) = 1 has first common return g,
and its limiting frequency is the total area of those cells divided by x*y.

All combinatorial decisions use exact integer arithmetic (integer k-th roots);
only the printed frequencies are floating point.
"""
from fractions import Fraction
from collections import Counter
import sys


def iroot(n, k):
    """floor(n ** (1/k)) for integers n >= 0, exact."""
    if n < 2:
        return n
    r = int(round(n ** (1.0 / k)))
    while r ** k > n:
        r -= 1
    while (r + 1) ** k <= n:
        r += 1
    return r


class Root:
    """The irrational number (p/q)^(1/k), with exact floor(i * value) for integers i."""

    def __init__(self, p, q, k, label):
        self.p, self.q, self.k, self.label = p, q, k, label
        self.value = (p / q) ** (1.0 / k)

    def floor_mul(self, i):
        if i == 0:
            return 0
        if i > 0:
            return iroot(i ** self.k * self.p // self.q, self.k)
        return -self.floor_mul(-i) - 1  # i*value is irrational, never an integer

    def s(self, i):
        """Indicator that i lies in the Beatty sequence of 1/value (two-sided)."""
        return self.floor_mul(i + 1) - self.floor_mul(i)

    def frac(self, i):
        return i * self.value - self.floor_mul(i)


def arcs(root, G):
    """Arcs of the circle cut at -k*x mod 1, k = 0..G+1: list of (k, length), k = left endpoint."""
    pts = sorted((root.frac(-k), k) for k in range(G + 2))
    out = []
    for idx, (pos, k) in enumerate(pts):
        nxt = pts[(idx + 1) % len(pts)][0]
        out.append((k, (nxt - pos) % 1.0 or 1.0))
    return out


def gap_set(x, y, G=60):
    ax, ay = arcs(x, G), arcs(y, G)
    res = Counter()
    unresolved = 0
    for k, lx in ax:
        if x.s(-k) != 1:
            continue
        for l, ly in ay:
            if y.s(-l) != 1:
                continue
            g = next((j for j in range(1, G + 1) if x.s(j - k) == 1 and y.s(j - l) == 1), None)
            if g is None:
                unresolved += 1
            else:
                res[g] += lx * ly
    return res, unresolved


def brute(x, y, N):
    c = Counter()
    prev = None
    count = 0
    for m in range(1, N + 1):
        if x.s(m) == 1 and y.s(m) == 1:
            count += 1
            if prev is not None:
                c[m - prev] += 1
            prev = m
    return c, count


def report(name, x, y, N=400_000):
    res, unresolved = gap_set(x, y)
    tot = sum(res.values())
    bc, count = brute(x, y, N)
    btot = sum(bc.values())
    print(f"== {name}:  1/alpha = {x.label}, 1/beta = {y.label}")
    print(f"   density x*y = {x.value * y.value:.6f}   brute-force density = {count / N:.6f}")
    print(f"   window area check: {tot:.9f} vs x*y = {x.value * y.value:.9f}; unresolved cells: {unresolved}")
    print(f"   exact gap set: {sorted(res)}   brute-force gap set (m <= {N}): {sorted(bc)}")
    for g in sorted(res):
        print(f"     gap {g:2d}: frequency {res[g] / tot:.6f}   brute force {bc.get(g, 0) / btot:.6f}")


if __name__ == "__main__":
    report("A346308  B(sqrt 2) ∩ B(sqrt 3)", Root(1, 2, 2, "1/sqrt2"), Root(1, 3, 2, "1/sqrt3"))
    report("A347793  B(2^(1/3)) ∩ B(2^(2/3))", Root(1, 2, 3, "2^(-1/3)"), Root(1, 4, 3, "2^(-2/3)"))
