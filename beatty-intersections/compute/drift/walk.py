"""The drift of A352676 as a walk.

Let w(m) = floor(m*sqrt 3), c(m) = w(m+1) - w(m) - 1 in {0,1}, kappa(m) = (w(m) + 3m) mod 6.
Then m is in S = B(sqrt 3) ∩ B(1+sqrt 3) iff c(m) = 1 and kappa(m) in {1,5}, and
    F(M) = sum over m <= M with c(m) = 1 of f(kappa(m)),  f = +2 on {1,5}, -1 elsewhere,
satisfies: d(n) = 0 iff F(a(n)) = 0, and d is unbounded above/below iff F is unbounded below/above.

c is the characteristic Sturmian word of slope sqrt 3 - 1 = [0; 1, 2, 1, 2, ...], built from the
standard words s_n = s_{n-1}^{a_n} s_{n-2}.  kappa advances by 4 + c(m) mod 6, so the sum of f over
s_n started in state kappa is a 6-vector Phi_n obeying a linear recurrence.
"""
from math import isqrt
import sys

f = lambda k: 2 if k % 6 in (1, 5) else -1

def brute(M):
    """F(1..M), membership list, by direct definition."""
    F = [0] * (M + 1); inS = [False] * (M + 2)
    w = isqrt(3)
    for m in range(1, M + 1):
        w1 = isqrt(3 * (m + 1) ** 2)
        c = w1 - w - 1
        kap = (w + 3 * m) % 6
        F[m] = F[m - 1] + (f(kap) if c == 1 else 0)
        inS[m] = (c == 1 and kap in (1, 5))
        # cross-check with the definition of S
        a = (w1 // 3) > (w // 3); b = ((w1 - (m + 1)) // 2) > ((w - m) // 2)
        assert inS[m] == (a and b)
        w = w1
    return F, inS

def shift(v, g):            # v'[k] = v[k+g]
    return [v[(k + g) % 6] for k in range(6)]

def add(u, v): return [x + y for x, y in zip(u, v)]

def standard(nmax):
    """q_n, g_n = gamma(s_n), Phi_n for n = -1..nmax (index n+1 in the lists)."""
    q = {-1: 1, 0: 1}; g = {-1: 5, 0: 4}
    Phi = {-1: [f(k) for k in range(6)], 0: [0] * 6}
    q[1], g[1], Phi[1] = 1, 5, Phi[-1][:]          # s_1 = s_0^{a_1 - 1} s_{-1} = "1"
    for n in range(2, nmax + 1):
        a = 2 if n % 2 == 0 else 1
        P = [0] * 6; gg = 0
        for _ in range(a):
            P = add(P, shift(Phi[n - 1], gg)); gg = (gg + g[n - 1]) % 6
        P = add(P, shift(Phi[n - 2], gg)); gg = (gg + g[n - 2]) % 6
        q[n], g[n], Phi[n] = a * q[n - 1] + q[n - 2], gg, P
    return q, g, Phi

if __name__ == "__main__":
    M = 600000
    F, inS = brute(M)
    q, g, Phi = standard(40)
    print("check Phi_n[4] against brute force F(q_n):")
    for n in range(1, 41):
        if q[n] <= M: assert Phi[n][4] == F[q[n]], (n, Phi[n][4], F[q[n]])
    print("  ok up to q_n <=", M)
    print(" n   q_n          g_n  F(q_n)=Phi_n[4]   Phi_n (states 0..5)")
    for n in range(1, 41):
        print(f"{n:2d} {q[n]:12d}  {g[n]}  {Phi[n][4]:6d}        {Phi[n]}")
