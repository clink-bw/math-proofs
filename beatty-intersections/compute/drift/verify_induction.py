"""Exact check of the closed forms for the block sums Phi_n (see walk.py), by induction.

Claim, for n = 4j + r (j >= 0), with g_n = gamma(s_n) in Z/6:
    r = 1:  Phi_n = [-1, 2,-1,-1,-1, 2] + j*[-1,-1,-1,-1, 2, 2],   g_n = 5
    r = 2:  Phi_n = [ 1, 1, 1,-2,-2, 1] + j*[ 2, 2,-1,-4,-1, 2],   g_n = 2
    r = 3:  Phi_n = [ 0, 0, 0, 0,-3, 3] + j*[ 1, 1, 1,-2,-2, 1],   g_n = 1
    r = 0:  Phi_n =                       j*[ 1,-2,-2,-2, 1, 4],   g_n = 4
Both sides of the recurrence
    Phi_n[k] = sum_{i < a_n} Phi_{n-1}[k + i g_{n-1}] + Phi_{n-2}[k + a_n g_{n-1}],  a_n = 2 (n even), 1 (n odd)
are affine in j, so it suffices to compare constant and linear coefficients.
Consequence: F(q_{4j+1}) = Phi[4] = 2j - 1  and  F(q_{4j+3}) = -2j - 3.
"""
from walk import standard

U = {1: [-1, 2, -1, -1, -1, 2], 2: [1, 1, 1, -2, -2, 1], 3: [0, 0, 0, 0, -3, 3], 0: [0] * 6}
V = {1: [-1, -1, -1, -1, 2, 2], 2: [2, 2, -1, -4, -1, 2], 3: [1, 1, 1, -2, -2, 1], 0: [1, -2, -2, -2, 1, 4]}
G = {1: 5, 2: 2, 3: 1, 0: 4}

def closed(r, dj):
    """(const, lin) of Phi_{4(j+dj)+r} as an affine function of j."""
    return ([u + dj * v for u, v in zip(U[r], V[r])], V[r][:])

def shift(pair, g):
    return tuple([vec[(k + g) % 6] for k in range(6)] for vec in pair)

def add(*pairs):
    return tuple([sum(x) for x in zip(*[p[i] for p in pairs])] for i in range(2))

ok = True
# n = 4j + r for r = 2, 3, 4, 5 (the last two are 4(j+1) and 4(j+1)+1)
for r in (2, 3, 4, 5):
    a = 2 if r % 2 == 0 else 1
    r1, d1 = (r - 1) % 4, (r - 1) // 4
    r2, d2 = (r - 2) % 4, (r - 2) // 4
    g1 = G[r1]
    rhs = add(*[shift(closed(r1, d1), i * g1) for i in range(a)], shift(closed(r2, d2), a * g1))
    lhs = tuple(list(v) for v in closed(r % 4, r // 4))
    gcheck = (a * g1 + G[r2]) % 6 == G[r % 4]
    print(f"n = 4j+{r}: recurrence {'holds' if lhs == rhs else 'FAILS'}; g recurrence {'holds' if gcheck else 'FAILS'}")
    ok &= lhs == rhs and gcheck
# base cases against the directly computed vectors
q, g, Phi = standard(60)
for n in range(0, 61):
    r, j = n % 4, n // 4
    ok &= Phi[n] == [u + j * v for u, v in zip(U[r], V[r])] and g[n] == G[r]
print("closed forms agree with the directly computed Phi_n, g_n for n = 0..60:", ok)
print("F(q_{4j+1}) = 2j - 1 and F(q_{4j+3}) = -2j - 3:",
      all(Phi[4 * j + 1][4] == 2 * j - 1 and Phi[4 * j + 3][4] == -2 * j - 3 for j in range(15)))
