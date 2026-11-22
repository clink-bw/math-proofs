"""Shared code: the column automaton, written to match lean/GridDomination/Automaton.lean.

Columns and need vectors are base-3 numbers: digit i is row i.
"""

def dg(c, i):
    return c // 3 ** i % 3

def tau(m, d, i):
    return dg(d, i) + (dg(d, i - 1) if i > 0 else 0) + (dg(d, i + 1) if i + 1 < m else 0)

def need(m, b, d):
    return sum(max(0, 2 - dg(b, i) - tau(m, d, i)) * 3 ** i for i in range(m))

def geq(m, d, nu):
    return all(dg(nu, i) <= dg(d, i) for i in range(m))

def wt(m, d):
    return sum(dg(d, i) for i in range(m))

def wf(m, d, nu):
    return all(dg(nu, i) == 0 or dg(nu, i) + tau(m, d, i) <= 2 for i in range(m))

class Strip:
    """States (d, nu) with wf(d, nu), numbered as in the Lean function `idx`."""

    def __init__(self, m):
        self.m = m
        self.ncol = 3 ** m
        self.offs = []
        total = 0
        for d in range(self.ncol):
            self.offs.append(total)
            r = 1
            for i in range(m):
                r *= 3 - min(2, tau(m, d, i))
            total += r
        self.nstates = total
        self.states = [None] * total
        for d in range(self.ncol):
            for nu in range(self.ncol):
                if wf(m, d, nu):
                    k = self.idx(d, nu)
                    assert self.states[k] is None
                    self.states[k] = (d, nu)
        assert all(s is not None for s in self.states)
        self.succ = [[] for _ in range(total)]     # (target, weight, column)
        for k, (b, nu) in enumerate(self.states):
            for d in range(self.ncol):
                if geq(m, d, nu):
                    self.succ[k].append((self.idx(d, need(m, b, d)), wt(m, d), d))
        self.start = self.idx(0, 0)
        self.final = [k for k, (b, nu) in enumerate(self.states) if nu == 0]

    def idx(self, d, nu):
        m = self.m
        acc = 0
        for i in reversed(range(m)):
            acc = dg(nu, i) + (3 - min(2, tau(m, d, i))) * acc
        return self.offs[d] + acc

    def forward(self, nmax, inf=1 << 50):
        """hist[j][k] = least weight of j columns leading from the start to state k."""
        v = [inf] * self.nstates
        v[self.start] = 0
        hist = [v]
        for _ in range(nmax):
            nv = [inf] * self.nstates
            for k, x in enumerate(v):
                if x < inf:
                    for t, w, _ in self.succ[k]:
                        if x + w < nv[t]:
                            nv[t] = x + w
            v = nv
            hist.append(v)
        return hist

def pack(values, bits):
    return sum(x << (bits * k) for k, x in enumerate(values))
