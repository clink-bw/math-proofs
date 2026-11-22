#!/usr/bin/env python3
"""Independent checks for search.c.

This file shares no code with search.c. It builds each tournament explicitly and tests
EVERY k-set of players (no symmetry, no translation classes, no ordering tricks): a k-set is
dominated when the players beating all of it form a nonempty set.

Run from this directory after ./run_all.sh (it calls ./search and reads results/*.log):
    python3 check.py
It prints one line per check and ends with "ALL CHECKS PASSED" or stops at the first failure.
"""
import itertools
import os
import random
import re
import subprocess
import sys
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
SEARCH = os.path.join(HERE, "search")


def fail(msg):
    print("FAILED:", msg)
    sys.exit(1)


def ok(msg):
    print("ok  ", msg)


# ----------------------------------------------------------------------------- tournaments
def masks_from(n, beats):
    """beaten_by[y] = bitmask of players x with x -> y; checks it is a tournament."""
    beaten_by = [0] * n
    for x in range(n):
        for y in range(n):
            if x != y and beats(x, y):
                beaten_by[y] |= 1 << x
    for x in range(n):
        for y in range(x + 1, n):
            if ((beaten_by[y] >> x) & 1) + ((beaten_by[x] >> y) & 1) != 1:
                fail(f"not a tournament at {x},{y}")
    return beaten_by


def undominated(beaten_by, k, stop_after=None):
    """Number of k-sets beaten by nobody (all C(n,k) sets examined)."""
    count = 0
    for A in itertools.combinations(range(len(beaten_by)), k):
        m = beaten_by[A[0]]
        for v in A[1:]:
            m &= beaten_by[v]
            if not m:
                break
        if not m:
            count += 1
            if stop_after is not None and count >= stop_after:
                break
    return count


def is_paradoxical(beaten_by, k):
    return undominated(beaten_by, k, stop_after=1) == 0


def circulant(n, S):
    S = set(S)
    return masks_from(n, lambda x, y: (y - x) % n in S)


def paley(p):
    # x beats y when y - x is a nonzero square mod p (Euler's criterion)
    return masks_from(p, lambda x, y: pow((y - x) % p, (p - 1) // 2, p) == 1)


def run_search(*args):
    out = subprocess.run([SEARCH, *map(str, args)], capture_output=True, text=True, check=True).stdout
    return out


# ----------------------------------------------------------------------------- groups
# Each group: list of elements (tuples), multiplication, and the index search.c uses.
def cyclic(n):
    els = [(a,) for a in range(n)]
    return els, (lambda x, y: ((x[0] + y[0]) % n,)), (lambda x: x[0])


def direct(p, q):
    els = [(a, b) for a in range(p) for b in range(q)]
    return els, (lambda x, y: ((x[0] + y[0]) % p, (x[1] + y[1]) % q)), (lambda x: x[0] * q + x[1])


def semidirect(p, q, r):
    assert pow(r, q, p) == 1
    els = [(a, b) for b in range(q) for a in range(p)]
    mul = lambda x, y: ((x[0] + pow(r, x[1], p) * y[0]) % p, (x[1] + y[1]) % q)
    return els, mul, (lambda x: x[1] * p + x[0])


def z3_x_f21():
    els = [(c, a, b) for c in range(3) for b in range(3) for a in range(7)]
    mul = lambda x, y: ((x[0] + y[0]) % 3, (x[1] + pow(2, x[2], 7) * y[1]) % 7, (x[2] + y[2]) % 3)
    return els, mul, (lambda x: x[0] * 21 + x[2] * 7 + x[1])


GROUPS = {
    "Z7xZ7": lambda: direct(7, 7),
    "Z11:Z5": lambda: semidirect(11, 5, 3),
    "Z19:Z3": lambda: semidirect(19, 3, 7),
    "Z3xZ21": lambda: direct(3, 21),
    "Z7:Z9": lambda: semidirect(7, 9, 2),
    "Z3x(Z7:Z3)": z3_x_f21,
    "Z7:Z3": lambda: semidirect(7, 3, 2),
}


def group_info(name):
    els, mul, idx = GROUPS[name]() if name in GROUPS else cyclic(int(name[1:]))
    n = len(els)
    e = els[0]
    assert sorted(idx(x) for x in els) == list(range(n)) and idx(e) == 0
    for x in els:
        assert mul(e, x) == x == mul(x, e)
    for x, y, z in itertools.product(els, repeat=3):
        if mul(mul(x, y), z) != mul(x, mul(y, z)):
            fail(f"{name} not associative")
    inv = {x: next(y for y in els if mul(x, y) == e) for x in els}
    abelian = all(mul(x, y) == mul(y, x) for x in els for y in els)
    orders = {}
    for x in els:
        o, y = 1, x
        while y != e:
            y, o = mul(y, x), o + 1
        orders[o] = orders.get(o, 0) + 1
    return els, mul, idx, inv, abelian, dict(sorted(orders.items()))


def cayley_masks(els, mul, idx, inv, S):
    """x beats y when x^-1 y is in S; returned in search.c's index order."""
    S = set(S)
    n = len(els)
    order = sorted(els, key=idx)
    return masks_from(n, lambda i, j: mul(inv[order[i]], order[j]) in S)


def random_connection_set(els, inv, rng):
    e = els[0]
    S, seen = [], set()
    for x in els:
        if x == e or x in seen:
            continue
        seen |= {x, inv[x]}
        S.append(x if rng.random() < 0.5 else inv[x])
    return S


# ----------------------------------------------------------------------------- checks
def check_paley():
    expected = {(7, 2): True, (7, 3): False, (19, 3): True, (19, 4): False,
                (59, 4): False, (67, 4): True}
    for (p, k), want in expected.items():
        bb = paley(p)
        bad = undominated(bb, k)
        got = bad == 0
        if got != want:
            fail(f"Paley {p}, k={k}: expected {want}")
        # search.c counts translation classes; every class of k-sets has exactly p members
        # here because p is prime and k < p.
        out = run_search("paley", p, k)
        c = int(re.search(r"undominated_classes=(\d+)", out).group(1))
        if c * p != bad:
            fail(f"Paley {p}, k={k}: python {bad} undominated {k}-sets, search.c {c} classes")
        ok(f"Paley tournament on {p} players, k={k}: {'is' if got else 'is NOT'} {k}-paradoxical "
           f"({bad} of {comb(p, k)} {k}-sets beaten by nobody; search.c agrees)")


def check_circulant_counts():
    """All circulant tournaments on Z_n, every connection set, every k-set."""
    for k, ns in [(2, range(3, 16, 2)), (3, range(3, 28, 2))]:
        for n in ns:
            m = (n - 1) // 2
            count = 0
            for bits in range(1 << m):
                S = [d if (bits >> (d - 1)) & 1 else n - d for d in range(1, m + 1)]
                if is_paradoxical(circulant(n, S), k):
                    count += 1
            out = run_search("circ", n, k, 8)
            c = int(re.search(r"k_paradoxical=(\d+)", out).group(1))
            if 2 * c != count:
                fail(f"Z_{n}, k={k}: python {count} sets, search.c {c} with 1 in S")
            ok(f"circulants on Z_{n}, k={k}: {count} of {1 << m} connection sets are {k}-paradoxical "
               f"(search.c: {c} with 1 in S, i.e. {2 * c} in all)")
            if k == 2 and n < 7 and count:
                fail("k=2 below 7")
            if k == 3 and n < 19 and count:
                fail("k=3 below 19")


def check_groups(samples=3):
    rng = random.Random(902)
    for name in ["Z7xZ7", "Z11:Z5", "Z19:Z3", "Z3xZ21", "Z7:Z9", "Z3x(Z7:Z3)", "Z65"]:
        els, mul, idx, inv, abelian, orders = group_info(name)
        n = len(els)
        ok(f"group {name}: order {n}, {'abelian' if abelian else 'non-abelian'}, element orders {orders}")
        for _ in range(samples):
            S = random_connection_set(els, inv, rng)
            bad = undominated(cayley_masks(els, mul, idx, inv, S), 4)
            out = run_search("gset", name, 4, ",".join(str(idx(x)) for x in S))
            c = int(re.search(r"undominated_classes=(\d+)", out).group(1))
            # left translation acts freely on 4-sets of an odd-order group, so each class has n members
            if c * n != bad:
                fail(f"{name}: python {bad} undominated 4-sets, search.c {c} classes")
            ok(f"  random connection set on {name}: {bad} undominated 4-sets = {n} x {c} classes (agree)")
    # the smallest non-abelian group of odd order, all connection sets, k = 2 and 3
    els, mul, idx, inv, abelian, orders = group_info("Z7:Z3")
    e = els[0]
    reps = []
    seen = set()
    for x in els:
        if x != e and x not in seen:
            seen |= {x, inv[x]}
            reps.append(x)
    for k in (2, 3):
        count = 0
        for bits in range(1 << len(reps)):
            S = [x if (bits >> i) & 1 else inv[x] for i, x in enumerate(reps)]
            if is_paradoxical(cayley_masks(els, mul, idx, inv, S), k):
                count += 1
        out = run_search("group", "Z7:Z3", k, 8)
        c = int(re.search(r"k_paradoxical=(\d+)", out).group(1))
        if c != count:
            fail(f"Z7:Z3 k={k}: python {count}, search.c {c}")
        ok(f"all {1 << len(reps)} Cayley tournaments on Z7:Z3 (order 21), k={k}: {count} are {k}-paradoxical (agree)")


def check_logged_hits():
    """Every k=4 hit printed in the logs must pass the full check."""
    hits = []
    for fn in sorted(os.listdir(os.path.join(HERE, "results"))):
        if not fn.endswith(".log"):
            continue
        for line in open(os.path.join(HERE, "results", fn)):
            m = re.match(r"HIT Z(\d+) k=4 S=\{([0-9,]*)\}", line)
            if m:
                hits.append((int(m.group(1)), [int(t) for t in m.group(2).split(",")]))
            elif line.startswith("HIT") and " k=4 " in line:
                hits.append((None, line.strip()))
    small = [h for h in hits if h[0] is None or h[0] < 67]
    if small:
        print("k=4 hits on fewer than 67 players were logged:")
        for h in small:
            print("   ", h)
    ok(f"logged k=4 hits on fewer than 67 players: {len(small)}")
    h67 = [S for n, S in hits if n == 67]
    for S in h67:
        if not is_paradoxical(circulant(67, S), 4):
            fail(f"logged hit on Z_67 is not 4-paradoxical: {S}")
    ok(f"all {len(h67)} logged 4-paradoxical circulants on Z_67 pass the full check")
    # group them up to multipliers x -> u x (u a unit mod 67)
    orbits = []
    for S in h67:
        fs = frozenset(S)
        if not any(fs in o for o in orbits):
            orbits.append({frozenset(u * s % 67 for s in S) for u in range(1, 67)})
    squares = frozenset(x * x % 67 for x in range(1, 67))
    print(f"     they form {len(orbits)} orbit(s) under the multipliers x -> u x;",
          "the Paley set (squares) is " + ("among them" if any(squares in o for o in orbits) else "NOT among them"))
    for o in orbits:
        S = sorted(min(o, key=sorted))
        print("     orbit of size", len(o), "e.g. S =", S)
    return small


def check_nearmiss():
    """Recount, from scratch, the example set reported for each near-miss minimum."""
    fn = os.path.join(HERE, "results", "nearmiss_k4.log")
    if not os.path.exists(fn):
        print("skip near-miss check (results/nearmiss_k4.log not present)")
        return
    for line in open(fn):
        m = re.match(r"MINEXAMPLE group=(\S+) n=(\d+) k=4 undominated_classes=(\d+) S=\{(.*)\}", line)
        if not m:
            continue
        name, n, c, body = m.group(1), int(m.group(2)), int(m.group(3)), m.group(4)
        if re.fullmatch(r"Z\d+", name):
            bb = circulant(n, [int(t) for t in body.split(",")])
        else:
            els, mul, idx, inv, _, _ = group_info(name)
            S = [tuple(int(v) for v in t.split(",")) for t in re.findall(r"\(([^)]*)\)", body)]
            if len(S) != (n - 1) // 2 or any(s not in inv for s in S):
                fail(f"could not parse example for {name}")
            if any(inv[s] in S for s in S):
                fail(f"example for {name} is not a connection set")
            bb = cayley_masks(els, mul, idx, inv, S)
        bad = undominated(bb, 4)
        if bad != n * c:
            fail(f"near-miss example on {name}: python {bad} undominated 4-sets, search.c {c} classes")
        ok(f"near-miss example on {name}: {bad} of {comb(n, 4)} 4-sets beaten by nobody = {n} x {c} classes (agree)")


if __name__ == "__main__":
    which = sys.argv[1:] or ["paley", "circ", "groups", "hits", "nearmiss"]
    if "paley" in which:
        check_paley()
    if "circ" in which:
        check_circulant_counts()
    if "groups" in which:
        check_groups()
    if "hits" in which:
        if check_logged_hits():
            fail("unexpected hits below 67: inspect them")
    if "nearmiss" in which:
        check_nearmiss()
    print("ALL CHECKS PASSED")
