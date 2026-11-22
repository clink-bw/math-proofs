#!/usr/bin/env python3
"""Generate the certificate files lean/GridDomination/Height<m>Data.lean  (m = 2, 3, 4).

    python3 grid-domination/compute/gen_lean.py

For each height m this script computes, by exact dynamic programming over columns,

  * tables T_0, ..., T_J:  T_j[s] = least weight of j columns leading from the start to state s;
  * a potential F on states with  F[t] + R <= F[s] + K * weight(d)  along every transition
    s --d--> t, which shows that from column J on each extra column costs at least R/K on average;
  * for every n < J an optimal list of columns, and for every residue of n modulo the period p a
    list  A ++ C ++ ... ++ C ++ B  whose block C can be repeated.

The Lean files contain only this data and the statements "the check function returns true",
proved by evaluation in Lean's kernel.  What the checks mean is proved once, by hand, in
lean/GridDomination/Certificate.lean.  So an error in this script can only make the Lean build
fail; it cannot produce a false theorem.

Every check is also run here in Python before the files are written, so that a mistake shows up
in seconds rather than after a long Lean build.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from strip import Strip, pack, wt, dg  # noqa: E402

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "lean", "GridDomination")
INF = 1 << 50

# K * gamma(n) >= R * n + C for n >= J;  p, q: gamma(n + p) = gamma(n) + q eventually.
PARAMS = {
    2: dict(K=1, R=1, C=1, p=2, q=2),
    3: dict(K=2, R=3, C=1, p=2, q=3),
    4: dict(K=10, R=19, C=9, p=10, q=19),
}


def formula(P, n):
    """ceil((R n + C) / K)"""
    return -((-(P["R"] * n + P["C"])) // P["K"])


def forward_with_parents(S, nmax):
    v = [INF] * S.nstates
    v[S.start] = 0
    hist, par = [v], [None]
    for _ in range(nmax):
        nv = [INF] * S.nstates
        np_ = [None] * S.nstates
        for k, x in enumerate(v):
            if x < INF:
                for t, w, d in S.succ[k]:
                    if x + w < nv[t]:
                        nv[t] = x + w
                        np_[t] = (k, d)
        v = nv
        hist.append(v)
        par.append(np_)
    return hist, par


def walk_from(S, x, steps):
    """Least-weight walks of exactly `steps` columns starting at x: (dist, parents)."""
    v = [INF] * S.nstates
    v[x] = 0
    pars = [None]
    for _ in range(steps):
        nv = [INF] * S.nstates
        np_ = [None] * S.nstates
        for k, y in enumerate(v):
            if y < INF:
                for t, w, d in S.succ[k]:
                    if y + w < nv[t]:
                        nv[t] = y + w
                        np_[t] = (k, d)
        v = nv
        pars.append(np_)
    return v, pars


def backtrack(pars, j, t):
    cols = []
    while j > 0:
        k, d = pars[j][t]
        cols.append(d)
        t = k
        j -= 1
    return cols[::-1], t


def run_cols(S, k, cols):
    """Follow the columns from state k; None if some column is not allowed."""
    for d in cols:
        nxt = [t for t, w, dd in S.succ[k] if dd == d]
        if not nxt:
            return None
        k = nxt[0]
    return k


def build(m):
    P = PARAMS[m]
    K, R, C, p, q = P["K"], P["R"], P["C"], P["p"], P["q"]
    S = Strip(m)
    NM = 160
    hist, par = forward_with_parents(S, NM)
    fin = set(S.final)
    gam = [min(hist[n][k] for k in S.final) for n in range(NM + 1)]
    J = 1 + max(n for n in range(NM - 2 * p) if K * gam[n] - R * n < C)
    assert all(gam[n] == formula(P, n) for n in range(J, NM + 1))

    # potential: least reduced weight K*w - R*j over all j >= J, by relaxation to a fixed point
    F = [K * hist[J][k] - R * J if hist[J][k] < INF else INF for k in range(S.nstates)]
    changed = True
    while changed:
        changed = False
        for k in range(S.nstates):
            if F[k] < INF:
                for t, w, d in S.succ[k]:
                    if F[k] + K * w - R < F[t]:
                        F[t] = F[k] + K * w - R
                        changed = True
    assert max(F) < INF
    OFF = max(0, -min(F))
    Fs = [x + OFF for x in F]
    tabs = [[min(x, 255) for x in hist[j]] for j in range(J + 1)]
    assert max(Fs) < 256 and all(x < 255 for j in range(J + 1) for x in hist[j] if x < INF)

    # --- the checks of Cert.Valid, in Python
    assert tabs[0][S.start] == 0
    for j in range(J):
        for k in range(S.nstates):
            for t, w, d in S.succ[k]:
                assert tabs[j + 1][t] <= tabs[j][k] + w
    for k in range(S.nstates):
        assert Fs[k] + R * J <= K * tabs[J][k] + OFF
        for t, w, d in S.succ[k]:
            assert Fs[t] + R <= Fs[k] + K * w
    assert all(C + OFF <= Fs[k] for k in S.final)
    for n in range(1, J):
        assert all(gam[n] <= tabs[n][k] for k in S.final)

    # --- transition table
    TR = [0] * (S.nstates * S.ncol)
    for k in range(S.nstates):
        for t, w, d in S.succ[k]:
            TR[k * S.ncol + d] = t + 1
    assert S.nstates + 1 < 4096

    # --- optimal words for n < J
    words = [[]]
    for n in range(1, J):
        t = min(S.final, key=lambda k: hist[n][k])
        cols, s0 = backtrack(par, n, t)
        assert s0 == S.start and run_cols(S, S.start, cols) in fin and sum(wt(m, d) for d in cols) == gam[n]
        words.append(cols)

    # --- repeating block: a state x with a closed walk of p columns and weight q, through which
    #     optimal lists of every length (beyond a few small ones) pass
    bw = [[0 if k in fin else INF for k in range(S.nstates)]]
    nxt = [None]
    for _ in range(NM):
        nv = [INF] * S.nstates
        nn = [None] * S.nstates
        for k in range(S.nstates):
            for t, w, d in S.succ[k]:
                if bw[-1][t] + w < nv[k]:
                    nv[k] = bw[-1][t] + w
                    nn[k] = (t, d)
        bw.append(nv)
        nxt.append(nn)
    best = None
    for x in range(S.nstates):
        dist, pars = walk_from(S, x, p)
        if dist[x] != q:
            continue
        res = {}
        for L in range(1, 6 * p + 4):
            if L % p in res:
                continue
            j = min(range(L + 1), key=lambda j: hist[j][x] + bw[L - j][x])
            if hist[j][x] + bw[L - j][x] == formula(P, L):
                res[L % p] = (L, j)
        if len(res) == p:
            key = (max(L for L, j in res.values()), x)
            if best is None or key < best[0]:
                best = (key, x, res, pars)
    (_, x, res, pars) = best
    cyc, x0 = backtrack(pars, p, x)
    assert x0 == x and run_cols(S, x, cyc) == x and sum(wt(m, d) for d in cyc) == q
    bases = []
    for r in range(p):
        L, j = res[r]
        A, s0 = backtrack(par, j, x)
        assert s0 == S.start
        B, k = [], x
        for i in range(L - j, 0, -1):
            t, d = nxt[i][k]
            B.append(d)
            k = t
        assert k in fin and run_cols(S, S.start, A) == x and run_cols(S, x, B) == k
        assert sum(wt(m, d) for d in A + B) == formula(P, L)
        bases.append((L, A, B))
    Lmax = max(L for L, A, B in bases)
    return dict(m=m, P=P, S=S, J=J, gam=gam, tabs=tabs, Fs=Fs, OFF=OFF, TR=TR, words=words,
                cyc=cyc, bases=bases, Lmax=Lmax, x=x)


# ----------------------------------------------------------------------------- pictures

def picture(m, cols):
    """Rows of the grid as text, one character per vertex ('.' for weight 0)."""
    return "\n".join(" ".join(".12"[dg(d, i)] for d in cols) for i in range(m))


# ----------------------------------------------------------------------------- Lean output

def hexlit(x):
    return f"0x{x:x}"


def lean_list(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def wrap_list(items, indent="    "):
    lines, cur = [], indent
    for i, it in enumerate(items):
        piece = it + ("," if i + 1 < len(items) else "")
        if len(cur) + len(piece) + 1 > 100 and cur.strip():
            lines.append(cur.rstrip())
            cur = indent
        cur += piece + " "
    lines.append(cur.rstrip())
    return "\n".join(lines)


GAMMA_DEF = {
    2: ("n + 1", "n + 1"),
    3: ("3 * n / 2 + 1", "3 * n / 2 + 1"),
}


def emit(D):
    m, P, S, J = D["m"], D["P"], D["S"], D["J"]
    K, R, C, p, q = P["K"], P["R"], P["C"], P["p"], P["q"]
    gam = D["gam"]
    o = []
    w = o.append
    w("import GridDomination.Automaton")
    w("")
    w("/-!")
    w(f"# Certificate data for the grid of height {m}")
    w("")
    w("Generated by `grid-domination/compute/gen_lean.py`; edit the generator, not this file.")
    w("")
    w("This file contains numbers and lists found by a script, and theorems of the form")
    w("\"this check returns `true`\", each proved by evaluating the check in Lean's kernel")
    w("(`decide +kernel`; no `native_decide`, so no axiom beyond Lean's standard three).")
    w(f"`Height{m}.lean` turns them into the theorem about the grid graph.")
    w("-/")
    w("")
    w("set_option linter.style.longLine false")
    w("set_option maxRecDepth 1000000")
    w("")
    w(f"namespace GridDomination.Height{m}")
    w("")
    w(f"/-- The lower-bound certificate: `{S.nstates}` states, tables for `0, …, {J}` columns, and a")
    w(f"potential for the rate `{R}/{K}`. -/")
    w("def cert : Cert where")
    w(f"  m := {m}")
    w(f"  offs := {hexlit(pack(S.offs, 16))}")
    w(f"  N := {S.nstates}")
    w(f"  TR := {hexlit(pack(D['TR'], 12))}")
    w("  fins := [")
    w(wrap_list([str(k) for k in S.final]) + "]")
    w("  tabs := [")
    w(",\n".join("    " + hexlit(pack(t, 8)) for t in D["tabs"]) + "]")
    w(f"  J := {J}")
    w(f"  F := {hexlit(pack(D['Fs'], 8))}")
    w(f"  K := {K}")
    w(f"  R := {R}")
    w(f"  C := {C}")
    w(f"  OFF := {D['OFF']}")
    w("")
    w("theorem start_ok : Nat.beq (fld (cert.tab 0) (idx cert.m cert.offs 0 0)) 0 = true := by")
    w("  decide +kernel")
    w("")
    w("theorem trans_ok : transOK cert.m cert.offs cert.N cert.TR cert.fins = true := by")
    w("  decide +kernel")
    w("")
    for j in range(J):
        w(f"theorem step_ok_{j} :")
        w(f"    relaxOK cert.m cert.N cert.TR (cert.tab {j}) (cert.tab ({j} + 1)) 1 0 = true := by")
        w("  decide +kernel")
        w("")
    w("theorem steps_ok : ∀ j, j < cert.J →")
    w("    relaxOK cert.m cert.N cert.TR (cert.tab j) (cert.tab (j + 1)) 1 0 = true")
    for j in range(J):
        w(f"  | {j}, _ => step_ok_{j}")
    w(f"  | j + {J}, h => absurd h (by change ¬ (j + {J} < {J}); omega)")
    w("")
    w("theorem link_ok :")
    w("    linkOK cert.N (cert.tab cert.J) cert.F cert.K cert.R cert.J cert.OFF = true := by")
    w("  decide +kernel")
    w("")
    w("theorem stat_ok : relaxOK cert.m cert.N cert.TR cert.F cert.F cert.K cert.R = true := by")
    w("  decide +kernel")
    w("")
    w("theorem fin_ok : finOK cert.fins cert.F (cert.C + cert.OFF) = true := by")
    w("  decide +kernel")
    w("")
    w("/-- All checks of the lower-bound certificate pass. -/")
    w("theorem valid : cert.Valid :=")
    w("  ⟨start_ok, trans_ok, steps_ok, link_ok, stat_ok, fin_ok⟩")
    w("")
    # ---- small n
    if m == 4:
        exc = [n for n in range(2, J) if gam[n] != formula(P, n)]
        assert gam[1] == 4 and all(gam[n] == formula(P, n) - 1 for n in exc)
        w("/-- The value of `γ_{2}(P_4 □ P_n)` for `n ≥ 1`.  It is `⌈(19 n + 9) / 10⌉`, which for")
        w("`n ≥ 9` is the `2 n - ⌊(n - 9) / 10⌋` of Lee and Liu, except at nine small values of `n`. -/")
        w("def gamma (n : ℕ) : ℕ :=")
        w("  if n = 1 then 4")
        w(f"  else if n ∈ {lean_list(exc)} then (19 * n + 18) / 10 - 1")
        w("  else (19 * n + 18) / 10")
    else:
        w(f"/-- The value of `γ_{{2}}(P_{m} □ P_n)` for `n ≥ 1`. -/")
        w(f"def gamma (n : ℕ) : ℕ := {GAMMA_DEF[m][0]}")
    w("")
    assert all(D["gam"][n] == gamma_py(m, n, D) for n in range(1, 150))
    w(f"/-- For `1 ≤ n < {J}`: every final state has lower bound at least `gamma n` after `n` columns. -/")
    w("theorem small_ok :")
    w(f"    ((List.range' 1 {J - 1}).all fun n => finOK cert.fins (cert.tab n) (gamma n)) = true := by")
    w("  decide +kernel")
    w("")
    w(f"/-- `words[n]`, for `1 ≤ n < {J}`: a list of `n` columns of weight `gamma n` that the automaton")
    w("accepts.  A column is a base-3 number; digit `i` is the weight in row `i`. -/")
    w("def words : List (List ℕ) := [")
    w(",\n".join("    " + lean_list(c) for c in D["words"]) + "]")
    w("")
    w("theorem words_ok :")
    w(f"    ((List.range' 1 {J - 1}).all fun n => acceptOK {m} (words.getD n []) n (gamma n)) = true := by")
    w("  decide +kernel")
    w("")
    # ---- pumping
    w(f"/-- A block of `{p}` columns of weight `{q}` that can be repeated any number of times. -/")
    w(f"def cyc : List ℕ := {lean_list(D['cyc'])}")
    w("")
    w(f"/-- `baseL[r]`, `baseA[r]`, `baseB[r]`, for `r < {p}`: lists of columns `A`, `B` with")
    w(f"`|A| + |B| = baseL[r]`, congruent to `r` modulo `{p}`, such that `A ++ cyc ++ … ++ cyc ++ B`")
    w(f"is accepted and has weight `⌈({R} n + {C}) / {K}⌉`, where `n` is its length. -/")
    w(f"def baseL : List ℕ := {lean_list([L for L, A, B in D['bases']])}")
    w("")
    w("@[inherit_doc baseL]")
    w("def baseA : List (List ℕ) := [")
    w(",\n".join("    " + lean_list(A) for L, A, B in D["bases"]) + "]")
    w("")
    w("@[inherit_doc baseL]")
    w("def baseB : List (List ℕ) := [")
    w(",\n".join("    " + lean_list(B) for L, A, B in D["bases"]) + "]")
    w("")
    w("theorem pump_ok :")
    w(f"    ((List.range {p}).all fun r =>")
    w(f"      pumpOK {m} (baseA.getD r []) cyc (baseB.getD r []) (baseL.getD r 0) {p}")
    w(f"        (({R} * baseL.getD r 0 + {C} + {K - 1}) / {K}) {q} &&")
    w(f"      Nat.beq (baseL.getD r 0 % {p}) r && Nat.ble (baseL.getD r 0) {D['Lmax']}) = true := by")
    w("  decide +kernel")
    w("")
    w(f"end GridDomination.Height{m}")
    return "\n".join(o) + "\n"


def gamma_py(m, n, D):
    P = D["P"]
    if m == 4:
        exc = [k for k in range(2, D["J"]) if D["gam"][k] != formula(P, k)]
        return 4 if n == 1 else formula(P, n) - (1 if n in exc else 0)
    return formula(P, n)


if __name__ == "__main__":
    heights = [int(a) for a in sys.argv[1:]] or [2, 3, 4]
    for m in heights:
        D = build(m)
        path = os.path.join(OUT, f"Height{m}Data.lean")
        with open(path, "w") as f:
            f.write(emit(D))
        P = D["P"]
        print(f"height {m}: {D['S'].nstates} states, J = {D['J']}, OFF = {D['OFF']}, "
              f"repeating block at state {D['S'].states[D['x']]}, base lengths "
              f"{[L for L, A, B in D['bases']]}, wrote {os.path.relpath(path)}")
        print(f"  repeating block ({P['p']} columns, weight {P['q']}):")
        print("    " + picture(m, D["cyc"]).replace("\n", "\n    "))
