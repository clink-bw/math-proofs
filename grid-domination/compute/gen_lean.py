#!/usr/bin/env python3
"""Generate lean/GridDomination/Height<m>Data.lean and Height<m>.lean  (m = 2, 3, 4, 5).

    python3 grid-domination/compute/gen_lean.py          (all heights; about a minute)
    python3 grid-domination/compute/gen_lean.py 5        (one height)

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
    2: dict(K=1, R=1, C=1, p=2, q=2, name="two", form="n + 1"),
    3: dict(K=2, R=3, C=1, p=2, q=3, name="three", form="3 * n / 2 + 1"),
    4: dict(K=10, R=19, C=9, p=10, q=19, name="four", form="(19 * n + 18) / 10"),
    5: dict(K=10, R=23, C=17, p=10, q=23, name="five", form="(23 * n + 26) / 10"),
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
    NM = 110
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

    # --- optimal words for n < N0 (N0 is fixed below, once the repeating block is known)
    words = [[]]
    for n in range(1, NM):
        t = min(S.final, key=lambda k: hist[n][k])
        cols, s0 = backtrack(par, n, t)
        assert s0 == S.start and run_cols(S, S.start, cols) in fin and sum(wt(m, d) for d in cols) == gam[n]
        words.append(cols)

    # --- repeating blocks.  A block that can be repeated for ever at the optimal rate is a closed
    #     walk of "tight" transitions (those where the potential inequality is an equality).
    #     pp = the least length of such a walk (a multiple of p), qq = its weight.
    tight = [[t for t, w, d in S.succ[k] if F[t] + R == F[k] + K * w] for k in range(S.nstates)]
    alive = set(range(S.nstates))
    changed = True
    while changed:
        changed = False
        has_pred = set(t for k in alive for t in tight[k] if t in alive)
        for k in list(alive):
            if k not in has_pred or not any(t in alive for t in tight[k]):
                alive.discard(k)
                changed = True
    short = {}
    for x in sorted(alive):
        reach = {x}
        for L in range(1, 8 * p + 1):
            reach = set(t for k in reach for t in tight[k] if t in alive)
            if x in reach:
                short[x] = L
                break
    pp = min(short.values())
    qq = R * pp // K
    assert pp % p == 0 and K * qq == R * pp
    horizon = min(NM, 3 * pp + 4)
    bw = [[0 if k in fin else INF for k in range(S.nstates)]]
    nxt = [None]
    for _ in range(horizon):
        nv = [INF] * S.nstates
        nn = [None] * S.nstates
        for k in range(S.nstates):
            for t, w, d in S.succ[k]:
                if bw[-1][t] + w < nv[k]:
                    nv[k] = bw[-1][t] + w
                    nn[k] = (t, d)
        bw.append(nv)
        nxt.append(nn)
    # For each residue r of n modulo pp: the shortest A ++ B through a state x on such a block,
    # with |A| + |B| congruent to r and weight given by the formula.
    choice = {}
    for x in sorted(x for x in short if short[x] == pp):
        for L in range(1, horizon):
            j = min(range(L + 1), key=lambda j: hist[j][x] + bw[L - j][x])
            if hist[j][x] + bw[L - j][x] == formula(P, L):
                if L % pp not in choice or (L, x) < choice[L % pp][:2]:
                    choice[L % pp] = (L, x, j)
    assert len(choice) == pp, sorted(choice)
    bases, blocks = [], {}
    for r in range(pp):
        L, x, j = choice[r]
        if x not in blocks:
            dist, pars = walk_from(S, x, pp)
            cyc, x0 = backtrack(pars, pp, x)
            assert dist[x] == qq and x0 == x and run_cols(S, x, cyc) == x
            assert sum(wt(m, d) for d in cyc) == qq
            blocks[x] = cyc
        A, s0 = backtrack(par, j, x)
        assert s0 == S.start
        B, k = [], x
        for i in range(L - j, 0, -1):
            t, d = nxt[i][k]
            B.append(d)
            k = t
        assert k in fin and run_cols(S, S.start, A) == x and run_cols(S, x, B) == k
        assert sum(wt(m, d) for d in A + B) == formula(P, L)
        bases.append((L, A, B, blocks[x]))
    # N0: explicit lists are given for n < N0, the repeating block is used for n >= N0
    missed = [n for n in range(1, 6 * pp) if n < bases[n % pp][0]]
    N0 = max(J, 1 + max(missed, default=0))
    assert all(b[0] < N0 + pp for b in bases)
    words = words[:N0]
    return dict(m=m, P=P, S=S, J=J, gam=gam, tabs=tabs, Fs=Fs, OFF=OFF, TR=TR, words=words,
                bases=bases, N0=N0, pp=pp, qq=qq)


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


def exceptions(D):
    """n < J where gamma(n) is one more / one less than the formula."""
    P, gam, J = D["P"], D["gam"], D["J"]
    plus = [n for n in range(1, J) if gam[n] == formula(P, n) + 1]
    minus = [n for n in range(1, J) if gam[n] == formula(P, n) - 1]
    assert all(gam[n] == formula(P, n) for n in range(1, J) if n not in plus + minus)
    return plus, minus


def eval_form(form, n):
    return eval(form.replace("/", "//"), {"n": n})


def emit_data(D):
    m, P, S, J, N0 = D["m"], D["P"], D["S"], D["J"], D["N0"]
    K, R, C, p, q = P["K"], P["R"], P["C"], P["p"], P["q"]
    N = S.nstates
    # rows per kernel computation: the comparison of the transition table with the automaton
    # is much heavier per row than the table inequalities, so it gets smaller chunks
    chunk = min(N, max(1, 50000 // S.ncol))
    nch = -(-N // chunk)
    tchunk = min(N, max(1, 6000 // S.ncol))
    tnch = -(-N // tchunk)
    plus, minus = exceptions(D)
    assert all(eval_form(P["form"], n) == formula(P, n) for n in range(1, 400))
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
    w("-- Check the proofs one after another: each is a large kernel computation, and running them")
    w("-- all at once needs several gigabytes of memory.")
    w("set_option Elab.async false")
    w("")
    w(f"namespace GridDomination.Height{m}")
    w("")
    w(f"/-- The lower-bound certificate: `{N}` states, tables for `0, …, {J}` columns, and a")
    w(f"potential for the rate `{R}/{K}`. -/")
    w("def cert : Cert where")
    w(f"  m := {m}")
    w(f"  offs := {hexlit(pack(S.offs, 16))}")
    w(f"  N := {N}")
    w(f"  ST := {hexlit(pack([b + S.ncol * nu for b, nu in S.states], 32))}")
    w("  rows := [")
    w(",\n".join("    " + hexlit(pack(D["TR"][k * S.ncol:(k + 1) * S.ncol], 12)) for k in range(N)) + "]")
    w(f"  tchunk := {tchunk}")
    w(f"  tnch := {tnch}")
    w(f"  chunk := {chunk}")
    w(f"  nch := {nch}")
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
    w("theorem size_ok :")
    w("    (Nat.beq cert.rows.length cert.N && Nat.blt 0 cert.chunk &&")
    w("      Nat.ble cert.N (cert.nch * cert.chunk) && Nat.blt 0 cert.tchunk &&")
    w("      Nat.ble cert.N (cert.tnch * cert.tchunk)) = true := by")
    w("  decide +kernel")
    w("")
    w("theorem st_ok : stOK cert.m cert.offs cert.N cert.ST = true := by")
    w("  decide +kernel")
    w("")

    def chunked(name, check, size="chunk", count=None):
        """One theorem per chunk, then the statement for all chunks."""
        count = nch if count is None else count
        cnt = "nch" if size == "chunk" else "tnch"
        for ch in range(count):
            w(f"theorem {name}_{ch} : chunkOK ({check}) cert.rows cert.{size} {ch} = true := by")
            w("  decide +kernel")
            w("")
        w(f"theorem {name} : ∀ ch, ch < cert.{cnt} →")
        w(f"    chunkOK ({check}) cert.rows cert.{size} ch = true")
        for ch in range(count):
            w(f"  | {ch}, _ => {name}_{ch}")
        w(f"  | ch + {count}, h => absurd h (by change ¬ (ch + {count} < {count}); omega)")
        w("")

    chunked("trans_ok", "transRow cert.m cert.offs cert.ST cert.fins", "tchunk", tnch)
    for j in range(J):
        chunked(f"step_ok_{j}", f"relaxRow cert.m (cert.tab {j}) (cert.tab ({j} + 1)) 1 0")
    w("theorem steps_ok : ∀ j, j < cert.J → ∀ ch, ch < cert.nch →")
    w("    chunkOK (relaxRow cert.m (cert.tab j) (cert.tab (j + 1)) 1 0) cert.rows cert.chunk ch = true")
    for j in range(J):
        w(f"  | {j}, _ => step_ok_{j}")
    w(f"  | j + {J}, h => absurd h (by change ¬ (j + {J} < {J}); omega)")
    w("")
    w("theorem link_ok :")
    w("    linkOK cert.N (cert.tab cert.J) cert.F cert.K cert.R cert.J cert.OFF = true := by")
    w("  decide +kernel")
    w("")
    chunked("stat_ok", "relaxRow cert.m cert.F cert.F cert.K cert.R")
    w("theorem fin_ok : finOK cert.fins cert.F (cert.C + cert.OFF) = true := by")
    w("  decide +kernel")
    w("")
    w("/-- All checks of the lower-bound certificate pass. -/")
    w("theorem valid : cert.Valid :=")
    w("  ⟨start_ok, size_ok, st_ok, trans_ok, steps_ok, link_ok, stat_ok, fin_ok⟩")
    w("")
    # ---- the value
    form = P["form"]
    w(f"/-- The value of `γ_{{2}}(P_{m} □ P_n)` for `n ≥ 1`: `⌈({R} n + {C}) / {K}⌉`"
      + (", corrected at the" if plus or minus else "."))
    if plus or minus:
        w("finitely many small `n` where the true value differs by one. -/")
    else:
        o[-1] = o[-1] + " -/"
    w("def gamma (n : ℕ) : ℕ :=")
    if plus:
        w(f"  if n ∈ {lean_list(plus)} then {form} + 1")
    if minus:
        w(f"  {'else ' if plus else ''}if n ∈ {lean_list(minus)} then {form} - 1")
    w(f"  {'else ' if plus or minus else ''}{form}")
    w("")
    w(f"/-- For `1 ≤ n < {J}`: every final state has lower bound at least `gamma n` after `n` columns. -/")
    w("theorem small_ok :")
    w(f"    ((List.range' 1 {J - 1}).all fun n => finOK cert.fins (cert.tab n) (gamma n)) = true := by")
    w("  decide +kernel")
    w("")
    w(f"/-- `words[n]`, for `1 ≤ n < {N0}`: a list of `n` columns of weight `gamma n` that the automaton")
    w("accepts.  A column is a base-3 number; digit `i` is the weight in row `i`. -/")
    w("def words : List (List ℕ) := [")
    w(",\n".join("    " + lean_list(c) for c in D["words"]) + "]")
    w("")
    w("theorem words_ok :")
    w(f"    ((List.range' 1 {N0 - 1}).all fun n => acceptOK {m} (words.getD n []) n (gamma n)) = true := by")
    w("  decide +kernel")
    w("")
    pp, qq = D["pp"], D["qq"]
    w(f"/-- `baseL[r]`, `baseA[r]`, `baseC[r]`, `baseB[r]`, for `r < {pp}`: lists of columns `A`, `C`, `B`")
    w(f"such that `|A| + |B| = baseL[r]` is congruent to `r` modulo `{pp}`, the block `C` has `{pp}` columns")
    w(f"and weight `{qq}` and can be repeated any number of times, and `A ++ C ++ … ++ C ++ B` is accepted")
    w(f"and has weight `⌈({R} n + {C}) / {K}⌉`, where `n` is its length. -/")
    w(f"def baseL : List ℕ := {lean_list([b[0] for b in D['bases']])}")
    w("")
    for nm, i in (("baseA", 1), ("baseC", 3), ("baseB", 2)):
        w("@[inherit_doc baseL]")
        w(f"def {nm} : List (List ℕ) := [")
        w(",\n".join("    " + lean_list(b[i]) for b in D["bases"]) + "]")
        w("")
    w("theorem pump_ok :")
    w(f"    ((List.range {pp}).all fun r =>")
    w(f"      pumpOK {m} (baseA.getD r []) (baseC.getD r []) (baseB.getD r []) (baseL.getD r 0) {pp}")
    w(f"        (({R} * baseL.getD r 0 + {C} + {K - 1}) / {K}) {qq} &&")
    w(f"      Nat.beq (baseL.getD r 0 % {pp}) r && Nat.blt (baseL.getD r 0) ({N0} + {pp})) = true := by")
    w("  decide +kernel")
    w("")
    w(f"end GridDomination.Height{m}")
    return "\n".join(o) + "\n"


HEAD = {
    2: """`domNum_grid_two`: `γ_{2}(P_2 □ P_n) = n + 1` for every `n ≥ 1`.  This is Theorem 2.3 of Lee and
Liu (arXiv:2502.00134), which they prove by hand; it is included as a test of the method.""",
    3: """`domNum_grid_three`: `γ_{2}(P_3 □ P_n) = ⌊3n/2⌋ + 1` for every `n ≥ 1`.
This is Conjecture 2.5 of Lee and Liu, *The integer {2}-domination number of grids*
(arXiv:2502.00134); they proved the upper bound.""",
    4: """* `domNum_grid_four`: `γ_{2}(P_4 □ P_n) = Height4.gamma n` for every `n ≥ 1`, where
  `Height4.gamma n` is `⌈(19 n + 9) / 10⌉`, except that it is one less for
  `n = 4, 7, 8, 15, 18, 26, 37, 48` and one more for `n = 1`.
* `domNum_grid_four_of_ge`: `γ_{2}(P_4 □ P_n) = 2n - ⌊(n - 9)/10⌋` for every `n ≥ 49`.
  This is Conjecture 3.7 of Lee and Liu, *The integer {2}-domination number of grids*
  (arXiv:2502.00134).""",
    5: """* `domNum_grid_five`: `γ_{2}(P_5 □ P_n) = Height5.gamma n` for every `n ≥ 1`, where
  `Height5.gamma n` is `⌈(23 n + 17) / 10⌉`, except that it is one less for
  `n = 2, 3, 5, 6, 8, 9, 12, 15, 18`.
* `domNum_grid_five_of_ge`: `γ_{2}(P_5 □ P_n) = ⌈(23 n + 17) / 10⌉` for every `n ≥ 19`.""",
}

EXTRA = {
    4: """/-- **Lee–Liu Conjecture 3.7.**  The integer `{2}`-domination number of the `4 × n` grid is
`2n - ⌊(n - 9)/10⌋`, for every `n ≥ 49`. -/
theorem domNum_grid_four_of_ge (n : ℕ) (hn : 49 ≤ n) :
    domNum (grid 4 n) 2 = 2 * n - (n - 9) / 10 := by
  rw [domNum_grid_four n (by omega), Height4.gamma_of_ge hn]
  omega

/-- The threshold 49 in Conjecture 3.7 cannot be lowered: for `n = 48` the value is 92, one less
than the formula gives. -/
theorem domNum_grid_four_48 : domNum (grid 4 48) 2 = 92 := by
  rw [domNum_grid_four 48 (by norm_num)]
  decide
""",
    5: """/-- The integer `{2}`-domination number of the `5 × n` grid is `⌈(23 n + 17) / 10⌉`, for every
`n ≥ 19`. -/
theorem domNum_grid_five_of_ge (n : ℕ) (hn : 19 ≤ n) :
    domNum (grid 5 n) 2 = (23 * n + 26) / 10 := by
  rw [domNum_grid_five n (by omega), Height5.gamma_of_ge hn]

/-- The threshold 19 cannot be lowered: for `n = 18` the value is 43, one less than the formula
gives. -/
theorem domNum_grid_five_18 : domNum (grid 5 18) 2 = 43 := by
  rw [domNum_grid_five 18 (by norm_num)]
  decide
""",
}

MAIN_DOC = {
    2: "The integer `{2}`-domination number of the `2 × n` grid is `n + 1` (Lee–Liu Theorem 2.3).",
    3: """**Lee–Liu Conjecture 2.5.**  The integer `{2}`-domination number of the `3 × n` grid is
`⌊3n/2⌋ + 1`, for every `n ≥ 1`.""",
    4: "The integer `{2}`-domination number of the `4 × n` grid, for every `n ≥ 1`.",
    5: "The integer `{2}`-domination number of the `5 × n` grid, for every `n ≥ 1`.",
}


def emit_main(D):
    m, P, J, N0 = D["m"], D["P"], D["J"], D["N0"]
    K, R, C, p = P["K"], P["R"], P["C"], D["pp"]
    name, form = P["name"], P["form"]
    plus, minus = exceptions(D)
    exc = bool(plus or minus)
    value = f"Height{m}.gamma n" if exc else form
    o = []
    w = o.append
    w("import GridDomination.Certificate")
    w(f"import GridDomination.Height{m}Data")
    w("")
    w("/-!")
    w(f"# The `{{2}}`-domination number of the `{m} × n` grid")
    w("")
    w("Generated by `grid-domination/compute/gen_lean.py`; edit the generator, not this file.")
    w("")
    w(HEAD[m])
    w("-/")
    w("")
    w("namespace GridDomination")
    w("")
    w("open Finset")
    w("")
    w(f"namespace Height{m}")
    w("")
    w(f"theorem gamma_of_ge {{n : ℕ}} (hn : {J} ≤ n) : gamma n = {form} := by")
    if exc:
        lists = [l for l in (plus, minus) if l]
        for i, l in enumerate(lists):
            w(f"  have h{i} : ¬ n ∈ {lean_list(l)} := by")
            w("    intro h")
            w("    simp at h")
            w("    omega")
        w("  unfold gamma")
        w("  rw [" + ", ".join(f"ite_eq_right h{i}" for i in range(len(lists))) + "]")
    else:
        o[-1] = f"theorem gamma_of_ge {{n : ℕ}} (_ : {J} ≤ n) : gamma n = {form} := rfl"
    w("")
    w(f"/-- Every `{{2}}`-dominating function of the `{m} × n` grid weighs at least `gamma n`. -/")
    w(f"theorem lower {{n : ℕ}} (hn : 1 ≤ n) (f : Fin {m} × Fin n → ℕ) (hf : IsDomFn (grid {m} n) 2 f) :")
    w("    gamma n ≤ ∑ v, f v := by")
    w(f"  rcases Nat.lt_or_ge n {J} with hJ | hJ")
    w("  · have hg := List.all_eq_true.mp small_ok n (List.mem_range'_1.mpr ⟨hn, by omega⟩)")
    w(f"    exact valid.lower_grid_small (n := n) (show n ≤ {J} by omega) hg f hf")
    w(f"  · have h : {C} + {R} * n ≤ {K} * ∑ v, f v := valid.lower_grid (n := n) hJ f hf")
    w("    rw [gamma_of_ge hJ]")
    w("    omega")
    w("")
    w(f"/-- Some `{{2}}`-dominating function of the `{m} × n` grid with values in `{{0,1,2}}` weighs")
    w("exactly `gamma n`. -/")
    w("theorem upper {n : ℕ} (hn : 1 ≤ n) :")
    w(f"    ∃ f : Fin {m} × Fin n → ℕ, IsDomFn (grid {m} n) 2 f ∧ (∀ v, f v ≤ 2) ∧ ∑ v, f v = gamma n := by")
    w(f"  rcases Nat.lt_or_ge n {N0} with h0 | h0")
    w("  · exact exists_dom_of_accept")
    w("      (List.all_eq_true.mp words_ok n (List.mem_range'_1.mpr ⟨hn, by omega⟩))")
    w(f"  · have hp := all_range pump_ok (Nat.mod_lt n (show 0 < {p} by norm_num))")
    w("    obtain ⟨hp12, hp3⟩ := and_true_split hp")
    w("    obtain ⟨hp1, hp2⟩ := and_true_split hp12")
    w("    have hmod := Nat.eq_of_beq_eq_true hp2")
    w(f"    have hlt : baseL.getD (n % {p}) 0 < {N0} + {p} := Nat.le_of_ble_eq_true hp3")
    w(f"    generalize baseL.getD (n % {p}) 0 = L at hp1 hmod hlt")
    w(f"    obtain ⟨f, hf, hb, hs⟩ := exists_dom_of_pump hp1 (n := n) (k := (n - L) / {p}) (by omega)")
    w(f"    exact ⟨f, hf, hb, by rw [hs, gamma_of_ge (show {J} ≤ n by omega)]; omega⟩")
    w("")
    w(f"end Height{m}")
    w("")
    w("/-- " + MAIN_DOC[m] + " -/")
    w(f"theorem domNum_grid_{name} (n : ℕ) (hn : 1 ≤ n) : domNum (grid {m} n) 2 = {value} := by")
    w(f"  obtain ⟨f, hf, -, hs⟩ := Height{m}.upper hn")
    w(f"  exact domNum_eq ⟨f, hf, hs⟩ (fun g hg => Height{m}.lower hn g hg)")
    w("")
    if m in EXTRA:
        w(EXTRA[m])
    w(f"/-- The minimum for the `{m} × n` grid is attained by a function with values in `{{0, 1, 2}}`, so it")
    w("does not matter whether weights above 2 are allowed. -/")
    w(f"theorem exists_dom_grid_{name} (n : ℕ) (hn : 1 ≤ n) :")
    w(f"    ∃ f : Fin {m} × Fin n → ℕ, IsDomFn (grid {m} n) 2 f ∧ (∀ v, f v ≤ 2) ∧")
    w(f"      ∑ v, f v = {value} :=")
    w(f"  Height{m}.upper hn")
    w("")
    w("end GridDomination")
    return "\n".join(o) + "\n"


if __name__ == "__main__":
    heights = [int(a) for a in sys.argv[1:]] or sorted(PARAMS)
    for m in heights:
        D = build(m)
        for suffix, text in (("Data", emit_data(D)), ("", emit_main(D))):
            with open(os.path.join(OUT, f"Height{m}{suffix}.lean"), "w") as f:
                f.write(text)
        P = D["P"]
        print(f"height {m}: {D['S'].nstates} states, J = {D['J']}, OFF = {D['OFF']}, "
              f"N0 = {D['N0']}, base lengths {[b[0] for b in D['bases']]}, "
              f"exceptions {exceptions(D)}")
        blocks = []
        for b in D["bases"]:
            if b[3] not in blocks:
                blocks.append(b[3])
        for c in blocks:
            print(f"  repeating block ({D['pp']} columns, weight {D['qq']}):")
            print("    " + picture(m, c).replace("\n", "\n    "))
