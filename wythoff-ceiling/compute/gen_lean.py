#!/usr/bin/env python3
"""Generate lean/WythoffCeiling/Gaps.lean: the gap sets of OEIS A341261 and A341262.

    python3 wythoff-ceiling/compute/gen_lean.py

Setting (proved in lean/WythoffCeiling/Basic.lean).  For m > 0 pick an integer y with
t = m - phi*y in [0, phi).  Then
    m occurs twice   <=>  Dt(t)    (column 1 and an even column >= 4),
    m does not occur <=>  Nt(t)    (no column),
and m + j has position t + j - phi*c for the integer c that puts it back in [0, phi).

The script splits the possible positions t of a member of each set into finitely many cells.
On each cell it finds, for every j up to the gap, the shift c and a lemma of Basic.lean that
decides membership of m + j on the whole cell (e.g. `not_Dt_above` needs 2 - phi <= t').  Lean
re-checks every inequality by `linarith`, so a mistake here can only break the build.

Exact arithmetic: a number p + q*phi is compared with another by the sign of
(2p + q) + q*sqrt(5), which is decided with integers.
"""
import os

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "lean",
                   "WythoffCeiling", "Gaps.lean")

# ------------------------------------------------------------------ exact numbers p + q*phi


def sign(f):
    p, q = f
    x, yy = 2 * p + q, q          # value = (x + yy*sqrt5) / 2
    if yy == 0:
        return (x > 0) - (x < 0)
    if x == 0:
        return (yy > 0) - (yy < 0)
    if x > 0 and yy > 0:
        return 1
    if x < 0 and yy < 0:
        return -1
    if x > 0:                     # yy < 0
        return 1 if x * x > 5 * yy * yy else -1
    return 1 if 5 * yy * yy > x * x else -1


def sub(f, g):
    return (f[0] - g[0], f[1] - g[1])


def cmp(f, g):
    return sign(sub(f, g))


PHI = (0, 1)
ZERO = (0, 0)


def lin(f):
    """Lean text for p + q*phi."""
    p, q = f
    if q == 0:
        return str(p)
    qs = "φ" if q == 1 else ("-φ" if q == -1 else f"{q} * φ")
    if p == 0:
        return qs
    if q < 0:
        return f"{p} - {qs[1:]}" if q == -1 else f"{p} - {-q} * φ"
    return f"{qs} + {p}" if p > 0 else f"{qs} - {-p}"


# ------------------------------------------------------------------ lemmas about a position t'
# Each lemma: name, membership (True = in the set, False = not), hypotheses.
# A hypothesis is (kind, bound): 'A<' bound < t', 'A<=' bound <= t', '<B' t' < bound, '<=B'.

D_LEMMAS = [
    ("Dt_of_4", True, [("A<", (-3, 2)), ("<B", (2, -1))]),
    ("Dt_of_6", True, [("A<", (-8, 5)), ("<B", (5, -3))]),
    ("Dt_of_8", True, [("A<", (-21, 13)), ("<B", (13, -8))]),
    ("not_Dt_above", False, [("A<=", (2, -1))]),
    ("not_Dt_gap46", False, [("A<=", (5, -3)), ("<=B", (-3, 2))]),
    ("not_Dt_gap68", False, [("A<=", (13, -8)), ("<=B", (-8, 5))]),
]
N_LEMMAS = [
    ("Nt_of_1", True, [("A<", (-2, 2)), ("<=B", (3, -1))]),
    ("Nt_of_2", True, [("A<", (-5, 4)), ("<=B", (8, -4))]),
    ("Nt_of_3", True, [("A<", (-13, 9)), ("<=B", (21, -12))]),
    ("not_Nt_c1", False, [("A<", (0, 0)), ("<B", (-1, 1))]),
    ("not_Nt_c2", False, [("A<", (-1, 1)), ("<B", (1, 0))]),
    ("not_Nt_c3", False, [("A<", (1, 0)), ("<B", (-2, 2))]),
    ("not_Nt_c5", False, [("A<", (3, -1)), ("<B", (-5, 4))]),
    ("not_Nt_c7", False, [("A<", (8, -4)), ("<B", (-13, 9))]),
]


def holds(kind, bound, lo, lo_closed, hi, hi_closed):
    """Does the hypothesis hold for every t' in the cell (lo, hi) with the given closedness?"""
    if kind == "A<":
        c = cmp(lo, bound)
        return c > 0 or (c == 0 and not lo_closed)
    if kind == "A<=":
        return cmp(lo, bound) >= 0
    if kind == "<B":
        c = cmp(hi, bound)
        return c < 0 or (c == 0 and not hi_closed)
    if kind == "<=B":
        return cmp(hi, bound) <= 0
    raise ValueError(kind)


def normalise(cell, j):
    """The integer c with t + j - c*phi in [0, phi) on the whole cell, and the shifted cell."""
    lo, lc, hi, hc = cell
    for c in range(-2, 12):
        lo2, hi2 = (lo[0] + j, lo[1] - c), (hi[0] + j, hi[1] - c)
        if holds("A<=", ZERO, lo2, lc, hi2, hc) and holds("<B", PHI, lo2, lc, hi2, hc):
            return c, (lo2, lc, hi2, hc)
    raise RuntimeError(f"cell {cell} straddles a wrap at j = {j}")


def certificate(lemmas, cell, j, want):
    c, cell2 = normalise(cell, j)
    for name, mem, hyps in lemmas:
        if mem == want and all(holds(k, b, *cell2) for k, b in hyps):
            return c, name, len(hyps)
    raise RuntimeError(f"no lemma for j = {j} on cell {cell} (shifted {cell2}), want {want}")


# ------------------------------------------------------------------ Lean text

SETS = {
    "D": dict(S="Twice", mem_iff="mem_twice_iff", r_iff="DR_iff", lemmas=D_LEMMAS),
    "N": dict(S="Missing", mem_iff="mem_missing_iff", r_iff="NR_iff", lemmas=N_LEMMAS),
}

T = "(m : ℝ) - φ * y"


def yexpr(c):
    return "y" if c == 0 else (f"(y + {c})" if c > 0 else f"(y - {-c})")


def mexpr(j):
    return "m" if j == 0 else f"m + {j}"


def cert_text(kind, cell, j, want):
    st = SETS[kind]
    c, name, nh = certificate(st["lemmas"], cell, j, want)
    tac = "(by push_cast; linarith)"
    conds = " ".join([tac] * nh)
    bridge = f"{st['r_iff']} {yexpr(c)} {tac} {tac}"
    pos = "(by omega)"
    if want:
        return f"({st['mem_iff']} {pos}).mpr (({bridge}).mpr ({name} {conds}))"
    return f"fun h => {name} {conds} (({bridge}).mp (({st['mem_iff']} {pos}).mp h))"


def cases_text(js):
    alts = " ∨ ".join(f"j = {j}" for j in js)
    pats = " | ".join("rfl" for _ in js)
    return f"obtain {pats} : {alts} := by omega"


def hyps_text(cell):
    lo, lc, hi, hc = cell
    if lo == hi:
        return f"(h1 : {T} = {lin(lo)})"
    a = "≤" if lc else "<"
    b = "≤" if hc else "<"
    return f"(h1 : {lin(lo)} {a} {T}) (h2 : {T} {b} {lin(hi)})"


def between(kind, cell, js, indent):
    """Lines proving `m + j ∉ S` for each j in js (after `intro j ...`)."""
    out = [f"{indent}{cases_text(js)}"] if len(js) > 1 else [f"{indent}obtain rfl : j = {js[0]} := by omega"]
    for j in js:
        out.append(f"{indent}· exact {cert_text(kind, cell, j, False)}")
    return out


def cell_lemma(name, kind, cell, spec, with_mem, doc):
    S = SETS[kind]["S"]
    lines = [f"/-- {doc} -/"]
    if spec[0] == "next":
        g = spec[1]
        concl = f"NextIs {S} m {g}"
        if with_mem:
            concl = f"m ∈ {S} ∧ " + concl
    else:
        _, j0, g = spec
        concl = f"NextIs {S} m {j0} ∨ NextIs {S} m {g}"
    lines.append(f"theorem {name} {{m : ℤ}} (hm : 0 < m) (y : ℤ) {hyps_text(cell)} :")
    lines.append(f"    {concl} := by")
    lines.append("  have hl := phi_lo")
    lines.append("  have hh := phi_hi")
    if spec[0] == "next":
        g = spec[1]
        if with_mem:
            lines.append(f"  refine ⟨{cert_text(kind, cell, 0, True)}, fun j hj1 hj2 => ?_, ?_⟩")
        else:
            lines.append("  refine ⟨fun j hj1 hj2 => ?_, ?_⟩")
        lines.append("  · " + between(kind, cell, list(range(1, g)), "    ")[0].strip())
        lines += between(kind, cell, list(range(1, g)), "    ")[1:]
        lines.append(f"  · exact {cert_text(kind, cell, g, True)}")
    else:
        _, j0, g = spec
        lines.append(f"  by_cases hb : {mexpr(j0)} ∈ {S}")
        lines.append("  · left")
        lines.append("    refine ⟨fun j hj1 hj2 => ?_, hb⟩")
        b1 = between(kind, cell, list(range(1, j0)), "    ")
        lines += b1
        lines.append("  · right")
        lines.append(f"    refine ⟨fun j hj1 hj2 => ?_, {cert_text(kind, cell, g, True)}⟩")
        js = list(range(1, g))
        lines.append(f"    {cases_text(js)}")
        for j in js:
            if j == j0:
                lines.append("    · exact hb")
            else:
                lines.append(f"    · exact {cert_text(kind, cell, j, False)}")
    return "\n".join(lines)


# Cells: (lo, lo_closed, hi, hi_closed) for t = m - phi*y.  In powers of phi:
# 2phi-3 = phi^-3, 2-phi = phi^-2, 5phi-8 = phi^-5, 5-3phi = phi^-4, 13-8phi = phi^-6,
# 13phi-21 = phi^-7, 10-6phi = phi^-3 + phi^-6, 7phi-11 = phi^-3 + phi^-5.
CELLS = [
    # name, kind, cell, spec, with_mem, doc
    ("twice_D1a", "D", ((-11, 7), False, (2, -1), False), ("next", 3), True,
     "`t ∈ (φ⁻³ + φ⁻⁵, φ⁻²)`: `m` occurs twice and the next such number is `m + 3`."),
    ("twice_D1b", "D", ((10, -6), False, (-11, 7), False), ("next", 13), True,
     "`t ∈ (φ⁻³ + φ⁻⁶, φ⁻³ + φ⁻⁵)`: `m` occurs twice and the next such number is `m + 13`."),
    ("twice_D1c", "D", ((-3, 2), False, (10, -6), True), ("branch", 3, 13), False,
     "`t ∈ (φ⁻³, φ⁻³ + φ⁻⁶]`: the next number occurring twice is `m + 3` or `m + 13`."),
    ("twice_D2", "D", ((-8, 5), False, (5, -3), False), ("next", 5), True,
     "`t ∈ (φ⁻⁵, φ⁻⁴)`: `m` occurs twice and the next such number is `m + 5`."),
    ("twice_D3", "D", ((0, 0), False, (13, -8), False), ("next", 10), False,
     "`t ∈ (0, φ⁻⁶)`: the next number occurring twice is `m + 10`."),
    ("twice_D8", "D", ((-21, 13), False, (13, -8), False), ("next", 10), True,
     "`t ∈ (φ⁻⁷, φ⁻⁶)`: `m` occurs twice and the next such number is `m + 10`."),
    ("missing_N0", "N", ((1, 0), True, (1, 0), True), ("next", 2), False,
     "`t = 1` (only `m = 1`): the next missing number is `m + 2`."),
    ("missing_N1a", "N", ((-10, 7), False, (3, -1), True), ("next", 5), True,
     "`φ - t ∈ [φ⁻³, 2 φ⁻⁴)`: `m` is missing and the next missing number is `m + 5`."),
    ("missing_N1b", "N", ((-2, 2), False, (-10, 7), False), ("branch", 10, 13), False,
     "`φ - t ∈ (2 φ⁻⁴, φ⁻²)`: the next missing number is `m + 10` or `m + 13`."),
    ("missing_N1bi", "N", ((-23, 15), False, (11, -6), True), ("next", 10), True,
     "`φ - t ∈ [2 φ⁻⁴ + φ⁻⁷, 2 φ⁻⁴ + φ⁻⁶)`: `m` is missing and the next missing number is `m + 10`."),
    ("missing_N1bii", "N", ((-2, 2), False, (-23, 15), False), ("next", 13), True,
     "`φ - t ∈ (2 φ⁻⁴ + φ⁻⁶, φ⁻²)`: `m` is missing and the next missing number is `m + 13`."),
    ("missing_N2", "N", ((-5, 4), False, (8, -4), True), ("next", 3), True,
     "`φ - t ∈ [φ⁻⁵, φ⁻⁴)`: `m` is missing and the next missing number is `m + 3`."),
    ("missing_N3", "N", ((-13, 9), False, (0, 1), False), ("next", 3), False,
     "`φ - t ∈ (0, φ⁻⁶)`: the next missing number is `m + 3`."),
]

HEADER = '''import WythoffCeiling.Basic

/-!
# The gaps of OEIS A341261 and A341262

Kimberling (February 2021) conjectured that consecutive numbers occurring twice in the Wythoff
ceiling array differ by 3, 5, 10 or 13, and consecutive numbers missing from it by 2, 3, 5, 10 or
13. Both are proved here:

* `isGap_twice_iff`: the gap set of `Twice` (A341261) is exactly `{3, 5, 10, 13}`;
* `isGap_missing_iff`: the gap set of `Missing` (A341262) is exactly `{2, 3, 5, 10, 13}`;
* `twice_gap_infinitely_often`, `missing_gap_infinitely_often`: every gap except the `2` of
  `Missing` occurs beyond any bound;
* `missing_two_apart`: the gap `2` of `Missing` occurs only once, between `1` and `3`.

Method. Write `t = m - φ y ∈ [0, φ)`. `Basic.lean` shows that whether `m` occurs twice, or not at
all, depends only on where `t` lies. The positions of members are split into the cells below; on
each cell, for every `j` up to the gap, the position of `m + j` is `t + j - φ c` for a fixed `c`
and lies in a range decided by one lemma of `Basic.lean`. Two cells (`twice_D1c`, `missing_N1b`)
branch on whether `m + 3`, resp. `m + 10`, is a member; the alternative gap 13 holds on the
whole cell either way.

Generated by `wythoff-ceiling/compute/gen_lean.py`; edit the generator, not this file.
-/

set_option linter.style.longLine false
set_option linter.unusedTactic false

open scoped goldenRatio

namespace WythoffCeiling

open Real

/-! ## Cells -/
'''

FOOTER = r'''
/-! ## The next member after any member -/

/-- After any number occurring twice, the next one is 3, 5, 10 or 13 further on. -/
theorem twice_next {m : ℤ} (hm : m ∈ Twice) :
    NextIs Twice m 3 ∨ NextIs Twice m 5 ∨ NextIs Twice m 10 ∨ NextIs Twice m 13 := by
  have hm0 := twice_pos hm
  obtain ⟨y, h0, h1⟩ := exists_y (m : ℝ)
  have hD := (DR_iff y h0 h1).mp ((mem_twice_iff hm0).mp hm)
  have hl := phi_lo
  have hh := phi_hi
  rcases Dt_cases hD with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩
  · rcases le_or_gt ((m : ℝ) - φ * y) (10 - 6 * φ) with b | b
    · rcases twice_D1c hm0 y a1 b with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
    rcases lt_trichotomy ((m : ℝ) - φ * y) (7 * φ - 11) with c | c | c
    · exact Or.inr (Or.inr (Or.inr (twice_D1b hm0 y b c).2))
    · have := irr_eq (m := m) (y := y) (a := -11) (b := 7) (by push_cast; linarith)
      omega
    · exact Or.inl (twice_D1a hm0 y c a2).2
  · exact Or.inr (Or.inl (twice_D2 hm0 y a1 a2).2)
  · exact Or.inr (Or.inr (Or.inl (twice_D3 hm0 y a1 a2)))

/-- After any missing number, the next one is 2 (only after `1`), 3, 5, 10 or 13 further on. -/
theorem missing_next {m : ℤ} (hm : m ∈ Missing) :
    (m = 1 ∧ NextIs Missing m 2) ∨ NextIs Missing m 3 ∨ NextIs Missing m 5 ∨
      NextIs Missing m 10 ∨ NextIs Missing m 13 := by
  have hm0 : 0 < m := hm.1
  obtain ⟨y, h0, h1⟩ := exists_y (m : ℝ)
  have hN := (NR_iff y h0 h1).mp ((mem_missing_iff hm0).mp hm)
  have hl := phi_lo
  have hh := phi_hi
  have hirr : ∀ a b : ℤ, (m : ℝ) - φ * y = a + b * φ → 1 ≤ a := fun a b h => by
    have := irr_eq h; omega
  rcases Nt_cases hN h0 h1 hirr with c | ⟨c1, c2⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩
  · have := irr_eq (m := m) (y := y) (a := 1) (b := 0) (by push_cast; linarith)
    exact Or.inl ⟨this.symm, missing_N0 hm0 y c⟩
  · rcases missing_N1b hm0 y c1 c2 with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inl (missing_N1a hm0 y c1 c2).2))
  · exact Or.inr (Or.inl (missing_N2 hm0 y c1 c2).2)
  · exact Or.inr (Or.inl (missing_N3 hm0 y c1 c2))

/-! ## Main theorems -/

/-- **A341261.** Each of the gaps 3, 5, 10, 13 occurs after arbitrarily large numbers occurring
twice in the array. -/
theorem twice_gap_infinitely_often {g : ℤ} (hg : g = 3 ∨ g = 5 ∨ g = 10 ∨ g = 13) (B : ℤ) :
    ∃ m, B < m ∧ m ∈ Twice ∧ NextIs Twice m g := by
  have hl := phi_lo
  have hh := phi_hi
  rcases hg with rfl | rfl | rfl | rfl
  · exact inf_often (fun m y hm h1 h2 => twice_D1a hm y h1 h2) 23 14 (by norm_num)
      (by push_cast; linarith) (by push_cast; linarith) B
  · exact inf_often (fun m y hm h1 h2 => twice_D2 hm y h1 h2) 26 16 (by norm_num)
      (by push_cast; linarith) (by push_cast; linarith) B
  · exact inf_often (fun m y hm h1 h2 => twice_D8 hm y h1 h2) 68 42 (by norm_num)
      (by push_cast; linarith) (by push_cast; linarith) B
  · exact inf_often (fun m y hm h1 h2 => twice_D1b hm y h1 h2) 44 27 (by norm_num)
      (by push_cast; linarith) (by push_cast; linarith) B

/-- **A341261 (Kimberling's conjecture).** The differences between consecutive numbers that
occur twice in the Wythoff ceiling array are exactly 3, 5, 10 and 13. -/
theorem isGap_twice_iff {g : ℤ} (hg : 0 < g) :
    IsGap Twice g ↔ g = 3 ∨ g = 5 ∨ g = 10 ∨ g = 13 := by
  constructor
  · rintro ⟨m, hm, h1, h2⟩
    rcases twice_next hm with h | h | h | h
    · exact Or.inl (nextIs_eq hg (by norm_num) h h1 h2)
    · exact Or.inr (Or.inl (nextIs_eq hg (by norm_num) h h1 h2))
    · exact Or.inr (Or.inr (Or.inl (nextIs_eq hg (by norm_num) h h1 h2)))
    · exact Or.inr (Or.inr (Or.inr (nextIs_eq hg (by norm_num) h h1 h2)))
  · intro h
    obtain ⟨m, -, hm, hn⟩ := twice_gap_infinitely_often h 0
    exact isGap_of_nextIs hm hn

/-- **A341262.** Each of the gaps 3, 5, 10, 13 occurs after arbitrarily large missing
numbers. -/
theorem missing_gap_infinitely_often {g : ℤ} (hg : g = 3 ∨ g = 5 ∨ g = 10 ∨ g = 13) (B : ℤ) :
    ∃ m, B < m ∧ m ∈ Missing ∧ NextIs Missing m g := by
  have hl := phi_lo
  have hh := phi_hi
  rcases hg with rfl | rfl | rfl | rfl
  · exact inf_often (fun m y hm h1 h2 => missing_N2 hm y h1 h2.le) 29 17 (by norm_num)
      (by push_cast; linarith) (by push_cast; linarith) B
  · exact inf_often (fun m y hm h1 h2 => missing_N1a hm y h1 h2.le) 24 14 (by norm_num)
      (by push_cast; linarith) (by push_cast; linarith) B
  · exact inf_often (fun m y hm h1 h2 => missing_N1bi hm y h1 h2.le) 66 40 (by norm_num)
      (by push_cast; linarith) (by push_cast; linarith) B
  · exact inf_often (fun m y hm h1 h2 => missing_N1bii hm y h1 h2) 32 19 (by norm_num)
      (by push_cast; linarith) (by push_cast; linarith) B

/-- `1` is not in the array. -/
theorem one_mem_missing : (1 : ℤ) ∈ Missing := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨n, k, hn, hk, e⟩
  have hc : 2 ≤ ⌈(n : ℝ) * φ⌉ := by
    rw [Int.le_ceil_iff]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    nlinarith [phi_lo]
  have hf : 1 ≤ (Nat.fib (k + 1) : ℤ) := by exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hf0 : 0 ≤ (Nat.fib k : ℤ) := by positivity
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  unfold W at e
  nlinarith

/-- **A341262 (Kimberling's conjecture).** The differences between consecutive positive integers
missing from the Wythoff ceiling array are exactly 2, 3, 5, 10 and 13. -/
theorem isGap_missing_iff {g : ℤ} (hg : 0 < g) :
    IsGap Missing g ↔ g = 2 ∨ g = 3 ∨ g = 5 ∨ g = 10 ∨ g = 13 := by
  constructor
  · rintro ⟨m, hm, h1, h2⟩
    rcases missing_next hm with ⟨-, h⟩ | h | h | h | h
    · exact Or.inl (nextIs_eq hg (by norm_num) h h1 h2)
    · exact Or.inr (Or.inl (nextIs_eq hg (by norm_num) h h1 h2))
    · exact Or.inr (Or.inr (Or.inl (nextIs_eq hg (by norm_num) h h1 h2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (nextIs_eq hg (by norm_num) h h1 h2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (nextIs_eq hg (by norm_num) h h1 h2))))
  · rintro (rfl | h)
    · exact isGap_of_nextIs one_mem_missing (missing_N0 (by norm_num) 0 (by push_cast; ring))
    · obtain ⟨m, -, hm, hn⟩ := missing_gap_infinitely_often h 0
      exact isGap_of_nextIs hm hn

/-- The gap 2 of A341262 occurs only once: if `m` and `m + 2` are both missing then `m = 1`. -/
theorem missing_two_apart {m : ℤ} (hm : m ∈ Missing) (h2 : m + 2 ∈ Missing) : m = 1 := by
  rcases missing_next hm with ⟨h, -⟩ | h | h | h | h
  · exact h
  all_goals exact absurd h2 (h.1 2 (by norm_num) (by norm_num))

end WythoffCeiling
'''


def main():
    parts = [HEADER]
    for name, kind, cell, spec, with_mem, doc in CELLS:
        parts.append(cell_lemma(name, kind, cell, spec, with_mem, doc))
        parts.append("")
    text = "\n".join(parts) + FOOTER
    with open(OUT, "w") as f:
        f.write(text)
    print(f"wrote {os.path.normpath(OUT)} ({text.count(chr(10))} lines)")


if __name__ == "__main__":
    main()
