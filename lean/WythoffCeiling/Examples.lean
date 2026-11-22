import WythoffCeiling.Basic

/-!
# Sanity checks against the OEIS data

The definitions in `Basic.lean` reproduce the corner of the array shown in OEIS A341260, and the
first members of A341261 and A341262 behave as listed there: 10 occurs in rows 1 and 4 (the
example given in A341261), and 1 does not occur at all.
-/

set_option linter.style.longLine false

open scoped goldenRatio

namespace WythoffCeiling

open Real

theorem ceil_eq_of {n : ℕ} {c : ℤ} (h1 : (c : ℝ) - 1 < (n : ℝ) * φ) (h2 : (n : ℝ) * φ ≤ c) :
    ⌈(n : ℝ) * φ⌉ = c :=
  Int.ceil_eq_iff.mpr ⟨h1, h2⟩

theorem ceil1 : ⌈((1 : ℕ) : ℝ) * φ⌉ = 2 :=
  ceil_eq_of (by push_cast; linarith [phi_lo]) (by push_cast; linarith [phi_hi])
theorem ceil2 : ⌈((2 : ℕ) : ℝ) * φ⌉ = 4 :=
  ceil_eq_of (by push_cast; linarith [phi_lo]) (by push_cast; linarith [phi_hi])
theorem ceil3 : ⌈((3 : ℕ) : ℝ) * φ⌉ = 5 :=
  ceil_eq_of (by push_cast; linarith [phi_lo]) (by push_cast; linarith [phi_hi])
theorem ceil4 : ⌈((4 : ℕ) : ℝ) * φ⌉ = 7 :=
  ceil_eq_of (by push_cast; linarith [phi_lo]) (by push_cast; linarith [phi_hi])

/-- The top-left corner of the array, as displayed in OEIS A341260:
`2 4 6 10 / 5 9 14 23 / 7 12 19 31 / 10 17 27 44`. -/
theorem corner :
    (W 1 1, W 1 2, W 1 3, W 1 4) = (2, 4, 6, 10) ∧
    (W 2 1, W 2 2, W 2 3, W 2 4) = (5, 9, 14, 23) ∧
    (W 3 1, W 3 2, W 3 3, W 3 4) = (7, 12, 19, 31) ∧
    (W 4 1, W 4 2, W 4 3, W 4 4) = (10, 17, 27, 44) := by
  simp only [W, ceil1, ceil2, ceil3, ceil4]
  norm_num

theorem W_1_4 : W 1 4 = 10 := by simp only [W, ceil1]; norm_num

theorem W_4_1 : W 4 1 = 10 := by simp only [W, ceil4]; norm_num

/-- 10 is in rows 1 and 4 (the example in OEIS A341261), so it occurs twice. -/
theorem ten_mem_twice : (10 : ℤ) ∈ Twice :=
  ⟨1, 4, 4, 1, le_rfl, by norm_num, by norm_num, le_rfl, by decide, W_1_4, W_4_1⟩

end WythoffCeiling
