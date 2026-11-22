import Mathlib

/-!
# The Wythoff ceiling array (OEIS A341260): definitions and the circle description

`W n k = F(k+1) ⌈n φ⌉ + (n - 1) F(k)` for `n, k ≥ 1` is Clark Kimberling's Wythoff ceiling array.
`Twice` (OEIS A341261) is the set of numbers occurring at two different places of the array, and
`Missing` (OEIS A341262) the set of positive integers not occurring at all.

The point of this file is to turn "`m` is in column `k`" into a statement about one real number.
Write `ψ = 1 - φ = -1/φ`. Along row `n`, the quantity `W n k - φ W n (k-1)` is
`ψ ^ k * u` with `u = ⌈n φ⌉ - (n - 1) φ` strictly between `φ` and `φ + 1` (`W_succ_sub`).
Conversely every such pair is reached from some row (`colR_imp`). So

  `m` is in column `k`  ⟺  `m - φ x ∈ ψ^k (φ, φ + 1)` for some integer `x`   (`inCol_iff`).

The intervals `ψ^k (φ, φ + 1)` are pairwise disjoint (`inI_inj`), lie in `(0, 1)` for even `k`
and in `(-φ, 0)` for odd `k`. Reducing `m` modulo `φ` to `t ∈ [0, φ)`, membership in column `k`
becomes `t ∈ ψ^k (φ, φ+1)` for even `k` and `t - φ ∈ ψ^k (φ, φ+1)` for odd `k` (`colR_iff`).
From this:

* `m` occurs at most twice, and when twice it is in column 1 and in an even column `≥ 4`
  (`at_most_twice`, `DR_iff`);
* `Twice` and `Missing` are described by where `t` lies (`Dt`, `Nt`), which the file `Gaps`
  turns into the exact gap sets.
-/

set_option linter.style.longLine false

open scoped goldenRatio

namespace WythoffCeiling

open Real

/-! ## Definitions -/

/-- The Wythoff ceiling array, OEIS A341260: `W*(n,k) = F(k+1) ⌈n φ⌉ + (n - 1) F(k)`.
The array is the part with `n, k ≥ 1`; the value `W n 0 = ⌈n φ⌉` is only used in proofs. -/
noncomputable def W (n k : ℕ) : ℤ :=
  (Nat.fib (k + 1) : ℤ) * ⌈(n : ℝ) * φ⌉ + ((n : ℤ) - 1) * (Nat.fib k : ℤ)

/-- `m` occurs in the array. -/
def Occurs (m : ℤ) : Prop := ∃ n k : ℕ, 1 ≤ n ∧ 1 ≤ k ∧ W n k = m

/-- OEIS A341261: the numbers occurring at two different places `(n, k) ≠ (n', k')` of the
array. -/
def Twice : Set ℤ :=
  {m | ∃ n k n' k' : ℕ, 1 ≤ n ∧ 1 ≤ k ∧ 1 ≤ n' ∧ 1 ≤ k' ∧ (n, k) ≠ (n', k') ∧
    W n k = m ∧ W n' k' = m}

/-- OEIS A341262: the positive integers that do not occur in the array. -/
def Missing : Set ℤ := {m | 0 < m ∧ ¬ Occurs m}

/-- `g` is a gap of `S`: two members of `S` at distance `g` with no member strictly between.
(The same definition as `BeattyGaps.IsGap`.) -/
def IsGap (S : Set ℤ) (g : ℤ) : Prop :=
  ∃ m ∈ S, m + g ∈ S ∧ ∀ j : ℤ, 0 < j → j < g → m + j ∉ S

/-! ## Numerical facts about `φ` and `ψ` -/

theorem sqrt5_lo : (2.2360679 : ℝ) < √5 := by
  have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h0 := Real.sqrt_nonneg (5 : ℝ)
  by_contra hc
  rw [not_lt] at hc
  nlinarith

theorem sqrt5_hi : √5 < (2.236068 : ℝ) := by
  have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h0 := Real.sqrt_nonneg (5 : ℝ)
  by_contra hc
  rw [not_lt] at hc
  nlinarith

theorem phi_lo : (1.6180339 : ℝ) < φ := by
  change (1.6180339 : ℝ) < (1 + √5) / 2
  linarith [sqrt5_lo]

theorem phi_hi : φ < (1.618034 : ℝ) := by
  change (1 + √5) / 2 < (1.618034 : ℝ)
  linarith [sqrt5_hi]

theorem phi_sq : φ * φ = φ + 1 := by
  rw [← sq]; exact goldenRatio_sq

theorem psi_eq : ψ = 1 - φ := one_sub_goldenConj.symm

theorem phi_psi : φ * ψ = -1 := goldenRatio_mul_goldenConj

/-- `ψ ^ k = F(k+1) - F(k) φ`. -/
theorem psi_pow (k : ℕ) : ψ ^ k = Nat.fib (k + 1) - φ * Nat.fib k :=
  (fib_succ_sub_goldenRatio_mul_fib k).symm

theorem psi_pow_eq {k a b : ℕ} (ha : Nat.fib (k + 1) = a) (hb : Nat.fib k = b) :
    ψ ^ k = (a : ℝ) - (b : ℝ) * φ := by
  rw [psi_pow, ha, hb]; ring

/-! ## The intervals `ψ ^ k (φ, φ + 1)` -/

/-- `e` lies in the open interval with endpoints `ψ^k φ` and `ψ^k (φ + 1)`. -/
def InI (k : ℕ) (e : ℝ) : Prop := ∃ u : ℝ, φ < u ∧ u < φ + 1 ∧ e = ψ ^ k * u

theorem inI_iff_pos {k : ℕ} {e : ℝ} (hk : 0 < ψ ^ k) :
    InI k e ↔ ψ ^ k * φ < e ∧ e < ψ ^ k * (φ + 1) := by
  constructor
  · rintro ⟨u, h1, h2, rfl⟩
    exact ⟨mul_lt_mul_of_pos_left h1 hk, mul_lt_mul_of_pos_left h2 hk⟩
  · rintro ⟨h1, h2⟩
    refine ⟨e / ψ ^ k, ?_, ?_, by field_simp⟩
    · rw [lt_div_iff₀ hk]; linarith
    · rw [div_lt_iff₀ hk]; linarith

theorem inI_iff_neg {k : ℕ} {e : ℝ} (hk : ψ ^ k < 0) :
    InI k e ↔ ψ ^ k * (φ + 1) < e ∧ e < ψ ^ k * φ := by
  constructor
  · rintro ⟨u, h1, h2, rfl⟩
    exact ⟨mul_lt_mul_of_neg_left h2 hk, mul_lt_mul_of_neg_left h1 hk⟩
  · rintro ⟨h1, h2⟩
    refine ⟨e / ψ ^ k, ?_, ?_, by have := hk.ne; field_simp⟩
    · rw [lt_div_iff_of_neg hk]; linarith
    · rw [div_lt_iff_of_neg hk]; linarith

/-- The interval for a given `k`, once `ψ ^ k = a - b φ` is known. -/
theorem inI_lin {k : ℕ} {a b : ℝ} (h : ψ ^ k = a - b * φ) {e : ℝ} :
    InI k e ↔ (0 < a - b * φ ∧ (a - b) * φ - b < e ∧ e < (a - b) + (a - 2 * b) * φ) ∨
      (a - b * φ < 0 ∧ (a - b) + (a - 2 * b) * φ < e ∧ e < (a - b) * φ - b) := by
  have e1 : ψ ^ k * φ = (a - b) * φ - b := by rw [h]; linear_combination (-b) * phi_sq
  have e2 : ψ ^ k * (φ + 1) = (a - b) + (a - 2 * b) * φ := by
    rw [h]; linear_combination (-b) * phi_sq
  rcases lt_trichotomy (ψ ^ k) 0 with hk | hk | hk
  · rw [inI_iff_neg hk, e1, e2]
    rw [h] at hk
    constructor
    · intro h'; exact Or.inr ⟨hk, h'⟩
    · rintro (⟨h', -⟩ | ⟨-, h'⟩)
      · linarith
      · exact h'
  · exact absurd hk (pow_ne_zero _ goldenConj_ne_zero)
  · rw [inI_iff_pos hk, e1, e2]
    rw [h] at hk
    constructor
    · intro h'; exact Or.inl ⟨hk, h'⟩
    · rintro (⟨-, h'⟩ | ⟨h', -⟩)
      · exact h'
      · linarith

theorem inI_one {e : ℝ} : InI 1 e ↔ -φ < e ∧ e < -1 := by
  rw [inI_lin (a := 1) (b := 1) (by exact_mod_cast psi_pow_eq (k := 1) (a := 1) (b := 1) (by norm_num) (by norm_num))]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h1, h2⟩)
    · linarith [phi_lo]
    · constructor <;> linarith
  · rintro ⟨h1, h2⟩; right; refine ⟨by linarith [phi_lo], by linarith, by linarith⟩

theorem inI_two {e : ℝ} : InI 2 e ↔ φ - 1 < e ∧ e < 1 := by
  rw [inI_lin (a := 2) (b := 1) (by exact_mod_cast psi_pow_eq (k := 2) (a := 2) (b := 1) (by norm_num) (by norm_num))]
  constructor
  · rintro (⟨-, h1, h2⟩ | ⟨h, -⟩)
    · constructor <;> linarith
    · linarith [phi_hi]
  · rintro ⟨h1, h2⟩; left; refine ⟨by linarith [phi_hi], by linarith, by linarith⟩

theorem inI_three {e : ℝ} : InI 3 e ↔ 1 - φ < e ∧ e < φ - 2 := by
  rw [inI_lin (a := 3) (b := 2) (by exact_mod_cast psi_pow_eq (k := 3) (a := 3) (b := 2) (by norm_num) (by norm_num))]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h1, h2⟩)
    · linarith [phi_lo]
    · constructor <;> linarith
  · rintro ⟨h1, h2⟩; right; refine ⟨by linarith [phi_lo], by linarith, by linarith⟩

theorem inI_four {e : ℝ} : InI 4 e ↔ 2 * φ - 3 < e ∧ e < 2 - φ := by
  rw [inI_lin (a := 5) (b := 3) (by exact_mod_cast psi_pow_eq (k := 4) (a := 5) (b := 3) (by norm_num) (by norm_num))]
  constructor
  · rintro (⟨-, h1, h2⟩ | ⟨h, -⟩)
    · constructor <;> linarith
    · linarith [phi_hi]
  · rintro ⟨h1, h2⟩; left; refine ⟨by linarith [phi_hi], by linarith, by linarith⟩

theorem inI_five {e : ℝ} : InI 5 e ↔ 3 - 2 * φ < e ∧ e < 3 * φ - 5 := by
  rw [inI_lin (a := 8) (b := 5) (by exact_mod_cast psi_pow_eq (k := 5) (a := 8) (b := 5) (by norm_num) (by norm_num))]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h1, h2⟩)
    · linarith [phi_lo]
    · constructor <;> linarith
  · rintro ⟨h1, h2⟩; right; refine ⟨by linarith [phi_lo], by linarith, by linarith⟩

theorem inI_six {e : ℝ} : InI 6 e ↔ 5 * φ - 8 < e ∧ e < 5 - 3 * φ := by
  rw [inI_lin (a := 13) (b := 8) (by exact_mod_cast psi_pow_eq (k := 6) (a := 13) (b := 8) (by norm_num) (by norm_num))]
  constructor
  · rintro (⟨-, h1, h2⟩ | ⟨h, -⟩)
    · constructor <;> linarith
    · linarith [phi_hi]
  · rintro ⟨h1, h2⟩; left; refine ⟨by linarith [phi_hi], by linarith, by linarith⟩

theorem inI_seven {e : ℝ} : InI 7 e ↔ 8 - 5 * φ < e ∧ e < 8 * φ - 13 := by
  rw [inI_lin (a := 21) (b := 13) (by exact_mod_cast psi_pow_eq (k := 7) (a := 21) (b := 13) (by norm_num) (by norm_num))]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h1, h2⟩)
    · linarith [phi_lo]
    · constructor <;> linarith
  · rintro ⟨h1, h2⟩; right; refine ⟨by linarith [phi_lo], by linarith, by linarith⟩

theorem inI_eight {e : ℝ} : InI 8 e ↔ 13 * φ - 21 < e ∧ e < 13 - 8 * φ := by
  rw [inI_lin (a := 34) (b := 21) (by exact_mod_cast psi_pow_eq (k := 8) (a := 34) (b := 21) (by norm_num) (by norm_num))]
  constructor
  · rintro (⟨-, h1, h2⟩ | ⟨h, -⟩)
    · constructor <;> linarith
    · linarith [phi_hi]
  · rintro ⟨h1, h2⟩; left; refine ⟨by linarith [phi_hi], by linarith, by linarith⟩

theorem inI_nine {e : ℝ} : InI 9 e ↔ 21 - 13 * φ < e ∧ e < 21 * φ - 34 := by
  rw [inI_lin (a := 55) (b := 34) (by exact_mod_cast psi_pow_eq (k := 9) (a := 55) (b := 34) (by norm_num) (by norm_num))]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h1, h2⟩)
    · linarith [phi_lo]
    · constructor <;> linarith
  · rintro ⟨h1, h2⟩; right; refine ⟨by linarith [phi_lo], by linarith, by linarith⟩

/-- All intervals `ψ^(K + 2j) (φ, φ+1)` lie between `0` and `ψ^K (φ + 1)`. -/
theorem inI_tail {K j : ℕ} {e : ℝ} (h : InI (K + 2 * j) e) :
    (0 < ψ ^ K → 0 < e ∧ e < ψ ^ K * (φ + 1)) ∧
      (ψ ^ K < 0 → ψ ^ K * (φ + 1) < e ∧ e < 0) := by
  obtain ⟨u, hu1, hu2, rfl⟩ := h
  have hu0 : 0 < u := by linarith [goldenRatio_pos]
  have hpsi := goldenConj_neg
  have hs0 : 0 < ψ ^ 2 := by nlinarith
  have hs1 : ψ ^ 2 ≤ 1 := by rw [goldenConj_sq]; linarith
  have hq0 : 0 < (ψ ^ 2) ^ j := pow_pos hs0 j
  have hq1 : (ψ ^ 2) ^ j ≤ 1 := pow_le_one₀ hs0.le hs1
  have e : ψ ^ (K + 2 * j) * u = ψ ^ K * ((ψ ^ 2) ^ j * u) := by rw [pow_add, pow_mul]; ring
  rw [e]
  have h1 : (ψ ^ 2) ^ j * u ≤ u := mul_le_of_le_one_left hu0.le hq1
  have h2 : 0 < (ψ ^ 2) ^ j * u := mul_pos hq0 hu0
  constructor
  · intro hK
    exact ⟨mul_pos hK h2, lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 hK.le)
      (mul_lt_mul_of_pos_left hu2 hK)⟩
  · intro hK
    exact ⟨lt_of_lt_of_le (mul_lt_mul_of_neg_left hu2 hK) (mul_le_mul_of_nonpos_left h1 hK.le),
      mul_neg_of_neg_of_pos hK h2⟩

theorem tail_pos {K : ℕ} {a b : ℝ} (hK : ψ ^ K = a - b * φ) (hpos : 0 < a - b * φ) {k : ℕ}
    (hk : ∃ j, k = K + 2 * j) {e : ℝ} (h : InI k e) :
    0 < e ∧ e < (a - b) + (a - 2 * b) * φ := by
  obtain ⟨j, rfl⟩ := hk
  have := (inI_tail h).1 (by rw [hK]; exact hpos)
  have e2 : ψ ^ K * (φ + 1) = (a - b) + (a - 2 * b) * φ := by
    rw [hK]; linear_combination (-b) * phi_sq
  rw [e2] at this
  exact this

theorem tail_neg {K : ℕ} {a b : ℝ} (hK : ψ ^ K = a - b * φ) (hneg : a - b * φ < 0) {k : ℕ}
    (hk : ∃ j, k = K + 2 * j) {e : ℝ} (h : InI k e) :
    (a - b) + (a - 2 * b) * φ < e ∧ e < 0 := by
  obtain ⟨j, rfl⟩ := hk
  have := (inI_tail h).2 (by rw [hK]; exact hneg)
  have e2 : ψ ^ K * (φ + 1) = (a - b) + (a - 2 * b) * φ := by
    rw [hK]; linear_combination (-b) * phi_sq
  rw [e2] at this
  exact this

theorem even_tail {k K : ℕ} (hk : Even k) (hK : Even K) (hKk : K ≤ k) : ∃ j, k = K + 2 * j := by
  obtain ⟨i, hi⟩ := hk
  obtain ⟨i', hi'⟩ := hK
  exact ⟨i - i', by omega⟩

theorem odd_tail {k K : ℕ} (hk : Odd k) (hK : Odd K) (hKk : K ≤ k) : ∃ j, k = K + 2 * j := by
  obtain ⟨i, hi⟩ := hk
  obtain ⟨i', hi'⟩ := hK
  exact ⟨i - i', by omega⟩

/-- Even `k ≥ 2`: the interval lies in `(0, 1)`. -/
theorem tail_even2 {k : ℕ} (hk : Even k) (h1 : 1 ≤ k) {e : ℝ} (h : InI k e) : 0 < e ∧ e < 1 := by
  have := tail_pos (K := 2) (a := 2) (b := 1) (by exact_mod_cast psi_pow_eq (k := 2) (a := 2) (b := 1) (by norm_num) (by norm_num))
    (by linarith [phi_hi]) (even_tail hk (by decide) (by obtain ⟨i, hi⟩ := hk; omega)) h
  constructor <;> linarith [this.1, this.2]

/-- Even `k ≥ 4`: the interval lies in `(0, 2 - φ)`. -/
theorem tail_even4 {k : ℕ} (hk : Even k) (h4 : 4 ≤ k) {e : ℝ} (h : InI k e) :
    0 < e ∧ e < 2 - φ := by
  have := tail_pos (K := 4) (a := 5) (b := 3) (by exact_mod_cast psi_pow_eq (k := 4) (a := 5) (b := 3) (by norm_num) (by norm_num))
    (by linarith [phi_hi]) (even_tail hk (by decide) h4) h
  constructor <;> linarith [this.1, this.2]

/-- Even `k ≥ 8`: the interval lies in `(0, 13 - 8 φ)`. -/
theorem tail_even8 {k : ℕ} (hk : Even k) (h8 : 8 ≤ k) {e : ℝ} (h : InI k e) :
    0 < e ∧ e < 13 - 8 * φ := by
  have := tail_pos (K := 8) (a := 34) (b := 21) (by exact_mod_cast psi_pow_eq (k := 8) (a := 34) (b := 21) (by norm_num) (by norm_num))
    (by linarith [phi_hi]) (even_tail hk (by decide) h8) h
  constructor <;> linarith [this.1, this.2]

/-- Even `k ≥ 10`: the interval lies in `(0, 34 - 21 φ)`. -/
theorem tail_even10 {k : ℕ} (hk : Even k) (h10 : 10 ≤ k) {e : ℝ} (h : InI k e) :
    0 < e ∧ e < 34 - 21 * φ := by
  have := tail_pos (K := 10) (a := 89) (b := 55) (by exact_mod_cast psi_pow_eq (k := 10) (a := 89) (b := 55) (by norm_num) (by norm_num))
    (by linarith [phi_hi]) (even_tail hk (by decide) h10) h
  constructor <;> linarith [this.1, this.2]

/-- Odd `k`: the interval lies in `(-φ, 0)`. -/
theorem tail_odd1 {k : ℕ} (hk : Odd k) {e : ℝ} (h : InI k e) : -φ < e ∧ e < 0 := by
  have := tail_neg (K := 1) (a := 1) (b := 1) (by exact_mod_cast psi_pow_eq (k := 1) (a := 1) (b := 1) (by norm_num) (by norm_num))
    (by linarith [phi_lo]) (odd_tail hk (by decide) (by obtain ⟨i, hi⟩ := hk; omega)) h
  constructor <;> linarith [this.1, this.2]

/-- Odd `k ≥ 3`: the interval lies in `(1 - φ, 0)`. -/
theorem tail_odd3 {k : ℕ} (hk : Odd k) (h3 : 3 ≤ k) {e : ℝ} (h : InI k e) :
    1 - φ < e ∧ e < 0 := by
  have := tail_neg (K := 3) (a := 3) (b := 2) (by exact_mod_cast psi_pow_eq (k := 3) (a := 3) (b := 2) (by norm_num) (by norm_num))
    (by linarith [phi_lo]) (odd_tail hk (by decide) h3) h
  constructor <;> linarith [this.1, this.2]

/-- Odd `k ≥ 11`: the interval lies in `(55 - 34 φ, 0)`. -/
theorem tail_odd11 {k : ℕ} (hk : Odd k) (h11 : 11 ≤ k) {e : ℝ} (h : InI k e) :
    55 - 34 * φ < e ∧ e < 0 := by
  have := tail_neg (K := 11) (a := 144) (b := 89) (by exact_mod_cast psi_pow_eq (k := 11) (a := 144) (b := 89) (by norm_num) (by norm_num))
    (by linarith [phi_lo]) (odd_tail hk (by decide) h11) h
  constructor <;> linarith [this.1, this.2]

/-- The intervals `ψ^k (φ, φ + 1)` are pairwise disjoint. -/
theorem inI_inj {k k' : ℕ} {e : ℝ} (h : InI k e) (h' : InI k' e) : k = k' := by
  by_contra hne
  wlog hlt : k < k' generalizing k k'
  · exact this h' h (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
  obtain ⟨u, hu1, hu2, rfl⟩ := h
  obtain ⟨u', hu1', hu2', he⟩ := h'
  obtain ⟨d, rfl⟩ : ∃ d, k' = k + (d + 1) := ⟨k' - k - 1, by omega⟩
  have hk0 : ψ ^ k ≠ 0 := pow_ne_zero _ goldenConj_ne_zero
  have hu : u = ψ ^ (d + 1) * u' := by
    apply mul_left_cancel₀ hk0
    rw [he, pow_add]; ring
  have habs : |ψ| = φ - 1 := by rw [abs_of_neg goldenConj_neg, psi_eq]; ring
  have hp : |ψ ^ (d + 1)| ≤ φ - 1 := by
    rw [abs_pow, habs]
    exact pow_le_of_le_one (by linarith [phi_lo]) (by linarith [phi_hi]) (Nat.succ_ne_zero d)
  have hu' : |u| ≤ (φ - 1) * u' := by
    rw [hu, abs_mul, abs_of_pos (by linarith [phi_lo] : (0 : ℝ) < u')]
    exact mul_le_mul_of_nonneg_right hp (by linarith [phi_lo])
  rw [abs_of_pos (by linarith [phi_lo] : (0 : ℝ) < u)] at hu'
  have := mul_lt_mul_of_pos_left hu2' (by linarith [phi_lo] : (0 : ℝ) < φ - 1)
  nlinarith [phi_sq]

/-! ## Rows of the array and the circle -/

theorem W_zero (n : ℕ) : W n 0 = ⌈(n : ℝ) * φ⌉ := by simp [W]

theorem W_one (n : ℕ) : W n 1 = ⌈(n : ℝ) * φ⌉ + ((n : ℤ) - 1) := by simp [W]

theorem W_add_two (n k : ℕ) : W n (k + 2) = W n (k + 1) + W n k := by
  simp only [W]
  rw [show k + 2 + 1 = (k + 1) + 2 by ring, Nat.fib_add_two, Nat.fib_add_two]
  push_cast; ring

/-- Along a row, `W n (k+1) - φ W n k = ψ^(k+1) (⌈n φ⌉ - (n - 1) φ)`. -/
theorem W_succ_sub (n k : ℕ) :
    (W n (k + 1) : ℝ) - φ * (W n k : ℝ) =
      ψ ^ (k + 1) * ((⌈(n : ℝ) * φ⌉ : ℝ) - ((n : ℝ) - 1) * φ) := by
  have h1 := fib_succ_sub_goldenRatio_mul_fib (k + 1)
  have h0 := fib_succ_sub_goldenRatio_mul_fib k
  simp only [W]
  push_cast
  linear_combination (⌈(n : ℝ) * φ⌉ : ℝ) * h1 + ((n : ℝ) - 1) * h0 +
    ((n : ℝ) - 1) * ψ ^ k * phi_psi

theorem ceil_bounds {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * φ < ⌈(n : ℝ) * φ⌉ ∧ (⌈(n : ℝ) * φ⌉ : ℝ) < n * φ + 1 := by
  refine ⟨lt_of_le_of_ne (Int.le_ceil _) ?_, Int.ceil_lt_add_one _⟩
  exact (goldenRatio_irrational.natCast_mul (by omega)).ne_int _

theorem W_lt {n n' : ℕ} (k : ℕ) (h : n < n') : W n k < W n' k := by
  have hc : ⌈(n : ℝ) * φ⌉ + 1 ≤ ⌈(n' : ℝ) * φ⌉ := by
    rw [← Int.ceil_add_one]
    apply Int.ceil_mono
    have : (n : ℝ) + 1 ≤ n' := by exact_mod_cast h
    nlinarith [phi_lo]
  have hf : 1 ≤ (Nat.fib (k + 1) : ℤ) := by exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hf0 : 0 ≤ (Nat.fib k : ℤ) := by positivity
  have hnn : (n : ℤ) < n' := by exact_mod_cast h
  unfold W
  nlinarith

theorem W_pos {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) : 0 < W n k := by
  have hc : 0 < ⌈(n : ℝ) * φ⌉ := by
    rw [Int.ceil_pos]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [phi_lo]
  have hf : 1 ≤ (Nat.fib (k + 1) : ℤ) := by exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hf0 : 0 ≤ (Nat.fib k : ℤ) := by positivity
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  unfold W
  nlinarith

/-- `m` is in column `k`, read on the circle `ℝ / φ ℤ`. -/
def ColR (k : ℕ) (s : ℝ) : Prop := ∃ x : ℤ, InI k (s - φ * x)

/-- The converse direction: a pair `(x, m)` with `m - φ x ∈ ψ^(k+1) (φ, φ+1)` is a pair of
consecutive entries of some row. -/
theorem colR_imp : ∀ (k : ℕ) {m x : ℤ}, 0 < m → InI (k + 1) ((m : ℝ) - φ * x) →
    ∃ n : ℕ, 1 ≤ n ∧ W n (k + 1) = m ∧ W n k = x
  | 0, m, x, hm, h => by
    rw [inI_one] at h
    obtain ⟨h1, h2⟩ := h
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hxm : x ≤ m := by
      by_contra hc
      have hc' : (m : ℝ) + 1 ≤ x := by exact_mod_cast (not_le.mp hc)
      nlinarith [phi_lo]
    refine ⟨(m - x + 1).toNat, by omega, ?_, ?_⟩
    all_goals
      have hn : (((m - x + 1).toNat : ℕ) : ℝ) = (m : ℝ) - x + 1 := by
        have : (((m - x + 1).toNat : ℕ) : ℤ) = m - x + 1 := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      have hc : ⌈(((m - x + 1).toNat : ℕ) : ℝ) * φ⌉ = x := by
        rw [Int.ceil_eq_iff, hn]
        have hx2 : φ * φ * (x : ℝ) = (φ + 1) * x := by rw [phi_sq]
        constructor
        · nlinarith [mul_lt_mul_of_pos_left h1 goldenRatio_pos, phi_sq]
        · nlinarith [mul_lt_mul_of_pos_left h2 goldenRatio_pos, phi_sq]
    · rw [W_one, hc]; omega
    · rw [W_zero, hc]
  | k + 1, m, x, hm, h => by
    have hb : -1 < (m : ℝ) - φ * x ∧ (m : ℝ) - φ * x < 1 := by
      rcases Nat.even_or_odd (k + 1 + 1) with he | ho
      · have := tail_even2 he (by omega) h
        constructor <;> linarith [this.1, this.2]
      · have := tail_odd3 ho (by obtain ⟨i, hi⟩ := ho; omega) h
        constructor <;> linarith [this.1, this.2, phi_hi]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hx : 0 < x := by
      by_contra hc
      have : (x : ℝ) ≤ 0 := by exact_mod_cast (not_lt.mp hc)
      nlinarith [phi_lo]
    obtain ⟨u, hu1, hu2, he⟩ := h
    have h' : InI (k + 1) ((x : ℝ) - φ * ((m - x : ℤ) : ℝ)) := by
      refine ⟨u, hu1, hu2, ?_⟩
      push_cast
      rw [pow_succ] at he
      linear_combination (-φ) * he - (x : ℝ) * phi_sq - ψ ^ (k + 1) * u * phi_psi
    obtain ⟨n, hn, e1, e2⟩ := colR_imp k hx h'
    exact ⟨n, hn, by rw [W_add_two, e1, e2]; ring, e1⟩

/-- **Column membership on the circle.** For `m > 0` and `k ≥ 1`, `m` is in column `k` exactly
when `m - φ x ∈ ψ^k (φ, φ+1)` for some integer `x`. -/
theorem inCol_iff {k : ℕ} (hk : 1 ≤ k) {m : ℤ} (hm : 0 < m) :
    (∃ n : ℕ, 1 ≤ n ∧ W n k = m) ↔ ColR k m := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hb := ceil_bounds hn
    refine ⟨W n k, (⌈(n : ℝ) * φ⌉ : ℝ) - ((n : ℝ) - 1) * φ, ?_, ?_, W_succ_sub n k⟩
    · linarith [hb.1]
    · linarith [hb.2]
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn, e1, -⟩ := colR_imp k hm hx
    exact ⟨n, hn, e1⟩

theorem int_eq_of_phi {z n : ℤ} (h1 : ((n : ℝ) - 1) * φ < z * φ) (h2 : (z : ℝ) * φ < (n + 1) * φ) :
    z = n := by
  have hp := goldenRatio_pos
  have a1 : ((n : ℝ) - 1) < z := lt_of_mul_lt_mul_right h1 hp.le
  have a2 : (z : ℝ) < n + 1 := lt_of_mul_lt_mul_right h2 hp.le
  have b1 : n - 1 < z := by exact_mod_cast a1
  have b2 : z < n + 1 := by exact_mod_cast a2
  omega

/-- Reduce modulo `φ`: with `t = s - φ y ∈ [0, φ)`, column `k` means `t ∈ ψ^k (φ, φ+1)` for even
`k` and `t - φ ∈ ψ^k (φ, φ+1)` for odd `k`. -/
theorem colR_iff {k : ℕ} (hk : 1 ≤ k) {s : ℝ} (y : ℤ) (h0 : 0 ≤ s - φ * y) (h1 : s - φ * y < φ) :
    ColR k s ↔ (Even k ∧ InI k (s - φ * y)) ∨ (Odd k ∧ InI k (s - φ * y - φ)) := by
  constructor
  · rintro ⟨x, hx⟩
    rcases Nat.even_or_odd k with he | ho
    · have hb := tail_even2 he hk hx
      have hz : y - x = 0 := int_eq_of_phi (by push_cast; linarith [phi_lo]) (by push_cast; linarith [phi_lo])
      have : x = y := by omega
      subst this
      exact Or.inl ⟨he, hx⟩
    · have hb := tail_odd1 ho hx
      have hz : y - x = -1 := int_eq_of_phi (by push_cast; linarith) (by push_cast; linarith)
      have : x = y + 1 := by omega
      subst this
      refine Or.inr ⟨ho, ?_⟩
      have e : s - φ * ((y + 1 : ℤ) : ℝ) = s - φ * y - φ := by push_cast; ring
      rwa [e] at hx
  · rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact ⟨y, h⟩
    · refine ⟨y + 1, ?_⟩
      have e : s - φ * ((y + 1 : ℤ) : ℝ) = s - φ * y - φ := by push_cast; ring
      rwa [e]

theorem exists_y (s : ℝ) : ∃ y : ℤ, 0 ≤ s - φ * y ∧ s - φ * y < φ := by
  have hp := goldenRatio_pos
  refine ⟨⌊s / φ⌋, ?_, ?_⟩
  · have := Int.floor_le (s / φ)
    have : φ * ⌊s / φ⌋ ≤ s := by
      calc φ * ⌊s / φ⌋ ≤ φ * (s / φ) := mul_le_mul_of_nonneg_left this hp.le
        _ = s := by field_simp
    linarith
  · have := Int.lt_floor_add_one (s / φ)
    have : s < φ * (⌊s / φ⌋ + 1) := by
      calc s = φ * (s / φ) := by field_simp
        _ < φ * (⌊s / φ⌋ + 1) := mul_lt_mul_of_pos_left this hp
    linarith

/-! ## Occurring twice, and not at all -/

/-- `s` is in two different columns. -/
def DR (s : ℝ) : Prop := ∃ k k' : ℕ, 1 ≤ k ∧ 1 ≤ k' ∧ k ≠ k' ∧ ColR k s ∧ ColR k' s

/-- `s` is in no column. -/
def NR (s : ℝ) : Prop := ∀ k : ℕ, 1 ≤ k → ¬ ColR k s

theorem W_inj {n n' k : ℕ} (h : W n k = W n' k) : n = n' := by
  rcases lt_trichotomy n n' with hl | hl | hl
  · exact absurd h (W_lt k hl).ne
  · exact hl
  · exact absurd h.symm (W_lt k hl).ne

theorem mem_twice_iff {m : ℤ} (hm : 0 < m) : m ∈ Twice ↔ DR m := by
  constructor
  · rintro ⟨n, k, n', k', hn, hk, hn', hk', hne, h1, h2⟩
    refine ⟨k, k', hk, hk', ?_, (inCol_iff hk hm).mp ⟨n, hn, h1⟩,
      (inCol_iff hk' hm).mp ⟨n', hn', h2⟩⟩
    rintro rfl
    exact hne (by rw [W_inj (h1.trans h2.symm)])
  · rintro ⟨k, k', hk, hk', hne, h1, h2⟩
    obtain ⟨n, hn, e1⟩ := (inCol_iff hk hm).mpr h1
    obtain ⟨n', hn', e2⟩ := (inCol_iff hk' hm).mpr h2
    exact ⟨n, k, n', k', hn, hk, hn', hk', fun h => hne (Prod.mk.inj h).2, e1, e2⟩

theorem mem_missing_iff {m : ℤ} (hm : 0 < m) : m ∈ Missing ↔ NR m := by
  constructor
  · rintro ⟨-, hno⟩ k hk hc
    obtain ⟨n, hn, e⟩ := (inCol_iff hk hm).mpr hc
    exact hno ⟨n, k, hn, hk, e⟩
  · intro h
    refine ⟨hm, ?_⟩
    rintro ⟨n, k, hn, hk, e⟩
    exact h k hk ((inCol_iff hk hm).mp ⟨n, hn, e⟩)

/-- An odd column and an even column can share a number only if they are column 1 and an even
column `≥ 4`. -/
theorem mixed {k k' : ℕ} (hk : Odd k) (hk' : Even k') (hk'1 : 1 ≤ k') {t : ℝ}
    (h : InI k (t - φ)) (h' : InI k' t) : k = 1 ∧ 4 ≤ k' := by
  have b' := tail_even2 hk' hk'1 h'
  have hk1 : k = 1 := by
    by_contra hne
    have := tail_odd3 hk (by obtain ⟨i, hi⟩ := hk; omega) h
    linarith [this.1]
  subst hk1
  refine ⟨rfl, ?_⟩
  by_contra hlt
  have h2 : k' = 2 := by obtain ⟨i, hi⟩ := hk'; omega
  subst h2
  rw [inI_one] at h
  rw [inI_two] at h'
  linarith [h.2, h'.1]

/-- The normalised form of "occurs twice": column 1 and some even column `≥ 4`. -/
def Dt (t : ℝ) : Prop := InI 1 (t - φ) ∧ ∃ k : ℕ, Even k ∧ 4 ≤ k ∧ InI k t

theorem DR_iff {s : ℝ} (y : ℤ) (h0 : 0 ≤ s - φ * y) (h1 : s - φ * y < φ) :
    DR s ↔ Dt (s - φ * y) := by
  constructor
  · rintro ⟨k, k', hk, hk', hne, c1, c2⟩
    rcases (colR_iff hk y h0 h1).mp c1 with ⟨e1, i1⟩ | ⟨o1, i1⟩ <;>
      rcases (colR_iff hk' y h0 h1).mp c2 with ⟨e2, i2⟩ | ⟨o2, i2⟩
    · exact absurd (inI_inj i1 i2) hne
    · obtain ⟨rfl, h4⟩ := mixed o2 e1 hk i2 i1
      exact ⟨i2, k, e1, h4, i1⟩
    · obtain ⟨rfl, h4⟩ := mixed o1 e2 hk' i1 i2
      exact ⟨i1, k', e2, h4, i2⟩
    · exact absurd (inI_inj i1 i2) hne
  · rintro ⟨i1, k, he, h4, ik⟩
    exact ⟨1, k, le_rfl, by omega, by omega,
      (colR_iff le_rfl y h0 h1).mpr (Or.inr ⟨odd_one, i1⟩),
      (colR_iff (by omega) y h0 h1).mpr (Or.inl ⟨he, ik⟩)⟩

/-- The normalised form of "occurs nowhere". -/
def Nt (t : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ¬ (Even k ∧ InI k t) ∧ ¬ (Odd k ∧ InI k (t - φ))

theorem NR_iff {s : ℝ} (y : ℤ) (h0 : 0 ≤ s - φ * y) (h1 : s - φ * y < φ) :
    NR s ↔ Nt (s - φ * y) := by
  constructor
  · intro h k hk
    refine ⟨fun h' => h k hk ((colR_iff hk y h0 h1).mpr (Or.inl h')),
      fun h' => h k hk ((colR_iff hk y h0 h1).mpr (Or.inr h'))⟩
  · intro h k hk hc
    rcases (colR_iff hk y h0 h1).mp hc with h' | h'
    · exact (h k hk).1 h'
    · exact (h k hk).2 h'

/-- **No number occurs more than twice** (stated without proof in OEIS A341260 and A341261). -/
theorem at_most_twice {m : ℤ} {n₁ k₁ n₂ k₂ n₃ k₃ : ℕ}
    (hn₁ : 1 ≤ n₁) (hk₁ : 1 ≤ k₁) (hn₂ : 1 ≤ n₂) (hk₂ : 1 ≤ k₂) (hn₃ : 1 ≤ n₃) (hk₃ : 1 ≤ k₃)
    (h₁ : W n₁ k₁ = m) (h₂ : W n₂ k₂ = m) (h₃ : W n₃ k₃ = m) :
    (n₁, k₁) = (n₂, k₂) ∨ (n₁, k₁) = (n₃, k₃) ∨ (n₂, k₂) = (n₃, k₃) := by
  have hm : 0 < m := h₁ ▸ W_pos hn₁ hk₁
  by_cases e12 : k₁ = k₂
  · subst e12; left; rw [W_inj (h₁.trans h₂.symm)]
  by_cases e13 : k₁ = k₃
  · subst e13; right; left; rw [W_inj (h₁.trans h₃.symm)]
  by_cases e23 : k₂ = k₃
  · subst e23; right; right; rw [W_inj (h₂.trans h₃.symm)]
  exfalso
  obtain ⟨y, h0, h1⟩ := exists_y (m : ℝ)
  have c₁ := (colR_iff hk₁ y h0 h1).mp ((inCol_iff hk₁ hm).mp ⟨n₁, hn₁, h₁⟩)
  have c₂ := (colR_iff hk₂ y h0 h1).mp ((inCol_iff hk₂ hm).mp ⟨n₂, hn₂, h₂⟩)
  have c₃ := (colR_iff hk₃ y h0 h1).mp ((inCol_iff hk₃ hm).mp ⟨n₃, hn₃, h₃⟩)
  rcases c₁ with ⟨-, i₁⟩ | ⟨-, i₁⟩ <;> rcases c₂ with ⟨-, i₂⟩ | ⟨-, i₂⟩ <;>
    rcases c₃ with ⟨-, i₃⟩ | ⟨-, i₃⟩
  all_goals first
    | exact e12 (inI_inj i₁ i₂)
    | exact e13 (inI_inj i₁ i₃)
    | exact e23 (inI_inj i₂ i₃)

/-- Irrationality of `φ`, in the form used for boundary points: if `m - φ y = a + b φ` with
integers `a, b` then `a = m`. -/
theorem irr_eq {m y a b : ℤ} (h : (m : ℝ) - φ * y = a + b * φ) : a = m := by
  by_contra hne
  have e : ((y + b : ℤ) : ℝ) * φ = ((m - a : ℤ) : ℝ) := by push_cast; linarith
  by_cases hz : y + b = 0
  · rw [hz] at e
    have h0 : ((m - a : ℤ) : ℝ) = 0 := by rw [← e]; simp
    have h1 : m - a = 0 := by exact_mod_cast h0
    exact hne (by omega)
  · exact (goldenRatio_irrational.intCast_mul hz).ne_int _ e

/-! ## Reading off `Twice` and `Missing` on the circle

Below, `t ∈ [0, φ)` is a normalised position. The lemmas say which `t` give a number occurring
twice (`Dt`) or nowhere (`Nt`); the endpoints are written as `a + b φ` with small integers, so
that each step of the case analysis in `Gaps` is a linear inequality. In powers of `φ`:
`2 φ - 3 = φ⁻³`, `2 - φ = φ⁻²`, `5 φ - 8 = φ⁻⁵`, `5 - 3 φ = φ⁻⁴`, `13 φ - 21 = φ⁻⁷`,
`13 - 8 φ = φ⁻⁶`. -/

theorem even4_cases {k : ℕ} (hk : Even k) (h4 : 4 ≤ k) {t : ℝ} (h : InI k t) :
    (2 * φ - 3 < t ∧ t < 2 - φ) ∨ (5 * φ - 8 < t ∧ t < 5 - 3 * φ) ∨
      (13 * φ - 21 < t ∧ t < 13 - 8 * φ) ∨ (0 < t ∧ t < 34 - 21 * φ) := by
  obtain ⟨i, rfl⟩ := hk
  rcases (show i = 2 ∨ i = 3 ∨ i = 4 ∨ 5 ≤ i by omega) with rfl | rfl | rfl | hi
  · exact Or.inl (inI_four.mp h)
  · exact Or.inr (Or.inl (inI_six.mp h))
  · exact Or.inr (Or.inr (Or.inl (inI_eight.mp h)))
  · exact Or.inr (Or.inr (Or.inr (tail_even10 ⟨i, rfl⟩ (by omega) h)))

theorem odd_cases {k : ℕ} (hk : Odd k) {e : ℝ} (h : InI k e) :
    (-φ < e ∧ e < -1) ∨ (1 - φ < e ∧ e < φ - 2) ∨ (3 - 2 * φ < e ∧ e < 3 * φ - 5) ∨
      (8 - 5 * φ < e ∧ e < 8 * φ - 13) ∨ (21 - 13 * φ < e ∧ e < 21 * φ - 34) ∨
      (55 - 34 * φ < e ∧ e < 0) := by
  obtain ⟨i, rfl⟩ := hk
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ 5 ≤ i by omega) with
    rfl | rfl | rfl | rfl | rfl | hi
  · exact Or.inl (inI_one.mp h)
  · exact Or.inr (Or.inl (inI_three.mp h))
  · exact Or.inr (Or.inr (Or.inl (inI_five.mp h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (inI_seven.mp h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (inI_nine.mp h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (tail_odd11 ⟨i, rfl⟩ (by omega) h)))))

theorem Dt_cases {t : ℝ} (h : Dt t) :
    (2 * φ - 3 < t ∧ t < 2 - φ) ∨ (5 * φ - 8 < t ∧ t < 5 - 3 * φ) ∨ (0 < t ∧ t < 13 - 8 * φ) := by
  obtain ⟨-, k, hk, h4, hi⟩ := h
  rcases even4_cases hk h4 hi with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨by linarith [h.1, phi_lo], h.2⟩)
  · exact Or.inr (Or.inr ⟨h.1, by linarith [h.2, phi_lo]⟩)

theorem Dt_of_col1 {t : ℝ} (h1 : 0 < t) (h2 : t < φ - 1) {k : ℕ} (hk : Even k) (h4 : 4 ≤ k)
    (hi : InI k t) : Dt t :=
  ⟨inI_one.mpr ⟨by linarith, by linarith⟩, k, hk, h4, hi⟩

theorem Dt_of_4 {t : ℝ} (h1 : 2 * φ - 3 < t) (h2 : t < 2 - φ) : Dt t :=
  Dt_of_col1 (by linarith [phi_lo]) (by linarith [phi_lo]) (k := 4) (by decide) le_rfl
    (inI_four.mpr ⟨h1, h2⟩)

theorem Dt_of_6 {t : ℝ} (h1 : 5 * φ - 8 < t) (h2 : t < 5 - 3 * φ) : Dt t :=
  Dt_of_col1 (by linarith [phi_lo]) (by linarith [phi_lo]) (k := 6) (by decide) (by norm_num)
    (inI_six.mpr ⟨h1, h2⟩)

theorem Dt_of_8 {t : ℝ} (h1 : 13 * φ - 21 < t) (h2 : t < 13 - 8 * φ) : Dt t :=
  Dt_of_col1 (by linarith [phi_lo]) (by linarith [phi_lo]) (k := 8) (by decide) (by norm_num)
    (inI_eight.mpr ⟨h1, h2⟩)

/-- Beyond `φ⁻²` nothing occurs twice. -/
theorem not_Dt_above {t : ℝ} (h : 2 - φ ≤ t) : ¬ Dt t := by
  rintro ⟨-, k, hk, h4, hi⟩
  linarith [(tail_even4 hk h4 hi).2]

/-- Between `φ⁻⁴` and `φ⁻³` nothing occurs twice. -/
theorem not_Dt_gap46 {t : ℝ} (h1 : 5 - 3 * φ ≤ t) (h2 : t ≤ 2 * φ - 3) : ¬ Dt t := by
  rintro ⟨-, k, hk, h4, hi⟩
  rcases even4_cases hk h4 hi with h | h | h | h <;> linarith [h.1, h.2, phi_lo, phi_hi]

/-- Between `φ⁻⁶` and `φ⁻⁵` nothing occurs twice. -/
theorem not_Dt_gap68 {t : ℝ} (h1 : 13 - 8 * φ ≤ t) (h2 : t ≤ 5 * φ - 8) : ¬ Dt t := by
  rintro ⟨-, k, hk, h4, hi⟩
  rcases even4_cases hk h4 hi with h | h | h | h <;> linarith [h.1, h.2, phi_lo, phi_hi]

theorem Nt_of {t : ℝ} (h1 : 1 < t)
    (c1 : t - φ ≤ 1 - φ ∨ φ - 2 ≤ t - φ) (c3 : t - φ ≤ 3 - 2 * φ ∨ 3 * φ - 5 ≤ t - φ)
    (c5 : t - φ ≤ 8 - 5 * φ ∨ 8 * φ - 13 ≤ t - φ) (c7 : t - φ ≤ 21 - 13 * φ ∨ 21 * φ - 34 ≤ t - φ)
    (c9 : t - φ ≤ 55 - 34 * φ) : Nt t := by
  intro k hk
  refine ⟨fun ⟨he, hi⟩ => ?_, fun ⟨ho, hi⟩ => ?_⟩
  · linarith [(tail_even2 he hk hi).2]
  · rcases odd_cases ho hi with h | h | h | h | h | h
    · linarith [h.2]
    · rcases c1 with c | c <;> linarith [h.1, h.2]
    · rcases c3 with c | c <;> linarith [h.1, h.2]
    · rcases c5 with c | c <;> linarith [h.1, h.2]
    · rcases c7 with c | c <;> linarith [h.1, h.2]
    · linarith [h.1]

/-- `t ∈ (2 φ - 2, 3 - φ]`, i.e. `φ - t ∈ [φ⁻³, φ⁻²)`: missing. -/
theorem Nt_of_1 {t : ℝ} (h1 : 2 * φ - 2 < t) (h2 : t ≤ 3 - φ) : Nt t :=
  Nt_of (by linarith [phi_lo, phi_hi]) (Or.inr (by linarith)) (Or.inl (by linarith))
    (Or.inl (by linarith [phi_lo, phi_hi])) (Or.inl (by linarith [phi_lo, phi_hi])) (by linarith [phi_lo, phi_hi])

/-- `t ∈ (4 φ - 5, 8 - 4 φ]`, i.e. `φ - t ∈ [φ⁻⁵, φ⁻⁴)`: missing. -/
theorem Nt_of_2 {t : ℝ} (h1 : 4 * φ - 5 < t) (h2 : t ≤ 8 - 4 * φ) : Nt t :=
  Nt_of (by linarith [phi_lo, phi_hi]) (Or.inr (by linarith [phi_lo, phi_hi])) (Or.inr (by linarith))
    (Or.inl (by linarith)) (Or.inl (by linarith [phi_lo, phi_hi])) (by linarith [phi_lo, phi_hi])

/-- `t ∈ (9 φ - 13, 21 - 12 φ]`, i.e. `φ - t ∈ [φ⁻⁷, φ⁻⁶)`: missing. -/
theorem Nt_of_3 {t : ℝ} (h1 : 9 * φ - 13 < t) (h2 : t ≤ 21 - 12 * φ) : Nt t :=
  Nt_of (by linarith [phi_lo, phi_hi]) (Or.inr (by linarith [phi_lo, phi_hi])) (Or.inr (by linarith [phi_lo, phi_hi]))
    (Or.inr (by linarith)) (Or.inl (by linarith)) (by linarith [phi_lo, phi_hi])

theorem not_Nt_c1 {t : ℝ} (h1 : 0 < t) (h2 : t < φ - 1) : ¬ Nt t := fun h =>
  (h 1 le_rfl).2 ⟨odd_one, inI_one.mpr ⟨by linarith, by linarith⟩⟩

theorem not_Nt_c2 {t : ℝ} (h1 : φ - 1 < t) (h2 : t < 1) : ¬ Nt t := fun h =>
  (h 2 (by norm_num)).1 ⟨even_two, inI_two.mpr ⟨h1, h2⟩⟩

theorem not_Nt_c3 {t : ℝ} (h1 : 1 < t) (h2 : t < 2 * φ - 2) : ¬ Nt t := fun h =>
  (h 3 (by norm_num)).2 ⟨by decide, inI_three.mpr ⟨by linarith, by linarith⟩⟩

theorem not_Nt_c5 {t : ℝ} (h1 : 3 - φ < t) (h2 : t < 4 * φ - 5) : ¬ Nt t := fun h =>
  (h 5 (by norm_num)).2 ⟨by decide, inI_five.mpr ⟨by linarith, by linarith⟩⟩

theorem not_Nt_c7 {t : ℝ} (h1 : 8 - 4 * φ < t) (h2 : t < 9 * φ - 13) : ¬ Nt t := fun h =>
  (h 7 (by norm_num)).2 ⟨by decide, inI_seven.mpr ⟨by linarith, by linarith⟩⟩

/-- Where a missing number can sit: `t = 1` (only `m = 1`), or one of four intervals. The
boundary points are excluded by the irrationality of `φ` (hypothesis `hirr`). -/
theorem Nt_cases {t : ℝ} (h : Nt t) (h0 : 0 ≤ t) (h1 : t < φ)
    (hirr : ∀ a b : ℤ, t = a + b * φ → 1 ≤ a) :
    t = 1 ∨ (2 * φ - 2 < t ∧ t < 7 * φ - 10) ∨ (7 * φ - 10 < t ∧ t ≤ 3 - φ) ∨
      (4 * φ - 5 < t ∧ t ≤ 8 - 4 * φ) ∨ (9 * φ - 13 < t ∧ t < φ) := by
  have bad : ∀ a b : ℤ, a ≤ 0 → t ≠ a + b * φ := fun a b ha he => by
    have := hirr a b he; omega
  have n0 : t ≠ 0 := by have := bad 0 0 le_rfl; push_cast at this; simpa using this
  have n1 : t ≠ φ - 1 := by have := bad (-1) 1 (by norm_num); push_cast at this; intro e; exact this (by linarith)
  have n2 : t ≠ 2 * φ - 2 := by have := bad (-2) 2 (by norm_num); push_cast at this; intro e; exact this (by linarith)
  have n3 : t ≠ 7 * φ - 10 := by have := bad (-10) 7 (by norm_num); push_cast at this; intro e; exact this (by linarith)
  have n4 : t ≠ 4 * φ - 5 := by have := bad (-5) 4 (by norm_num); push_cast at this; intro e; exact this (by linarith)
  have n5 : t ≠ 9 * φ - 13 := by have := bad (-13) 9 (by norm_num); push_cast at this; intro e; exact this (by linarith)
  rcases lt_or_ge t (φ - 1) with a | a
  · exact absurd h (not_Nt_c1 (lt_of_le_of_ne h0 (Ne.symm n0)) a)
  rcases lt_or_ge t 1 with b | b
  · exact absurd h (not_Nt_c2 (lt_of_le_of_ne a (Ne.symm n1)) b)
  rcases eq_or_lt_of_le b with b | b
  · exact Or.inl b.symm
  rcases lt_or_ge t (2 * φ - 2) with c | c
  · exact absurd h (not_Nt_c3 b c)
  have c' : 2 * φ - 2 < t := lt_of_le_of_ne c (Ne.symm n2)
  rcases lt_or_ge t (7 * φ - 10) with d | d
  · exact Or.inr (Or.inl ⟨c', d⟩)
  have d' : 7 * φ - 10 < t := lt_of_le_of_ne d (Ne.symm n3)
  rcases le_or_gt t (3 - φ) with e | e
  · exact Or.inr (Or.inr (Or.inl ⟨d', e⟩))
  rcases lt_or_ge t (4 * φ - 5) with f | f
  · exact absurd h (not_Nt_c5 e f)
  have f' : 4 * φ - 5 < t := lt_of_le_of_ne f (Ne.symm n4)
  rcases le_or_gt t (8 - 4 * φ) with g | g
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f', g⟩)))
  rcases lt_or_ge t (9 * φ - 13) with i | i
  · exact absurd h (not_Nt_c7 g i)
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨lt_of_le_of_ne i (Ne.symm n5), h1⟩)))

theorem twice_pos {m : ℤ} (hm : m ∈ Twice) : 0 < m := by
  obtain ⟨n, k, -, -, hn, hk, -, -, -, rfl, -⟩ := hm
  exact W_pos hn hk

/-- The next member of `S` after `m` is `m + g`. -/
def NextIs (S : Set ℤ) (m g : ℤ) : Prop := (∀ j : ℤ, 0 < j → j < g → m + j ∉ S) ∧ m + g ∈ S

theorem nextIs_eq {S : Set ℤ} {m g g' : ℤ} (hg : 0 < g) (hg' : 0 < g') (h : NextIs S m g')
    (h1 : m + g ∈ S) (h2 : ∀ j : ℤ, 0 < j → j < g → m + j ∉ S) : g = g' := by
  rcases lt_trichotomy g g' with l | l | l
  · exact absurd h1 (h.1 g hg l)
  · exact l
  · exact absurd h.2 (h2 g' hg' l)

theorem isGap_of_nextIs {S : Set ℤ} {m g : ℤ} (hm : m ∈ S) (h : NextIs S m g) : IsGap S g :=
  ⟨m, hm, h.2, h.1⟩

/-- The `t`-coordinate moves by `ψ ^ i` when `m` grows by `F(i+1)`; for large `i` it stays inside
any open interval around its starting value, while `m` becomes as large as we like. -/
theorem shift_into {a b t : ℝ} (ha : a < t) (hb : t < b) (B : ℕ) :
    ∃ i : ℕ, B < Nat.fib (i + 1) ∧ a < t + ψ ^ i ∧ t + ψ ^ i < b := by
  have habs : |ψ| = φ - 1 := by rw [abs_of_neg goldenConj_neg, psi_eq]; ring
  have hlt : |ψ| < 1 := by rw [habs]; linarith [phi_hi]
  have hδ : 0 < min (t - a) (b - t) := lt_min (by linarith) (by linarith)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hlt
  refine ⟨max n (B + 1), ?_, ?_⟩
  · have := Nat.le_fib_add_one (max n (B + 1) + 1)
    have h2 : max n (B + 1) + 1 ≤ Nat.fib (max n (B + 1) + 1) + 1 := this
    have : B + 1 ≤ max n (B + 1) := le_max_right _ _
    omega
  · have hle : |ψ| ^ max n (B + 1) ≤ |ψ| ^ n :=
      pow_le_pow_of_le_one (abs_nonneg _) hlt.le (le_max_left _ _)
    have h3 : |ψ ^ max n (B + 1)| < min (t - a) (b - t) := by
      rw [abs_pow]; exact lt_of_le_of_lt hle hn
    have h4 := abs_lt.mp h3
    have h5 := min_le_left (t - a) (b - t)
    have h6 := min_le_right (t - a) (b - t)
    constructor <;> linarith [h4.1, h4.2]

/-- If every `m > 0` whose position lies in `(a, b)` is in `S` and is followed in `S` by `m + g`,
and one such `m₀` exists, then there are such `m` beyond any bound. -/
theorem inf_often {S : Set ℤ} {g : ℤ} {a b : ℝ}
    (cell : ∀ m y : ℤ, 0 < m → a < (m : ℝ) - φ * y → (m : ℝ) - φ * y < b → m ∈ S ∧ NextIs S m g)
    (m₀ y₀ : ℤ) (hm₀ : 0 < m₀) (ha : a < (m₀ : ℝ) - φ * y₀) (hb : (m₀ : ℝ) - φ * y₀ < b)
    (B : ℤ) : ∃ m, B < m ∧ m ∈ S ∧ NextIs S m g := by
  obtain ⟨i, hi, h1, h2⟩ := shift_into ha hb B.toNat
  have e : ((m₀ + Nat.fib (i + 1) : ℤ) : ℝ) - φ * ((y₀ + Nat.fib i : ℤ) : ℝ) =
      (m₀ : ℝ) - φ * y₀ + ψ ^ i := by
    rw [psi_pow]; push_cast; ring
  have hB : B < m₀ + Nat.fib (i + 1) := by
    have : (B.toNat : ℤ) < Nat.fib (i + 1) := by exact_mod_cast hi
    have := Int.self_le_toNat B
    omega
  refine ⟨m₀ + Nat.fib (i + 1), hB, cell _ _ (by omega) (by rw [e]; exact h1) (by rw [e]; exact h2)⟩

end WythoffCeiling
