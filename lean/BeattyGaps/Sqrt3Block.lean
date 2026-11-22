import BeattyGaps.Sqrt3Drift

/-!
# The block structure of the step word of `√3`

This file proves `BlockHypothesis`: for every `k ≥ 1` the first `q_k` letters of the step word of
`√3` form the standard word `s_k`. With it, the drift theorem for OEIS A352676 holds without
assumptions (`drift_theorem_zero`, `drift_theorem_above`, `drift_theorem_below`).

The proof is the classical one, specialised to `√3`.

* `qq k` and `pp k` are the denominators and numerators of the convergents `pp k / qq k` of `√3`
  taken along the continued fraction of `√3 - 1 = [0; 1, 2, 1, 2, …]`; `qq k` is the length of
  the `k`-th standard word.
* `det_qp`, `norm_qp`: consecutive convergents have determinant `±1`, and
  `pp k ^ 2 - 3 qq k ^ 2` is `-2` for even `k` and `1` for odd `k`. Hence the errors
  `eps k = qq k · √3 - pp k` alternate in sign.
* `best_approx_even`, `best_approx_odd`: for `1 ≤ m < qq (k + 1)` and any integer `N`,
  `|m √3 - N| ≥ |eps k|`.
* `w_shift`: therefore `⌊(m + qq k) √3⌋ = ⌊m √3⌋ + pp k` for `1 ≤ m < qq (k + 1)`, so the step
  word repeats itself after a shift by `qq k` on that range (`cBit_shift`).
* `block_hypothesis`: the recursion defining the standard words then follows by induction.
-/

set_option linter.style.longLine false

namespace BeattyGaps.Sqrt3

/-! ## The convergents -/

/-- Denominators: `1, 1, 3, 4, 11, 15, 41, 56, …`. -/
def qq : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | (k + 2) => if k % 2 = 0 then 2 * qq (k + 1) + qq k else qq (k + 1) + qq k

/-- Numerators: `1, 2, 5, 7, 19, 26, 71, 97, …`. -/
def pp : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | (k + 2) => if k % 2 = 0 then 2 * pp (k + 1) + pp k else pp (k + 1) + pp k

theorem qq_even {k : ℕ} (h : k % 2 = 0) : qq (k + 2) = 2 * qq (k + 1) + qq k := by
  rw [qq, ite_eq_left h]

theorem qq_odd {k : ℕ} (h : k % 2 = 1) : qq (k + 2) = qq (k + 1) + qq k := by
  rw [qq, ite_eq_right (by omega)]

theorem pp_even {k : ℕ} (h : k % 2 = 0) : pp (k + 2) = 2 * pp (k + 1) + pp k := by
  rw [pp, ite_eq_left h]

theorem pp_odd {k : ℕ} (h : k % 2 = 1) : pp (k + 2) = pp (k + 1) + pp k := by
  rw [pp, ite_eq_right (by omega)]

theorem qq_pos (k : ℕ) : 1 ≤ qq k ∧ 1 ≤ qq (k + 1) := by
  induction k with
  | zero => simp [qq]
  | succ k ih =>
    obtain ⟨i1, i2⟩ := ih
    refine ⟨i2, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · rw [qq_even h]; omega
    · rw [qq_odd h]; omega

theorem pp_pos (k : ℕ) : 1 ≤ pp k ∧ 1 ≤ pp (k + 1) := by
  induction k with
  | zero => simp [pp]
  | succ k ih =>
    obtain ⟨i1, i2⟩ := ih
    refine ⟨i2, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · rw [pp_even h]; omega
    · rw [pp_odd h]; omega

theorem length_eq_qq (k : ℕ) :
    ((stdWord k).length : ℤ) = qq k ∧ ((stdWord (k + 1)).length : ℤ) = qq (k + 1) := by
  induction k with
  | zero => simp [stdWord, qq]
  | succ k ih =>
    obtain ⟨i1, i2⟩ := ih
    refine ⟨i2, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · rw [stdWord_even h, qq_even h]
      simp only [List.length_append]
      push_cast
      omega
    · rw [stdWord_odd h, qq_odd h]
      simp only [List.length_append]
      push_cast
      omega

/-- Consecutive convergents have determinant `+1` (even index) or `-1` (odd index). -/
theorem det_qp (k : ℕ) :
    (k % 2 = 0 → qq k * pp (k + 1) - qq (k + 1) * pp k = 1) ∧
    (k % 2 = 1 → qq k * pp (k + 1) - qq (k + 1) * pp k = -1) := by
  induction k with
  | zero => simp [qq, pp]
  | succ k ih =>
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have hd := ih.1 h
      refine ⟨fun h' => absurd h' (by omega), fun _ => ?_⟩
      rw [qq_even h, pp_even h]
      linear_combination -hd
    · have hd := ih.2 h
      refine ⟨fun _ => ?_, fun h' => absurd h' (by omega)⟩
      rw [qq_odd h, pp_odd h]
      linear_combination -hd

/-- The norms `pp k ^ 2 - 3 qq k ^ 2` are `-2` for even `k` and `1` for odd `k`. -/
theorem norm_qp (k : ℕ) :
    (k % 2 = 0 → pp k ^ 2 - 3 * qq k ^ 2 = -2 ∧ pp (k + 1) ^ 2 - 3 * qq (k + 1) ^ 2 = 1 ∧
        pp k * pp (k + 1) - 3 * (qq k * qq (k + 1)) = -1) ∧
    (k % 2 = 1 → pp k ^ 2 - 3 * qq k ^ 2 = 1 ∧ pp (k + 1) ^ 2 - 3 * qq (k + 1) ^ 2 = -2 ∧
        pp k * pp (k + 1) - 3 * (qq k * qq (k + 1)) = 1) := by
  induction k with
  | zero => simp [qq, pp]
  | succ k ih =>
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · obtain ⟨hA0, hA1, hB⟩ := ih.1 h
      refine ⟨fun h' => absurd h' (by omega), fun _ => ⟨hA1, ?_, ?_⟩⟩
      · rw [qq_even h, pp_even h]; linear_combination 4 * hA1 + 4 * hB + hA0
      · rw [qq_even h, pp_even h]; linear_combination 2 * hA1 + hB
    · obtain ⟨hA0, hA1, hB⟩ := ih.2 h
      refine ⟨fun _ => ⟨hA1, ?_, ?_⟩, fun h' => absurd h' (by omega)⟩
      · rw [qq_odd h, pp_odd h]; linear_combination hA1 + 2 * hB + hA0
      · rw [qq_odd h, pp_odd h]; linear_combination hA1 + hB

/-! ## The approximation errors -/

/-- `eps k = qq k · √3 - pp k`. -/
noncomputable def eps (k : ℕ) : ℝ := (qq k : ℝ) * √3 - (pp k : ℝ)

theorem eps_pos {k : ℕ} (h : k % 2 = 0) : 0 < eps k := by
  have hA := ((norm_qp k).1 h).1
  have hAR : (pp k : ℝ) ^ 2 - 3 * (qq k : ℝ) ^ 2 = -2 := by exact_mod_cast hA
  have hq : (1 : ℝ) ≤ (qq k : ℝ) := by exact_mod_cast (qq_pos k).1
  have hp : (1 : ℝ) ≤ (pp k : ℝ) := by exact_mod_cast (pp_pos k).1
  have hs := sq_pos
  have hprod : eps k * ((qq k : ℝ) * √3 + (pp k : ℝ)) = 2 := by
    unfold eps; linear_combination ((qq k : ℝ)) ^ 2 * sq_sq - hAR
  have hfac : 0 < (qq k : ℝ) * √3 + (pp k : ℝ) := by nlinarith
  by_contra hc
  rw [not_lt] at hc
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hfac.le]

theorem eps_neg {k : ℕ} (h : k % 2 = 1) : eps k < 0 := by
  have hA := ((norm_qp k).2 h).1
  have hAR : (pp k : ℝ) ^ 2 - 3 * (qq k : ℝ) ^ 2 = 1 := by exact_mod_cast hA
  have hq : (1 : ℝ) ≤ (qq k : ℝ) := by exact_mod_cast (qq_pos k).1
  have hp : (1 : ℝ) ≤ (pp k : ℝ) := by exact_mod_cast (pp_pos k).1
  have hs := sq_pos
  have hprod : eps k * ((qq k : ℝ) * √3 + (pp k : ℝ)) = -1 := by
    unfold eps; linear_combination ((qq k : ℝ)) ^ 2 * sq_sq - hAR
  have hfac : 0 < (qq k : ℝ) * √3 + (pp k : ℝ) := by nlinarith
  by_contra hc
  rw [not_lt] at hc
  nlinarith [mul_nonneg hc hfac.le]

/-! ## Best approximation -/

/-- For even `k`, `1 ≤ m < qq (k+1)` and any integer `N`: `|m √3 - N| ≥ eps k`. -/
theorem best_approx_even {k : ℕ} (hk : k % 2 = 0) (m N : ℤ) (hm1 : 1 ≤ m)
    (hm2 : m < qq (k + 1)) :
    eps k ≤ (m : ℝ) * √3 - (N : ℝ) ∨ (m : ℝ) * √3 - (N : ℝ) ≤ -eps k := by
  have hdet := (det_qp k).1 hk
  have he := eps_pos hk
  have he' := eps_neg (k := k + 1) (by omega)
  have hq := (qq_pos k).1
  have hq' := (qq_pos k).2
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x = m * pp (k + 1) - N * qq (k + 1) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y = N * qq k - m * pp k := ⟨_, rfl⟩
  have hxq : x * qq k + y * qq (k + 1) = m := by rw [hx, hy]; linear_combination m * hdet
  have hxp : x * pp k + y * pp (k + 1) = N := by rw [hx, hy]; linear_combination N * hdet
  have hxqR : (x : ℝ) * (qq k : ℝ) + (y : ℝ) * (qq (k + 1) : ℝ) = (m : ℝ) := by exact_mod_cast hxq
  have hxpR : (x : ℝ) * (pp k : ℝ) + (y : ℝ) * (pp (k + 1) : ℝ) = (N : ℝ) := by exact_mod_cast hxp
  have key : (m : ℝ) * √3 - (N : ℝ) = (x : ℝ) * eps k + (y : ℝ) * eps (k + 1) := by
    unfold eps; linear_combination (-√3) * hxqR + hxpR
  rw [key]
  rcases lt_trichotomy y 0 with hy0 | hy0 | hy0
  · -- y ≤ -1, hence x ≥ 1
    have h1 : y * qq (k + 1) ≤ -qq (k + 1) := by
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -1 - y) (by omega : (0 : ℤ) ≤ qq (k + 1))]
    have hx1 : 1 ≤ x := by
      by_contra hc
      have : x * qq k ≤ 0 := by
        nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -x) (by omega : (0 : ℤ) ≤ qq k)]
      linarith
    have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    have hyR : (y : ℝ) < 0 := by exact_mod_cast hy0
    left
    nlinarith [mul_nonneg (sub_nonneg.mpr hxR) he.le, mul_pos (neg_pos.mpr hyR) (neg_pos.mpr he')]
  · -- y = 0, hence x ≥ 1
    have hx1 : 1 ≤ x := by
      by_contra hc
      have : x * qq k ≤ 0 := by
        nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -x) (by omega : (0 : ℤ) ≤ qq k)]
      rw [hy0] at hxq
      linarith
    have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    have hyR : (y : ℝ) = 0 := by exact_mod_cast hy0
    left
    rw [hyR]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxR) he.le]
  · -- y ≥ 1, hence x ≤ -1
    have h1 : qq (k + 1) ≤ y * qq (k + 1) := by
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ y - 1) (by omega : (0 : ℤ) ≤ qq (k + 1))]
    have hx1 : x ≤ -1 := by
      by_contra hc
      have : 0 ≤ x * qq k := mul_nonneg (by omega) (by omega)
      linarith
    have hxR : (x : ℝ) ≤ -1 := by exact_mod_cast hx1
    have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy0
    right
    nlinarith [mul_nonneg (sub_nonneg.mpr hxR) he.le, mul_pos hyR (neg_pos.mpr he')]

/-- For odd `k`, `1 ≤ m < qq (k+1)` and any integer `N`: `|m √3 - N| ≥ -eps k`. -/
theorem best_approx_odd {k : ℕ} (hk : k % 2 = 1) (m N : ℤ) (hm1 : 1 ≤ m)
    (hm2 : m < qq (k + 1)) :
    -eps k ≤ (m : ℝ) * √3 - (N : ℝ) ∨ (m : ℝ) * √3 - (N : ℝ) ≤ eps k := by
  have hdet := (det_qp k).2 hk
  have he := eps_neg hk
  have he' := eps_pos (k := k + 1) (by omega)
  have hq := (qq_pos k).1
  have hq' := (qq_pos k).2
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x = N * qq (k + 1) - m * pp (k + 1) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y = m * pp k - N * qq k := ⟨_, rfl⟩
  have hxq : x * qq k + y * qq (k + 1) = m := by rw [hx, hy]; linear_combination (-m) * hdet
  have hxp : x * pp k + y * pp (k + 1) = N := by rw [hx, hy]; linear_combination (-N) * hdet
  have hxqR : (x : ℝ) * (qq k : ℝ) + (y : ℝ) * (qq (k + 1) : ℝ) = (m : ℝ) := by exact_mod_cast hxq
  have hxpR : (x : ℝ) * (pp k : ℝ) + (y : ℝ) * (pp (k + 1) : ℝ) = (N : ℝ) := by exact_mod_cast hxp
  have key : (m : ℝ) * √3 - (N : ℝ) = (x : ℝ) * eps k + (y : ℝ) * eps (k + 1) := by
    unfold eps; linear_combination (-√3) * hxqR + hxpR
  rw [key]
  rcases lt_trichotomy y 0 with hy0 | hy0 | hy0
  · -- y ≤ -1, hence x ≥ 1
    have h1 : y * qq (k + 1) ≤ -qq (k + 1) := by
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -1 - y) (by omega : (0 : ℤ) ≤ qq (k + 1))]
    have hx1 : 1 ≤ x := by
      by_contra hc
      have : x * qq k ≤ 0 := by
        nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -x) (by omega : (0 : ℤ) ≤ qq k)]
      linarith
    have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    have hyR : (y : ℝ) < 0 := by exact_mod_cast hy0
    right
    nlinarith [mul_nonneg (sub_nonneg.mpr hxR) (neg_nonneg.mpr he.le), mul_pos (neg_pos.mpr hyR) he']
  · -- y = 0, hence x ≥ 1
    have hx1 : 1 ≤ x := by
      by_contra hc
      have : x * qq k ≤ 0 := by
        nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -x) (by omega : (0 : ℤ) ≤ qq k)]
      rw [hy0] at hxq
      linarith
    have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    have hyR : (y : ℝ) = 0 := by exact_mod_cast hy0
    right
    rw [hyR]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxR) (neg_nonneg.mpr he.le)]
  · -- y ≥ 1, hence x ≤ -1
    have h1 : qq (k + 1) ≤ y * qq (k + 1) := by
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ y - 1) (by omega : (0 : ℤ) ≤ qq (k + 1))]
    have hx1 : x ≤ -1 := by
      by_contra hc
      have : 0 ≤ x * qq k := mul_nonneg (by omega) (by omega)
      linarith
    have hxR : (x : ℝ) ≤ -1 := by exact_mod_cast hx1
    have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy0
    left
    nlinarith [mul_nonneg (sub_nonneg.mpr hxR) (neg_nonneg.mpr he.le), mul_pos hyR he']

/-! ## Shifting by a denominator -/

/-- `⌊(m + qq k) √3⌋ = ⌊m √3⌋ + pp k` for `1 ≤ m < qq (k+1)`. -/
theorem w_shift (k m : ℕ) (hm1 : 1 ≤ m) (hm2 : m < (stdWord (k + 1)).length) :
    w (m + (stdWord k).length) = w m + pp k := by
  have hq : ((stdWord k).length : ℝ) = (qq k : ℝ) := by exact_mod_cast (length_eq_qq k).1
  have hq' : (m : ℤ) < qq (k + 1) := by
    rw [← (length_eq_qq k).2]; exact_mod_cast hm2
  have hm1' : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm1
  have h1 := w_le m
  have h2 := lt_w_add_one m
  have he : (qq k : ℝ) * √3 = (pp k : ℝ) + eps k := by unfold eps; ring
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have hpos := eps_pos hk
    apply w_eq
    · push_cast; rw [hq]; nlinarith
    · push_cast; rw [hq]
      by_contra hcon
      rw [not_lt] at hcon
      rcases best_approx_even hk (m : ℤ) (w m + 1) hm1' hq' with hba | hba
      · push_cast at hba; linarith
      · push_cast at hba
        refine mul_sqrt3_ne_int (m := m + (stdWord k).length) (by omega) (w m + 1 + pp k) ?_
        push_cast; rw [hq]; linarith
  · have hneg := eps_neg hk
    apply w_eq
    · push_cast; rw [hq]
      by_contra hcon
      rw [not_le] at hcon
      rcases best_approx_odd hk (m : ℤ) (w m) hm1' hq' with hba | hba
      · push_cast at hba; linarith
      · push_cast at hba; linarith
    · push_cast; rw [hq]; nlinarith

/-- The step word repeats after a shift by `qq k`, as long as the position stays below
`qq (k+1) - 1`. -/
theorem cBit_shift (k i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 < (stdWord (k + 1)).length) :
    cBit (i + (stdWord k).length) = cBit i := by
  have a := w_shift k i h1 (by omega)
  have b := w_shift k (i + 1) (by omega) h2
  unfold cBit
  rw [show i + (stdWord k).length + 1 = i + 1 + (stdWord k).length by omega, a, b]
  exact decide_eq_decide.mpr (by omega)

theorem pref_add (q L : ℕ) (h : ∀ i, 1 ≤ i → i ≤ L → cBit (i + q) = cBit i) :
    pref (q + L) = pref q ++ pref L := by
  induction L with
  | zero => simp [pref]
  | succ L ih =>
    have hc : cBit (q + L + 1) = cBit (L + 1) := by
      have := h (L + 1) (by omega) le_rfl
      rwa [show L + 1 + q = q + L + 1 by omega] at this
    rw [← Nat.add_assoc, pref_succ, pref_succ, ih (fun i h1 h2 => h i h1 (by omega)), hc,
      List.append_assoc]

/-! ## The block hypothesis -/

theorem block_aux (k : ℕ) (hk : 1 ≤ k) :
    pref (stdWord k).length = stdWord k ∧ pref (stdWord (k + 1)).length = stdWord (k + 1) := by
  induction k, hk using Nat.le_induction with
  | base => exact ⟨block_small (by norm_num) (by norm_num), block_small (by norm_num) (by norm_num)⟩
  | succ k hk ih =>
    obtain ⟨hB, hA⟩ := ih
    refine ⟨hA, ?_⟩
    have hA2 : 2 ≤ (stdWord (k + 1)).length := by
      have := le_stdWord_length (k := k + 1) (by omega); omega
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · -- s_{k+2} = s_{k+1} s_{k+1} s_k
      have hL : (stdWord (k + 1 + 1)).length =
          (stdWord (k + 1)).length + ((stdWord (k + 1)).length + (stdWord k).length) := by
        rw [stdWord_even h]; simp only [List.length_append]; omega
      have hs : ∀ i, 1 ≤ i → i ≤ (stdWord (k + 1)).length + (stdWord k).length →
          cBit (i + (stdWord (k + 1)).length) = cBit i :=
        fun i h1 h2 => cBit_shift (k + 1) i h1 (by rw [hL]; omega)
      rw [hL, pref_add _ _ hs, pref_add _ _ (fun i h1 h2 => hs i h1 (by omega)), hA, hB,
        stdWord_even h, List.append_assoc]
    · -- s_{k+2} = s_{k+1} s_k
      have hL : (stdWord (k + 1 + 1)).length = (stdWord (k + 1)).length + (stdWord k).length := by
        rw [stdWord_odd h]; simp only [List.length_append]
      have hs : ∀ i, 1 ≤ i → i ≤ (stdWord k).length →
          cBit (i + (stdWord (k + 1)).length) = cBit i :=
        fun i h1 h2 => cBit_shift (k + 1) i h1 (by rw [hL]; omega)
      rw [hL, pref_add _ _ hs, hA, hB, stdWord_odd h]

/-- **The block hypothesis holds**: for every `k ≥ 1`, the first `q_k` letters of the step word
of `√3` form the `k`-th standard word. -/
theorem block_hypothesis : BlockHypothesis := fun k hk => (block_aux k hk).1

/-! ## The drift theorem, with no assumptions -/

/-- **Conjecture (3) of OEIS A352676, first half**: `d(n) = 0` for infinitely many `n`, where
`a n` is the `n`-th element of the intersection of the Beatty sequences of `√3` and `1 + √3` and
`d n = a n - ⌊(3/2)(1 + √3) n⌋`. -/
theorem drift_theorem_zero (N : ℕ) : ∃ n, N ≤ n ∧ d n = 0 :=
  d_zero_infinitely_often block_hypothesis N

/-- **Conjecture (3) of OEIS A352676, second half**: `d` is unbounded above. -/
theorem drift_theorem_above (B : ℤ) : ∃ n, 1 ≤ n ∧ B ≤ d n :=
  d_unbounded_above block_hypothesis B

/-- **Conjecture (3) of OEIS A352676, second half**: `d` is unbounded below. -/
theorem drift_theorem_below (B : ℤ) : ∃ n, 1 ≤ n ∧ d n ≤ -B :=
  d_unbounded_below block_hypothesis B

end BeattyGaps.Sqrt3
