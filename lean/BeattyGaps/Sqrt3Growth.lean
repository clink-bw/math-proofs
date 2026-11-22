import BeattyGaps.Sqrt3Block

/-!
# The growth rate of OEIS A352676

Conjecture (2) of the entry: `a(n) / n → (3/2)(1 + √3)`, where `a(n)` is the `n`-th element of
the intersection of the Beatty sequences of `√3` and `1 + √3`. This is a consequence of a 1957
theorem of T. Bang on the density of such intersections; here it is proved directly
(`growth_rate`), with an explicit error bound (`a_sub_le`):

  `|a(n) - (3/2)(1 + √3) n| ≤ 91 √n`.

The proof bounds the walk `F`. Every initial stretch of the step word splits into standard words
(`pref_shift_split`), the sum of the walk over a standard word `s_k` is at most `k + 2` in
absolute value (`Phi_std_bound`), and the lengths of the standard words grow exponentially
(`poly_le_qq`). Together these give `F(M)² ≤ 324 M` (`F_sq_le`), and `|a(n) - τ n| ≤ 2|F| + 1`
(`tau_sub_le`).

The bound `√n` is far from sharp: the true order is logarithmic.
-/

set_option linter.style.longLine false

namespace BeattyGaps.Sqrt3

/-! ## Sums of the walk over standard words are small -/

theorem Phi_std_bound (k : ℕ) (κ : ℤ) : |Phi κ (stdWord k)| ≤ (k : ℤ) + 2 := by
  have hr0 : 0 ≤ κ % 6 := by omega
  have hr6 : κ % 6 < 6 := by omega
  rw [Phi_congr (κ := κ) (κ' := κ % 6) (by omega)]
  have hG := (good_all k).1
  have hj : 4 * ((k / 4 : ℕ) : ℤ) ≤ (k : ℤ) := by omega
  have hj0 : (0 : ℤ) ≤ ((k / 4 : ℕ) : ℤ) := by omega
  have hk : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  generalize κ % 6 = r at hr0 hr6
  rw [abs_le]
  rcases hk with hk | hk | hk | hk
  · rw [(hG.1 hk).1 r hr0 hr6]
    interval_cases r <;> simp [tbl] <;> omega
  · rw [(hG.2.1 hk).1 r hr0 hr6]
    interval_cases r <;> simp [tbl] <;> omega
  · rw [(hG.2.2.1 hk).1 r hr0 hr6]
    interval_cases r <;> simp [tbl] <;> omega
  · rw [(hG.2.2.2 hk).1 r hr0 hr6]
    interval_cases r <;> simp [tbl] <;> omega

/-! ## Splitting an initial stretch of the step word -/

theorem length_mono (n : ℕ) : (stdWord n).length ≤ (stdWord (n + 1)).length := by
  rcases n with _ | n
  · decide
  · have h1 := (stdWord_length n).1
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [stdWord_even h]; simp only [List.length_append]; omega
    · rw [stdWord_odd h]; simp only [List.length_append]; omega

theorem length_succ_le (n : ℕ) :
    (stdWord (n + 1 + 1)).length ≤ 2 * (stdWord (n + 1)).length + (stdWord n).length := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [stdWord_even h]; simp only [List.length_append]; omega
  · rw [stdWord_odd h]; simp only [List.length_append]; omega

/-- For `q_{n+1} ≤ M < q_{n+2}`, the first `M` letters are `s_{n+1}` followed by the first
`M - q_{n+1}` letters. -/
theorem pref_shift_split (n M : ℕ) (h1 : (stdWord (n + 1)).length ≤ M)
    (h2 : M < (stdWord (n + 1 + 1)).length) :
    pref M = stdWord (n + 1) ++ pref (M - (stdWord (n + 1)).length) := by
  obtain ⟨L, rfl⟩ : ∃ L, M = (stdWord (n + 1)).length + L :=
    ⟨M - (stdWord (n + 1)).length, by omega⟩
  have hpos := (stdWord_length (n + 1)).1
  rw [pref_add _ L (fun i hi1 hi2 => cBit_shift (n + 1) i hi1 (by omega)),
    block_hypothesis (n + 1) (by omega)]
  simp

/-- Below `q_{n+1}`, the walk started in any state stays within `(n + 3)²`. -/
theorem level_bound (n : ℕ) :
    ∀ M : ℕ, M < (stdWord (n + 1)).length → ∀ κ : ℤ, |Phi κ (pref M)| ≤ ((n : ℤ) + 3) ^ 2 := by
  induction n with
  | zero =>
    intro M hM κ
    have h1 : (stdWord (0 + 1)).length = 1 := by decide
    have h0 : M = 0 := by omega
    subst h0
    simp [pref, Phi]
  | succ n ih =>
    intro M hM κ
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := by omega
    by_cases h1 : M < (stdWord (n + 1)).length
    · have h := ih M h1 κ
      have hmono : ((n : ℤ) + 3) ^ 2 ≤ (((n + 1 : ℕ) : ℤ) + 3) ^ 2 := by push_cast; nlinarith
      linarith
    · rw [not_lt] at h1
      have hlen := length_succ_le n
      have hmn := length_mono n
      rw [pref_shift_split n M h1 hM, Phi_append]
      have hb := abs_le.mp (Phi_std_bound (n + 1) κ)
      push_cast at hb
      by_cases h2 : M - (stdWord (n + 1)).length < (stdWord (n + 1)).length
      · have h := abs_le.mp (ih _ h2 (κ + gam (stdWord (n + 1))))
        rw [abs_le]
        push_cast
        constructor <;> nlinarith
      · rw [not_lt] at h2
        rw [pref_shift_split n _ h2 (by omega), Phi_append]
        have hb2 := abs_le.mp (Phi_std_bound (n + 1) (κ + gam (stdWord (n + 1))))
        push_cast at hb2
        have h := abs_le.mp (ih (M - (stdWord (n + 1)).length - (stdWord (n + 1)).length)
          (by omega) (κ + gam (stdWord (n + 1)) + gam (stdWord (n + 1))))
        rw [abs_le]
        push_cast
        constructor <;> nlinarith

/-! ## The standard words grow fast -/

theorem qq_mono (n : ℕ) : qq n ≤ qq (n + 1) := by
  rcases n with _ | n
  · decide
  · have h1 := (qq_pos n).1
    have h2 := (qq_pos n).2
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [qq_even h]; omega
    · rw [qq_odd h]; omega

theorem qq_double (n : ℕ) : 2 * qq n ≤ qq (n + 2) := by
  have hm := qq_mono n
  have hp := (qq_pos n).1
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [qq_even h]; omega
  · rw [qq_odd h]; omega

theorem poly_le_qq : ∀ n : ℕ, ((n : ℤ) + 3) ^ 4 ≤ 324 * qq n
  | 0 => by decide
  | 1 => by decide
  | (n + 2) => by
    have ih := poly_le_qq n
    by_cases hn : n < 8
    · interval_cases n <;> decide
    · have hd := qq_double n
      have hx : (11 : ℤ) ≤ (n : ℤ) + 3 := by omega
      have h1 : 5 * ((n : ℤ) + 5) ^ 2 ≤ 7 * ((n : ℤ) + 3) ^ 2 := by nlinarith
      have h2 := mul_le_mul h1 h1 (by positivity) (by positivity)
      have h3 : (0 : ℤ) ≤ ((n : ℤ) + 3) ^ 4 := by positivity
      push_cast
      nlinarith

/-! ## The walk is at most of order `√M` -/

theorem Phi_sq_bound (n : ℕ) :
    ∀ M : ℕ, M < (stdWord (n + 1)).length → ∀ κ : ℤ, (Phi κ (pref M)) ^ 2 ≤ 324 * (M : ℤ) := by
  induction n with
  | zero =>
    intro M hM κ
    have h1 : (stdWord (0 + 1)).length = 1 := by decide
    have h0 : M = 0 := by omega
    subst h0
    simp [pref, Phi]
  | succ n ih =>
    intro M hM κ
    by_cases h1 : M < (stdWord (n + 1)).length
    · exact ih M h1 κ
    · rw [not_lt] at h1
      have hb := abs_le.mp (level_bound (n + 1) M hM κ)
      have hg := poly_le_qq (n + 1)
      have hl : qq (n + 1) ≤ (M : ℤ) := by
        rw [← (length_eq_qq n).2]; exact_mod_cast h1
      have hsq : (Phi κ (pref M)) ^ 2 ≤ ((((n + 1 : ℕ) : ℤ) + 3) ^ 2) ^ 2 := sq_le_sq' hb.1 hb.2
      have e : ((((n + 1 : ℕ) : ℤ) + 3) ^ 2) ^ 2 = (((n + 1 : ℕ) : ℤ) + 3) ^ 4 := by ring
      linarith

theorem F_sq_le (M : ℕ) : (F M) ^ 2 ≤ 324 * (M : ℤ) := by
  rw [F_eq_Phi]
  exact Phi_sq_bound M M (by have := (stdWord_length M).2; omega) 4

/-! ## From the walk to `a(n)` -/

theorem a_succ_le (n : ℕ) (hn : 1 ≤ n) : a (n + 1) ≤ a n + 6 := by
  obtain ⟨g, hg2, hg6, hin, hno, -⟩ := next_elem (inS_a n)
  have hc : cnt (a n + g) = cnt (a n) + 1 := cnt_next (a n) g (by omega) hin hno
  rw [cnt_a hn] at hc
  have h := a_cnt hin
  rw [hc] at h
  omega

theorem a_le (n : ℕ) (hn : 1 ≤ n) : a n ≤ 6 * n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h5 := a_cnt inS_five
    have hp := cnt_pos inS_five
    have h : a 1 ≤ a (cnt 5) := by
      unfold a
      exact (Nat.nth_le_nth infinite_inS).mpr (by omega)
    omega
  | succ n hn ih =>
    have := a_succ_le n hn
    omega

/-- At an element `x` of the intersection, `(3/2)(1+√3) · cnt x` is within `2|F x| + 1` of `x`. -/
theorem tau_sub_le {x : ℕ} (hx : inS x) :
    |(3 / 2 * (1 + √3)) * (cnt x : ℝ) - (x : ℝ)| ≤ 2 * |(F x : ℝ)| + 1 := by
  obtain ⟨hW1, hW2⟩ := floor_succ_bounds hx
  have hξ : (0 : ℝ) < √3 - 1 := sqm1_pos
  have hlo := sq_lo
  have hF : (F x : ℝ) = 3 * (cnt x : ℝ) - ((w (x + 1) : ℝ) - ((x : ℝ) + 1)) := by
    unfold F; push_cast; ring
  have e : (3 / 2 * (1 + √3)) * (cnt x : ℝ) * (√3 - 1) = 3 * (cnt x : ℝ) := by
    linear_combination (cnt x : ℝ) * tau_mul
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (3 / 2 * (1 + √3)) * (cnt x : ℝ) - (x : ℝ) := ⟨_, rfl⟩
  have hDξ : D * (√3 - 1) = 3 * (cnt x : ℝ) - (x : ℝ) * (√3 - 1) := by
    rw [hD]; linear_combination e
  have hlow : (F x : ℝ) ≤ D * (√3 - 1) := by rw [hDξ, hF]; linarith
  have hupp : D * (√3 - 1) < (F x : ℝ) + (√3 - 1) := by rw [hDξ, hF]; linarith
  have h2ξ : (0 : ℝ) < 2 * (√3 - 1) - 1 := by linarith
  rw [← hD, abs_le]
  rcases le_or_gt 0 (F x : ℝ) with hpos | hneg
  · rw [abs_of_nonneg hpos]
    constructor
    · by_contra hc
      rw [not_le] at hc
      have hDneg : D < 0 := by linarith
      nlinarith [mul_pos (neg_pos.mpr hDneg) hξ]
    · by_contra hc
      rw [not_le] at hc
      nlinarith [mul_pos (sub_pos.mpr hc) hξ, mul_nonneg hpos h2ξ.le]
  · rw [abs_of_neg hneg]
    constructor
    · by_contra hc
      rw [not_le] at hc
      nlinarith [mul_pos (sub_pos.mpr hc) hξ, mul_pos (neg_pos.mpr hneg) h2ξ]
    · by_contra hc
      rw [not_le] at hc
      nlinarith [mul_pos (sub_pos.mpr hc) hξ]

/-- **Error bound**: `|a(n) - (3/2)(1 + √3) n| ≤ 91 √n`. -/
theorem a_sub_le (n : ℕ) (hn : 1 ≤ n) :
    |(a n : ℝ) - (3 / 2 * (1 + √3)) * (n : ℝ)| ≤ 91 * √(n : ℝ) := by
  have h1 := tau_sub_le (inS_a n)
  rw [cnt_a hn] at h1
  have hF := F_sq_le (a n)
  have hle := a_le n hn
  have hFR : ((F (a n) : ℝ)) ^ 2 ≤ 324 * (a n : ℝ) := by exact_mod_cast hF
  have h2 : |(F (a n) : ℝ)| ≤ √(324 * (a n : ℝ)) := Real.abs_le_sqrt hFR
  have hleR : (a n : ℝ) ≤ 6 * (n : ℝ) := by exact_mod_cast hle
  have h3 : √(324 * (a n : ℝ)) ≤ √(2025 * (n : ℝ)) := Real.sqrt_le_sqrt (by linarith)
  have h4 : √(2025 * (n : ℝ)) = 45 * √(n : ℝ) := by
    rw [Real.sqrt_mul (by norm_num), show (2025 : ℝ) = 45 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have h5 : (1 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.one_le_sqrt]; exact_mod_cast hn
  rw [abs_sub_comm]
  linarith

/-! ## The limit -/

/-- **Conjecture (2) of OEIS A352676**: `a(n) / n → (3/2)(1 + √3)`. -/
theorem growth_rate :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) Filter.atTop
      (nhds (3 / 2 * (1 + √3))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ᶠ n : ℕ in Filter.atTop,
      dist ((a n : ℝ) / (n : ℝ)) (3 / 2 * (1 + √3)) ≤ 91 / √(n : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hs : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hn0
    have hsq : √(n : ℝ) * √(n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0.le
    have h := a_sub_le n hn
    have e : (a n : ℝ) / (n : ℝ) - 3 / 2 * (1 + √3)
        = ((a n : ℝ) - (3 / 2 * (1 + √3)) * (n : ℝ)) / (n : ℝ) := by
      field_simp
    rw [Real.dist_eq, e, abs_div, abs_of_pos hn0, div_le_div_iff₀ hn0 hs]
    have h' := mul_le_mul_of_nonneg_right h hs.le
    nlinarith
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => dist_nonneg) hbound ?_
  exact tendsto_const_nhds.div_atTop
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

end BeattyGaps.Sqrt3
