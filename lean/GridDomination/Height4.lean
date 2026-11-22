import GridDomination.Certificate
import GridDomination.Height4Data

/-!
# The `{2}`-domination number of the `4 × n` grid

* `domNum_grid_four`: `γ_{2}(P_4 □ P_n) = Height4.gamma n` for every `n ≥ 1`, where
  `Height4.gamma n` is `⌈(19 n + 9) / 10⌉`, except that it is one less for
  `n = 4, 7, 8, 15, 18, 26, 37, 48` and one more for `n = 1`.
* `domNum_grid_four_of_ge`: `γ_{2}(P_4 □ P_n) = 2n - ⌊(n - 9)/10⌋` for every `n ≥ 49`.
  This is Conjecture 3.7 of Lee and Liu, *The integer {2}-domination number of grids*
  (arXiv:2502.00134).
-/

namespace GridDomination

open Finset

namespace Height4

theorem gamma_of_ge {n : ℕ} (hn : 49 ≤ n) : gamma n = (19 * n + 18) / 10 := by
  unfold gamma
  rw [ite_eq_right (by omega), ite_eq_right (by simp; omega)]

/-- Every `{2}`-dominating function of the `4 × n` grid weighs at least `gamma n`. -/
theorem lower {n : ℕ} (hn : 1 ≤ n) (f : Fin 4 × Fin n → ℕ) (hf : IsDomFn (grid 4 n) 2 f) :
    gamma n ≤ ∑ v, f v := by
  rcases Nat.lt_or_ge n 49 with h49 | h49
  · have hg := List.all_eq_true.mp small_ok n (List.mem_range'_1.mpr ⟨hn, by omega⟩)
    exact valid.lower_grid_small (n := n) (show n ≤ 49 by omega) hg f hf
  · have h : 9 + 19 * n ≤ 10 * ∑ v, f v := valid.lower_grid (n := n) h49 f hf
    rw [gamma_of_ge h49]
    omega

/-- Some `{2}`-dominating function of the `4 × n` grid with values in `{0,1,2}` weighs exactly
`gamma n`. -/
theorem upper {n : ℕ} (hn : 1 ≤ n) :
    ∃ f : Fin 4 × Fin n → ℕ, IsDomFn (grid 4 n) 2 f ∧ (∀ v, f v ≤ 2) ∧ ∑ v, f v = gamma n := by
  rcases Nat.lt_or_ge n 49 with h49 | h49
  · exact exists_dom_of_accept
      (List.all_eq_true.mp words_ok n (List.mem_range'_1.mpr ⟨hn, by omega⟩))
  · have hp := all_range pump_ok (Nat.mod_lt n (show 0 < 10 by norm_num))
    obtain ⟨hp12, hp3⟩ := and_true_split hp
    obtain ⟨hp1, hp2⟩ := and_true_split hp12
    have hmod := Nat.eq_of_beq_eq_true hp2
    have hlt : baseL.getD (n % 10) 0 < 49 + 10 := Nat.le_of_ble_eq_true hp3
    generalize baseL.getD (n % 10) 0 = L at hp1 hmod hlt
    obtain ⟨f, hf, hb, hs⟩ := exists_dom_of_pump hp1 (n := n) (k := (n - L) / 10) (by omega)
    exact ⟨f, hf, hb, by rw [hs, gamma_of_ge h49]; omega⟩

end Height4

/-- The integer `{2}`-domination number of the `4 × n` grid, for every `n ≥ 1`. -/
theorem domNum_grid_four (n : ℕ) (hn : 1 ≤ n) : domNum (grid 4 n) 2 = Height4.gamma n := by
  obtain ⟨f, hf, -, hs⟩ := Height4.upper hn
  exact domNum_eq ⟨f, hf, hs⟩ (fun g hg => Height4.lower hn g hg)

/-- **Lee–Liu Conjecture 3.7.**  The integer `{2}`-domination number of the `4 × n` grid is
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

/-- The minimum for the `4 × n` grid is attained by a function with values in `{0, 1, 2}`, so it
does not matter whether weights above 2 are allowed. -/
theorem exists_dom_grid_four (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : Fin 4 × Fin n → ℕ, IsDomFn (grid 4 n) 2 f ∧ (∀ v, f v ≤ 2) ∧
      ∑ v, f v = Height4.gamma n :=
  Height4.upper hn

end GridDomination
