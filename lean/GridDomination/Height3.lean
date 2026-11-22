import GridDomination.Certificate
import GridDomination.Height3Data

/-!
# The `{2}`-domination number of the `3 × n` grid

`domNum_grid_three`: `γ_{2}(P_3 □ P_n) = ⌊3n/2⌋ + 1` for every `n ≥ 1`.
This is Conjecture 2.5 of Lee and Liu, *The integer {2}-domination number of grids*
(arXiv:2502.00134); they proved the upper bound.
-/

namespace GridDomination

open Finset

namespace Height3

/-- Every `{2}`-dominating function of the `3 × n` grid weighs at least `⌊3n/2⌋ + 1`. -/
theorem lower {n : ℕ} (hn : 1 ≤ n) (f : Fin 3 × Fin n → ℕ) (hf : IsDomFn (grid 3 n) 2 f) :
    3 * n / 2 + 1 ≤ ∑ v, f v := by
  have h : 1 + 3 * n ≤ 2 * ∑ v, f v := valid.lower_grid (n := n) hn f hf
  omega

/-- Some `{2}`-dominating function of the `3 × n` grid with values in `{0,1,2}` weighs exactly
`⌊3n/2⌋ + 1`. -/
theorem upper {n : ℕ} (hn : 1 ≤ n) :
    ∃ f : Fin 3 × Fin n → ℕ, IsDomFn (grid 3 n) 2 f ∧ (∀ v, f v ≤ 2) ∧
      ∑ v, f v = 3 * n / 2 + 1 := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · exact exists_dom_of_accept
      (List.all_eq_true.mp words_ok n (List.mem_range'_1.mpr ⟨hn, by omega⟩))
  · have hp := all_range pump_ok (Nat.mod_lt n (show 0 < 2 by norm_num))
    obtain ⟨hp12, hp3⟩ := and_true_split hp
    obtain ⟨hp1, hp2⟩ := and_true_split hp12
    have hmod := Nat.eq_of_beq_eq_true hp2
    have hlt : baseL.getD (n % 2) 0 < 2 + 2 := Nat.le_of_ble_eq_true hp3
    generalize baseL.getD (n % 2) 0 = L at hp1 hmod hlt
    obtain ⟨f, hf, hb, hs⟩ := exists_dom_of_pump hp1 (n := n) (k := (n - L) / 2) (by omega)
    exact ⟨f, hf, hb, by rw [hs]; omega⟩

end Height3

/-- **Lee–Liu Conjecture 2.5.**  The integer `{2}`-domination number of the `3 × n` grid is
`⌊3n/2⌋ + 1`, for every `n ≥ 1`. -/
theorem domNum_grid_three (n : ℕ) (hn : 1 ≤ n) : domNum (grid 3 n) 2 = 3 * n / 2 + 1 := by
  obtain ⟨f, hf, -, hs⟩ := Height3.upper hn
  exact domNum_eq ⟨f, hf, hs⟩ (fun g hg => Height3.lower hn g hg)

/-- The minimum for the `3 × n` grid is attained by a function with values in `{0, 1, 2}`, so it
does not matter whether weights above 2 are allowed. -/
theorem exists_dom_grid_three (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : Fin 3 × Fin n → ℕ, IsDomFn (grid 3 n) 2 f ∧ (∀ v, f v ≤ 2) ∧
      ∑ v, f v = 3 * n / 2 + 1 :=
  Height3.upper hn

end GridDomination
