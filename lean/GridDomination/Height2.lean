import GridDomination.Certificate
import GridDomination.Height2Data

/-!
# The `{2}`-domination number of the `2 × n` grid

`domNum_grid_two`: `γ_{2}(P_2 □ P_n) = n + 1` for every `n ≥ 1`.  This is Theorem 2.3 of Lee and
Liu (arXiv:2502.00134), which they prove by hand; it is included as a test of the method.
-/

namespace GridDomination

open Finset

namespace Height2

theorem lower {n : ℕ} (hn : 1 ≤ n) (f : Fin 2 × Fin n → ℕ) (hf : IsDomFn (grid 2 n) 2 f) :
    n + 1 ≤ ∑ v, f v := by
  have h : 1 + 1 * n ≤ 1 * ∑ v, f v := valid.lower_grid (n := n) hn f hf
  omega

theorem upper {n : ℕ} (hn : 1 ≤ n) :
    ∃ f : Fin 2 × Fin n → ℕ, IsDomFn (grid 2 n) 2 f ∧ (∀ v, f v ≤ 2) ∧ ∑ v, f v = n + 1 := by
  have hp := all_range pump_ok (Nat.mod_lt n (show 0 < 2 by norm_num))
  obtain ⟨hp12, hp3⟩ := and_true_split hp
  obtain ⟨hp1, hp2⟩ := and_true_split hp12
  have hmod := Nat.eq_of_beq_eq_true hp2
  have hlt : baseL.getD (n % 2) 0 < 1 + 2 := Nat.le_of_ble_eq_true hp3
  generalize baseL.getD (n % 2) 0 = L at hp1 hmod hlt
  obtain ⟨f, hf, hb, hs⟩ := exists_dom_of_pump hp1 (n := n) (k := (n - L) / 2) (by omega)
  exact ⟨f, hf, hb, by rw [hs]; omega⟩

end Height2

/-- The integer `{2}`-domination number of the `2 × n` grid is `n + 1` (Lee–Liu Theorem 2.3). -/
theorem domNum_grid_two (n : ℕ) (hn : 1 ≤ n) : domNum (grid 2 n) 2 = n + 1 := by
  obtain ⟨f, hf, -, hs⟩ := Height2.upper hn
  exact domNum_eq ⟨f, hf, hs⟩ (fun g hg => Height2.lower hn g hg)

end GridDomination
