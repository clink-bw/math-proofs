import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Integer `{k}`-domination of grid graphs: definitions

* `IsDomFn G k f`: `f` gives every vertex a weight in `ℕ` so that the weights on each vertex and
  its neighbours add up to at least `k` (an integer `{k}`-dominating function, in the sense of
  Domke, Hedetniemi, Laskar and Fricke).
* `domNum G k`: the least total weight of such a function, written `γ_{k}(G)` in the literature.
* `grid m n`: the grid graph `P_m □ P_n` with `m` rows and `n` columns.

The only other content of this file is `nbhd_sum_grid`, which writes the weight seen by a vertex
of the grid as a sum of five entries of the weight function extended by zero outside the grid.
-/

namespace GridDomination

open Finset SimpleGraph

section Defs

variable {V : Type*} [Fintype V]

/-- `f` is an integer `{k}`-dominating function of `G`: for every vertex `v`, the weights on `v`
and on its neighbours add up to at least `k`. -/
def IsDomFn (G : SimpleGraph V) [G.LocallyFinite] (k : ℕ) (f : V → ℕ) : Prop :=
  ∀ v, k ≤ f v + ∑ u ∈ G.neighborFinset v, f u

/-- The integer `{k}`-domination number `γ_{k}(G)`: the least total weight of an integer
`{k}`-dominating function. -/
noncomputable def domNum (G : SimpleGraph V) [G.LocallyFinite] (k : ℕ) : ℕ :=
  sInf {w | ∃ f, IsDomFn G k f ∧ ∑ v, f v = w}

/-- To show `domNum G k = w`: exhibit a dominating function of weight `w`, and show that every
dominating function weighs at least `w`. -/
theorem domNum_eq {G : SimpleGraph V} [G.LocallyFinite] {k w : ℕ}
    (hex : ∃ f, IsDomFn G k f ∧ ∑ v, f v = w) (hlb : ∀ f, IsDomFn G k f → w ≤ ∑ v, f v) :
    domNum G k = w := by
  apply le_antisymm
  · exact Nat.sInf_le hex
  · apply le_csInf ⟨w, hex⟩
    rintro _ ⟨f, hf, rfl⟩
    exact hlb f hf

end Defs

/-- The grid graph with `m` rows and `n` columns: the Cartesian product of two paths. -/
abbrev grid (m n : ℕ) : SimpleGraph (Fin m × Fin n) := pathGraph m □ pathGraph n

/-- A function on `Fin n` extended by zero to `ℕ`, with `Fin n` placed at positions `1, …, n`. -/
def zext1 {n : ℕ} (h : Fin n → ℕ) (k : ℕ) : ℕ :=
  if hk : 1 ≤ k ∧ k ≤ n then h ⟨k - 1, by omega⟩ else 0

/-- Weights on the `m × n` grid extended by zero to `ℕ × ℕ`, with the grid placed at rows
`1, …, m` and columns `1, …, n`. -/
def zext {m n : ℕ} (f : Fin m × Fin n → ℕ) (i j : ℕ) : ℕ :=
  if h : (1 ≤ i ∧ i ≤ m) ∧ (1 ≤ j ∧ j ≤ n) then f (⟨i - 1, by omega⟩, ⟨j - 1, by omega⟩) else 0

theorem zext_apply {m n : ℕ} (f : Fin m × Fin n → ℕ) (i : Fin m) (j : Fin n) :
    zext f (i.val + 1) (j.val + 1) = f (i, j) := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [zext]
  rw [dif_pos (by omega)]
  rfl

/-- In a path, the weights on the neighbours of `v` are the two entries either side of it. -/
theorem sum_neighbor_path {n : ℕ} (h : Fin n → ℕ) (v : Fin n) :
    ∑ u ∈ (pathGraph n).neighborFinset v, h u = zext1 h v.val + zext1 h (v.val + 2) := by
  have hv := v.isLt
  have key : ∑ u ∈ (pathGraph n).neighborFinset v, h u
      = (∑ u : Fin n, if u.val + 1 = v.val then h u else 0)
        + ∑ u : Fin n, if v.val + 1 = u.val then h u else 0 := by
    rw [← Finset.sum_add_distrib]
    have : (pathGraph n).neighborFinset v
        = Finset.univ.filter (fun u : Fin n => v.val + 1 = u.val ∨ u.val + 1 = v.val) := by
      ext u
      simp [pathGraph_adj]
    rw [this, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h1 : u.val + 1 = v.val <;> by_cases h2 : v.val + 1 = u.val <;>
      simp [h1, h2] <;> omega
  rw [key]
  congr 1
  · by_cases h0 : 1 ≤ v.val
    · rw [Finset.sum_eq_single (⟨v.val - 1, by omega⟩ : Fin n)]
      · simp only [zext1]
        rw [if_pos (by simp; omega), dif_pos (by omega)]
      · intro u _ hu
        rw [if_neg]
        intro hh
        exact hu (Fin.ext (by simp; omega))
      · intro hh
        exact absurd (Finset.mem_univ _) hh
    · rw [Finset.sum_eq_zero]
      · simp only [zext1]
        rw [dif_neg (by omega)]
      · intro u _
        rw [if_neg (by omega)]
  · by_cases h0 : v.val + 1 < n
    · rw [Finset.sum_eq_single (⟨v.val + 1, h0⟩ : Fin n)]
      · simp only [zext1]
        rw [if_pos (by simp), dif_pos (by omega)]
        rfl
      · intro u _ hu
        rw [if_neg]
        intro hh
        exact hu (Fin.ext (by simp; omega))
      · intro hh
        exact absurd (Finset.mem_univ _) hh
    · rw [Finset.sum_eq_zero]
      · simp only [zext1]
        rw [dif_neg (by omega)]
      · intro u _
        have := u.isLt
        rw [if_neg (by omega)]

/-- The weight seen by the vertex in row `i`, column `j` of the grid: itself, the vertices above
and below, and the vertices to the left and right, where anything outside the grid counts 0. -/
theorem nbhd_sum_grid {m n : ℕ} (f : Fin m × Fin n → ℕ) (i : Fin m) (j : Fin n) :
    f (i, j) + ∑ u ∈ (grid m n).neighborFinset (i, j), f u
      = zext f (i.val + 1) (j.val + 1) + zext f i.val (j.val + 1) + zext f (i.val + 2) (j.val + 1)
        + zext f (i.val + 1) j.val + zext f (i.val + 1) (j.val + 2) := by
  have hi := i.isLt
  have hj := j.isLt
  rw [neighborFinset_boxProd, Finset.sum_disjUnion, Finset.sum_product, Finset.sum_product]
  simp only [Finset.sum_singleton]
  rw [sum_neighbor_path (fun a => f (a, j)) i, sum_neighbor_path (fun b => f (i, b)) j,
    zext_apply]
  have e1 : ∀ a, zext f a (j.val + 1) = zext1 (fun a => f (a, j)) a := by
    intro a
    simp only [zext, zext1]
    by_cases ha : 1 ≤ a ∧ a ≤ m
    · rw [dif_pos ⟨ha, by omega⟩, dif_pos ha]
      rfl
    · rw [dif_neg (fun hh => ha hh.1), dif_neg ha]
  have e2 : ∀ b, zext f (i.val + 1) b = zext1 (fun b => f (i, b)) b := by
    intro b
    simp only [zext, zext1]
    by_cases hb : 1 ≤ b ∧ b ≤ n
    · rw [dif_pos ⟨by omega, hb⟩, dif_pos hb]
      rfl
    · rw [dif_neg (fun hh => hb hh.2), dif_neg hb]
  rw [e1, e1, e2, e2]
  ring

end GridDomination
