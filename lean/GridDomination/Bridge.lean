import GridDomination.Basic
import GridDomination.Automaton

/-!
# The automaton accepts exactly the `{2}`-dominating functions of the grid

Two theorems connect the grid graph of `Basic.lean` with the automaton of `Automaton.lean`.

* `exists_run_of_dom`: a `{2}`-dominating function of the `m × n` grid gives an accepted list of
  `n` columns whose weight is at most the weight of the function (weights above 2 are cut to 2).
* `exists_dom_of_run`: an accepted list of `n` columns gives a `{2}`-dominating function of the
  `m × n` grid with values in `{0,1,2}` and the same weight.

So the least weight of an accepted list of length `n` is `γ_{2}(P_m □ P_n)`.
-/

namespace GridDomination

open Finset SimpleGraph

/-! ### Base-3 digits -/

theorem dg_lt (c i : ℕ) : dg c i < 3 := Nat.mod_lt _ (by norm_num)

@[simp] theorem dg_zero (i : ℕ) : dg 0 i = 0 := by simp [dg]

theorem encode_lt (m : ℕ) (x : ℕ → ℕ) (hx : ∀ i, x i ≤ 2) : encode m x < 3 ^ m := by
  induction m with
  | zero => simp [encode]
  | succ m ih =>
    have h2 : x m * 3 ^ m ≤ 2 * 3 ^ m := Nat.mul_le_mul_right _ (hx m)
    simp only [encode, pow_succ]
    omega

theorem dg_encode (m : ℕ) (x : ℕ → ℕ) (hx : ∀ i, x i ≤ 2) {i : ℕ} (hi : i < m) :
    dg (encode m x) i = x i := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [encode]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · obtain ⟨k, rfl⟩ : ∃ k, m = i + (k + 1) := ⟨m - i - 1, by omega⟩
      have e : x (i + (k + 1)) * 3 ^ (i + (k + 1)) = (x (i + (k + 1)) * 3 ^ k * 3) * 3 ^ i := by
        ring
      have := ih h
      unfold dg at this ⊢
      rw [e, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right]
      exact this
    · have hlt := encode_lt i x hx
      have := hx i
      unfold dg
      rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
      omega

theorem encode_eq_zero (m : ℕ) (x : ℕ → ℕ) (hx : ∀ i, i < m → x i = 0) : encode m x = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [encode]
    rw [ih (fun i hi => hx i (by omega)), hx m (by omega)]
    simp

theorem wt_eq_sum (m c : ℕ) : wt m c = ∑ i ∈ range m, dg c i := by
  induction m with
  | zero => simp [wt]
  | succ m ih => simp [wt, Finset.sum_range_succ, ih]

theorem geq_iff {m d ν : ℕ} : geq m d ν = true ↔ ∀ i, i < m → dg ν i ≤ dg d i := by
  simp [geq, List.all_eq_true]

theorem geq_zero_right (m d : ℕ) : geq m d 0 = true := by
  rw [geq_iff]
  intro i _
  simp

theorem needAt_le (m b d i : ℕ) : needAt m b d i ≤ 2 := by
  unfold needAt
  omega

theorem dg_need (m b d : ℕ) {i : ℕ} (hi : i < m) : dg (need m b d) i = needAt m b d i :=
  dg_encode m _ (needAt_le m b d) hi

theorem need_lt (m b d : ℕ) : need m b d < 3 ^ m := encode_lt m _ (needAt_le m b d)

/-! ### Runs of the automaton -/

theorem step_eq_some {m b ν d : ℕ} {t : ℕ × ℕ} :
    step m (b, ν) d = some t ↔ d < 3 ^ m ∧ geq m d ν = true ∧ t = (d, need m b d) := by
  unfold step
  by_cases h : d < 3 ^ m ∧ geq m d ν = true
  · rw [if_pos h]
    constructor
    · intro ht
      exact ⟨h.1, h.2, (Option.some.inj ht).symm⟩
    · rintro ⟨-, -, rfl⟩
      rfl
  · rw [if_neg h]
    constructor
    · intro ht
      cases ht
    · rintro ⟨h1, h2, -⟩
      exact absurd ⟨h1, h2⟩ h

@[simp] theorem run_nil (m : ℕ) (s : ℕ × ℕ) : run m s [] = some s := rfl

theorem run_cons (m : ℕ) (s : ℕ × ℕ) (d : ℕ) (ds : List ℕ) :
    run m s (d :: ds) = (step m s d).bind fun t => run m t ds := rfl

theorem run_cons_eq_some {m b ν d : ℕ} {ds : List ℕ} {s : ℕ × ℕ} :
    run m (b, ν) (d :: ds) = some s ↔
      d < 3 ^ m ∧ geq m d ν = true ∧ run m (d, need m b d) ds = some s := by
  rw [run_cons]
  constructor
  · intro h
    cases hst : step m (b, ν) d with
    | none => rw [hst] at h; cases h
    | some t =>
      rw [hst] at h
      obtain ⟨h1, h2, rfl⟩ := step_eq_some.mp hst
      exact ⟨h1, h2, h⟩
  · rintro ⟨h1, h2, h3⟩
    rw [step_eq_some.mpr ⟨h1, h2, rfl⟩]
    exact h3

theorem run_append (m : ℕ) (s : ℕ × ℕ) (u v : List ℕ) :
    run m s (u ++ v) = (run m s u).bind fun t => run m t v := by
  induction u generalizing s with
  | nil => rfl
  | cons d ds ih =>
    rw [List.cons_append, run_cons, run_cons]
    cases step m s d with
    | none => rfl
    | some t => exact ih t

@[simp] theorem wtL_nil (m : ℕ) : wtL m [] = 0 := rfl

@[simp] theorem wtL_cons (m d : ℕ) (ds : List ℕ) : wtL m (d :: ds) = wt m d + wtL m ds := by
  simp [wtL]

@[simp] theorem wtL_append (m : ℕ) (u v : List ℕ) : wtL m (u ++ v) = wtL m u + wtL m v := by
  simp [wtL]

/-! ### Sums over lists -/

theorem sum_map_range' (g : ℕ → ℕ) (s n : ℕ) :
    ((List.range' s n).map g).sum = ∑ j ∈ range n, g (s + j) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [List.range'_succ, List.map_cons, List.sum_cons, ih, Finset.sum_range_succ']
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    omega

theorem sum_map_getD (g : ℕ → ℕ) (l : List ℕ) :
    (l.map g).sum = ∑ j ∈ range l.length, g (l.getD j 0) := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ', ih]
    simp [add_comm]

/-! ### From a dominating function to an accepted list -/

section FromGrid

variable {m n : ℕ}

theorem zext_eq_zero_of_row (f : Fin m × Fin n → ℕ) {i : ℕ} (hi : i = 0 ∨ m < i) (j : ℕ) :
    zext f i j = 0 := by
  unfold zext
  rw [dif_neg (by omega)]

theorem zext_eq_zero_of_col (f : Fin m × Fin n → ℕ) (i : ℕ) {j : ℕ} (hj : j = 0 ∨ n < j) :
    zext f i j = 0 := by
  unfold zext
  rw [dif_neg (by omega)]

/-- Column `j` of the weights `f` (columns numbered from 1), with weights cut to at most 2,
as a base-3 number. -/
def col (f : Fin m × Fin n → ℕ) (j : ℕ) : ℕ := encode m fun i => min 2 (zext f (i + 1) j)

theorem dg_col (f : Fin m × Fin n → ℕ) (j : ℕ) {i : ℕ} (hi : i < m) :
    dg (col f j) i = min 2 (zext f (i + 1) j) :=
  dg_encode m _ (fun _ => min_le_left _ _) hi

theorem col_lt (f : Fin m × Fin n → ℕ) (j : ℕ) : col f j < 3 ^ m :=
  encode_lt m _ (fun _ => min_le_left _ _)

theorem col_zero (f : Fin m × Fin n → ℕ) : col f 0 = 0 :=
  encode_eq_zero m _ (fun i _ => by rw [zext_eq_zero_of_col f _ (Or.inl rfl)]; rfl)

theorem run_of_dom (f : Fin m × Fin n → ℕ) (hf : IsDomFn (grid m n) 2 f) :
    ∀ k j ν, 1 ≤ j → j + k = n + 1 → (∀ i, i < m → dg ν i ≤ dg (col f j) i) →
      ∃ s, run m (col f (j - 1), ν) ((List.range' j k).map (col f)) = some s ∧
        geq m 0 s.2 = true := by
  intro k
  induction k with
  | zero =>
    intro j ν _ hjk hν
    refine ⟨(col f (j - 1), ν), rfl, ?_⟩
    rw [geq_iff]
    intro i hi
    have := hν i hi
    rw [dg_col f j hi, zext_eq_zero_of_col f _ (Or.inr (by omega))] at this
    simpa using this
  | succ k ih =>
    intro j ν hj hjk hν
    have hneed : ∀ i, i < m →
        dg (need m (col f (j - 1)) (col f j)) i ≤ dg (col f (j + 1)) i := by
      intro i hi
      have hdom := hf (⟨i, hi⟩, ⟨j - 1, by omega⟩)
      rw [nbhd_sum_grid] at hdom
      have e1 : j - 1 + 1 = j := by omega
      have e2 : j - 1 + 2 = j + 1 := by omega
      simp only [e1, e2] at hdom
      have hup : (if i = 0 then 0 else dg (col f j) (i - 1)) = min 2 (zext f i j) := by
        by_cases h0 : i = 0
        · rw [if_pos h0, zext_eq_zero_of_row f (Or.inl h0)]
          rfl
        · rw [if_neg h0, dg_col f j (by omega)]
          have : i - 1 + 1 = i := by omega
          rw [this]
      have hdown : (if i + 1 < m then dg (col f j) (i + 1) else 0) = min 2 (zext f (i + 2) j) := by
        by_cases h1 : i + 1 < m
        · rw [if_pos h1, dg_col f j h1]
        · rw [if_neg h1, zext_eq_zero_of_row f (Or.inr (by omega))]
          rfl
      rw [dg_need _ _ _ hi, dg_col f (j + 1) hi]
      unfold needAt tau
      rw [dg_col f (j - 1) hi, dg_col f j hi, hup, hdown]
      omega
    obtain ⟨s, hs, hfin⟩ := ih (j + 1) (need m (col f (j - 1)) (col f j)) (by omega) (by omega)
      hneed
    refine ⟨s, ?_, hfin⟩
    rw [List.range'_succ, List.map_cons]
    apply run_cons_eq_some.mpr
    refine ⟨col_lt f j, geq_iff.mpr hν, ?_⟩
    have e : j + 1 - 1 = j := by omega
    rw [e] at hs
    exact hs

/-- A `{2}`-dominating function of the `m × n` grid gives an accepted list of `n` columns that
weighs no more. -/
theorem exists_run_of_dom (f : Fin m × Fin n → ℕ) (hf : IsDomFn (grid m n) 2 f) :
    ∃ l : List ℕ, l.length = n ∧ (∃ s, run m (0, 0) l = some s ∧ geq m 0 s.2 = true) ∧
      wtL m l ≤ ∑ v, f v := by
  refine ⟨(List.range' 1 n).map (col f), by simp, ?_, ?_⟩
  · have := run_of_dom f hf n 1 0 le_rfl (by omega) (fun i _ => by simp)
    rw [show (1 : ℕ) - 1 = 0 from rfl, col_zero] at this
    exact this
  · unfold wtL
    rw [List.map_map, sum_map_range']
    calc ∑ j ∈ range n, (wt m ∘ col f) (1 + j)
        ≤ ∑ j ∈ range n, ∑ i ∈ range m, zext f (i + 1) (j + 1) := by
          apply Finset.sum_le_sum
          intro j _
          have e : 1 + j = j + 1 := by omega
          rw [Function.comp_apply, wt_eq_sum, e]
          apply Finset.sum_le_sum
          intro i hi
          rw [dg_col f _ (Finset.mem_range.mp hi)]
          exact min_le_right _ _
      _ = ∑ v, f v := by
          rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_range]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_range]
          apply Finset.sum_congr rfl
          intro i _
          exact zext_apply f i j

end FromGrid

/-! ### From an accepted list to a dominating function -/

theorem dom_cond_of_run {m : ℕ} : ∀ (l : List ℕ) (b ν : ℕ) (s : ℕ × ℕ),
    run m (b, ν) l = some s → geq m 0 s.2 = true →
    (∀ i, i < m → dg ν i ≤ dg (l.getD 0 0) i) ∧
    ∀ p, p < l.length → ∀ i, i < m →
      2 ≤ dg (if p = 0 then b else l.getD (p - 1) 0) i + tau m (l.getD p 0) i
        + dg (l.getD (p + 1) 0) i := by
  intro l
  induction l with
  | nil =>
    intro b ν s hrun hfin
    rw [run_nil] at hrun
    obtain rfl := Option.some.inj hrun
    refine ⟨?_, ?_⟩
    · intro i hi
      simpa using geq_iff.mp hfin i hi
    · intro p hp
      simp at hp
  | cons d ds ih =>
    intro b ν s hrun hfin
    obtain ⟨-, hg, hrun'⟩ := run_cons_eq_some.mp hrun
    obtain ⟨ih1, ih2⟩ := ih d (need m b d) s hrun' hfin
    refine ⟨?_, ?_⟩
    · intro i hi
      simpa using geq_iff.mp hg i hi
    · intro p hp i hi
      rcases p with _ | q
      · have h1 := ih1 i hi
        rw [dg_need _ _ _ hi] at h1
        unfold needAt at h1
        simp only [List.getD_cons_zero, List.getD_cons_succ, if_true]
        omega
      · have hq : q < ds.length := by simpa using hp
        have h2 := ih2 q hq i hi
        rcases q with _ | r
        · simpa using h2
        · simpa using h2

/-- An accepted list of `n` columns gives a `{2}`-dominating function of the `m × n` grid with
values in `{0,1,2}` and the same weight. -/
theorem exists_dom_of_run {m : ℕ} (l : List ℕ) (n : ℕ) (hn : l.length = n)
    (h : ∃ s, run m (0, 0) l = some s ∧ geq m 0 s.2 = true) :
    ∃ f : Fin m × Fin n → ℕ, IsDomFn (grid m n) 2 f ∧ (∀ v, f v ≤ 2) ∧ ∑ v, f v = wtL m l := by
  subst hn
  obtain ⟨s, hrun, hfin⟩ := h
  obtain ⟨-, hcond⟩ := dom_cond_of_run l 0 0 s hrun hfin
  let f : Fin m × Fin l.length → ℕ := fun v => dg (l.getD v.2.val 0) v.1.val
  have hz : ∀ a b, zext f a b =
      if (1 ≤ a ∧ a ≤ m) ∧ (1 ≤ b ∧ b ≤ l.length) then dg (l.getD (b - 1) 0) (a - 1) else 0 := by
    intro a b
    unfold zext
    by_cases hab : (1 ≤ a ∧ a ≤ m) ∧ (1 ≤ b ∧ b ≤ l.length)
    · rw [dif_pos hab, if_pos hab]
    · rw [dif_neg hab, if_neg hab]
  refine ⟨f, ?_, ?_, ?_⟩
  · rintro ⟨i, j⟩
    have hi := i.isLt
    have hj := j.isLt
    rw [nbhd_sum_grid]
    have hc := hcond j.val hj i.val hi
    unfold tau at hc
    have hout : j.val + 1 < l.length ∨ l.getD (j.val + 1) 0 = 0 := by
      by_cases hh : j.val + 1 < l.length
      · exact Or.inl hh
      · exact Or.inr (List.getD_eq_default _ _ (by omega))
    have t1 : zext f (i.val + 1) (j.val + 1) = dg (l.getD j.val 0) i.val := by
      rw [hz, if_pos (by omega)]
      rfl
    have t2 : zext f i.val (j.val + 1) = if i.val = 0 then 0 else dg (l.getD j.val 0) (i.val - 1) := by
      rw [hz]
      by_cases h0 : i.val = 0
      · rw [if_neg (by omega), if_pos h0]
      · rw [if_pos (by omega), if_neg h0]
        rfl
    have t3 : zext f (i.val + 2) (j.val + 1)
        = if i.val + 1 < m then dg (l.getD j.val 0) (i.val + 1) else 0 := by
      rw [hz]
      by_cases h1 : i.val + 1 < m
      · rw [if_pos (by omega), if_pos h1]
        rfl
      · rw [if_neg (by omega), if_neg h1]
    have t4 : zext f (i.val + 1) j.val
        = dg (if j.val = 0 then 0 else l.getD (j.val - 1) 0) i.val := by
      rw [hz]
      by_cases h0 : j.val = 0
      · rw [if_neg (by omega), if_pos h0, dg_zero]
      · rw [if_pos (by omega), if_neg h0]
        rfl
    have t5 : zext f (i.val + 1) (j.val + 2) = dg (l.getD (j.val + 1) 0) i.val := by
      rw [hz]
      rcases hout with h1 | h1
      · rw [if_pos (by omega)]
        rfl
      · rw [h1, dg_zero]
        by_cases h2 : j.val + 2 ≤ l.length
        · rw [if_pos (by omega)]
          have : j.val + 2 - 1 = j.val + 1 := by omega
          rw [this, h1, dg_zero]
        · rw [if_neg (by omega)]
    rw [t1, t2, t3, t4, t5]
    omega
  · intro v
    have := dg_lt (l.getD v.2.val 0) v.1.val
    show dg (l.getD v.2.val 0) v.1.val ≤ 2
    omega
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    unfold wtL
    rw [sum_map_getD, Finset.sum_range]
    apply Finset.sum_congr rfl
    intro j _
    rw [wt_eq_sum, Finset.sum_range]

end GridDomination
