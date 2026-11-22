import BeattyGaps.Sqrt3

/-!
# The drift of OEIS A352676

Let `S` be the intersection of the Beatty sequences of `√3` and `1 + √3`, let `cnt M` be the
number of its elements in `[1, M]`, and for `M ∈ S` let

  `drift M = M - ⌊(3/2)(1 + √3) · cnt M⌋`.

If `M` is the `n`-th element of `S` then `cnt M = n`, so `drift M` is the quantity `d(n)` of
conjecture (3) in the OEIS entry.

This file proves, **assuming one classical fact** (`BlockHypothesis`, below), that the drift is
`0` at infinitely many elements and is unbounded above and below:

* `drift_zero_infinitely_often`
* `drift_unbounded_above`, `drift_unbounded_below`

Everything else is proved here, in particular:

* `inS_iff`: the membership rule in terms of `w m = ⌊m √3⌋`;
* `F_eq_Phi`: the walk `F M = 3 cnt M - ⌊(M+1)(√3 - 1)⌋` as a sum along the step word of `√3`;
* `next_elem`: `F` moves by exactly `±1` from one element of `S` to the next;
* `drift_eq_zero_iff`: at an element of `S`, the drift is `0` exactly when `F` is `0`;
* `good_all`: the closed forms for the sums of the walk over the standard words.

`BlockHypothesis` says that the first `q_k` letters of the step word of `√3` form the `k`-th
standard word. It is a case of the classical theorem on characteristic Sturmian words
(Lothaire, *Algebraic Combinatorics on Words*, Section 2.2.2) and is not proved here.
-/

set_option linter.style.longLine false

namespace BeattyGaps.Sqrt3

/-! ## Floors of multiples of `√3` -/

/-- `w m = ⌊m √3⌋`. -/
noncomputable def w (m : ℕ) : ℤ := ⌊(m : ℝ) * √3⌋

theorem w_le (m : ℕ) : (w m : ℝ) ≤ (m : ℝ) * √3 := Int.floor_le _

theorem lt_w_add_one (m : ℕ) : (m : ℝ) * √3 < (w m : ℝ) + 1 := Int.lt_floor_add_one _

theorem w_eq {m : ℕ} {z : ℤ} (h1 : (z : ℝ) ≤ (m : ℝ) * √3) (h2 : (m : ℝ) * √3 < (z : ℝ) + 1) :
    w m = z :=
  Int.floor_eq_iff.mpr ⟨h1, h2⟩

theorem w_one : w 1 = 1 :=
  w_eq (by push_cast; linarith [sq_lo]) (by push_cast; linarith [sq_hi])

theorem w_int (n : ℕ) : ⌊((n : ℤ) : ℝ) * √3⌋ = w n := by simp [w]

theorem w_step (m : ℕ) : w (m + 1) = w m + 1 ∨ w (m + 1) = w m + 2 := by
  have h1 := w_le m
  have h2 := lt_w_add_one m
  have h3 := w_le (m + 1)
  have h4 := lt_w_add_one (m + 1)
  have hlo := sq_lo
  have hhi := sq_hi
  push_cast at h3 h4
  have a : w m < w (m + 1) := by
    have : (w m : ℝ) < (w (m + 1) : ℝ) := by linarith
    exact_mod_cast this
  have b : w (m + 1) < w m + 3 := by
    have : (w (m + 1) : ℝ) < (w m : ℝ) + 3 := by linarith
    exact_mod_cast this
  omega

theorem irrational_sqrt3 : Irrational (√3 : ℝ) := by
  have h := Nat.prime_three.irrational_sqrt
  simpa using h

theorem mul_sqrt3_ne_int {m : ℕ} (hm : 0 < m) (z : ℤ) : (m : ℝ) * √3 ≠ (z : ℝ) := by
  intro h
  apply irrational_sqrt3
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨(z : ℚ) / (m : ℚ), ?_⟩
  push_cast
  rw [div_eq_iff hm']
  linarith

theorem w_lt {m : ℕ} (hm : 0 < m) : (w m : ℝ) < (m : ℝ) * √3 :=
  lt_of_le_of_ne (w_le m) (fun h => mul_sqrt3_ne_int hm (w m) h.symm)

/-! ## Membership in terms of `w` -/

theorem mem_beatty_sqrt3_iff {m : ℕ} (hm : 0 < m) :
    (m : ℤ) ∈ Beatty (√3) ↔ ∃ k : ℤ, w m + 1 ≤ 3 * k ∧ 3 * k ≤ w (m + 1) := by
  have hm0 : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  rw [mem_beatty_iff_of_pos sq_pos hm0, beatty_hit sq_pos sq_sq]
  have h1 := w_lt hm
  have h2 := lt_w_add_one m
  have h4 := lt_w_add_one (m + 1)
  have h5 := w_lt (m := m + 1) (by omega)
  push_cast at h4 h5
  constructor
  · rintro ⟨k, hk1, hk2⟩
    push_cast at hk1 hk2
    refine ⟨k, ?_, ?_⟩
    · have h : (w m : ℝ) < 3 * (k : ℝ) := by linarith
      have h' : w m < 3 * k := by exact_mod_cast h
      omega
    · have h : 3 * (k : ℝ) < (w (m + 1) : ℝ) + 1 := by linarith
      have h' : 3 * k < w (m + 1) + 1 := by exact_mod_cast h
      omega
  · rintro ⟨k, hk1, hk2⟩
    have a : (w m : ℝ) + 1 ≤ 3 * (k : ℝ) := by exact_mod_cast hk1
    have b : 3 * (k : ℝ) ≤ (w (m + 1) : ℝ) := by exact_mod_cast hk2
    refine ⟨k, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith

theorem mem_beatty_one_add_sqrt3_iff {m : ℕ} (hm : 0 < m) :
    (m : ℤ) ∈ Beatty (1 + √3) ↔ w (m + 1) = w m + 2 ∧ (w m - m) % 2 = 1 := by
  have hm0 : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  rw [mem_beatty_iff_of_pos partner_pos hm0, beatty_hit sqm1_pos partner_mul]
  have h1 := w_lt hm
  have h2 := lt_w_add_one m
  have h4 := lt_w_add_one (m + 1)
  have h5 := w_lt (m := m + 1) (by omega)
  have hstep := w_step m
  push_cast at h4 h5
  constructor
  · rintro ⟨l, hl1, hl2⟩
    push_cast at hl1 hl2
    have a : w m < 2 * l + m := by
      have h : (w m : ℝ) < 2 * (l : ℝ) + (m : ℝ) := by linarith
      exact_mod_cast h
    have b : 2 * l + m + 1 < w (m + 1) + 1 := by
      have h : 2 * (l : ℝ) + (m : ℝ) + 1 < (w (m + 1) : ℝ) + 1 := by linarith
      exact_mod_cast h
    omega
  · rintro ⟨hs, hpar⟩
    have hsR : (w (m + 1) : ℝ) = (w m : ℝ) + 2 := by exact_mod_cast hs
    have e : 2 * ((w m + 1 - (m : ℤ)) / 2) = w m + 1 - (m : ℤ) := by omega
    have eR : (2 : ℝ) * (((w m + 1 - (m : ℤ)) / 2 : ℤ) : ℝ) = (w m : ℝ) + 1 - (m : ℝ) := by
      exact_mod_cast e
    refine ⟨(w m + 1 - (m : ℤ)) / 2, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith

/-- `m`, as a natural number, lies in the intersection. -/
def inS (m : ℕ) : Prop := (m : ℤ) ∈ S

theorem not_inS_zero : ¬ inS 0 := fun h => by
  have := pos_of_mem_S h
  simp at this

theorem pos_of_inS {m : ℕ} (h : inS m) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; exact absurd h not_inS_zero
  · exact h0

/-- **Membership rule.** `m ∈ S` exactly when `⌊(m+1)√3⌋ - ⌊m√3⌋ = 2` and `⌊m√3⌋ + 3m` is
`1` or `5` modulo `6`. -/
theorem inS_iff {m : ℕ} (hm : 0 < m) :
    inS m ↔ w (m + 1) = w m + 2 ∧ ((w m + 3 * (m : ℤ)) % 6 = 1 ∨ (w m + 3 * (m : ℤ)) % 6 = 5) := by
  unfold inS S
  rw [Set.mem_inter_iff, mem_beatty_sqrt3_iff hm, mem_beatty_one_add_sqrt3_iff hm]
  constructor
  · rintro ⟨⟨k, hk1, hk2⟩, hs, hpar⟩
    refine ⟨hs, ?_⟩
    omega
  · rintro ⟨hs, hk⟩
    refine ⟨⟨(w m + 2) / 3, ?_, ?_⟩, hs, ?_⟩ <;> omega

/-! ## Counting, and the walk `F` -/

open Classical in
/-- The number of elements of the intersection in `[1, M]`. -/
noncomputable def cnt (M : ℕ) : ℕ := Nat.count inS (M + 1)

theorem cnt_zero : cnt 0 = 0 := by
  unfold cnt
  rw [Nat.count_succ, ite_eq_right not_inS_zero]
  simp

theorem cnt_succ_of_mem {M : ℕ} (h : inS (M + 1)) : cnt (M + 1) = cnt M + 1 := by
  unfold cnt
  rw [Nat.count_succ, ite_eq_left h]

theorem cnt_succ_of_not_mem {M : ℕ} (h : ¬ inS (M + 1)) : cnt (M + 1) = cnt M := by
  unfold cnt
  rw [Nat.count_succ, ite_eq_right h]
  rfl

theorem cnt_eq_of_no_mem {a : ℕ} :
    ∀ d : ℕ, (∀ x, a < x → x ≤ a + d → ¬ inS x) → cnt (a + d) = cnt a := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro h
    have h1 : ¬ inS (a + d + 1) := h (a + d + 1) (by omega) (by omega)
    rw [← Nat.add_assoc, cnt_succ_of_not_mem h1]
    exact ih (fun x hx1 hx2 => h x hx1 (by omega))

theorem cnt_next (m g : ℕ) (hg : 1 ≤ g) (hin : inS (m + g))
    (hno : ∀ x, m < x → x < m + g → ¬ inS x) : cnt (m + g) = cnt m + 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, g = d + 1 := ⟨g - 1, by omega⟩
  have h1 : cnt (m + d) = cnt m := cnt_eq_of_no_mem d (fun x hx1 hx2 => hno x hx1 (by omega))
  have h2 : cnt (m + d + 1) = cnt (m + d) + 1 :=
    cnt_succ_of_mem (by rw [Nat.add_assoc]; exact hin)
  rw [← Nat.add_assoc, h2, h1]

/-- The walk: `F M = 3 cnt M - ⌊(M+1)(√3 - 1)⌋`, written with `⌊(M+1)(√3-1)⌋ = w (M+1) - (M+1)`. -/
noncomputable def F (M : ℕ) : ℤ := 3 * (cnt M : ℤ) - (w (M + 1) - ((M : ℤ) + 1))

/-- The value added to the walk at a letter `1` when the state is `κ`. -/
def fval (κ : ℤ) : ℤ := if κ % 6 = 1 ∨ κ % 6 = 5 then 2 else -1

/-- The `m`-th letter of the step word of `√3`: whether `⌊(m+1)√3⌋ - ⌊m√3⌋ = 2`. -/
noncomputable def cBit (m : ℕ) : Bool := decide (w (m + 1) = w m + 2)

theorem cBit_toNat (m : ℕ) : ((cBit m).toNat : ℤ) = w (m + 1) - w m - 1 := by
  unfold cBit
  rcases w_step m with h | h
  · have hne : ¬ (w (m + 1) = w m + 2) := by omega
    simp [hne, h]
  · simp [h]

theorem F_succ (M : ℕ) :
    F (M + 1) = F M + ((cBit (M + 1)).toNat : ℤ) * fval (w (M + 1) + 3 * ((M : ℤ) + 1)) := by
  have hC := inS_iff (m := M + 1) (by omega)
  have hb := cBit_toNat (M + 1)
  push_cast at hC
  rcases w_step (M + 1) with hs | hs
  · have hnot : ¬ inS (M + 1) := fun h => by have := (hC.mp h).1; omega
    unfold F
    rw [cnt_succ_of_not_mem hnot, hb, hs]
    push_cast
    ring
  · by_cases hk : (w (M + 1) + 3 * ((M : ℤ) + 1)) % 6 = 1 ∨ (w (M + 1) + 3 * ((M : ℤ) + 1)) % 6 = 5
    · have hin : inS (M + 1) := hC.mpr ⟨hs, hk⟩
      have hf : fval (w (M + 1) + 3 * ((M : ℤ) + 1)) = 2 := by unfold fval; rw [ite_eq_left hk]
      unfold F
      rw [cnt_succ_of_mem hin, hb, hf, hs]
      push_cast
      ring
    · have hnot : ¬ inS (M + 1) := fun h => hk (hC.mp h).2
      have hf : fval (w (M + 1) + 3 * ((M : ℤ) + 1)) = -1 := by unfold fval; rw [ite_eq_right hk]
      unfold F
      rw [cnt_succ_of_not_mem hnot, hb, hf, hs]
      push_cast
      ring

/-! ## The walk as a sum along a word -/

/-- The first `M` letters of the step word. -/
noncomputable def pref (M : ℕ) : List Bool := (List.range M).map (fun i => cBit (i + 1))

theorem pref_succ (M : ℕ) : pref (M + 1) = pref M ++ [cBit (M + 1)] := by
  simp [pref, List.range_succ]

/-- Sum of the walk over a word, started in state `κ`. A letter advances the state by `4`, plus
`1` if the letter is `1`. -/
def Phi : ℤ → List Bool → ℤ
  | _, [] => 0
  | κ, b :: v => (b.toNat : ℤ) * fval κ + Phi (κ + 4 + (b.toNat : ℤ)) v

/-- Total advance of the state over a word. -/
def gam : List Bool → ℤ
  | [] => 0
  | b :: v => 4 + (b.toNat : ℤ) + gam v

theorem gam_append (u v : List Bool) : gam (u ++ v) = gam u + gam v := by
  induction u with
  | nil => simp [gam]
  | cons b u ih => simp only [List.cons_append, gam, ih]; ring

theorem Phi_congr {κ κ' : ℤ} (h : κ % 6 = κ' % 6) (v : List Bool) : Phi κ v = Phi κ' v := by
  induction v generalizing κ κ' with
  | nil => simp [Phi]
  | cons b v ih =>
    have hf : fval κ = fval κ' := by unfold fval; rw [h]
    simp only [Phi]
    rw [hf, ih (κ := κ + 4 + (b.toNat : ℤ)) (κ' := κ' + 4 + (b.toNat : ℤ)) (by omega)]

theorem Phi_append (κ : ℤ) (u v : List Bool) :
    Phi κ (u ++ v) = Phi κ u + Phi (κ + gam u) v := by
  induction u generalizing κ with
  | nil => simp [Phi, gam]
  | cons b u ih =>
    simp only [List.cons_append, Phi, gam, ih]
    rw [show κ + 4 + (b.toNat : ℤ) + gam u = κ + (4 + (b.toNat : ℤ) + gam u) by ring]
    ring

theorem gam_pref (M : ℕ) : gam (pref M) = w (M + 1) + 3 * (M : ℤ) - 1 := by
  induction M with
  | zero => simp [pref, gam, w_one]
  | succ M ih =>
    rw [pref_succ, gam_append, ih]
    simp only [gam]
    rw [cBit_toNat]
    push_cast
    ring

/-- The walk is the sum along the step word, started in state `4`. -/
theorem F_eq_Phi (M : ℕ) : F M = Phi 4 (pref M) := by
  induction M with
  | zero => simp [F, cnt_zero, w_one, pref, Phi]
  | succ M ih =>
    rw [F_succ, pref_succ, Phi_append, ← ih, gam_pref]
    simp only [Phi]
    rw [show (4 : ℤ) + (w (M + 1) + 3 * (M : ℤ) - 1) = w (M + 1) + 3 * ((M : ℤ) + 1) by ring]
    ring

/-! ## Standard words and the closed forms -/

/-- The standard words of slope `√3 - 1 = [0; 1, 2, 1, 2, …]`:
`s₀ = 0`, `s₁ = 1`, `s_k = s_{k-1} s_{k-1} s_{k-2}` for even `k`, `s_{k-1} s_{k-2}` for odd `k`. -/
def stdWord : ℕ → List Bool
  | 0 => [false]
  | 1 => [true]
  | (k + 2) =>
    if k % 2 = 0 then stdWord (k + 1) ++ stdWord (k + 1) ++ stdWord k
    else stdWord (k + 1) ++ stdWord k

theorem stdWord_even {k : ℕ} (h : k % 2 = 0) :
    stdWord (k + 2) = stdWord (k + 1) ++ stdWord (k + 1) ++ stdWord k := by
  rw [stdWord, ite_eq_left h]

theorem stdWord_odd {k : ℕ} (h : k % 2 = 1) :
    stdWord (k + 2) = stdWord (k + 1) ++ stdWord k := by
  rw [stdWord, ite_eq_right (by omega)]

theorem stdWord_length (k : ℕ) :
    1 ≤ (stdWord k).length ∧ k + 1 ≤ (stdWord (k + 1)).length := by
  induction k with
  | zero => simp [stdWord]
  | succ k ih =>
    refine ⟨by omega, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · rw [stdWord_even h]; simp only [List.length_append]; omega
    · rw [stdWord_odd h]; simp only [List.length_append]; omega

theorem le_stdWord_length {k : ℕ} (hk : 1 ≤ k) : k ≤ (stdWord k).length := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact (stdWord_length k').2

theorem Phi_AB (r : ℤ) (A B : List Bool) (g : ℤ) (hg : gam A % 6 = g) :
    Phi r (A ++ B) = Phi r A + Phi ((r + g) % 6) B := by
  rw [Phi_append, Phi_congr (κ := r + gam A) (κ' := (r + g) % 6) (by omega)]

theorem Phi_AAB (r : ℤ) (A B : List Bool) (g : ℤ) (hg : gam A % 6 = g) :
    Phi r (A ++ A ++ B) = Phi r A + Phi ((r + g) % 6) A + Phi ((r + 2 * g) % 6) B := by
  rw [Phi_append, Phi_append, gam_append,
    Phi_congr (κ := r + gam A) (κ' := (r + g) % 6) (by omega),
    Phi_congr (κ := r + (gam A + gam A)) (κ' := (r + 2 * g) % 6) (by omega)]

/-- A vector indexed by the states `0, …, 5`. -/
def tbl (a0 a1 a2 a3 a4 a5 : ℤ) (r : ℤ) : ℤ :=
  if r = 0 then a0 else if r = 1 then a1 else if r = 2 then a2 else if r = 3 then a3
  else if r = 4 then a4 else a5

/-- The closed forms for `Phi r (stdWord k)` and for the state advance, by `k` modulo `4`. -/
def Good (k : ℕ) : Prop :=
  (k % 4 = 0 → (∀ r : ℤ, 0 ≤ r → r < 6 →
      Phi r (stdWord k) = ((k / 4 : ℕ) : ℤ) * tbl 1 (-2) (-2) (-2) 1 4 r) ∧
    gam (stdWord k) % 6 = 4) ∧
  (k % 4 = 1 → (∀ r : ℤ, 0 ≤ r → r < 6 →
      Phi r (stdWord k) =
        tbl (-1) 2 (-1) (-1) (-1) 2 r + ((k / 4 : ℕ) : ℤ) * tbl (-1) (-1) (-1) (-1) 2 2 r) ∧
    gam (stdWord k) % 6 = 5) ∧
  (k % 4 = 2 → (∀ r : ℤ, 0 ≤ r → r < 6 →
      Phi r (stdWord k) =
        tbl 1 1 1 (-2) (-2) 1 r + ((k / 4 : ℕ) : ℤ) * tbl 2 2 (-1) (-4) (-1) 2 r) ∧
    gam (stdWord k) % 6 = 2) ∧
  (k % 4 = 3 → (∀ r : ℤ, 0 ≤ r → r < 6 →
      Phi r (stdWord k) =
        tbl 0 0 0 0 (-3) 3 r + ((k / 4 : ℕ) : ℤ) * tbl 1 1 1 (-2) (-2) 1 r) ∧
    gam (stdWord k) % 6 = 1)

theorem good_zero : Good 0 := by
  refine ⟨fun _ => ⟨fun r _ _ => ?_, ?_⟩, fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  · simp [stdWord, Phi]
  · simp [stdWord, gam]

theorem good_one : Good 1 := by
  refine ⟨fun h => absurd h (by decide), fun _ => ⟨fun r h0 h6 => ?_, ?_⟩,
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  · interval_cases r <;> simp [stdWord, Phi, fval, tbl]
  · simp [stdWord, gam]

theorem good_step (k : ℕ) (h0 : Good k) (h1 : Good (k + 1)) : Good (k + 2) := by
  have hk : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hk with hk | hk | hk | hk
  · -- k ≡ 0: s_{k+2} = s_{k+1} s_{k+1} s_k with s_{k+1} of type 1, s_k of type 0
    obtain ⟨PB, gB⟩ := h0.1 hk
    obtain ⟨PA, gA⟩ := h1.2.1 (by omega)
    have d1 : (k + 1) / 4 = k / 4 := by omega
    have d2 : (k + 2) / 4 = k / 4 := by omega
    refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega),
      fun _ => ⟨fun r hr0 hr6 => ?_, ?_⟩, fun h => absurd h (by omega)⟩
    · rw [stdWord_even (by omega), Phi_AAB r _ _ 5 gA, PA r hr0 hr6,
        PA ((r + 5) % 6) (by omega) (by omega), PB ((r + 2 * 5) % 6) (by omega) (by omega), d1, d2]
      interval_cases r <;> simp [tbl] <;> ring
    · rw [stdWord_even (by omega), gam_append, gam_append]; omega
  · -- k ≡ 1: s_{k+2} = s_{k+1} s_k with s_{k+1} of type 2, s_k of type 1
    obtain ⟨PB, gB⟩ := h0.2.1 hk
    obtain ⟨PA, gA⟩ := h1.2.2.1 (by omega)
    have d1 : (k + 1) / 4 = k / 4 := by omega
    have d2 : (k + 2) / 4 = k / 4 := by omega
    refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega),
      fun h => absurd h (by omega), fun _ => ⟨fun r hr0 hr6 => ?_, ?_⟩⟩
    · rw [stdWord_odd (by omega), Phi_AB r _ _ 2 gA, PA r hr0 hr6,
        PB ((r + 2) % 6) (by omega) (by omega), d1, d2]
      interval_cases r <;> simp [tbl] <;> ring
    · rw [stdWord_odd (by omega), gam_append]; omega
  · -- k ≡ 2: s_{k+2} = s_{k+1} s_{k+1} s_k with s_{k+1} of type 3, s_k of type 2
    obtain ⟨PB, gB⟩ := h0.2.2.1 hk
    obtain ⟨PA, gA⟩ := h1.2.2.2 (by omega)
    have d1 : (k + 1) / 4 = k / 4 := by omega
    have d2 : (k + 2) / 4 = k / 4 + 1 := by omega
    refine ⟨fun _ => ⟨fun r hr0 hr6 => ?_, ?_⟩, fun h => absurd h (by omega),
      fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · rw [stdWord_even (by omega), Phi_AAB r _ _ 1 gA, PA r hr0 hr6,
        PA ((r + 1) % 6) (by omega) (by omega), PB ((r + 2 * 1) % 6) (by omega) (by omega), d1, d2]
      interval_cases r <;> simp [tbl] <;> ring
    · rw [stdWord_even (by omega), gam_append, gam_append]; omega
  · -- k ≡ 3: s_{k+2} = s_{k+1} s_k with s_{k+1} of type 0, s_k of type 3
    obtain ⟨PB, gB⟩ := h0.2.2.2 hk
    obtain ⟨PA, gA⟩ := h1.1 (by omega)
    have d1 : (k + 1) / 4 = k / 4 + 1 := by omega
    have d2 : (k + 2) / 4 = k / 4 + 1 := by omega
    refine ⟨fun h => absurd h (by omega), fun _ => ⟨fun r hr0 hr6 => ?_, ?_⟩,
      fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · rw [stdWord_odd (by omega), Phi_AB r _ _ 4 gA, PA r hr0 hr6,
        PB ((r + 4) % 6) (by omega) (by omega), d1, d2]
      interval_cases r <;> simp [tbl] <;> ring
    · rw [stdWord_odd (by omega), gam_append]; omega

/-- The closed forms hold for every standard word. -/
theorem good_all (k : ℕ) : Good k ∧ Good (k + 1) := by
  induction k with
  | zero => exact ⟨good_zero, good_one⟩
  | succ k ih => exact ⟨ih.2, good_step k ih.1 ih.2⟩

/-! ## The classical input -/

/-- **The block hypothesis** (not proved here): for every `k ≥ 1`, the first `q_k` letters of the
step word of `√3` form the standard word `s_k`, where `q_k` is the length of `s_k`. -/
def BlockHypothesis : Prop := ∀ k : ℕ, 1 ≤ k → pref (stdWord k).length = stdWord k

theorem F_block (H : BlockHypothesis) {k : ℕ} (hk : 1 ≤ k) :
    F (stdWord k).length = Phi 4 (stdWord k) := by
  rw [F_eq_Phi, H k hk]

theorem F_block_one (H : BlockHypothesis) (j : ℕ) :
    F (stdWord (4 * j + 1)).length = 2 * (j : ℤ) - 1 := by
  rw [F_block H (by omega)]
  obtain ⟨P, -⟩ := (good_all (4 * j + 1)).1.2.1 (by omega)
  rw [P 4 (by norm_num) (by norm_num), show (4 * j + 1) / 4 = j by omega]
  simp [tbl]
  ring

theorem F_block_three (H : BlockHypothesis) (j : ℕ) :
    F (stdWord (4 * j + 3)).length = -2 * (j : ℤ) - 3 := by
  rw [F_block H (by omega)]
  obtain ⟨P, -⟩ := (good_all (4 * j + 3)).1.2.2.2 (by omega)
  rw [P 4 (by norm_num) (by norm_num), show (4 * j + 3) / 4 = j by omega]
  simp [tbl]
  ring

/-! ## The walk moves by one step between consecutive elements -/

theorem F_next (m g : ℕ) (hg : 1 ≤ g) (hin : inS (m + g))
    (hno : ∀ x, m < x → x < m + g → ¬ inS x) :
    F (m + g) = F m + 3 - (w (m + g + 1) - w (m + 1)) + (g : ℤ) := by
  unfold F
  rw [cnt_next m g hg hin hno]
  push_cast
  ring

/-- **The step rule.** From an element `m` of `S` to the next element `m + g`, the walk `F` goes
up by one if `g ∈ {2, 3}` and down by one if `g ∈ {5, 6}`. -/
theorem next_elem {m : ℕ} (hm : inS m) :
    ∃ g : ℕ, 2 ≤ g ∧ g ≤ 6 ∧ inS (m + g) ∧ (∀ x, m < x → x < m + g → ¬ inS x) ∧
      (((g = 2 ∨ g = 3) ∧ F (m + g) = F m + 1) ∨ ((g = 5 ∨ g = 6) ∧ F (m + g) = F m - 1)) := by
  have e1 : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rcases walk_step hm with ⟨n1, h2, hw⟩ | ⟨n1, n2, h3, hw⟩ | ⟨n1, n2, n3, n4, h5, hw⟩ |
    ⟨n1, n2, n3, n4, n5, h6, hw⟩
  · have hin : inS (m + 2) := by unfold inS; push_cast; exact h2
    have hno : ∀ x, m < x → x < m + 2 → ¬ inS x := by
      intro x hx1 hx2 hx
      obtain rfl : x = m + 1 := by omega
      exact n1 (by simpa [inS] using hx)
    have e : (m : ℤ) + 3 = ((m + 2 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e, e1, w_int, w_int] at hw
    refine ⟨2, by norm_num, by norm_num, hin, hno, Or.inl ⟨Or.inl rfl, ?_⟩⟩
    rw [F_next m 2 (by norm_num) hin hno, hw]; push_cast; ring
  · have hin : inS (m + 3) := by unfold inS; push_cast; exact h3
    have hno : ∀ x, m < x → x < m + 3 → ¬ inS x := by
      intro x hx1 hx2 hx
      obtain rfl | rfl : x = m + 1 ∨ x = m + 2 := by omega
      · exact n1 (by simpa [inS] using hx)
      · exact n2 (by simpa [inS] using hx)
    have e : (m : ℤ) + 4 = ((m + 3 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e, e1, w_int, w_int] at hw
    refine ⟨3, by norm_num, by norm_num, hin, hno, Or.inl ⟨Or.inr rfl, ?_⟩⟩
    rw [F_next m 3 (by norm_num) hin hno, hw]; push_cast; ring
  · have hin : inS (m + 5) := by unfold inS; push_cast; exact h5
    have hno : ∀ x, m < x → x < m + 5 → ¬ inS x := by
      intro x hx1 hx2 hx
      obtain rfl | rfl | rfl | rfl : x = m + 1 ∨ x = m + 2 ∨ x = m + 3 ∨ x = m + 4 := by omega
      · exact n1 (by simpa [inS] using hx)
      · exact n2 (by simpa [inS] using hx)
      · exact n3 (by simpa [inS] using hx)
      · exact n4 (by simpa [inS] using hx)
    have e : (m : ℤ) + 6 = ((m + 5 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e, e1, w_int, w_int] at hw
    refine ⟨5, by norm_num, by norm_num, hin, hno, Or.inr ⟨Or.inl rfl, ?_⟩⟩
    rw [F_next m 5 (by norm_num) hin hno, hw]; push_cast; ring
  · have hin : inS (m + 6) := by unfold inS; push_cast; exact h6
    have hno : ∀ x, m < x → x < m + 6 → ¬ inS x := by
      intro x hx1 hx2 hx
      obtain rfl | rfl | rfl | rfl | rfl :
          x = m + 1 ∨ x = m + 2 ∨ x = m + 3 ∨ x = m + 4 ∨ x = m + 5 := by omega
      · exact n1 (by simpa [inS] using hx)
      · exact n2 (by simpa [inS] using hx)
      · exact n3 (by simpa [inS] using hx)
      · exact n4 (by simpa [inS] using hx)
      · exact n5 (by simpa [inS] using hx)
    have e : (m : ℤ) + 7 = ((m + 6 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e, e1, w_int, w_int] at hw
    refine ⟨6, by norm_num, by norm_num, hin, hno, Or.inr ⟨Or.inr rfl, ?_⟩⟩
    rw [F_next m 6 (by norm_num) hin hno, hw]; push_cast; ring

/-! ## The last element below a given bound -/

theorem inS_five : inS 5 := by unfold inS; exact_mod_cast mem5

theorem last_elem (M : ℕ) (hM : 5 ≤ M) :
    ∃ m, inS m ∧ m ≤ M ∧ (∀ x, m < x → x ≤ M → ¬ inS x) := by
  induction M, hM using Nat.le_induction with
  | base => exact ⟨5, inS_five, le_rfl, fun x h1 h2 => by exfalso; omega⟩
  | succ M hM ih =>
    obtain ⟨m, hm, hle, hno⟩ := ih
    by_cases h : inS (M + 1)
    · exact ⟨M + 1, h, le_rfl, fun x h1 h2 => by exfalso; omega⟩
    · refine ⟨m, hm, by omega, fun x h1 h2 => ?_⟩
      rcases Nat.lt_or_ge x (M + 1) with hx | hx
      · exact hno x h1 (by omega)
      · obtain rfl : x = M + 1 := by omega
        exact h

theorem last_elem' (M : ℕ) (hM : 5 ≤ M) :
    ∃ m, inS m ∧ m ≤ M ∧ M < m + 6 ∧ cnt M = cnt m := by
  obtain ⟨m, hm, hle, hno⟩ := last_elem M hM
  obtain ⟨g, hg2, hg6, hin, -, -⟩ := next_elem hm
  refine ⟨m, hm, hle, ?_, ?_⟩
  · by_contra hc
    exact hno (m + g) (by omega) (by omega) hin
  · obtain ⟨d, rfl⟩ : ∃ d, M = m + d := ⟨M - m, by omega⟩
    exact cnt_eq_of_no_mem d (fun x h1 h2 => hno x h1 h2)

theorem w_sub_mono (a d : ℕ) :
    w a - (a : ℤ) ≤ w (a + d) - ((a + d : ℕ) : ℤ) ∧
      w (a + d) - ((a + d : ℕ) : ℤ) ≤ w a - (a : ℤ) + (d : ℤ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have := w_step (a + d)
    rw [← Nat.add_assoc]
    push_cast at ih ⊢
    omega

theorem F_near {m M : ℕ} (hle : m ≤ M) (hlt : M < m + 6) (hc : cnt M = cnt m) :
    F M ≤ F m ∧ F m ≤ F M + 5 := by
  obtain ⟨d, rfl⟩ : ∃ d, M = m + d := ⟨M - m, by omega⟩
  have h := w_sub_mono (m + 1) d
  rw [show m + 1 + d = m + d + 1 by omega] at h
  unfold F
  rw [hc]
  push_cast at h ⊢
  constructor <;> omega

/-! ## From the walk to the drift -/

/-- The drift at `M`: for `M` the `n`-th element of `S` this is `a(n) - ⌊(3/2)(1 + √3) n⌋`. -/
noncomputable def drift (M : ℕ) : ℤ := (M : ℤ) - ⌊(3 / 2 * (1 + √3)) * (cnt M : ℝ)⌋

theorem tau_mul : (3 / 2 * (1 + √3)) * (√3 - 1) = (3 : ℝ) := by
  linear_combination (3 / 2 : ℝ) * sq_sq

theorem floor_succ_bounds {x : ℕ} (hx : inS x) :
    (x : ℝ) * √3 + 1 ≤ (w (x + 1) : ℝ) ∧ (w (x + 1) : ℝ) < ((x : ℝ) + 1) * √3 := by
  have hx0 := pos_of_inS hx
  have hx' : (x : ℤ) ∈ S := hx
  have hmem := (mem_beatty_one_add_sqrt3_iff hx0).mp hx'.2
  have h2 := lt_w_add_one x
  have h5 := w_lt (m := x + 1) (by omega)
  push_cast at h5
  have hs : (w (x + 1) : ℝ) = (w x : ℝ) + 2 := by exact_mod_cast hmem.1
  constructor <;> linarith

/-- At an element of `S`, the sign of the drift is opposite to that of the walk, and the drift
is at least as large in absolute value. -/
theorem drift_of_F {x : ℕ} (hx : inS x) :
    (F x = 0 → drift x = 0) ∧ (1 ≤ F x → drift x ≤ -F x) ∧ (F x ≤ -1 → -F x ≤ drift x) := by
  obtain ⟨hW1, hW2⟩ := floor_succ_bounds hx
  have hξ : (0 : ℝ) < √3 - 1 := sqm1_pos
  have hhi := sq_hi
  have hF : (F x : ℝ) = 3 * (cnt x : ℝ) - ((w (x + 1) : ℝ) - ((x : ℝ) + 1)) := by
    unfold F; push_cast; ring
  have e : (3 / 2 * (1 + √3)) * (cnt x : ℝ) * (√3 - 1) = 3 * (cnt x : ℝ) := by
    linear_combination (cnt x : ℝ) * tau_mul
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · have h0R : (F x : ℝ) = 0 := by exact_mod_cast h0
    have hfl : ⌊(3 / 2 * (1 + √3)) * (cnt x : ℝ)⌋ = (x : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · refine le_of_mul_le_mul_right ?_ hξ
        rw [e]; push_cast; linarith
      · refine lt_of_mul_lt_mul_right ?_ hξ.le
        rw [e]; push_cast; linarith
    unfold drift
    rw [hfl]
    ring
  · have h1R : (1 : ℝ) ≤ (F x : ℝ) := by exact_mod_cast h1
    have hp : (F x : ℝ) * (√3 - 2) ≤ 0 := by nlinarith
    have hfl : (x : ℤ) + F x ≤ ⌊(3 / 2 * (1 + √3)) * (cnt x : ℝ)⌋ := by
      rw [Int.le_floor]
      refine le_of_mul_le_mul_right ?_ hξ
      rw [e]; push_cast; linarith
    unfold drift
    omega
  · have h1R : (F x : ℝ) ≤ -1 := by exact_mod_cast h1
    have hp : 0 ≤ (F x : ℝ) * (√3 - 2) := by nlinarith
    have hfl : ⌊(3 / 2 * (1 + √3)) * (cnt x : ℝ)⌋ < (x : ℤ) + F x + 1 := by
      rw [Int.floor_lt]
      refine lt_of_mul_lt_mul_right ?_ hξ.le
      rw [e]; push_cast; linarith
    unfold drift
    omega

/-- At an element of `S`, the drift vanishes exactly when the walk does. -/
theorem drift_eq_zero_iff {x : ℕ} (hx : inS x) : drift x = 0 ↔ F x = 0 := by
  obtain ⟨h0, hpos, hneg⟩ := drift_of_F hx
  constructor
  · intro hd
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hneg (by omega); omega
    · have := hpos (by omega); omega
  · exact h0

/-! ## A unit-step walk that changes sign passes through zero -/

theorem zero_between : ∀ d m m' : ℕ, inS m → inS m' → m < m' → m' ≤ m + d → F m ≤ -1 → 1 ≤ F m' →
    ∃ x, inS x ∧ m ≤ x ∧ x ≤ m' ∧ F x = 0 := by
  intro d
  induction d with
  | zero => intro m m' _ _ h1 h2 _ _; exfalso; omega
  | succ d ih =>
    intro m m' hm hm' hlt hle hF hF'
    obtain ⟨g, hg2, hg6, hin, hno, hstep⟩ := next_elem hm
    have hge : m + g ≤ m' := by
      by_contra hc
      exact hno m' hlt (by omega) hm'
    have hFg : F (m + g) ≤ 0 := by rcases hstep with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
    rcases eq_or_lt_of_le hFg with h0 | hneg
    · exact ⟨m + g, hin, by omega, hge, h0⟩
    · have hne : m + g ≠ m' := fun h => by rw [h] at hneg; omega
      obtain ⟨x, hx, h1, h2, h3⟩ :=
        ih (m + g) m' hin hm' (by omega) (by omega) (by omega) hF'
      exact ⟨x, hx, by omega, h2, h3⟩

/-! ## The main theorems, under the block hypothesis -/

theorem exists_low (H : BlockHypothesis) (L : ℕ) (K : ℤ) : ∃ m, inS m ∧ L ≤ m ∧ F m ≤ -K := by
  set j : ℕ := L + 6 + K.toNat with hj
  have hlen := le_stdWord_length (k := 4 * j + 3) (by omega)
  obtain ⟨m, hm, hle, hlt, hc⟩ := last_elem' (stdWord (4 * j + 3)).length (by omega)
  have hF := F_block_three H j
  have hnear := (F_near hle hlt hc).2
  exact ⟨m, hm, by omega, by omega⟩

theorem exists_high (H : BlockHypothesis) (L : ℕ) (K : ℤ) : ∃ m, inS m ∧ L ≤ m ∧ K ≤ F m := by
  set j : ℕ := L + 6 + K.toNat with hj
  have hlen := le_stdWord_length (k := 4 * j + 1) (by omega)
  obtain ⟨m, hm, hle, hlt, hc⟩ := last_elem' (stdWord (4 * j + 1)).length (by omega)
  have hF := F_block_one H j
  have hnear := (F_near hle hlt hc).1
  exact ⟨m, hm, by omega, by omega⟩

/-- **Conjecture (3) of A352676, first half** (assuming the block hypothesis): the drift is `0`
at elements of `S` beyond any bound. -/
theorem drift_zero_infinitely_often (H : BlockHypothesis) (L : ℕ) :
    ∃ M, L ≤ M ∧ inS M ∧ drift M = 0 := by
  obtain ⟨m, hm, hLm, hFm⟩ := exists_low H L 1
  obtain ⟨m', hm', hLm', hFm'⟩ := exists_high H (m + 1) 1
  obtain ⟨x, hx, h1, -, h3⟩ :=
    zero_between (m' - m) m m' hm hm' (by omega) (by omega) hFm hFm'
  exact ⟨x, by omega, hx, (drift_of_F hx).1 h3⟩

/-- **Conjecture (3) of A352676, second half** (assuming the block hypothesis): the drift is
unbounded above. -/
theorem drift_unbounded_above (H : BlockHypothesis) (B : ℤ) : ∃ M, inS M ∧ B ≤ drift M := by
  obtain ⟨m, hm, -, hFm⟩ := exists_low H 0 (max B 1)
  have := (drift_of_F hm).2.2 (by omega)
  exact ⟨m, hm, by omega⟩

/-- **Conjecture (3) of A352676, second half** (assuming the block hypothesis): the drift is
unbounded below. -/
theorem drift_unbounded_below (H : BlockHypothesis) (B : ℤ) : ∃ M, inS M ∧ drift M ≤ -B := by
  obtain ⟨m, hm, -, hFm⟩ := exists_high H 0 (max B 1)
  have := (drift_of_F hm).2.1 (by omega)
  exact ⟨m, hm, by omega⟩

/-! ## The statement in terms of the `n`-th element -/

theorem exists_inS_ge (L : ℕ) : ∃ m, inS m ∧ L ≤ m := by
  induction L with
  | zero => exact ⟨5, inS_five, by omega⟩
  | succ L ih =>
    obtain ⟨m, hm, hL⟩ := ih
    obtain ⟨g, hg2, -, hin, -, -⟩ := next_elem hm
    exact ⟨m + g, hin, by omega⟩

theorem infinite_inS : (Set.ofPred inS).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨b, hb⟩
  obtain ⟨m, hm, hL⟩ := exists_inS_ge (b + 1)
  have : m ≤ b := hb hm
  omega

/-- `a n` is the `n`-th element of the intersection (OEIS A352676), for `n ≥ 1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth inS (n - 1)

/-- `d n = a(n) - ⌊(3/2)(1 + √3) n⌋`, the quantity in conjecture (3) of OEIS A352676. -/
noncomputable def d (n : ℕ) : ℤ := (a n : ℤ) - ⌊(3 / 2 * (1 + √3)) * (n : ℝ)⌋

theorem inS_a (n : ℕ) : inS (a n) := Nat.nth_mem_of_infinite infinite_inS _

theorem cnt_pos {M : ℕ} (hM : inS M) : 1 ≤ cnt M := by
  unfold cnt
  rw [Nat.count_succ, ite_eq_left hM]
  omega

open Classical in
theorem cnt_a {n : ℕ} (hn : 1 ≤ n) : cnt (a n) = n := by
  unfold cnt a
  rw [Nat.count_nth_succ (fun hf => absurd hf infinite_inS)]
  omega

open Classical in
theorem a_cnt {M : ℕ} (hM : inS M) : a (cnt M) = M := by
  unfold a cnt
  rw [Nat.count_succ, ite_eq_left hM, Nat.add_sub_cancel, Nat.nth_count hM]

theorem drift_a {n : ℕ} (hn : 1 ≤ n) : drift (a n) = d n := by
  unfold drift d
  rw [cnt_a hn]

/-- **Conjecture (3) of OEIS A352676, first half**, assuming the block hypothesis:
`d(n) = 0` for infinitely many `n`. -/
theorem d_zero_infinitely_often (H : BlockHypothesis) (N : ℕ) : ∃ n, N ≤ n ∧ d n = 0 := by
  obtain ⟨M, hLM, hM, hd⟩ := drift_zero_infinitely_often H (a (N + 1))
  have hpos := cnt_pos hM
  refine ⟨cnt M, ?_, ?_⟩
  · have h1 : a (N + 1) ≤ a (cnt M) := by rw [a_cnt hM]; exact hLM
    unfold a at h1
    have := (Nat.nth_le_nth infinite_inS).mp h1
    omega
  · rw [← drift_a hpos, a_cnt hM]; exact hd

/-- **Conjecture (3) of OEIS A352676, second half**, assuming the block hypothesis:
`d` is unbounded above. -/
theorem d_unbounded_above (H : BlockHypothesis) (B : ℤ) : ∃ n, 1 ≤ n ∧ B ≤ d n := by
  obtain ⟨M, hM, hB⟩ := drift_unbounded_above H B
  have hpos := cnt_pos hM
  exact ⟨cnt M, hpos, by rw [← drift_a hpos, a_cnt hM]; exact hB⟩

/-- **Conjecture (3) of OEIS A352676, second half**, assuming the block hypothesis:
`d` is unbounded below. -/
theorem d_unbounded_below (H : BlockHypothesis) (B : ℤ) : ∃ n, 1 ≤ n ∧ d n ≤ -B := by
  obtain ⟨M, hM, hB⟩ := drift_unbounded_below H B
  have hpos := cnt_pos hM
  exact ⟨cnt M, hpos, by rw [← drift_a hpos, a_cnt hM]; exact hB⟩

/-! ## Sanity check: the block hypothesis holds for the first four standard words

This does not prove `BlockHypothesis`; it guards against a slip in the definitions of `pref`
and `stdWord`, which would make the theorems above vacuous. -/

theorem w_values : w 2 = 3 ∧ w 3 = 5 ∧ w 4 = 6 ∧ w 5 = 8 ∧ w 6 = 10 ∧ w 7 = 12 ∧ w 8 = 13 ∧
    w 9 = 15 ∧ w 10 = 17 ∧ w 11 = 19 ∧ w 12 = 20 := by
  have hlo := sq_lo
  have hhi := sq_hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact w_eq (by push_cast; linarith) (by push_cast; linarith)

theorem block_small {k : ℕ} (h1 : 1 ≤ k) (h4 : k ≤ 4) :
    pref (stdWord k).length = stdWord k := by
  obtain ⟨h2, h3, h4', h5, h6, h7, h8, h9, h10, h11, h12⟩ := w_values
  have s1 : stdWord 1 = [true] := by decide
  have s2 : stdWord 2 = [true, true, false] := by decide
  have s3 : stdWord 3 = [true, true, false, true] := by decide
  have s4 : stdWord 4 =
      [true, true, false, true, true, true, false, true, true, true, false] := by decide
  have r1 : List.range 1 = [0] := by decide
  have r3 : List.range 3 = [0, 1, 2] := by decide
  have r4 : List.range 4 = [0, 1, 2, 3] := by decide
  have r11 : List.range 11 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by decide
  interval_cases k
  · rw [s1]; simp [pref, r1, cBit, w_one, h2]
  · rw [s2]; simp [pref, r3, cBit, w_one, h2, h3, h4']
  · rw [s3]; simp [pref, r4, cBit, w_one, h2, h3, h4', h5]
  · rw [s4]
    simp [pref, r11, cBit, w_one, h2, h3, h4', h5, h6, h7, h8, h9, h10, h11, h12]

end BeattyGaps.Sqrt3
