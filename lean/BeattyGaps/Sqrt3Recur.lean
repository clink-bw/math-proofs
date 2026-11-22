import BeattyGaps.Sqrt3Block

/-!
# Each gap of OEIS A352676 occurs infinitely often

The gaps of the intersection of the Beatty sequences of `√3` and `1 + √3` are `2, 3, 5, 6`
(`BeattyGaps.Sqrt3.isGap_iff`). This file proves that each of them occurs beyond any bound
(`each_gap_infinitely_often`), which completes the corrected form of conjecture (1) of the entry.

The proof is a recurrence argument. Let `per j = q_{4j} + q_{4j+2}`. Shifting by `per j` adds a
constant to `⌊m √3⌋` on a long initial range (`w_per`), and that constant together with `3 · per j`
is divisible by `6` (`per_state`), so membership in the intersection is unchanged by the shift
(`inS_per`). Hence any pattern of consecutive elements seen once is seen again after every
sufficiently large shift (`gapAt_per`).
-/

set_option linter.style.longLine false

namespace BeattyGaps.Sqrt3

theorem length_even {k : ℕ} (h : k % 2 = 0) :
    (stdWord (k + 2)).length = 2 * (stdWord (k + 1)).length + (stdWord k).length := by
  rw [stdWord_even h]; simp only [List.length_append]; omega

theorem length_odd {k : ℕ} (h : k % 2 = 1) :
    (stdWord (k + 2)).length = (stdWord (k + 1)).length + (stdWord k).length := by
  rw [stdWord_odd h]; simp only [List.length_append]

/-- The state advance over the `k`-th standard word is `3 q_k + p_k`. -/
theorem gam_stdWord (k : ℕ) :
    gam (stdWord k) = 3 * qq k + pp k ∧ gam (stdWord (k + 1)) = 3 * qq (k + 1) + pp (k + 1) := by
  induction k with
  | zero => simp [stdWord, gam, qq, pp]
  | succ k ih =>
    obtain ⟨i1, i2⟩ := ih
    refine ⟨i2, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · rw [stdWord_even h, gam_append, gam_append, qq_even h, pp_even h]; omega
    · rw [stdWord_odd h, gam_append, qq_odd h, pp_odd h]; omega

/-- The shift `q_{4j} + q_{4j+2}`. -/
def per (j : ℕ) : ℕ := (stdWord (4 * j)).length + (stdWord (4 * j + 2)).length

theorem w_per (j m : ℕ) (h1 : 1 ≤ m) (h2 : m < (stdWord (4 * j + 1)).length) :
    w (m + per j) = w m + (pp (4 * j) + pp (4 * j + 2)) := by
  have hL2 := length_even (k := 4 * j) (by omega)
  have hL3 : (stdWord (4 * j + 2 + 1)).length =
      (stdWord (4 * j + 2)).length + (stdWord (4 * j + 1)).length :=
    length_odd (k := 4 * j + 1) (by omega)
  have a := w_shift (4 * j) m h1 h2
  have b := w_shift (4 * j + 2) (m + (stdWord (4 * j)).length) (by omega) (by omega)
  unfold per
  rw [← Nat.add_assoc, b, a]
  ring

theorem per_state (j : ℕ) : (pp (4 * j) + pp (4 * j + 2) + 3 * ((per j : ℕ) : ℤ)) % 6 = 0 := by
  have g0 := (((good_all (4 * j)).1).1 (by omega)).2
  have g2 := (((good_all (4 * j + 2)).1).2.2.1 (by omega)).2
  have e0 := (gam_stdWord (4 * j)).1
  have e2 := (gam_stdWord (4 * j + 2)).1
  have l0 := (length_eq_qq (4 * j)).1
  have l2 := (length_eq_qq (4 * j + 2)).1
  unfold per
  push_cast
  omega

/-- Membership in the intersection is unchanged by a shift by `per j`, on a long initial range. -/
theorem inS_per (j m : ℕ) (h1 : 1 ≤ m) (h2 : m + 1 < (stdWord (4 * j + 1)).length) :
    inS (m + per j) ↔ inS m := by
  have a := w_per j m h1 (by omega)
  have b := w_per j (m + 1) (by omega) h2
  have hs := per_state j
  rw [inS_iff (m := m + per j) (by omega), inS_iff (m := m) (by omega),
    show m + per j + 1 = m + 1 + per j by omega, a, b]
  push_cast
  constructor
  · rintro ⟨h, hk⟩; exact ⟨by omega, by omega⟩
  · rintro ⟨h, hk⟩; exact ⟨by omega, by omega⟩

/-- `m` and `m + g` are consecutive elements of the intersection. -/
def GapAt (m g : ℕ) : Prop := inS m ∧ inS (m + g) ∧ ∀ x, m < x → x < m + g → ¬ inS x

theorem gapAt_per {m g : ℕ} (h : GapAt m g) (j : ℕ)
    (hj : m + g + 1 < (stdWord (4 * j + 1)).length) : GapAt (m + per j) g := by
  obtain ⟨h1, h2, h3⟩ := h
  have hm := pos_of_inS h1
  refine ⟨(inS_per j m hm (by omega)).mpr h1, ?_, ?_⟩
  · rw [show m + per j + g = m + g + per j by omega]
    exact (inS_per j (m + g) (by omega) hj).mpr h2
  · intro x hx1 hx2 hx
    obtain ⟨y, rfl⟩ : ∃ y, x = y + per j := ⟨x - per j, by omega⟩
    exact h3 y (by omega) (by omega) ((inS_per j y (by omega) (by omega)).mp hx)

/-- A gap that occurs once occurs beyond any bound. -/
theorem gapAt_infinitely_often {m g : ℕ} (h : GapAt m g) (L : ℕ) : ∃ m', L ≤ m' ∧ GapAt m' g := by
  have hlen := le_stdWord_length (k := 4 * (L + m + g + 2) + 1) (by omega)
  have hlen0 := le_stdWord_length (k := 4 * (L + m + g + 2)) (by omega)
  refine ⟨m + per (L + m + g + 2), ?_, gapAt_per h _ (by omega)⟩
  unfold per
  omega

theorem gapAt_two : GapAt 8 2 :=
  ⟨by simpa [inS] using mem8, by simpa [inS] using mem10, fun x h1 h2 hx => by
    obtain rfl : x = 9 := by omega
    exact nmem9 (by simpa [inS] using hx)⟩

theorem gapAt_three : GapAt 5 3 :=
  ⟨by simpa [inS] using mem5, by simpa [inS] using mem8, fun x h1 h2 hx => by
    obtain rfl | rfl : x = 6 ∨ x = 7 := by omega
    · exact nmem6 (by simpa [inS] using hx)
    · exact nmem7 (by simpa [inS] using hx)⟩

theorem gapAt_five : GapAt 19 5 :=
  ⟨by simpa [inS] using mem19, by simpa [inS] using mem24, fun x h1 h2 hx => by
    obtain rfl | rfl | rfl | rfl : x = 20 ∨ x = 21 ∨ x = 22 ∨ x = 23 := by omega
    · exact nmem20 (by simpa [inS] using hx)
    · exact nmem21 (by simpa [inS] using hx)
    · exact nmem22 (by simpa [inS] using hx)
    · exact nmem23 (by simpa [inS] using hx)⟩

theorem gapAt_six : GapAt 13 6 :=
  ⟨by simpa [inS] using mem13, by simpa [inS] using mem19, fun x h1 h2 hx => by
    obtain rfl | rfl | rfl | rfl | rfl : x = 14 ∨ x = 15 ∨ x = 16 ∨ x = 17 ∨ x = 18 := by omega
    · exact nmem14 (by simpa [inS] using hx)
    · exact nmem15 (by simpa [inS] using hx)
    · exact nmem16 (by simpa [inS] using hx)
    · exact nmem17 (by simpa [inS] using hx)
    · exact nmem18 (by simpa [inS] using hx)⟩

/-- **Each of the gaps `2, 3, 5, 6` of OEIS A352676 occurs infinitely often**: beyond any bound
`L` there are consecutive elements `m`, `m + g` of the intersection. -/
theorem each_gap_infinitely_often {g : ℕ} (hg : g = 2 ∨ g = 3 ∨ g = 5 ∨ g = 6) (L : ℕ) :
    ∃ m, L ≤ m ∧ GapAt m g := by
  rcases hg with rfl | rfl | rfl | rfl
  · exact gapAt_infinitely_often gapAt_two L
  · exact gapAt_infinitely_often gapAt_three L
  · exact gapAt_infinitely_often gapAt_five L
  · exact gapAt_infinitely_often gapAt_six L

end BeattyGaps.Sqrt3
