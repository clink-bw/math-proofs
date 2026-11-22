import GridDomination.Bridge

/-!
# What the certificate checks prove

`Automaton.lean` defines boolean checks on explicit data.  This file proves what a `true` answer
means for the grid graph:

* `Cert.Valid.lower_grid`: a valid certificate gives `C + R * n ≤ K * (weight of f)` for every
  `{2}`-dominating function `f` of the `m × n` grid with `n ≥ J`;
* `Cert.Valid.lower_grid_small`: for `n ≤ J`, the table for `n` columns gives a lower bound;
* `exists_dom_of_accept`, `exists_dom_of_pump`: accepted lists of columns, and lists with a
  repeated block, give `{2}`-dominating functions of the stated weight.
-/

namespace GridDomination

open Finset

/-! ### Small facts about booleans and loops -/

theorem bimp {a b : Bool} (h : (!a || b) = true) (ha : a = true) : b = true := by
  cases a <;> cases b <;> simp_all

theorem and_true_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem or_true_right {a b : Bool} (h : (a || b) = true) (ha : a = false) : b = true := by
  cases a <;> cases b <;> simp_all

theorem all_range {n : ℕ} {p : ℕ → Bool} (h : (List.range n).all p = true) {k : ℕ} (hk : k < n) :
    p k = true :=
  List.all_eq_true.mp h k (List.mem_range.mpr hk)

theorem beq_succ_zero (t : ℕ) : Nat.beq (t + 1) 0 = false := by
  cases h : Nat.beq (t + 1) 0 with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true h) (Nat.succ_ne_zero t)

theorem wf_zero (m : ℕ) : wf m 0 0 = true := by
  unfold wf
  rw [List.all_eq_true]
  intro i _
  rw [dg_zero]
  rfl

/-! ### Unpacking the checks -/

theorem allRows_spec {f : ℕ → ℕ → Bool} : ∀ (rows : List ℕ) (k0 : ℕ),
    allRows f k0 rows = true → ∀ i, i < rows.length → f (k0 + i) (rows.getD i 0) = true := by
  intro rows
  induction rows with
  | nil =>
    intro k0 _ i hi
    simp at hi
  | cons row rest ih =>
    intro k0 h i hi
    obtain ⟨h1, h2⟩ :=
      and_true_split (show (f k0 row && allRows f (k0 + 1) rest) = true from h)
    rcases i with _ | i
    · simpa using h1
    · have h3 := ih (k0 + 1) h2 i (by simpa using hi)
      have e : k0 + (i + 1) = k0 + 1 + i := by omega
      rw [e]
      simpa using h3

/-- If a check passes on every chunk of the rows, it holds for every row. -/
theorem chunk_spec {f : ℕ → ℕ → Bool} {rows : List ℕ} {len nch : ℕ} (hlen : 0 < len)
    (hN : rows.length ≤ nch * len) (h : ∀ c, c < nch → chunkOK f rows len c = true)
    {k : ℕ} (hk : k < rows.length) : f k (rows.getD k 0) = true := by
  have hc : k / len < nch := by
    apply Nat.div_lt_of_lt_mul
    calc k < rows.length := hk
      _ ≤ nch * len := hN
      _ = len * nch := Nat.mul_comm _ _
  have hdm : k / len * len + k % len = k := Nat.div_add_mod' k len
  have hmod : k % len < len := Nat.mod_lt _ hlen
  have hsub : k % len < ((rows.drop (k / len * len)).take len).length := by
    rw [List.length_take, List.length_drop]
    omega
  have h1 := allRows_spec _ _ (h (k / len) hc) (k % len) hsub
  have e : ((rows.drop (k / len * len)).take len).getD (k % len) 0 = rows.getD k 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt hmod, List.getElem?_drop, hdm]
  rw [hdm, e] at h1
  exact h1

theorem finOK_spec {fins : List ℕ} {T g : ℕ} (h : finOK fins T g = true) {k : ℕ} (hk : k ∈ fins) :
    g ≤ fld T k :=
  Nat.le_of_ble_eq_true (List.all_eq_true.mp h k hk)

theorem linkOK_spec {N A F K R J OFF : ℕ} (h : linkOK N A F K R J OFF = true) {k : ℕ}
    (hk : k < N) : fld F k + R * J ≤ K * fld A k + OFF := by
  unfold linkOK at h
  exact Nat.le_of_ble_eq_true (all_range h hk)

/-! ### Lower bounds from a valid certificate -/

namespace Cert.Valid

variable {c : Cert}

theorem size_spec (hc : c.Valid) :
    c.rows.length = c.N ∧ 0 < c.chunk ∧ c.N ≤ c.nch * c.chunk ∧
      0 < c.tchunk ∧ c.N ≤ c.tnch * c.tchunk := by
  obtain ⟨hs1234, hs5⟩ := and_true_split hc.size
  obtain ⟨hs123, hs4⟩ := and_true_split hs1234
  obtain ⟨hs12, hs3⟩ := and_true_split hs123
  obtain ⟨hs1, hs2⟩ := and_true_split hs12
  exact ⟨Nat.eq_of_beq_eq_true hs1, Nat.le_of_ble_eq_true hs2, Nat.le_of_ble_eq_true hs3,
    Nat.le_of_ble_eq_true hs4, Nat.le_of_ble_eq_true hs5⟩

/-- What the checks `st` and `trans` say about a state `(b, ν)`: its position is below `N`, it
is listed as final if it is final, and its row of the transition table is correct. -/
theorem state_spec (hc : c.Valid) {b ν : ℕ} (hb : b < 3 ^ c.m) (hν : ν < 3 ^ c.m)
    (hw : wf c.m b ν = true) :
    idx c.m c.offs b ν < c.N ∧ (geq c.m 0 ν = true → idx c.m c.offs b ν ∈ c.fins) ∧
      ∀ d, d < 3 ^ c.m → geq c.m d ν = true →
        wf c.m d (need c.m b d) = true ∧
          rowEntry (c.rows.getD (idx c.m c.offs b ν) 0) d
            = idx c.m c.offs d (need c.m b d) + 1 := by
  obtain ⟨hlenN, -, -, hchunk, hcover⟩ := hc.size_spec
  have hst := hc.st
  unfold stOK at hst
  obtain ⟨h3, h4⟩ := and_true_split (bimp (all_range (all_range hst hb) hν) hw)
  have hN : idx c.m c.offs b ν < c.N := Nat.le_of_ble_eq_true h3
  have hST : fld32 c.ST (idx c.m c.offs b ν) = b + 3 ^ c.m * ν := Nat.eq_of_beq_eq_true h4
  have hrow := chunk_spec hchunk (by rw [hlenN]; exact hcover) hc.trans
    (k := idx c.m c.offs b ν) (by rw [hlenN]; exact hN)
  unfold transRow rowOK at hrow
  have hbmod : (b + 3 ^ c.m * ν) % 3 ^ c.m = b := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have hbdiv : (b + 3 ^ c.m * ν) / 3 ^ c.m = ν := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hb, Nat.zero_add]
  rw [hST, hbmod, hbdiv] at hrow
  obtain ⟨h5, h6⟩ := and_true_split hrow
  refine ⟨hN, fun hg => ?_, fun d hd hg => ?_⟩
  · obtain ⟨k, hk, hk2⟩ := List.any_eq_true.mp (bimp h5 hg)
    rw [Nat.eq_of_beq_eq_true hk2]
    exact hk
  · obtain ⟨h7, h8⟩ := and_true_split (bimp (all_range h6 hd) hg)
    exact ⟨h7, Nat.eq_of_beq_eq_true h8⟩

/-- A checked table inequality holds along every transition of the automaton. -/
theorem relax (hc : c.Valid) {A B K R : ℕ}
    (h : ∀ ch, ch < c.nch → chunkOK (relaxRow c.m A B K R) c.rows c.chunk ch = true)
    {b ν d : ℕ} (hb : b < 3 ^ c.m) (hν : ν < 3 ^ c.m) (hw : wf c.m b ν = true)
    (hd : d < 3 ^ c.m) (hg : geq c.m d ν = true) :
    wf c.m d (need c.m b d) = true ∧
      fld B (idx c.m c.offs d (need c.m b d)) + R ≤ fld A (idx c.m c.offs b ν) + K * wt c.m d := by
  obtain ⟨hlenN, hchunk, hcover, -, -⟩ := hc.size_spec
  obtain ⟨hN, -, htr⟩ := hc.state_spec hb hν hw
  obtain ⟨hw', he⟩ := htr d hd hg
  have hrow := chunk_spec hchunk (by rw [hlenN]; exact hcover) h
    (k := idx c.m c.offs b ν) (by rw [hlenN]; exact hN)
  unfold relaxRow at hrow
  have h2 := all_range hrow hd
  unfold relaxAt at h2
  rw [he, Nat.add_sub_cancel] at h2
  exact ⟨hw', Nat.le_of_ble_eq_true (or_true_right h2 (beq_succ_zero _))⟩

/-- The potential argument: once `F + R * j ≤ K * (weight so far) + OFF` holds at the current
state, it keeps holding, and at a final state it gives the bound. -/
theorem lower_stat (hc : c.Valid) :
    ∀ (l : List ℕ) (b ν j W0 : ℕ) (s : ℕ × ℕ), b < 3 ^ c.m → ν < 3 ^ c.m → wf c.m b ν = true →
      fld c.F (idx c.m c.offs b ν) + c.R * j ≤ c.K * W0 + c.OFF →
      run c.m (b, ν) l = some s → geq c.m 0 s.2 = true →
      c.C + c.R * (j + l.length) ≤ c.K * (W0 + wtL c.m l) := by
  intro l
  induction l with
  | nil =>
    intro b ν j W0 s hb hν hw hF hrun hfin
    rw [run_nil] at hrun
    obtain rfl := Option.some.inj hrun
    obtain ⟨-, hmem, -⟩ := hc.state_spec hb hν hw
    have := finOK_spec hc.fin (hmem hfin)
    simp only [List.length_nil, wtL_nil, Nat.add_zero]
    omega
  | cons d ds ih =>
    intro b ν j W0 s hb hν hw hF hrun hfin
    obtain ⟨hd, hg, hrun'⟩ := run_cons_eq_some.mp hrun
    obtain ⟨hw', hrel⟩ := hc.relax hc.stat hb hν hw hd hg
    have key : fld c.F (idx c.m c.offs d (need c.m b d)) + c.R * (j + 1)
        ≤ c.K * (W0 + wt c.m d) + c.OFF := by
      rw [mul_add c.R, mul_add c.K, mul_one]
      omega
    have := ih d (need c.m b d) (j + 1) (W0 + wt c.m d) s hd (need_lt _ _ _) hw' key hrun' hfin
    have e1 : j + (d :: ds).length = j + 1 + ds.length := by
      rw [List.length_cons]
      omega
    have e2 : W0 + wtL c.m (d :: ds) = W0 + wt c.m d + wtL c.m ds := by
      rw [wtL_cons]
      omega
    rw [e1, e2]
    exact this

/-- At column `J` the table of lower bounds is handed over to the potential. -/
theorem handoff (hc : c.Valid) (l : List ℕ) (b ν W0 : ℕ) (s : ℕ × ℕ) (hb : b < 3 ^ c.m)
    (hν : ν < 3 ^ c.m) (hw : wf c.m b ν = true)
    (hT : fld (c.tab c.J) (idx c.m c.offs b ν) ≤ W0)
    (hrun : run c.m (b, ν) l = some s) (hfin : geq c.m 0 s.2 = true) :
    c.C + c.R * (c.J + l.length) ≤ c.K * (W0 + wtL c.m l) := by
  obtain ⟨hN, -, -⟩ := hc.state_spec hb hν hw
  have hl := linkOK_spec hc.link hN
  have hmul : c.K * fld (c.tab c.J) (idx c.m c.offs b ν) ≤ c.K * W0 := Nat.mul_le_mul_left _ hT
  exact hc.lower_stat l b ν c.J W0 s hb hν hw (by omega) hrun hfin

theorem lower_aux (hc : c.Valid) :
    ∀ (l : List ℕ) (b ν j W0 : ℕ) (s : ℕ × ℕ), b < 3 ^ c.m → ν < 3 ^ c.m → wf c.m b ν = true →
      fld (c.tab j) (idx c.m c.offs b ν) ≤ W0 → j ≤ c.J → c.J ≤ j + l.length →
      run c.m (b, ν) l = some s → geq c.m 0 s.2 = true →
      c.C + c.R * (j + l.length) ≤ c.K * (W0 + wtL c.m l) := by
  intro l
  induction l with
  | nil =>
    intro b ν j W0 s hb hν hw hT hj hJ hrun hfin
    have hjJ : j = c.J := by
      rw [List.length_nil] at hJ
      omega
    subst hjJ
    exact hc.handoff [] b ν W0 s hb hν hw hT hrun hfin
  | cons d ds ih =>
    intro b ν j W0 s hb hν hw hT hj hJ hrun hfin
    rcases Nat.lt_or_ge j c.J with hlt | hge
    · obtain ⟨hd, hg, hrun'⟩ := run_cons_eq_some.mp hrun
      obtain ⟨hw', hrel⟩ := hc.relax (hc.steps j hlt) hb hν hw hd hg
      rw [List.length_cons] at hJ
      have := ih d (need c.m b d) (j + 1) (W0 + wt c.m d) s hd (need_lt _ _ _) hw'
        (by omega) (by omega) (by omega) hrun' hfin
      have e1 : j + (d :: ds).length = j + 1 + ds.length := by
        rw [List.length_cons]
        omega
      have e2 : W0 + wtL c.m (d :: ds) = W0 + wt c.m d + wtL c.m ds := by
        rw [wtL_cons]
        omega
      rw [e1, e2]
      exact this
    · have hjJ : j = c.J := Nat.le_antisymm hj hge
      subst hjJ
      exact hc.handoff (d :: ds) b ν W0 s hb hν hw hT hrun hfin

theorem small_aux (hc : c.Valid) :
    ∀ (l : List ℕ) (b ν j W0 : ℕ) (s : ℕ × ℕ) (g : ℕ), b < 3 ^ c.m → ν < 3 ^ c.m →
      wf c.m b ν = true → fld (c.tab j) (idx c.m c.offs b ν) ≤ W0 → j + l.length ≤ c.J →
      finOK c.fins (c.tab (j + l.length)) g = true →
      run c.m (b, ν) l = some s → geq c.m 0 s.2 = true → g ≤ W0 + wtL c.m l := by
  intro l
  induction l with
  | nil =>
    intro b ν j W0 s g hb hν hw hT _ hg hrun hfin
    rw [run_nil] at hrun
    obtain rfl := Option.some.inj hrun
    obtain ⟨-, hmem, -⟩ := hc.state_spec hb hν hw
    rw [List.length_nil, Nat.add_zero] at hg
    have := finOK_spec hg (hmem hfin)
    rw [wtL_nil]
    omega
  | cons d ds ih =>
    intro b ν j W0 s g hb hν hw hT hJ hg hrun hfin
    obtain ⟨hd, hgeq, hrun'⟩ := run_cons_eq_some.mp hrun
    have e1 : j + (d :: ds).length = j + 1 + ds.length := by
      rw [List.length_cons]
      omega
    rw [e1] at hJ hg
    obtain ⟨hw', hrel⟩ := hc.relax (hc.steps j (by omega)) hb hν hw hd hgeq
    have := ih d (need c.m b d) (j + 1) (W0 + wt c.m d) s g hd (need_lt _ _ _) hw'
      (by omega) hJ hg hrun' hfin
    rw [wtL_cons]
    omega

theorem start_le (hc : c.Valid) : fld (c.tab 0) (idx c.m c.offs 0 0) ≤ 0 :=
  le_of_eq (Nat.eq_of_beq_eq_true hc.start)

/-- Every accepted list of at least `J` columns satisfies `C + R * length ≤ K * weight`. -/
theorem lower_run (hc : c.Valid) {l : List ℕ} {s : ℕ × ℕ} (hrun : run c.m (0, 0) l = some s)
    (hfin : geq c.m 0 s.2 = true) (hl : c.J ≤ l.length) :
    c.C + c.R * l.length ≤ c.K * wtL c.m l := by
  have h := hc.lower_aux l 0 0 0 0 s (by positivity) (by positivity) (wf_zero _) hc.start_le
    (Nat.zero_le _) (by omega) hrun hfin
  rw [Nat.zero_add, Nat.zero_add] at h
  exact h

/-- Every accepted list of `n ≤ J` columns weighs at least `g`, if the table for `n` columns has
all final entries at least `g`. -/
theorem lower_run_small (hc : c.Valid) {l : List ℕ} {s : ℕ × ℕ} {g : ℕ}
    (hrun : run c.m (0, 0) l = some s) (hfin : geq c.m 0 s.2 = true) (hl : l.length ≤ c.J)
    (hg : finOK c.fins (c.tab l.length) g = true) : g ≤ wtL c.m l := by
  have h := hc.small_aux l 0 0 0 0 s g (by positivity) (by positivity) (wf_zero _) hc.start_le
    (by omega) (by rw [Nat.zero_add]; exact hg) hrun hfin
  rw [Nat.zero_add] at h
  exact h

/-- **Lower bound for the grid.**  For `n ≥ J`, every `{2}`-dominating function `f` of the
`m × n` grid has `C + R * n ≤ K * (weight of f)`. -/
theorem lower_grid (hc : c.Valid) {n : ℕ} (hn : c.J ≤ n) (f : Fin c.m × Fin n → ℕ)
    (hf : IsDomFn (grid c.m n) 2 f) : c.C + c.R * n ≤ c.K * ∑ v, f v := by
  obtain ⟨l, hlen, ⟨s, hrun, hfin⟩, hwt⟩ := exists_run_of_dom f hf
  have h := hc.lower_run hrun hfin (by omega)
  rw [hlen] at h
  exact le_trans h (Nat.mul_le_mul_left _ hwt)

/-- **Lower bound for short grids.**  For `n ≤ J`, every `{2}`-dominating function of the
`m × n` grid weighs at least `g`, if the table for `n` columns has all final entries at least
`g`. -/
theorem lower_grid_small (hc : c.Valid) {n g : ℕ} (hn : n ≤ c.J)
    (hg : finOK c.fins (c.tab n) g = true) (f : Fin c.m × Fin n → ℕ)
    (hf : IsDomFn (grid c.m n) 2 f) : g ≤ ∑ v, f v := by
  obtain ⟨l, hlen, ⟨s, hrun, hfin⟩, hwt⟩ := exists_run_of_dom f hf
  subst hlen
  exact le_trans (hc.lower_run_small hrun hfin hn hg) hwt

end Cert.Valid

/-! ### Upper bounds from explicit lists of columns -/

theorem finalOpt_eq_true {m : ℕ} {o : Option (ℕ × ℕ)} (h : finalOpt m o = true) :
    ∃ s, o = some s ∧ geq m 0 s.2 = true := by
  cases o with
  | none => exact absurd h (by simp [finalOpt])
  | some s => exact ⟨s, rfl, h⟩

theorem loopOpt_eq_true {x : ℕ × ℕ} {o : Option (ℕ × ℕ)} (h : loopOpt x o = true) :
    o = some x := by
  cases o with
  | none => exact absurd h (by simp [loopOpt])
  | some y =>
    obtain ⟨h1, h2⟩ := and_true_split (show (Nat.beq y.1 x.1 && Nat.beq y.2 x.2) = true from h)
    rw [Prod.ext (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)]

/-- An accepted list of `n` columns of weight `w` gives a `{2}`-dominating function of the
`m × n` grid with values in `{0,1,2}` and weight `w`. -/
theorem exists_dom_of_accept {m : ℕ} {l : List ℕ} {n w : ℕ} (h : acceptOK m l n w = true) :
    ∃ f : Fin m × Fin n → ℕ, IsDomFn (grid m n) 2 f ∧ (∀ v, f v ≤ 2) ∧ ∑ v, f v = w := by
  unfold acceptOK at h
  obtain ⟨h12, h3⟩ := and_true_split h
  obtain ⟨h1, h2⟩ := and_true_split h12
  obtain ⟨s, hs, hfin⟩ := finalOpt_eq_true h1
  obtain ⟨f, hf, hb, hsum⟩ := exists_dom_of_run l n (Nat.eq_of_beq_eq_true h2) ⟨s, hs, hfin⟩
  exact ⟨f, hf, hb, by rw [hsum, Nat.eq_of_beq_eq_true h3]⟩

/-- `k` copies of the block `C`, one after the other. -/
def rep (C : List ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => C ++ rep C k

theorem run_rep {m : ℕ} {x : ℕ × ℕ} {C : List ℕ} (h : run m x C = some x) (k : ℕ) :
    run m x (rep C k) = some x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rep, run_append, h]
    exact ih

theorem length_rep (C : List ℕ) (k : ℕ) : (rep C k).length = k * C.length := by
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    rw [rep, List.length_append, ih]
    ring

theorem wtL_rep (m : ℕ) (C : List ℕ) (k : ℕ) : wtL m (rep C k) = k * wtL m C := by
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    rw [rep, wtL_append, ih]
    ring

/-- A list of columns with a block that can be repeated gives `{2}`-dominating functions of the
`m × n` grid, with values in `{0,1,2}`, for every `n = L + k * p`; the weight is `W + k * q`. -/
theorem exists_dom_of_pump {m : ℕ} {A C B : List ℕ} {L p W q : ℕ}
    (h : pumpOK m A C B L p W q = true) {n k : ℕ} (hn : n = L + k * p) :
    ∃ f : Fin m × Fin n → ℕ, IsDomFn (grid m n) 2 f ∧ (∀ v, f v ≤ 2) ∧ ∑ v, f v = W + k * q := by
  unfold pumpOK at h
  obtain ⟨h1234, h5⟩ := and_true_split h
  obtain ⟨h123, h4⟩ := and_true_split h1234
  obtain ⟨h12, h3⟩ := and_true_split h123
  obtain ⟨h1, h2⟩ := and_true_split h12
  have hL := Nat.eq_of_beq_eq_true h2
  have hp := Nat.eq_of_beq_eq_true h3
  have hW := Nat.eq_of_beq_eq_true h4
  have hq := Nat.eq_of_beq_eq_true h5
  cases hA : run m (0, 0) A with
  | none =>
    rw [hA] at h1
    exact absurd h1 (by simp [pumpAt])
  | some x =>
    rw [hA] at h1
    obtain ⟨hloop, hfinal⟩ :=
      and_true_split (show (loopOpt x (run m x C) && finalOpt m (run m x B)) = true from h1)
    have hC := loopOpt_eq_true hloop
    obtain ⟨y, hB, hy⟩ := finalOpt_eq_true hfinal
    have hrun : run m (0, 0) (A ++ (rep C k ++ B)) = some y := by
      rw [run_append, hA]
      change run m x (rep C k ++ B) = some y
      rw [run_append, run_rep hC k]
      exact hB
    have hlen : (A ++ (rep C k ++ B)).length = n := by
      rw [List.length_append, List.length_append, length_rep, hp, hn, ← hL]
      omega
    obtain ⟨f, hf, hb, hsum⟩ := exists_dom_of_run _ n hlen ⟨y, hrun, hy⟩
    refine ⟨f, hf, hb, ?_⟩
    rw [hsum, wtL_append, wtL_append, wtL_rep, hq, ← hW]
    omega

end GridDomination
