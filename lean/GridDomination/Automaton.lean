import Mathlib.Data.Nat.Notation

/-!
# The column automaton for `{2}`-domination of a grid of height `m`

A column of the grid is a vector in `{0,1,2}^m`, stored as the base-3 number `c` whose digit `i`
is the weight in row `i`.  Reading the grid one column at a time, the only thing that matters
about the past is the pair `(b, ν)`: the last column `b`, and for each row `i` the amount `ν i`
that the next column must still contribute so that the vertex in row `i` of the last column is
dominated.  `step` is the resulting deterministic automaton and `Accepts` its language.
-/

namespace GridDomination

/-- Digit `i` of `c` in base 3. -/
def dg (c i : ℕ) : ℕ := c / 3 ^ i % 3

/-- What row `i` receives from column `d` itself: its own weight and its vertical neighbours. -/
def tau (m d i : ℕ) : ℕ :=
  dg d i + (if i = 0 then 0 else dg d (i - 1)) + (if i + 1 < m then dg d (i + 1) else 0)

/-- What row `i` of column `d` still needs from the next column, when the previous column is `b`.
(Subtraction of natural numbers stops at zero.) -/
def needAt (m b d i : ℕ) : ℕ := 2 - (dg b i + tau m d i)

/-- The number with base-3 digits `x 0, …, x (m-1)`. -/
def encode : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | m + 1, x => encode m x + x m * 3 ^ m

/-- The need vector of column `d` after column `b`, as a base-3 number. -/
def need (m b d : ℕ) : ℕ := encode m (needAt m b d)

/-- `d` is at least `ν` in every one of the `m` rows. -/
def geq (m d ν : ℕ) : Bool := (List.range m).all fun i => Nat.ble (dg ν i) (dg d i)

/-- Weight of a column: the sum of its `m` digits. -/
def wt : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, d => wt m d + dg d m

/-- One step of the automaton: from state `(b, ν)` read column `d`. -/
def step (m : ℕ) (s : ℕ × ℕ) (d : ℕ) : Option (ℕ × ℕ) :=
  if d < 3 ^ m ∧ geq m d s.2 = true then some (d, need m s.1 d) else none

/-- Run the automaton on a list of columns. -/
def run (m : ℕ) (s : ℕ × ℕ) : List ℕ → Option (ℕ × ℕ)
  | [] => some s
  | d :: ds => (step m s d).bind fun t => run m t ds

/-- Total weight of a list of columns. -/
def wtL (m : ℕ) (l : List ℕ) : ℕ := (l.map (wt m)).sum

/-! ### Packed tables and the certificate checks

Everything below is a function returning `true` or `false`, to be evaluated by Lean's kernel on
explicit data.  `Certificate.lean` proves what a `true` answer implies. -/

/-- Entry `k` of a table packed into one natural number, 8 bits per entry. -/
def fld (T k : ℕ) : ℕ := (T >>> (8 * k)) % 256

/-- Entry `k` of a table packed 16 bits per entry. -/
def fld16 (T k : ℕ) : ℕ := (T >>> (16 * k)) % 65536

/-- `ν` is a possible need vector after column `d`. -/
def wf (m d ν : ℕ) : Bool :=
  (List.range m).all fun i => Nat.beq (dg ν i) 0 || Nat.ble (dg ν i + tau m d i) 2

/-- Position of the state `(d, ν)` in the tables.  (Any function would do here: the checks below
never use that it is injective, and a collision could only make a check fail.) -/
def idx (m offs d ν : ℕ) : ℕ :=
  fld16 offs d + (List.range m).foldr (fun i acc => dg ν i + (3 - min 2 (tau m d i)) * acc) 0

/-- Entry `k` of a table packed 32 bits per entry. -/
def fld32 (T k : ℕ) : ℕ := (T >>> (32 * k)) % 4294967296

/-- Entry `d` of one row of the transition table.  The row of a state lists, for every next
column `d`, one more than the position of the state reached, or `0` if `d` is not allowed. -/
def rowEntry (row d : ℕ) : ℕ := (row >>> (12 * d)) % 4096

/-- Apply the check `f k row` to the rows of a list, where `k` counts up from the given start. -/
def allRows (f : ℕ → ℕ → Bool) : ℕ → List ℕ → Bool
  | _, [] => true
  | k, row :: rest => f k row && allRows f (k + 1) rest

/-- The check `f` on the rows numbered `c * len, …, c * len + len - 1`.  Checking the table in
chunks keeps each kernel computation small. -/
def chunkOK (f : ℕ → ℕ → Bool) (rows : List ℕ) (len c : ℕ) : Bool :=
  allRows f (c * len) ((rows.drop (c * len)).take len)

/-- Check: every state `(b, ν)` is recorded in the list of states `ST` at its position
(`ST` holds the number `b + 3 ^ m * ν` at position `idx b ν`), and positions are below `N`. -/
def stOK (m offs N ST : ℕ) : Bool :=
  (List.range (3 ^ m)).all fun b => (List.range (3 ^ m)).all fun ν =>
    !wf m b ν ||
      (Nat.blt (idx m offs b ν) N && Nat.beq (fld32 ST (idx m offs b ν)) (b + 3 ^ m * ν))

/-- Check that `row` is the row of the transition table for the state `(b, ν)` in position `k`,
and that `k` is listed in `fins` if the state is final. -/
def rowOK (m offs : ℕ) (fins : List ℕ) (k b ν row : ℕ) : Bool :=
  (!geq m 0 ν || fins.any (Nat.beq k)) &&
    (List.range (3 ^ m)).all fun d =>
      !geq m d ν || (wf m d (need m b d) &&
        Nat.beq (rowEntry row d) (idx m offs d (need m b d) + 1))

/-- `rowOK` for the state stored at position `k` of `ST`. -/
def transRow (m offs ST : ℕ) (fins : List ℕ) (k row : ℕ) : Bool :=
  rowOK m offs fins k (fld32 ST k % 3 ^ m) (fld32 ST k / 3 ^ m) row

/-- One comparison of `relaxRow`: `e` is a transition-table entry, `a` the source value, `w` the
weight of the column read. -/
def relaxAt (B a K R e w : ℕ) : Bool :=
  Nat.beq e 0 || Nat.ble (fld B (e - 1) + R) (a + K * w)

/-- Check, for the state in position `k` with transition row `row`: along every transition
`s → t` reading a column `d`, `B t + R ≤ A s + K * (weight of d)`. -/
def relaxRow (m A B K R k row : ℕ) : Bool :=
  (List.range (3 ^ m)).all fun d => relaxAt B (fld A k) K R (rowEntry row d) (wt m d)

/-- Check: every final state has entry at least `g` in the table `T`. -/
def finOK (fins : List ℕ) (T g : ℕ) : Bool := fins.all fun k => Nat.ble g (fld T k)

/-- Check: `F + R * J ≤ K * A + OFF` at every state. -/
def linkOK (N A F K R J OFF : ℕ) : Bool :=
  (List.range N).all fun k => Nat.ble (fld F k + R * J) (K * fld A k + OFF)

/-- The data of a lower-bound certificate for height `m`.

* `offs`, `N`, `ST`, `rows`, `fins` describe the automaton: where each state sits in the tables,
  how many states there are, the list of states, the transition table (one row per state), and
  which states are final.  The table is checked against the automaton in `tnch` chunks of
  `tchunk` rows, and the inequalities along transitions in `nch` chunks of `chunk` rows.
* `tabs[j]`, for `j ≤ J`, is a table of lower bounds for the weight of `j` columns ending in each
  state.
* `F` is a potential showing that from column `J` on, every further column costs at least `R / K`
  on average; `OFF` is a constant added to keep the entries of `F` nonnegative.

The conclusion (`Cert.Valid.lower_grid` in `Certificate.lean`) is `C + R * n ≤ K * weight` for
every `{2}`-dominating function of the `m × n` grid with `n ≥ J`. -/
structure Cert where
  m : ℕ
  offs : ℕ
  N : ℕ
  ST : ℕ
  rows : List ℕ
  tchunk : ℕ
  tnch : ℕ
  chunk : ℕ
  nch : ℕ
  fins : List ℕ
  tabs : List ℕ
  J : ℕ
  F : ℕ
  K : ℕ
  R : ℕ
  C : ℕ
  OFF : ℕ

/-- The table of lower bounds after `j` columns. -/
def Cert.tab (c : Cert) (j : ℕ) : ℕ := c.tabs.getD j 0

/-- The checks that make a certificate valid.  Each field is a computation for Lean's kernel. -/
structure Cert.Valid (c : Cert) : Prop where
  start : Nat.beq (fld (c.tab 0) (idx c.m c.offs 0 0)) 0 = true
  size : (Nat.beq c.rows.length c.N && Nat.blt 0 c.chunk && Nat.ble c.N (c.nch * c.chunk) &&
    Nat.blt 0 c.tchunk && Nat.ble c.N (c.tnch * c.tchunk)) = true
  st : stOK c.m c.offs c.N c.ST = true
  trans : ∀ ch, ch < c.tnch →
    chunkOK (transRow c.m c.offs c.ST c.fins) c.rows c.tchunk ch = true
  steps : ∀ j, j < c.J → ∀ ch, ch < c.nch →
    chunkOK (relaxRow c.m (c.tab j) (c.tab (j + 1)) 1 0) c.rows c.chunk ch = true
  link : linkOK c.N (c.tab c.J) c.F c.K c.R c.J c.OFF = true
  stat : ∀ ch, ch < c.nch → chunkOK (relaxRow c.m c.F c.F c.K c.R) c.rows c.chunk ch = true
  fin : finOK c.fins c.F (c.C + c.OFF) = true

/-! ### Checks for explicit patterns -/

/-- The run ended, in a final state (one whose need vector is zero). -/
def finalOpt (m : ℕ) : Option (ℕ × ℕ) → Bool
  | none => false
  | some s => geq m 0 s.2

/-- The run ended in the state `x`. -/
def loopOpt (x : ℕ × ℕ) : Option (ℕ × ℕ) → Bool
  | none => false
  | some y => Nat.beq y.1 x.1 && Nat.beq y.2 x.2

/-- From the state reached, `C` leads back to the same state and `B` leads to a final state. -/
def pumpAt (m : ℕ) (C B : List ℕ) : Option (ℕ × ℕ) → Bool
  | none => false
  | some x => loopOpt x (run m x C) && finalOpt m (run m x B)

/-- The list of columns `l` is accepted, has length `n` and weight `w`. -/
def acceptOK (m : ℕ) (l : List ℕ) (n w : ℕ) : Bool :=
  finalOpt m (run m (0, 0) l) && Nat.beq l.length n && Nat.beq (wtL m l) w

/-- The block `C` can be repeated: `A` leads from the start to some state `x`, `C` leads from `x`
back to `x`, and `B` leads from `x` to a final state.  Also records lengths and weights:
`A ++ B` has length `L` and weight `W`, and `C` has length `p` and weight `q`. -/
def pumpOK (m : ℕ) (A C B : List ℕ) (L p W q : ℕ) : Bool :=
  pumpAt m C B (run m (0, 0) A) &&
  Nat.beq (A.length + B.length) L && Nat.beq C.length p &&
  Nat.beq (wtL m A + wtL m B) W && Nat.beq (wtL m C) q

end GridDomination
