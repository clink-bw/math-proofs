# The integer {2}-domination number of 3 × n and 4 × n grids

Row for the results table in the root `README.md`:

| Project | Result | How it was checked |
|---|---|---|
| [grid-domination](grid-domination/) | The integer {2}-domination number of the 3 × n grid is ⌊3n/2⌋ + 1 for every n ≥ 1, and of the 4 × n grid is 2n − ⌊(n − 9)/10⌋ for every n ≥ 49 (Conjectures 2.5 and 3.7 of Lee and Liu, arXiv:2502.00134), with the exact 4 × n value for every smaller n too. Independent proofs; not the first (see the project page). | Lean |

## The problem

Take a grid of squares with m rows and n columns. Write a weight 0, 1 or 2 in every square so
that each square, together with the squares directly above, below, left and right of it, has
total weight at least 2. The **integer {2}-domination number** of the grid is the smallest
possible sum of all the weights. (Allowing weights larger than 2 does not change the answer.)

In 2025 Jia-Ying Lee and Chia-An Liu
([arXiv:2502.00134](https://arxiv.org/abs/2502.00134)) worked out the answer for 1 and 2 rows and
conjectured it for 3 and 4 rows:

* **Conjecture 2.5.** For 3 rows the answer is ⌊3n/2⌋ + 1 for every n ≥ 1. They proved that this
  much weight is enough; the open part was that nothing smaller works.
* **Conjecture 3.7.** For 4 rows the answer is 2n − ⌊(n − 9)/10⌋ for every n ≥ 49. They had
  computed the answer for n ≤ 100.

## Results

Both conjectures are true as stated. All of the following are proved in Lean, with no `sorry`,
no `native_decide`, and no axioms beyond Lean's standard three (`propext`, `Classical.choice`,
`Quot.sound`); `#print axioms` was run on each theorem in the table to confirm this.

| Statement | Lean theorem |
|---|---|
| 3 × n grid: the number is ⌊3n/2⌋ + 1 for all n ≥ 1 (Conjecture 2.5) | `GridDomination.domNum_grid_three` |
| 4 × n grid: the number is 2n − ⌊(n − 9)/10⌋ for all n ≥ 49 (Conjecture 3.7) | `GridDomination.domNum_grid_four_of_ge` |
| 4 × n grid, every n ≥ 1: the number is ⌈(19n + 9)/10⌉, except that it is 1 less for n = 4, 7, 8, 15, 18, 26, 37, 48 and 1 more for n = 1 | `GridDomination.domNum_grid_four` |
| The bound 49 cannot be lowered: for n = 48 the number is 92, and the formula gives 93 | `GridDomination.domNum_grid_four_48` |
| 2 × n grid: the number is n + 1 (already proved by Lee and Liu; here as a test of the method) | `GridDomination.domNum_grid_two` |
| In each case the minimum is reached using only the weights 0, 1, 2 | `exists_dom_grid_three`, `exists_dom_grid_four` |

For n ≥ 9 the expressions ⌈(19n + 9)/10⌉ and 2n − ⌊(n − 9)/10⌋ are the same number. The third row
agrees with every entry of Lee and Liu's table for n ≤ 100 (their Theorem 3.6), which
`compute/check_small.py` checks.

### What the Lean statements say

The definitions are in [`lean/GridDomination/Basic.lean`](../lean/GridDomination/Basic.lean) and
are short:

* `grid m n` is Mathlib's Cartesian product of two path graphs,
  `SimpleGraph.pathGraph m □ SimpleGraph.pathGraph n`, on the vertex set `Fin m × Fin n`.
* `IsDomFn G k f` says: `f` gives each vertex a natural number, and for every vertex `v`,
  `k ≤ f v + ∑ u ∈ G.neighborFinset v, f u`.
* `domNum G k` is the least value of `∑ v, f v` over all such `f`.

So `domNum_grid_three` reads: for all `n ≥ 1`, `domNum (grid 3 n) 2 = 3 * n / 2 + 1` (division
of natural numbers rounds down). The theorems are about these definitions directly; the column
encoding described below appears only inside the proofs.

## Is this new?

**No.** The search recorded in [novelty-log.md](novelty-log.md) found no paper that settles
either conjecture, but it did find that both had been settled about five weeks earlier in a public
GitHub repository of AI-produced, machine-checked mathematics
([`the-omega-institute/trureturing`](https://github.com/the-omega-institute/trureturing)):

* a Lean proof of Conjecture 2.5 was merged there on 18 October 2026;
* a proof of Conjecture 3.7 by exact computation was posted there on 16 October 2026, with a Lean
  proof reported as compiled but not yet merged when checked on 21 November 2026.

Neither has been peer reviewed, and neither was read or used here; this project found them
through its own literature search, part-way through. What this project contributes is an
independent proof and an independent Lean formalisation of both conjectures, and the 4 × n value
for every n in Lean. Two independent machine-checked proofs agreeing is some evidence that the
statements were formalised correctly both times.

## How the proof works

**Reading the grid one column at a time.** Suppose the columns are filled in from left to right.
Once a column is written, the squares in the column before it can be checked, because all their
neighbours are now known. To carry on, only two things about the past matter: the last column,
and how much each of its squares still needs from the next column. That pair is a *state*. There
are 95 possible states for 3 rows and 389 for 4 rows (the same counts as in Lee and Liu's
algorithm). A filled grid is a walk through states, and its weight is the sum of the weights of
the columns read. `Bridge.lean` proves that walks that start in the empty state and end in a
state that needs nothing more correspond exactly to valid fillings of the grid.

**Enough weight (upper bound).** Explicit patterns, checked by Lean. For long grids a block of
columns is repeated. For 3 rows the block is two columns of weight 3; for 4 rows it is ten columns
of weight 19, which is where the rate 19/10 per column comes from (`.` is 0):

```
3 rows:  . 1        4 rows:  . . 2 . . 1 . 1 . 1
         . 1                 1 . . . 1 1 . 1 . 1
         . 1                 . 1 . 1 . . . 1 . .
                             . 1 . 1 . 1 1 . 1 1
```

A short start and a short end are added on either side, one choice for each remainder of n
modulo the length of the block. For example, the 4 × 49 grid with weight 94:

```
. 1 . . 2 . . 1 . 1 . 1 . . 2 . . 1 . 1 . 1 . . 2 . . 1 . 1 . 1 . . 2 . . 1 . 1 . 1 . . 2 . . 1 .
1 1 1 . . . 1 1 . 1 . 1 1 . . . 1 1 . 1 . 1 1 . . . 1 1 . 1 . 1 1 . . . 1 1 . 1 . 1 1 . . . 1 1 1
. . . 1 . 1 . . . 1 . . . 1 . 1 . . . 1 . . . 1 . 1 . . . 1 . . . 1 . 1 . . . 1 . . . 1 . 1 . . .
1 1 . 1 . 1 . 1 1 . 1 1 . 1 . 1 . 1 1 . 1 1 . 1 . 1 . 1 1 . 1 1 . 1 . 1 . 1 1 . 1 1 . 1 . 1 . 1 1
```

**Nothing smaller works (lower bound).** This is the part that was open. The proof is a
certificate that Lean checks, in two pieces.

1. *A potential.* Give every state a number F so that, whenever a column of weight w is read and
   the state changes from s to t, F(t) − F(s) ≤ 10w − 19 (for 4 rows; 2w − 3 for 3 rows). Adding
   these inequalities along a whole grid shows that every column costs at least 19/10 on average,
   up to a fixed amount lost at the two ends. Such an F exists and is just a table of 389 numbers;
   Lean checks the inequality on all 15,412 possible steps.
2. *The first 49 columns.* For 3 rows the potential alone gives the exact answer from n = 1. For
   4 rows it does not: short grids can do slightly better than the long-run formula, because a
   different block, 11 columns of weight 21, fits the two ends more snugly. It is more expensive
   per column (21/11 > 19/10), so it loses in the long run, but it wins at n = 15, 26, 37 and 48:

   ```
   4 × 15, weight 29:   . 1 1 . . 1 1 . 1 1 . . 1 1 .
                        1 . . 1 1 . . 1 . . 1 1 . . 1
                        1 . . 1 . . . 2 . . . 1 . . 1
                        . 1 1 . . 2 . . . 2 . . 1 1 .
   ```

   So for 4 rows the certificate also contains, for each j from 0 to 49, a table giving for every
   state the least weight of j columns that lead to it. Lean checks that each table follows from
   the one before (49 rounds over the 15,412 steps). Table n gives the exact answer for n < 49,
   and table 49 is the starting point for the potential.

The script `compute/gen_lean.py` finds all of this data by dynamic programming and writes it into
`Height*Data.lean`. The data files contain only numbers and statements of the form "this check
returns true", proved by evaluation in Lean's kernel. What the checks mean is proved once by hand
in `Certificate.lean`. So a bug in the script can only make the build fail; it cannot produce a
false theorem.

**How far the kernel can be pushed.** The 4-row case is well within reach: the 389-state
certificate checks in two to three minutes of processor time on a laptop, using packed tables (one
big number per table) and Lean's built-in arithmetic on natural numbers. A first attempt that recomputed every
state transition from the definition in each of the 49 rounds took over ten seconds a round and
used a lot of memory; checking a transition table once and then looking transitions up made it
about ten times faster. Five rows (1,595 states) has not been tried.

## How each claim was checked

| Claim | Checked by |
|---|---|
| The theorems in the table above | **Lean** (kernel evaluation with `decide +kernel`; standard axioms only) |
| Both formulas, by a second argument: the whole vector of the dynamic programme repeats (3 rows: v(n+4) = v(n) + 6 from n = 15; 4 rows: v(n+10) = v(n) + 19 from n = 67), which forces the formula for all n | **Exact computation**, `compute/analyze.py`, with its own construction of the automaton |
| The automaton matches the definition: brute force over all weightings for the 28 grids with at most 14 squares; transposed grids agree; agreement with Lee and Liu's theorems and their table for 4 × n, n ≤ 100 | **Exact computation**, `compute/check_small.py` |
| The description of prior work | Literature search; see [novelty-log.md](novelty-log.md) for what was and was not read |

Nothing here rests on a paper-only argument.

## Files

* `../lean/GridDomination/Basic.lean` - the definitions (`IsDomFn`, `domNum`, `grid`).
* `../lean/GridDomination/Automaton.lean` - the column automaton and the check functions.
* `../lean/GridDomination/Bridge.lean` - accepted lists of columns are exactly the valid
  weightings of the grid.
* `../lean/GridDomination/Certificate.lean` - what a passing check proves.
* `../lean/GridDomination/Height2.lean`, `Height3.lean`, `Height4.lean` - the theorems;
  `Height2Data.lean`, `Height3Data.lean`, `Height4Data.lean` - the generated certificates.
* `compute/gen_lean.py` - finds the certificates and writes the data files.
* `compute/strip.py` - the automaton in Python, written to match `Automaton.lean`.
* `compute/analyze.py` - exact values for large n and the repetition argument.
* `compute/check_small.py` - brute-force and consistency checks.
* `novelty-log.md` - the prior-work search.

## Reproducing

The scripts need only Python 3 (no packages).

```bash
python3 grid-domination/compute/check_small.py
```

```bash
python3 grid-domination/compute/analyze.py 4 2000
```

```bash
python3 grid-domination/compute/gen_lean.py
```

```bash
lake build GridDomination
```

`GridDomination` is not yet listed in `defaultTargets` in `lakefile.toml`, so a plain
`lake build` does not build it; add it there when this project is merged.
