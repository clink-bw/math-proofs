# The integer {2}-domination number of grids with at most ten rows

Row for the results table in the root `README.md`:

| Project | Result | How it was checked |
|---|---|---|
| [grid-domination](grid-domination/) | The integer {2}-domination number of the m × n grid, for every n, for m = 3, 4, 5: for example ⌊3n/2⌋ + 1 for 3 rows and 2n − ⌊(n − 9)/10⌋ for 4 rows and n ≥ 49 (Conjectures 2.5 and 3.7 of Lee and Liu, arXiv:2502.00134; independent proofs, not the first), and ⌈(23n + 17)/10⌉ for 5 rows and n ≥ 19 (apparently new). | Lean |
| [grid-domination](grid-domination/) | The same number for m = 6 to 10 rows and every n (apparently new); for 9 rows it is exactly 4n + 2. | Exact computation |

A draft paper is at [paper/grid-2-domination.pdf](paper/grid-2-domination.pdf). It has not been
peer reviewed.

## The problem

Take a grid of squares with m rows and n columns. Write a weight 0, 1 or 2 in every square so
that each square, together with the squares directly above, below, left and right of it, has
total weight at least 2. The **integer {2}-domination number** of the grid, written γ(m, n)
here, is the smallest possible sum of all the weights. (Allowing weights larger than 2 does not
change the answer.)

In 2025 Jia-Ying Lee and Chia-An Liu
([arXiv:2502.00134](https://arxiv.org/abs/2502.00134)) worked out the answer for 1 and 2 rows and
conjectured it for 3 and 4 rows:

* **Conjecture 2.5.** γ(3, n) = ⌊3n/2⌋ + 1 for every n ≥ 1. They proved that this much weight is
  enough; the open part was that nothing smaller works.
* **Conjecture 3.7.** γ(4, n) = 2n − ⌊(n − 9)/10⌋ for every n ≥ 49. They had computed the answer
  for n ≤ 100.

## Results

Both conjectures are true, and the same method gives the answer for every number of columns for
5 to 10 rows.

| Rows | γ(m, n) | Exceptions (small n) | Checked by |
|---|---|---|---|
| 2 | n + 1 (Lee and Liu) | none | Lean |
| 3 | ⌊3n/2⌋ + 1 (Conjecture 2.5) | none | Lean |
| 4 | ⌈(19n + 9)/10⌉, which is 2n − ⌊(n − 9)/10⌋ for n ≥ 9 (Conjecture 3.7) | one more for n = 1; one less for n = 4, 7, 8, 15, 18, 26, 37, 48 | Lean |
| 5 | ⌈(23n + 17)/10⌉ (equivalently, with no exceptions: the smaller of that and ⌊(7n + 5)/3⌋) | one less for n = 2, 3, 5, 6, 8, 9, 12, 15, 18 | Lean |
| 6 | ⌈(41n + 18)/15⌉ | one more for n = 16 | exact computation, two programs |
| 7 | 3n + 3 + ⌊n/11⌋, plus 1 when n leaves remainder 8 or 10 on division by 11 | one less for n = 2, 3, 4, 8 | exact computation, two programs |
| 8 | ⌈(46n + 32)/13⌉ | one less for n = 2, 3, 4, 5, 7, 9, 16, 18 | exact computation, two programs |
| 9 | 4n + 2 | none | exact computation, two programs |
| 10 | ⌈(57n + 28)/13⌉, minus 1 when n leaves remainder 1, 5 or 21 on division by 26, plus 1 when it leaves remainder 2 | one more for n = 5, 7, 10, 17, 21, 25, 31, 33, 36, 51; two more for n = 1; one less for n = 2 | exact computation, one program for the lower bound |

Each row holds for **every** n ≥ 1 once the listed exceptions are applied. Rows 3 and 4 are Lee
and Liu's conjectures; rows 5 to 10 appear to be new.

### The Lean theorems

Proved with no `sorry`, no `native_decide`, and no axioms beyond Lean's standard three
(`propext`, `Classical.choice`, `Quot.sound`); `#print axioms` was run on each.

| Statement | Lean theorem |
|---|---|
| γ(2, n) = n + 1 for all n ≥ 1 | `GridDomination.domNum_grid_two` |
| γ(3, n) = ⌊3n/2⌋ + 1 for all n ≥ 1 | `GridDomination.domNum_grid_three` |
| γ(4, n) = 2n − ⌊(n − 9)/10⌋ for all n ≥ 49 | `GridDomination.domNum_grid_four_of_ge` |
| γ(4, n) for every n ≥ 1, as in the table above | `GridDomination.domNum_grid_four` |
| γ(4, 48) = 92, so the bound 49 cannot be lowered | `GridDomination.domNum_grid_four_48` |
| γ(5, n) = ⌈(23n + 17)/10⌉ for all n ≥ 19 | `GridDomination.domNum_grid_five_of_ge` |
| γ(5, n) for every n ≥ 1, as in the table above | `GridDomination.domNum_grid_five` |
| γ(5, 18) = 43, so the bound 19 cannot be lowered | `GridDomination.domNum_grid_five_18` |
| In each case the minimum is reached using only the weights 0, 1, 2 | `exists_dom_grid_three`, `_four`, `_five` |

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

**Three and four rows: no.** The search recorded in [novelty-log.md](novelty-log.md) found no
paper that settles either conjecture, but both had been settled about five weeks earlier in a
public GitHub repository of AI-produced, machine-checked mathematics
([`the-omega-institute/trureturing`](https://github.com/the-omega-institute/trureturing)):

* a Lean proof of Conjecture 2.5 was merged there on 18 October 2026;
* a proof of Conjecture 3.7 by exact computation was posted there on 16 October 2026, with a Lean
  proof reported as compiled but not yet merged when checked on 21 November 2026.

Neither has been peer reviewed, and neither was read or used here. For these two rows this
project is an independent proof and an independent Lean formalisation.

**Five to ten rows: apparently yes, with one caveat.** A second search found no paper, preprint,
OEIS entry or repository that gives these values, and the other repository has nothing beyond
four rows. The caveat: a 1990 paper by E. O. Hare (*k-weight domination and fractional domination
of P_m × P_n*, Congressus Numerantium 78) studies the same quantity for grids under another name.
It is not online and could not be read, so it is possible that some of these values already
appear there. Lee and Liu do not cite it.

## How the proof works

**Reading the grid one column at a time.** Suppose the columns are filled in from left to right.
Once a column is written, the squares in the column before it can be checked, because all their
neighbours are now known. To carry on, only two things about the past matter: the last column,
and how much each of its squares still needs from the next column. That pair is a *state*. There
are 95 possible states for 3 rows, 389 for 4, 1,595 for 5 and 1,846,415 for 10. A filled grid is
a walk through states, and its weight is the sum of the weights of the columns read.
`Bridge.lean` proves that walks that start in the empty state and end in a state that needs
nothing more correspond exactly to valid fillings of the grid.

**Enough weight (upper bound).** Explicit patterns. For long grids a block of columns is
repeated, with a short start and a short end, one choice for each remainder of n modulo the
length of the block. The blocks for 3, 4 and 5 rows (`.` is 0):

```
3 rows, 2 columns, weight 3      4 rows, 10 columns, weight 19
  . 1                              . . 2 . . 1 . 1 . 1
  . 1                              1 . . . 1 1 . 1 . 1
  . 1                              . 1 . 1 . . . 1 . .
                                   . 1 . 1 . 1 1 . 1 1

5 rows, 20 columns, weight 46
  . 1 . 1 . 1 1 . . 1 1 . 1 . 1 1 . . 1 1
  . 1 . 1 . . . 1 1 . . . 2 . . . 1 1 . .
  1 . . . 1 1 . . . 1 1 . . . 1 1 . . . 1
  . . 2 . . . 1 1 . . . 1 . 1 . . . 1 1 .
  1 . 1 . 1 1 . . 1 1 . 1 . 1 . 1 1 . . 1
```

The weight divided by the number of columns is the long-run cost per column: 3/2, 19/10, 23/10,
and then 41/15, 34/11, 46/13, 4 and 57/13 for 6 to 10 rows. The paper shows the blocks for 6,
7 and 8 rows.

**Nothing smaller works (lower bound).** This is the hard part. There are two ways it is done
here.

1. *The whole table repeats.* The computation keeps, for every state, the least weight of n
   columns leading to that state. If the table after N + p columns equals the table after N
   columns with the same number q added to every entry, then the same must be true for ever
   after, because each step only looks at the previous table. So the answer for n + p columns is
   the answer for n columns plus q, for all n ≥ N, and checking finitely many n proves a formula
   for all n. This is what `compute/fast.c` does, for every number of rows up to 10.
2. *A certificate that Lean can check.* Running that computation inside Lean would be slow, so
   for up to 5 rows the proof is recast as a certificate that can be checked one step at a time:
   a number F for every state such that, whenever a column of weight w is read and the state
   changes from s to t, F(t) − F(s) ≤ 10w − 23 (for 5 rows). Adding these up along a grid shows
   that every column costs at least 23/10 on average, up to a fixed amount lost at the two ends.
   Short grids need extra care, because they can be slightly cheaper than the long-run formula:
   for 4 rows a different block, 11 columns of weight 21, fits the ends more snugly and wins for
   n = 15, 26, 37 and 48. So the certificate also has one table for each number of columns up to
   49 (for 4 rows) or 19 (for 5 rows), each checked against the one before.

The script `compute/gen_lean.py` finds the certificates and writes them into
`Height*Data.lean`. Those files contain only numbers and statements of the form "this check
returns true", proved by evaluation in Lean's kernel. What the checks mean is proved once by hand
in `Certificate.lean`. So a bug in the script can only make the build fail; it cannot produce a
false theorem.

**How far the Lean kernel can be pushed.** Five rows (1,595 states, 387,585 table entries) is
feasible: its certificate checks in about ten minutes, as 236 separate kernel computations.
They have to be run one at a time (`set_option Elab.async false`): by default Lean checks the
proofs in a file in parallel, and together they need several gigabytes of memory; one at a time
they need about 700 MB. Six rows would need a table about fifty times larger and was not attempted.

## How each claim was checked

| Claim | Checked by |
|---|---|
| Rows 2 to 5 of the results table, for every n | **Lean** (kernel evaluation with `decide +kernel`; standard axioms only) |
| Rows 6, 7, 8, 9 | **Exact computation**: `compute/fast.c` (the table repeats), and independently `compute/pairs.c`, a different program with no compression of states, which reproduces every value and the repetition |
| Row 10, lower bound | **Exact computation** by `compute/fast.c` only. The independent program needs more memory than this machine has. The values do agree with all the other rows through γ(m, n) = γ(n, m). |
| Upper bounds for rows 1 to 9: an explicit valid pattern of the stated weight for every n. For 10 rows the same check was done for n ≤ 125 only; beyond that the upper bound rests on `fast.c` | **Exact computation** straight from the definition: `compute/check_words.py` checks every square of every pattern and the repeatable blocks; no dynamic programme is involved |
| The automaton matches the definition: brute force over all weightings for the 28 grids with at most 14 squares; γ(m, n) = γ(n, m) for all m, n ≤ 10; agreement with Lee and Liu's theorems and their table for 4 × n, n ≤ 100 | **Exact computation**, `compute/check_small.py` and the outputs of `fast.c` |
| The description of prior work | Literature search; see [novelty-log.md](novelty-log.md) for what was and was not read |

Nothing here rests on a paper-only argument.

## Files

* `../lean/GridDomination/Basic.lean` - the definitions (`IsDomFn`, `domNum`, `grid`).
* `../lean/GridDomination/Automaton.lean` - the column automaton and the check functions.
* `../lean/GridDomination/Bridge.lean` - accepted lists of columns are exactly the valid
  weightings of the grid.
* `../lean/GridDomination/Certificate.lean` - what a passing check proves.
* `../lean/GridDomination/Height2.lean` to `Height5.lean` - the theorems; `Height2Data.lean` to
  `Height5Data.lean` - the certificates. All eight are generated.
* `compute/gen_lean.py` - finds the certificates and writes the generated Lean files.
* `compute/strip.py` - the automaton in Python, written to match `Automaton.lean`.
* `compute/fast.c` - the fast exact computation for up to 10 rows.
* `compute/pairs.c` - the independent second program.
* `compute/check_words.py` - checks the patterns printed by `fast.c` from the definition.
* `compute/results/out_M.txt` - the output of `fast.c` for M rows: the values, the repetition
  found, and one optimal pattern for each n up to 90 or more.
* `compute/analyze.py`, `compute/check_small.py` - a third, slow implementation for up to 4
  rows, brute force and consistency checks.
* `paper/` - the draft paper (LaTeX source and PDF).
* `novelty-log.md` - the prior-work search.

## Reproducing

The scripts need only Python 3 and a C compiler.

```bash
python3 grid-domination/compute/check_small.py
```

```bash
python3 grid-domination/compute/check_words.py grid-domination/compute/results/out_*.txt
```

To recompute instead of using the saved outputs:

```bash
cc -O2 -o fast grid-domination/compute/fast.c -lpthread
```

```bash
./fast 8 400 4 90 > out8.txt
```

```bash
python3 grid-domination/compute/check_words.py out8.txt --pictures
```

```bash
cc -O2 -o pairs grid-domination/compute/pairs.c
```

```bash
./pairs 8 51 34 13 46
```

```bash
python3 grid-domination/compute/gen_lean.py
```

```bash
lake build GridDomination
```

The arguments of `fast` are the number of rows, the largest n to try, the number of threads and
the largest n for which to print a pattern; those of `pairs` are the number of rows, the largest
n, and the N, p, q reported by `fast`. Ten rows takes about two hours of processor time and nine
rows a few minutes; the others take seconds.

`GridDomination` is not yet listed in `defaultTargets` in `lakefile.toml`, so a plain
`lake build` does not build it; add it there when this project is merged.
