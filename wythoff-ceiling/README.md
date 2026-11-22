# Numbers occurring twice in, and missing from, the Wythoff ceiling array

Proposed row for the results table in the root README (not added there, to avoid editing a file
another branch is changing):

| Project | Result | How it was checked |
|---|---|---|
| [wythoff-ceiling](wythoff-ceiling/) | Both of Kimberling's 2021 gap conjectures for the Wythoff ceiling array are true: numbers occurring twice (OEIS A341261) are spaced exactly 3, 5, 10 or 13 apart, and missing numbers (OEIS A341262) exactly 2, 3, 5, 10 or 13 apart (the 2 only once, between 1 and 3). No number occurs more than twice. | Lean |

## The array

Let φ = (1 + √5)/2 be the golden ratio and F(1) = F(2) = 1, F(3) = 2, ... the Fibonacci numbers.
Clark Kimberling's *Wythoff ceiling array* ([A341260](https://oeis.org/A341260)) is

    W*(n, k) = F(k+1) · ⌈n φ⌉ + (n − 1) · F(k)        (n, k ≥ 1).

Row n starts ⌈nφ⌉ + n − 1, 2⌈nφ⌉ + n − 1 and continues like the Fibonacci numbers (each entry is
the sum of the two before it):

    2   4   6  10  16  26 ...
    5   9  14  23  37  60 ...
    7  12  19  31  50  81 ...
   10  17  27  44  71 115 ...

Some numbers appear twice (10 is in rows 1 and 4), some not at all (1, 3, 8, 11, ...).

* [A341261](https://oeis.org/A341261) lists the numbers that occur twice: 10, 23, 26, 31, 44, 57, ...
  Conjecture (Kimberling, Feb 2021): consecutive terms differ by 3, 5, 10 or 13 only.
  The entry also states, without proof, that no number occurs more than twice.
* [A341262](https://oeis.org/A341262) lists the positive integers that do not occur: 1, 3, 8, 11,
  21, 24, ... Conjecture: consecutive terms differ by 2, 3, 5, 10 or 13 only.

Both conjectures were still listed as open on 21 November 2026 (A341261 last changed in Feb 2021,
A341262 in Dec 2021, wording only).

## Results

All of the following are proved in Lean (namespace `WythoffCeiling`, files under
[`../lean/WythoffCeiling/`](../lean/WythoffCeiling/)), with no `sorry`.

| Statement | Lean theorem |
|---|---|
| No number occurs at three different places of the array. | `at_most_twice` |
| The differences between consecutive terms of A341261 are exactly 3, 5, 10 and 13. | `isGap_twice_iff` |
| Each of 3, 5, 10, 13 occurs as such a difference beyond any bound. | `twice_gap_infinitely_often` |
| The differences between consecutive terms of A341262 are exactly 2, 3, 5, 10 and 13. | `isGap_missing_iff` |
| The difference 2 occurs only once (between 1 and 3); each of 3, 5, 10, 13 occurs beyond any bound. | `missing_two_apart`, `missing_gap_infinitely_often` |
| A number occurs twice exactly when it is in column 1 and in some even column k ≥ 4. | `mem_twice_iff`, `DR_iff` |

So both conjectures are true as stated. One detail the conjecture does not mention: the
difference 2 in A341262 occurs only at the very start.

The definitions the theorems are about are short and are at the top of
[`Basic.lean`](../lean/WythoffCeiling/Basic.lean): `W` is the array, `Twice` is A341261 (numbers
at two different places (n, k) ≠ (n', k') with n, k, n', k' ≥ 1), `Missing` is A341262 (positive
integers at no place), and `IsGap S g` says that some two consecutive members of S are g apart.

**Checked by computation, not in Lean.**

* The array was enumerated directly from its definition up to 2,000,000,000, with ⌈nφ⌉ computed
  exactly in integer arithmetic ([`compute/brute_force.c`](compute/brute_force.c); output in
  [`compute/brute_force_2e9.txt`](compute/brute_force_2e9.txt)). No number occurs three times; the
  differences of A341261 are exactly 3, 5, 10, 13 and those of A341262 exactly 2, 3, 5, 10, 13,
  with 2 occurring once. The first terms agree with the data in both OEIS entries.
* The Zeckendorf description below agrees with the enumeration for every number up to
  2,000,000,000.
* Each sequence has density φ⁻⁴ ≈ 0.1459, and the differences 3, 5, 10, 13 occur with relative
  frequencies φ⁻², φ⁻³, φ⁻⁴, φ⁻³ (≈ 38.2%, 23.6%, 14.6%, 23.6%), in both sequences. The counts up
  to 2,000,000,000 match these to six decimal places. On paper this follows from the proof below
  and equidistribution of nφ modulo 1; it is not formalised.

## A description by Zeckendorf representation (paper proof, checked by computation)

Every positive integer is a sum of non-consecutive Fibonacci numbers from 1, 2, 3, 5, 8, 13, ...
in exactly one way (Zeckendorf). Split those Fibonacci numbers into two kinds:

* kind A: 2, 5, 13, 34, 89, ... (F(3), F(5), F(7), ...)
* kind B: 1, 3, 8, 21, 55, ... (F(2), F(4), F(6), ...)

Look at the two smallest parts of a number's Zeckendorf representation.

* **A341261 (occurs twice):** the smallest part is of kind A and the second smallest is of kind B.
  Example: 10 = 2 + 8, 26 = 5 + 21, 31 = 2 + 8 + 21.
* **A341262 (missing):** the number is 1, or its smallest part is of kind B but not 1, and the
  second smallest part (if there is one) is also of kind B. Example: 3, 8, 11 = 3 + 8,
  45 = 3 + 8 + 34.

This follows on paper from the circle description below, using F(i) − φ F(i−1) = ψ^(i−1)
(ψ = 1 − φ): if m = F(i₁) + F(i₂) + ... then m − φ(F(i₁−1) + F(i₂−1) + ...) = ψ^(i₁−1) + ψ^(i₂−1)
+ ..., and the sign pattern of the two leading terms decides which interval this lands in. That
argument has not been formalised; the description was checked against the full enumeration up
to 2,000,000,000.

## How the proof works

1. **Rows behave like the Fibonacci numbers.** Write ψ = 1 − φ = −1/φ ≈ −0.618. If x and m are
   neighbours in row n, x in column k − 1 and m in column k, then

       m − φ·x = ψ^k · u,  where u = ⌈nφ⌉ − (n − 1)φ lies strictly between φ and φ + 1.

   Conversely, every pair of integers (x, m) with m > 0 and m − φx in the interval ψ^k·(φ, φ + 1)
   is a pair of neighbours in some row, found by running the Fibonacci rule backwards
   (`inCol_iff`).

2. **One number on a circle decides everything.** So m is in column k exactly when m − φx lands in
   the interval ψ^k·(φ, φ + 1) for some integer x. These intervals are disjoint; they shrink by a
   factor φ at each step and alternate sides of 0 (even k: between 0 and 1; odd k: between −φ and
   0). Only two values of x can work, so everything is decided by t = m − φ·⌊m/φ⌋, the position
   of m on a circle of circumference φ (`colR_iff`). Two columns of the same parity can never
   both contain m, which gives "at most twice". Twice happens only for column 1 together with an
   even column ≥ 4.

3. **Gaps are return times.** Going from m to m + 1 moves t forward by 1 around the circle. The
   numbers occurring twice are those with t in (φ⁻³, φ⁻²) ∪ (φ⁻⁵, φ⁻⁴) ∪ (φ⁻⁷, φ⁻⁶) ∪ ...: infinitely
   many pieces, piling up near 0. The missing numbers correspond to the mirror image, near φ. The
   proof only needs the first few pieces by name; everything closer to the pile-up point is
   handled as a single block. Starting from each piece, a script finds how far t must move before
   it lands in the set again, and for every step in between which lemma rules that number out.
   Lean checks each of these steps by linear arithmetic with φ between 1.6180339 and 1.618034.
   Two pieces need one extra case split ("is m + 3 also a member?"), and two boundary points are
   excluded because φ is irrational.

4. **Infinitely often.** Adding the Fibonacci number F(i + 1) to m moves t by ψ^i, which is tiny
   for large i. So a number whose t sits strictly inside one piece can be pushed arbitrarily far
   out while keeping the same gap (`inf_often`).

This is the same method as the [beatty-intersections](../beatty-intersections/) project (points on
a circle, finitely many cells, a certificate per cell checked by Lean). The new ingredient is
that the target set has infinitely many pieces, handled by the bounds on all far-out columns at
once (`inI_tail`).

## Paper

[paper/wythoff-ceiling.pdf](paper/wythoff-ceiling.pdf) is a draft write-up with full proofs,
including the pen-and-paper proofs of the Zeckendorf description and of the gap frequencies
(LaTeX source alongside; the two case tables are generated by `compute/paper_tables.py` from
the same data as the Lean proof). It is a preprint: it has not been peer reviewed, and its final
section states how AI tools were used.

## Prior work

A search on 21 November 2026 found no proof or disproof of either conjecture, and no mention of
A341260, A341261, A341262 or the "Wythoff ceiling array" outside the OEIS.
[novelty-log.md](novelty-log.md) lists what was checked, including J. Shallit, *An "Experimental
Mathematics" Approach to Stolarsky Interspersions via Automata Theory* (arXiv:2502.03312, v1 Feb
2025 and v2 Nov 2026), which does not mention these entries.

## Files

* [`../lean/WythoffCeiling/Basic.lean`](../lean/WythoffCeiling/Basic.lean): definitions, the
  circle description, `at_most_twice`, and the lemmas that decide membership on each interval.
* [`../lean/WythoffCeiling/Gaps.lean`](../lean/WythoffCeiling/Gaps.lean): the case analysis and
  the main theorems. Generated by `compute/gen_lean.py`; the script finds the cases, Lean checks
  them, so an error in the script can only break the build, not produce a false theorem.
* [`../lean/WythoffCeiling/Examples.lean`](../lean/WythoffCeiling/Examples.lean): checks that
  the definition reproduces the corner of the array shown in A341260, and that 10 occurs twice
  (rows 1 and 4, the example in A341261).
* [`compute/brute_force.c`](compute/brute_force.c): enumeration to 2·10⁹ and Zeckendorf check.
  Build with `cc -O2 -o wc brute_force.c` and run `./wc 2000000000` (about 2 GB of memory,
  1.5 minutes).
* [`compute/brute_force.py`](compute/brute_force.py): the same in Python, for smaller limits.
* [`compute/paper_tables.py`](compute/paper_tables.py): writes `paper/tables.tex`. Compile the
  paper with `tectonic wythoff-ceiling.tex` (or `pdflatex`) inside `paper/`.

To check the Lean proofs: `lake build WythoffCeiling` from the repository root (see the root
README for setup).
