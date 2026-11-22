# Intersections of Beatty sequences

The Beatty sequence of an irrational number r > 1 is floor(r), floor(2r), floor(3r), ...
In 2021-22 Clark Kimberling recorded conjectures in the OEIS about the integers lying in two such
sequences at once. This project settles the ones about gaps for four pairs, and all three
conjectures for one pair.

## Results

**Gap sets (verified in Lean).** A gap is the difference between consecutive members of the
intersection.

| Pair | OEIS | Gaps that occur | Lean theorem |
|---|---|---|---|
| sqrt 3 and 1 + sqrt 3 | [A352676](https://oeis.org/A352676) | exactly 2, 3, 5, 6 | `BeattyGaps.Sqrt3.isGap_iff` |
| golden ratio and sqrt 5 | [A351415](https://oeis.org/A351415) | exactly 2, 3, 4, 5, 6 | `BeattyGaps.Golden.isGap_iff` |
| sqrt 2 and sqrt 3 | [A346308](https://oeis.org/A346308) | exactly 1, 2, 3, 4 | `BeattyGaps.Sqrt2Sqrt3.isGap_iff` |
| 2^(1/3) and 2^(2/3) | [A347793](https://oeis.org/A347793) | exactly 1, 2, 3, 4 | `BeattyGaps.CubeRoot2.isGap_iff_cbrt` |

The OEIS entry A352676 conjectures that the gaps are 2, 3, 4, 5 and 6. The gap 4 never occurs
(`BeattyGaps.Sqrt3.four_not_gap`). For A351415 the conjectured list is correct.

Each `isGap_iff` says: `g` is a gap if and only if `g` is in the list. Lean shows each listed gap
occurs at least once. That each occurs infinitely often, with an explicit frequency, follows from
equidistribution; that argument is not formalised here.

**The three conjectures of A352676.**

1. Gaps are 2, 3, 4, 5, 6, each infinitely often: false as stated; the gap set is {2, 3, 5, 6}.
2. a(n)/n tends to (3/2)(1 + sqrt 3): true, and already a consequence of a 1957 theorem of
   T. Bang on the density of such intersections.
3. a(n) - floor(n (3/2)(1 + sqrt 3)) is zero infinitely often and unbounded above and below:
   true, and verified in Lean with no assumptions (`BeattyGaps.Sqrt3.drift_theorem_zero`,
   `drift_theorem_above`, `drift_theorem_below`), reading the entry's A352673 as A352674.
   [drift-proof.md](drift-proof.md) explains the argument.

## Prior work

The question of gaps in the intersection of two Beatty sequences is due to Fraenkel and Holzman
(J. Number Theory 50, 1995), who reduced it to return times of a torus translation and proved the
gap set is always finite, without a way to compute it. The contribution here is the exact gap
sets for these pairs, the correction to A352676, the drift theorem, and the formal proofs.
[novelty-log.md](novelty-log.md) records what was searched and read.

## Paper

[paper/beatty-gaps.pdf](paper/beatty-gaps.pdf) is a draft write-up of these results, with
full proofs (LaTeX source alongside). It is a preprint: it has not been peer reviewed, and its
final section states how AI tools were used.

## Files

* `../lean/BeattyGaps/` - the Lean proofs. `Basic.lean` has the definitions (`Beatty`, `IsGap`);
  there is one file per pair, and `Sqrt3Drift.lean` and `Sqrt3Block.lean` for the drift theorem.
* `compute/gen_lean.py` - writes the Lean files. It finds the case analysis; Lean checks every
  case, so an error in the script can only produce a failed build, not a false theorem.
* `compute/same_field_case.py`, `compute/independent_case.py` - exact gap sets and frequencies,
  with brute-force comparison.
* `compute/drift/` - the drift walk: exact computation to 2,000,000,000 (`drift_sqrt3.c`), the
  block structure (`walk.py`) and the induction check (`verify_induction.py`).
