# Math proofs

Proofs of small open problems, with the checking made explicit. Each result says how it was
verified: by the Lean proof assistant, by exact computation, or on paper only.

## Results

| Project | Result | How it was checked |
|---|---|---|
| [beatty-intersections](beatty-intersections/) | Exact gap sets for four intersections of Beatty sequences (OEIS A352676, A351415, A346308, A347793). The gap set of A352676 is {2, 3, 5, 6}, so the gap 4 conjectured in the OEIS entry never occurs. | Lean |
| [beatty-intersections](beatty-intersections/) | All three conjectures of OEIS A352676, in corrected form: the gaps are exactly 2, 3, 5, 6 and each occurs infinitely often; a(n)/n tends to (3/2)(1 + sqrt 3); and a(n) - floor(n (3/2)(1 + sqrt 3)) is zero infinitely often and unbounded above and below. | Lean |
| [wythoff-ceiling](wythoff-ceiling/) | Both of Kimberling's 2021 gap conjectures for the Wythoff ceiling array are true: numbers occurring twice (OEIS A341261) are spaced exactly 3, 5, 10 or 13 apart, and missing numbers (OEIS A341262) exactly 2, 3, 5, 10 or 13 apart (the 2 only once, between 1 and 3). No number occurs more than twice. | Lean |
| [grid-domination](grid-domination/) | The integer {2}-domination number of the m × n grid, for every n, for m = 3, 4, 5: for example ⌊3n/2⌋ + 1 for 3 rows and 2n − ⌊(n − 9)/10⌋ for 4 rows and n ≥ 49 (Conjectures 2.5 and 3.7 of Lee and Liu, arXiv:2502.00134; independent proofs, not the first), and ⌈(23n + 17)/10⌉ for 5 rows and n ≥ 19 (apparently new). | Lean |
| [grid-domination](grid-domination/) | The same number for m = 6 to 10 rows and every n (apparently new); for 9 rows it is exactly 4n + 2. | Exact computation |
| [paradoxical-tournaments](paradoxical-tournaments/) | Erdős problem 902 (Schütte's tournament problem), a negative search: no Cayley tournament with 47 to 65 players (circulant, or on any of the six non-cyclic groups of those orders) is 4-paradoxical. The bounds 47 ≤ f(4) ≤ 67 are unchanged. The circulant half repeats an unpublished 1996 computation of D. Fisher. | Exact computation (C), cross-checked by an independent Python checker |

Draft papers, none of them peer reviewed:
[Beatty intersections](beatty-intersections/paper/beatty-gaps.pdf) (both Beatty rows),
[Wythoff ceiling array](wythoff-ceiling/paper/wythoff-ceiling.pdf) and
[grid domination](grid-domination/paper/grid-2-domination.pdf).

## Checking the Lean proofs

The Lean code is one [Lake](https://github.com/leanprover/lean4/tree/master/src/lake) package
built on [Mathlib](https://github.com/leanprover-community/mathlib4).

1. Install Lean with [elan](https://github.com/leanprover/elan).
2. Fetch the prebuilt Mathlib, then build:

```bash
lake exe cache get
```

```bash
lake build
```

A successful build means every theorem in `lean/` has been checked. The proofs contain no `sorry`
and depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The same
build runs on every push (see the Actions tab).

Lean confirms that a proof matches its formal statement. Whether the formal statement says what
the English summary says is for the reader to judge; each project README points to the
definitions, which are short.

## Layout

```
lakefile.toml, lean-toolchain, lake-manifest.json   one Lean package for the whole repository
lean/<Library>.lean, lean/<Library>/                one Lean library per project
<project>/README.md                                 statements, status, prior work
<project>/compute/                                  generators and exact computations
```

To add a project: create `<project>/`, add `lean/<Library>/` with a `[[lean_lib]]` entry in
`lakefile.toml`, and add a row to the table above.

## How this was made

The mathematics, code and text here were produced with substantial assistance from an AI model
(Claude, by Anthropic), directed and checked by the repository owner. That is the reason for the
emphasis on machine-checked statements and on labelling everything that is not machine-checked.

## Licence

Apache License 2.0; see [LICENSE](LICENSE).
