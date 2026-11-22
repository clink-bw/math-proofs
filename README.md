# Math proofs

Proofs of small open problems, with the checking made explicit. Each result says how it was
verified: by the Lean proof assistant, by exact computation, or on paper only.

## Results

| Project | Result | How it was checked |
|---|---|---|
| [beatty-intersections](beatty-intersections/) | Exact gap sets for four intersections of Beatty sequences (OEIS A352676, A351415, A346308, A347793). The gap set of A352676 is {2, 3, 5, 6}, so the gap 4 conjectured in the OEIS entry never occurs. | Lean |
| [beatty-intersections](beatty-intersections/) | The drift conjecture for A352676: the sequence returns to its linear trend infinitely often and strays arbitrarily far on both sides. | Lean |

A draft paper covering both rows is at
[beatty-intersections/paper/beatty-gaps.pdf](beatty-intersections/paper/beatty-gaps.pdf). It has
not been peer reviewed.

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
