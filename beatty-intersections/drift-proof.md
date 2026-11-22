# The drift conjecture for A352676: proof

Status (21 November 2026): the theorem is verified in Lean with no assumptions
(`drift_theorem_zero`, `drift_theorem_above`, `drift_theorem_below` in
`lean/BeattyGaps/Sqrt3Block.lean`). The write-up below has not yet been read by another person.

## Statement

Let s = sqrt 3, let S be the set of positive integers in both Beatty sequences B(s) and B(1+s),
and let a(1) < a(2) < ... be its elements (OEIS A352676). Put

    d(n) = a(n) - floor(n * (3/2)(1 + s)).

**Theorem.** d(n) = 0 for infinitely many n, and d is unbounded above and below.

This is conjecture (3) of A352676, reading its "A352673" as A352674 (the Beatty sequence of
(3/2)(1+s)); A352673 is a decimal expansion and cannot be what was meant.

**Sharper form.** Call a gap a(n+1) - a(n) *short* if it is 2 or 3 and *long* if it is 5 or 6
(these are the only gaps). Let G(n) = -1 + (number of short gaps) - (number of long gaps) among
the first n-1 gaps. Then

* d(n) = 0 exactly when G(n) = 0; d(n) < 0 exactly when G(n) > 0; d(n) > 0 exactly when G(n) < 0;
* d(n) = -1 - floor((G(n) - phi)/(s-1)) with phi = frac((a(n)+1) s), 0 < phi < s-1;
* G takes the value 2j-1 near a = q_{4j+1} and -2j-3 near a = q_{4j+3}, where q_n are the
  denominators 1, 1, 3, 4, 11, 15, 41, 56, ... of the convergents of sqrt 3 - 1.

So the drift is a +1/-1 walk driven by the gap sequence, and it grows like the logarithm of n.

## Proof

Notation: xi = s - 1, w(m) = floor(m s), N(M) = number of elements of S up to M.

**Step A: the walk (Lean-verified).** Define G(n) = 3n - floor((a(n)+1) xi)
= 3n + a(n) + 1 - w(a(n)+1). By `Sqrt3.walk_step` in the Lean project, if m is in S and the next
element is m+g, then w(m+g+1) - w(m+1) equals g+2 for g = 2, 3 and g+4 for g = 5, 6. Hence

    G(n+1) - G(n) = 3 + g - (w(a(n)+g+1) - w(a(n)+1)) = +1 (short gap), -1 (long gap).

G(1) = 3 + 5 + 1 - w(6) = 9 - 10 = -1.

**Step B: from G to d (elementary).** Let M = a(n) and phi = frac((M+1) xi). From the definition,
3n = G + (M+1) xi - phi, so n * 3/xi = M + 1 + (G - phi)/xi, and 3/xi = (3/2)(1+s). Therefore
d(n) = -1 - floor((G - phi)/xi). Since M is in B(1+s), w(M+1) - w(M) = 2, which gives
0 < phi < xi. If G = 0 the floor is -1 and d = 0. If G >= 1 the floor is >= 0 and d <= -1, with
d <= -floor(G/xi). If G <= -1 the floor is <= -2 and d >= 1, with d >= -1 - floor(G/xi).

**Step C: G is unbounded above and below.** Put F(M) = 3 N(M) - floor((M+1) xi), so
G(n) = F(a(n)), and F(M) lies in [G(n) - 5, G(n)] for a(n) <= M < a(n+1). It suffices to show F
is unbounded above and below.

C1. Let c(m) = w(m+1) - w(m) - 1 (0 or 1) and kappa(m) = (w(m) + 3m) mod 6. A direct calculation
with floors shows: m is in S exactly when c(m) = 1 and kappa(m) is 1 or 5. (m in B(s) iff
floor(w(m+1)/3) > floor(w(m)/3); m in B(1+s) iff floor((w(m+1)-m-1)/2) > floor((w(m)-m)/2).)
Since floor((M+1) xi) is the number of m <= M with c(m) = 1,

    F(M) = sum over m <= M with c(m) = 1 of f(kappa(m)),   f = +2 on {1, 5}, -1 on {0, 2, 3, 4},

with kappa(1) = 4 and kappa(m+1) = kappa(m) + 4 + c(m) (mod 6).

C2. c(1) c(2) ... is the characteristic Sturmian word of slope xi = [0; 1, 2, 1, 2, ...]. By the
classical theorem on standard words (Lothaire, Algebraic Combinatorics on Words, Section 2.2.2),
its prefix of length q_n is s_n, where s_{-1} = 1, s_0 = 0, s_1 = 1 and
s_n = s_{n-1}^{a_n} s_{n-2} with a_n = 2 for even n and 1 for odd n.

C3. For a word v let g(v) = 4|v| + (number of 1s in v) mod 6 and let Phi_v[k] be the sum of f over
the 1s of v when the state starts at k. Then Phi_{vw}[k] = Phi_v[k] + Phi_w[k + g(v)]. Writing
Phi_n, g_n for v = s_n, induction on n gives, for n = 4j + r:

    r = 1:  Phi_n = [-1, 2,-1,-1,-1, 2] + j [-1,-1,-1,-1, 2, 2],   g_n = 5
    r = 2:  Phi_n = [ 1, 1, 1,-2,-2, 1] + j [ 2, 2,-1,-4,-1, 2],   g_n = 2
    r = 3:  Phi_n = [ 0, 0, 0, 0,-3, 3] + j [ 1, 1, 1,-2,-2, 1],   g_n = 1
    r = 0:  Phi_n =                       j [ 1,-2,-2,-2, 1, 4],   g_n = 4

(entries indexed by k = 0..5). The induction step is four linear identities, checked exactly by
`compute/drift/verify_induction.py`. Taking k = kappa(1) = 4:

    F(q_{4j+1}) = 2j - 1,     F(q_{4j+3}) = -2j - 3.

**Step D: conclusion.** G moves by +1 or -1 at each step and is unbounded above and below, so it
changes sign infinitely often and each time passes through 0. By Step B, d(n) = 0 infinitely often
and d is unbounded above and below.

## What has been checked, and how

Lean names are in `lean/BeattyGaps/Sqrt3Drift.lean` and `lean/BeattyGaps/Sqrt3Block.lean`
(namespace `BeattyGaps.Sqrt3`).

| Part | Check |
|---|---|
| Step A (walk step) | Lean: `walk_step` and `next_elem` (the walk moves by exactly +1 or -1 from one element to the next) |
| Step B (walk to drift) | Lean: `drift_of_F` and `drift_eq_zero_iff`. Lean proves the sign statements and that the drift is at least as large as the walk in absolute value, not the exact floor formula |
| C1 (membership rule, walk as a sum) | Lean: `inS_iff`, `F_succ`, `F_eq_Phi` |
| C2 (block structure of the step word) | Lean: `block_hypothesis`. Mathlib has no Sturmian word theory, so this is proved from scratch for sqrt 3: the convergents p_k/q_k have norms p_k^2 - 3 q_k^2 in {1, -2} and determinant +1 or -1 (`norm_qp`, `det_qp`), so \|m sqrt 3 - N\| >= \|q_k sqrt 3 - p_k\| for 1 <= m < q_{k+1} (`best_approx_even`, `best_approx_odd`), so floor((m + q_k) sqrt 3) = floor(m sqrt 3) + p_k on that range (`w_shift`) |
| C3 (closed forms) | Lean: `good_all`; consequences `F_block_one`, `F_block_three` |
| Step D (a unit-step walk that changes sign hits zero) | Lean: `zero_between` |
| Whole theorem | Lean, no assumptions: `drift_theorem_zero`, `drift_theorem_above`, `drift_theorem_below`, stated for the n-th element `a n` and `d n = a n - floor(n (3/2)(1 + sqrt 3))` |
| Independent numerical check | `drift_sqrt3.c`: exact drift for the first 2,000,000,000 integers; records at a = 10865, 151317, ... = q_n + 1 and a = 40543, 564717, ... = q_n - 2, drift between -22 and 21, 12.9% of n have d(n) = 0 |

All of these Lean theorems depend only on the three standard axioms.

## Not done

* The exact formula of the sharper form (first bullet) and the constants in its last bullet are
  proved on paper only; Lean proves slightly weaker statements that suffice for the theorem.
* The Lean statement is for the reading of the conjecture given above (A352674 in place of
  A352673). Lean cannot check that this is what the OEIS entry intends.
* No analogue has been attempted for the other pairs. For sqrt 2 with sqrt 3 and for the cube
  roots of 2 the same question lives on a two-dimensional torus and looks much harder.
