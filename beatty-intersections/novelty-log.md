# Novelty search log

Search date: 21 November 2026. Question: has anyone already determined the gap sets of the
intersections of Beatty sequences in OEIS A352676, A351415, A346308 and A347793, or settled
Kimberling's conjectures recorded there?

## Verdict by claim

| Claim | Status | Basis |
|---|---|---|
| The gap set of an intersection of two Beatty sequences is finite | Known | Fraenkel and Holzman 1995, Corollary 5.2 |
| The circle / torus (return time) method | Known | Fraenkel and Holzman 1995, Section 3 (the "two-dimensional Slater problem") |
| Growth rate when 1, 1/r, 1/s are independent (limit is r*s) | Known | Skolem 1957 and Bang, as cited by Begunts and Goryashin 2022; Kalmynin's MathOverflow answer 2022 |
| Growth rate for A352676, (3/2)(1+sqrt 3) | Known: it is Bang's 1957 formula with (a,b,c) = (3,-2,1). Checked numerically: the formula gives density (sqrt 3 - 1)/3, matching ours. Same check passes for A351415 with (a,b,c) = (-2,5,1) | Bang 1957, quoted as Theorem 1 in Begunts and Goryashin 2025; also MathOverflow 418749 |
| Exact gap set {2,3,5,6} for A352676; gap 4 never occurs | No prior source found | all searches below |
| Exact gap set {2,...,6} for A351415 | No prior source found | all searches below |
| Exact gap sets {1,2,3,4} for A346308 and A347793 | No prior source found | all searches below |
| Exact gap frequencies; an effective procedure for computing the gap set | No prior source found. Fraenkel and Holzman's finiteness proof is by compactness and gives no bound or procedure | read in full: abstract, intro, Section 5 |
| Drift conjectures (unbounded above and below, zero infinitely often) | Not found settled. Begunts and Goryashin 2025 prove the drift is at most O(ln^5 N) for pairs like ours; they give no lower bound and say nothing about zeros | read in full |

## Sources read

- **OEIS entries and histories.** A352676 last edited 26 Dec 2024 (typo and link formatting only);
  A351415 Nov 2022; A346308 Aug 2022; A347793 and A347469 Nov 2021. No entry records a proof.
- **MathOverflow 418749** (Kimberling's question, March 2022). Stanley's comment guesses
  (3/2)(1+sqrt 3) and r*s in the independent case. Kalmynin's answer proves the independent case
  by Weyl equidistribution and gives a recipe for the dependent case. It uses the membership
  test {n/a} > 1 - 1/a. Nothing about gaps.
- **A. S. Fraenkel and R. Holzman, Gap problems for integer part and fractional part sequences,
  J. Number Theory 50 (1995) 66-86.** Read from the author-hosted scan (abstract, Sections 1 and 5).
  Poses the "generalized intersection problem" (gaps of the intersection of two Beatty sequences),
  reduces it to return times of a torus translation to a rectangle, proves the number of gaps is at
  most q+3 when a modulus is rational with denominator q, and proves it is finite for arbitrary
  moduli (Theorem 5.1, Corollary 5.2) with a bound that "depends only on the moduli" but is not
  computed. No explicit gap set for any irrational pair.
- **J. Simpson, Intersecting rational Beatty sequences, Integers 13 (2013) #A50.** Rational moduli
  only (at most three gaps under the Morikawa condition).
- **A. V. Begunts and D. V. Goryashin, On the intersection of two homogeneous Beatty sequences,
  Chebyshevskii Sb. 23:5 (2022) 145-151.** Abstract only. Counting function N/(ab) + O(N^(1/2+eps))
  for algebraic a, b with 1, 1/a, 1/b independent. Nothing about gaps.
- **A. V. Begunts and D. V. Goryashin, On the intersection of two dependent Beatty sequences,
  Mat. Zametki 118:5 (2025) 670-678 (Math. Notes 118:5, 933-939).** Read in full (Russian
  original, in `literature/`). Quotes Bang's theorem: if a/alpha + b/beta = c with integers
  a, b, c, gcd 1, the counting function is delta*N + o(N) with
  delta = 1/(alpha*beta) - (1/(a*b)) * {a/alpha} * {b/beta}. New result (Theorem 3): the remainder
  is O(N^eps) for algebraic alpha, beta and O(ln^5 N) when they have bounded partial quotients
  (which covers quadratic irrationals). Then numerical tables. Nothing on gaps, lower bounds,
  zeros of the remainder, Kimberling, or the OEIS. Does not cite Fraenkel and Holzman.
- **Th. Skolem, Math. Scand. 5 (1957) 57-68, and T. Bang, Math. Scand. 5 (1957) 69-76.** Not read
  directly; known through the quotation above. Skolem: the intersection is infinite in the
  independent case and in the dependent case with a, b of opposite signs. Bang: the density
  formulas. These are the correct citations for the growth-rate statements.
- **L. Schaeffer, J. Shallit and S. Zorcic, Beatty sequences for a quadratic irrational:
  decidability and applications, arXiv:2402.08331v3.** First-order statements about floor(n*a+b)
  with a, b in one quadratic field are decidable (Walnut). Does not mention our entries or the gaps
  of an intersection. Says pairs from different quadratic fields are out of reach of the method.
- **H. Bruin and R. Fokkink, On the records and zeros of a deterministic random walk,
  arXiv:2503.11734.** Different sequence (A120243), but the same kind of question as the drift
  conjectures; a possible model for the method.
- **A. Haynes and J. Marklof, Higher dimensional Steinhaus and Slater problems via homogeneous
  dynamics, arXiv:1707.04094.** For almost all parameters the number of gaps in the
  higher-dimensional problems is unbounded. Context for why no uniform bound exists.
- **Fokkink et al., On Cloitre's hiccup sequences, arXiv:2507.16956.** Settles other Kimberling
  conjectures involving 1+sqrt 3; does not mention our entries.

## Searches run

- Web searches for "A352676", "A351415", "A346308", "A347793", "A347469" outside oeis.org: no
  paper cites any of them.
- Topic searches: intersection of Beatty sequences with gaps / consecutive differences / return
  times / Slater problem; Kimberling conjectures with Walnut or Ostrowski numeration.
- Citations forward (Semantic Scholar): all 7 papers citing Schaeffer-Shallit-Zorcic, all 29
  citing Fraenkel-Holzman, all 3 citing Begunts-Goryashin 2022. None determines gap sets for
  irrational pairs. Semantic Scholar's lists are incomplete.

## Not reached

- zbMATH Open and Google Scholar: both showed a bot check, which was not attempted.
- ScienceDirect: blocked; the Fraenkel-Holzman paper was read from the author's site instead.
- M. Technau, On Beatty sets and some generalisations thereof (Wuerzburg Univ. Press, 2018), a
  thesis cited by Begunts and Goryashin: not read.
- Wolff and Pitman (cited by Fraenkel and Holzman for the integer-modulus case): not looked up.
- No expert has been asked yet (Kimberling, OEIS editors).
