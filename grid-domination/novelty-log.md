# Prior-work search for the grid {2}-domination results

Searched on 21 November 2026. The question: were Conjecture 2.5 (the 3 × n grid) and Conjecture 3.7
(the 4 × n grid) of Lee and Liu, *The integer {2}-domination number of grids*
([arXiv:2502.00134](https://arxiv.org/abs/2502.00134)), already settled?

Each item says how far it was read: **full** (the text itself), **abstract**, or **snippet**
(seen only in search results or in another paper's citation).

## Conclusion

1. **No paper settles either conjecture.** No journal article or arXiv preprint was found that
   proves, disproves or even cites them.
2. **Both were already settled, without peer review, in a public GitHub repository**,
   [`the-omega-institute/trureturing`](https://github.com/the-omega-institute/trureturing), about
   five weeks before this project. That repository is AI-produced (its own issue texts say which
   models did what) and has no human review on the relevant pull request.
   * Conjecture 2.5: a Lean 4 proof was merged on 18 October 2026
     ([issue 17651](https://github.com/the-omega-institute/trureturing/issues/17651),
     [pull request 18785](https://github.com/the-omega-institute/trureturing/pull/18785); the file
     `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.lean` is on the `dev`
     branch). Its lower bound uses a potential on pairs of adjacent columns (a 27 × 27 table).
     Read: issue and pull-request text in full through the GitHub API; the Lean file was not
     compiled or audited here.
   * Conjecture 3.7: a proof by exact computation was posted on 16 October 2026
     ([issue 17664](https://github.com/the-omega-institute/trureturing/issues/17664), still open on
     21 November 2026). It uses the same 389-state column automaton as this project and the same
     argument as `compute/analyze.py` here: the vector of the dynamic programme satisfies
     E_77 = E_67 + 19, so the pattern repeats for ever. A comment on that issue reports a Lean
     proof (6 modules, 1183 lines) that had compiled on the author's machine but was not yet
     merged; no four-row file was in the repository's `Domination` folder on 21 November 2026.
     Read: issue and comment in full through the GitHub API.
3. So the results here are **not new mathematics**. What this project adds is an independent proof
   and an independently written Lean formalisation of both, plus the exact value of the 4 × n
   number for every n ≥ 1 in Lean. As far as this search could tell, the Lean proof of the 4 × n
   case here is the first one publicly available, but that could change at any moment and should
   not be claimed without re-checking the repository above.

The work in this project was done without reading the other repository's proofs or Lean code; its
existence was found by the search below while the Lean proof here was being written. The two
approaches turned out to be close for 4 × n (same automaton, same periodicity argument for the
computation), which is unsurprising since it is the standard method for such problems.

## The paper itself

* arXiv:2502.00134 has a single version (v1, 31 January 2025), no journal reference and no DOI.
  Read: **full** (HTML version), except the figures, which are images.
* Confirmed from the text: the definition (weights in {0, 1, 2}, every closed neighbourhood sums to
  at least 2; Section 1 gives the general definition with nonnegative integer weights), Theorem 2.1
  (1 × n: 2⌈n/3⌉), Theorem 2.3 (2 × n: n + 1), Theorem 2.4 (3 × n: at most ⌊3n/2⌋ + 1),
  Conjecture 2.5, Theorem 3.6 (a table of values for 4 × n, n ≤ 100, found by their algorithm) and
  Conjecture 3.7. The earlier summary of the paper given to this project was accurate.
* Their column algorithm has 6, 23, 95, 389 "feasible columns" for heights 1 to 4. The automaton
  here has exactly those numbers of states.

## Citations and follow-ups

| Source | Query | Result |
|---|---|---|
| OpenAlex | the paper's record; works citing it | found (arXiv only); 0 citing works |
| Semantic Scholar API | citations of arXiv:2502.00134 | empty list (metadata endpoint rate-limited) |
| Crossref, zbMATH Open | title and authors | no published version; zbMATH has the preprint only |
| arXiv API | authors; "integer domination"; "{2}-domination"; "{k}-domination"; domination AND grid, 2025-01 to 2026-11 | no follow-up |
| Google Scholar | exact title | not accessible (CAPTCHA) |
| OEIS | terms 4,5,7,8,11,13,14,16,18,20,22,24,26,28,29,32,34,35 and keywords | no sequence for the 4 × n values; the 3 × n values are the numbers not divisible by 3 (A001651), with no mention of domination |
| Web search (about 30 queries) | the title; the conjectures; {k}-domination of Cartesian products of paths; double, Italian and Roman {2}-domination of grids; theses | found the GitHub issues above and the thesis below; no paper proving either conjecture |
| GitHub REST API | issues 17651 and 17664, pull request 18785, the `Domination` folder on `dev`, issue search | as described in the conclusion |

## Older literature that might already contain the 3 × n value

None does. The details:

* **Brešar, Henning, Klavžar**, *On integer domination in graphs and Vizing-like problems*,
  Taiwanese J. Math. 10 (2006) 1317–1328. Read: **full**. General bounds (γ_{k} ≤ kγ) and
  Vizing-type results; the exact identity γ_{k}(G) = γ_{×k}(G ⊠ K_k) with the *strong* product,
  which turns the question into k-tuple domination of a graph that is not a grid. No grid values.
* **Bonomo, Brešar, Grippo, Milanič, Safe**, *Domination parameters with number 2*, Discrete
  Appl. Math. 235 (2018) 23–50, arXiv:1511.00410. Read: **full** for the relations table. Every
  known relation between γ_{2} and its neighbours (double domination, Italian domination,
  2-domination, Roman domination, total domination) is an inequality, so known grid values of
  those parameters give bounds only. For 3 × n the best transferable lower bound is about 10n/7,
  below 3n/2; for 4 × n it is about 20n/11, below 19n/10.
* **Rao, Talon**, *The 2-domination and Roman domination numbers of grid graphs*, DMTCS 21 (2019),
  arXiv:1810.12896, and **Talon**'s thesis, arXiv:2002.11615. Read: abstract and parts of the
  text. The same transfer-matrix method over the (min, +) algebra as used here, applied to other
  parameters; {k}-domination does not appear.
* **Y.-T. Kuan**, *A study of integer domination number*, M.Sc. thesis, National Chiao Tung
  University, 2017 (advisor H.-L. Fu). Read: **abstract** only (through the Wayback Machine; the
  full text is behind a CAPTCHA). The abstract says it finds γ_{k}(P_2 □ P_n) exactly and gives
  bounds for P_m □ P_n. Lee and Liu do not cite it. **Not checked**: what its bounds for heights 3
  and 4 are.
* **Hou, Lu**, *On the {k}-domination number of Cartesian products of graphs*, Discrete Math. 309
  (2009) 3413–3419. Read: **snippet** only (paywall). Vizing-type bounds by its title and
  citations; not verified.
* **Cheng, Fu, Liu**, *The integer {k}-domination number of circulant graphs*, arXiv:1905.03388.
  Read: **abstract**. Cycles and circulants, not grids.
* Other Vizing-type papers on {k}-domination (Choudhary–Margulies–Hicks; John–Suen; Davila–Krop)
  and transfer-matrix papers on other domination parameters of grids and cylinders (Gonçalves,
  Pinlou, Rao, Thomassé; Garzón, Martínez, Moreno, Puertas; Pavlič and Žerovnik; Bouznif, Moncel,
  Preissmann): abstracts or snippets only; none states γ_{2} for a 3 × n or 4 × n grid.

## Not done

* The Kuan thesis was not read in full.
* Google Scholar's "cited by" list and MathSciNet were not available.
* The Lean code in the other repository was not compiled or compared with the code here.
