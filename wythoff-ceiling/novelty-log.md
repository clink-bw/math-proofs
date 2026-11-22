# Prior-work search log

Search date: 21 November 2026. Question: has anyone proved or disproved Kimberling's conjectures
on the differences of OEIS A341261 and A341262, or the statement in A341260/A341261 that no number
occurs more than twice in the Wythoff ceiling array?

## Verdict

No source found that proves, disproves or discusses either conjecture. Outside the OEIS, no source
found mentions A341260, A341261, A341262 or the "Wythoff ceiling array".

## Sources checked

| Source | What was read | Finding |
|---|---|---|
| OEIS A341260, A341261, A341262 (JSON records, history pages, draft pages) | Full | Conjectures still stated as conjectures. A341260 revision 15 and A341261 revision 4, both Feb 2021; A341262 revision 8, Dec 2021 (comment wording only). No pending edits. The entries cross-reference only each other and A000045, A001950, A035513. |
| J. Shallit, *An "Experimental Mathematics" Approach to Stolarsky Interspersions via Automata Theory*, arXiv:2502.03312, v1 5 Feb 2025, v2 12 Nov 2026 | Full text of both versions (arXiv HTML), searched for A34126x, "ceiling", "twice" | Does not mention these entries. Covers the Wythoff, Stolarsky and dual Wythoff arrays with Walnut; its OEIS references are A035513 and A380835. |
| Shallit's arXiv papers Feb 2021 – Nov 2026, and every 2021-or-later arXiv paper on his "Walnut papers and books" page (117 papers in all, including 2308.06544, 2312.11706, 2208.06025, 2402.08331, 2501.08823, 2510.11318) | Full text extracted and searched for A341260/1/2, "Wythoff ceiling", "ceiling array" | None mentions them. (The search did find A035513 where it occurs, so the extraction worked.) |
| Other papers settling OEIS conjectures (Bosma et al. 2503.04122; Ashburn 2610.04842, 2610.05776; Fried 2410.07237, 2606.09913, 2607.24832; Macfarlane 2405.18128; Chen, Khovanova et al. 2211.01410; Hendel 2207.11200) | Full text, searched | None mentions them. |
| Benchmarks of open OEIS conjectures: Tsoukalas et al. arXiv:2605.22763 (492 OEIS conjectures in Lean); Adamczewski arXiv:2608.11941; the repositories google-deepmind/formal-conjectures and epoch-research/LeanOpenProblems | Full text and file lists | These entries are not included. |
| arXiv metadata search; web search (several engines); OpenAlex full-text search; Zenodo; GitHub code search | Search listings | Only the OEIS itself, Kimberling's home page (a bare link to A341260) and a LODA program for A341260. |

## Not reached

* Shallit's book *The Logical Approach to Automatic Sequences* (Cambridge University Press, 2022):
  paywalled, not checked.
* Google Scholar and Semantic Scholar snippet search: bot checks or rate limits, not checked.
* Full text of paywalled journals (Fibonacci Quarterly, Integers): not searched.

## Context

The membership questions here are first-order statements about Zeckendorf representations, so in
principle they are within reach of Walnut (Shallit's automata-based prover), the method of the
paper above. No such run was found. The proof in this project is independent of that approach: it
uses the circle description and Lean.
