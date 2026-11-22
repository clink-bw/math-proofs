# Prior-work log

Search date: 21 November 2026. Question: has anyone already searched for 4-paradoxical
tournaments on fewer than 67 players among circulant or other Cayley tournaments, and what is
known about f(4)?

## Verdict by claim

| Claim | Status | Basis |
|---|---|---|
| f(1) = 3, f(2) = 7, f(3) = 19 | Known | Szekeres and Szekeres 1965, as quoted by Graham and Spencer 1971, Reid et al. 2004 and Javier, Llano and Zuazua 2026; Reid et al. also give their own proof that f(3) >= 19 (their Theorem 5) |
| f(k) >= (k+2) 2^(k-1) - 1, so f(4) >= 47 | Known | Szekeres and Szekeres 1965, formula quoted in the same words by Reid et al. 2004 ("(k + 2)2^(k-1) - 1 <= f(k)"), Bonato et al. 2010, Javier et al. 2026 and Jeffries 2026. The 1965 paper itself was not read (JSTOR) |
| The Paley tournament on 67 players is 4-paradoxical, so f(4) <= 67 | Known | Graham and Spencer 1971 ("it is true that T67 has property P4"); Javier et al. 2026 give a proof (their Corollary 4.11) |
| 67 is the smallest prime p for which the Paley tournament is 4-paradoxical | Known | Fisher, reported by Reid et al. 2004; Bonato et al. 2010 |
| **No circulant tournament on fewer than 67 players is 4-paradoxical** | **Known, but only as an unpublished computation.** Reid et al. 2004 report "computational results due to Fisher [4]" (private communication, 1996): "the smallest rotational tournament with domination number 5 is QRT67". A rotational tournament is a circulant tournament, and on fewer than 111 players "domination number 5" is the same as 4-paradoxical. No method, code or counts are given | Reid et al. 2004, Section 3 |
| No Cayley tournament on a non-cyclic group of order 47 to 65 is 4-paradoxical | No prior source found | all sources below |
| f(4) is still open: 47 <= f(4) <= 67 | Known | OEIS A362137 ("only the smallest sizes of the known solutions"); Jeffries 2026 (table lists f(4) = 67 without the mark for confirmed values, and says the bounds on f(k) "have remained un-improved for 60 years"); Erdős problems database entry 902, status "open", last updated 2025-08-31 |

So the circulant half of this project repeats Fisher's 1996 computation independently, with
published code and counts. The Cayley-tournament half (non-cyclic groups) was not found in the
literature. Neither changes the bounds on f(4).

## Sources read

- **OEIS A362137** (read 21 Nov 2026). "Smallest size of an n-paradoxical tournament built as a
  directed Paley graph": 1, 3, 7, 19, 67, 331, 1163. Says a(0)..a(3) are proved minimal over all
  tournaments and that 67, 331, 1163 "are only the smallest sizes of the known solutions". Links
  Bloom's Erdős problem 902, Erdős 1963, Graham and Spencer 1971, Reid et al. 2004, Szekeres and
  Szekeres 1965. No lower bound for n = 4 and no search beyond Paley tournaments.
- **R. L. Graham and J. H. Spencer, A constructive solution to a tournament problem, Canad. Math.
  Bull. 14 (1971) 45-48.** Read from the scan (OCR text layer). Proves the Paley tournament on p
  players is k-paradoxical when p > k^2 2^(2k-2). Concluding remarks: T7 has P2, T19 has P3,
  f(2) = 7 and f(3) = 19 were shown in Szekeres and Szekeres, "it is true that T67 has property
  P4", and since the Szekeres bound gives f(4) >= 47 "it is possible that T67 is also minimal".
  No method is given for the 67 claim.
- **K. B. Reid, A. A. McRae, S. M. Hedetniemi, S. T. Hedetniemi, Domination and irredundance in
  tournaments, Australas. J. Combin. 29 (2004) 157-172.** Read in full (Section 3). Restates the
  Szekeres bound as (k + 2)2^(k-1) - 1 <= f(k) and quotes Graham and Spencer ("f(4) >= 47").
  Theorem 5: every tournament on fewer than 19 vertices has domination number at most 3. Then
  "computational results due to Fisher [4]" ([4] = D. Fisher, private communication, 1996),
  defining a rotational tournament of order 2m+1 exactly as a circulant tournament: the smallest
  rotational tournament with domination number 5 is QRT67; the smallest Paley tournaments with
  domination number 6 and 7 have p = 331 and 1163; domination number 8 needs p >= 3079.
- **A. Bonato, P. Gordinowicz, P. Pralat, Bounds and constructions for n-e.c. tournaments,
  Contrib. Discrete Math. 5 (2010) 52-66.** Read in full. Calls Schutte's property P_n and
  restates the Szekeres bound. Verified by computer that T67 is the smallest Paley tournament with
  property P4 (= S_4). Their searches are about the stronger 4-e.c. property: no 4-e.c.
  tournaments on 47 or 48 vertices, and 3 doubly regular tournaments on 47 vertices and 36,350 on
  51 vertices were tested for 4-e.c. (none was). Nothing on circulant or Cayley tournaments with
  S_4 below 67.
- **N. Y. Javier, B. Llano, R. Zuazua, 2- and 3-existentially closed tournaments, Contrib.
  Discrete Math. 21 (2026) 73-90.** Read in full. Shows QR_p has S_4 iff the in- and
  out-neighbourhoods of a vertex have S_3, and deduces that QR_67 has S_4 (Corollary 4.11).
  Poses characterising circulant tournaments with P2 and P3 as an open problem. No search for
  S_4 below 67.
- **J. Jeffries, Schutte's property for sets of tournaments and an application to dice games,
  arXiv:2604.08790 (April 2026).** Read in full (HTML). Lists f(4) = 67 as an upper bound only,
  cites Bozoki (2014) for Fisher's computation that P67, P331, P1163 are the smallest S_4, S_5,
  S_6 Paley tournaments, and says the bounds on f(k) are unimproved for 60 years. Its SAT
  computations (from Jeffries's 2024 dissertation) concern a generalisation (sets of several
  tournaments); no search for S_4 tournaments below 67 is reported.
- **Erdős problems database** (github.com/teorth/erdosproblems, data/problems.yaml): problem 902
  is "open", last updated 2025-08-31, linked to OEIS A362137. The erdosproblems.com page itself
  refused automated access and was not read.

## Not read

- E. Szekeres and G. Szekeres, On a problem of Schutte and Erdos, Math. Gaz. 49 (1965) 290-293
  (JSTOR). The bound is quoted identically by five later sources above.
- J. W. Moon, Topics on Tournaments (1968); Project Gutenberg was unavailable (HTTP 503).
- S. Bozoki, Nontransitive dice sets realizing the Paley tournaments for solving Schutte's
  tournament problem, Miskolc Math. Notes 15 (2014) 39-50 (known here only through Jeffries).
- W. Ananchuen and L. Caccetta, On tournaments with a prescribed property, Ars Combin. 36 (1993)
  89-96 (bounds for Paley tournaments, according to later citations).
