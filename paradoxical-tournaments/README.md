Proposed row for the results table in the root README:

| Project | Result | How it was checked |
|---|---|---|
| [paradoxical-tournaments](paradoxical-tournaments/) | Erdős problem 902 (Schütte's tournament problem), a negative search: no Cayley tournament with 47 to 65 players (circulant, or on any of the six non-cyclic groups of those orders) is 4-paradoxical. The bounds 47 ≤ f(4) ≤ 67 are unchanged. The circulant half repeats an unpublished 1996 computation of D. Fisher. | Exact computation (C), cross-checked by an independent Python checker |

# Schütte's tournament problem: a search below 67 players

A tournament is a set of players in which every pair plays once and one of the two wins. It is
**k-paradoxical** if every group of k players is beaten by some single other player. Let f(k)
be the fewest players a k-paradoxical tournament can have. Finding f(k) is
[Erdős problem 902](https://www.erdosproblems.com/902) (the question is due to K. Schütte).

Known: f(1) = 3, f(2) = 7 and f(3) = 19 (the last two shown by Szekeres and Szekeres in 1965).
For k = 4 only bounds are known: **47 ≤ f(4) ≤ 67**. The lower bound is the Szekeres bound
f(k) ≥ (k+2)·2^(k-1) − 1; the upper bound is the Paley tournament on 67 players (player x
beats player y when y − x is a nonzero square mod 67), noted by Graham and Spencer in 1971.
Both bounds have stood since then. See [novelty-log.md](novelty-log.md) for sources.

This project asks: is there a 4-paradoxical tournament on fewer than 67 players among the most
symmetric tournaments, the ones every known record holder belongs to?

## Result

**Negative.** Checked by exact computation, every connection set, no sampling:

* **Circulant tournaments.** For every odd n from 47 to 65, none of the 2^((n-1)/2) circulant
  tournaments on n players is 4-paradoxical. (In a circulant tournament the players are
  0, 1, ..., n-1 and x beats y exactly when y − x lies in a fixed set S, the *connection set*,
  which holds exactly one of d and −d for each d ≠ 0. The Paley tournaments are circulant.)
* **Cayley tournaments on the other groups.** A Cayley tournament is the same idea with the
  players labelled by the elements of some other group (a finite set with a multiplication
  that can be undone, like the numbers mod n under addition): x beats y when x⁻¹y lies in S.
  Circulants are the case of the numbers mod n. None of the Cayley tournaments on any of the
  six non-cyclic groups of order between 47 and 65 is 4-paradoxical: Z7×Z7 (order 49),
  Z11⋊Z5 (55), Z19⋊Z3 (57), and Z3×Z21, Z7⋊Z9, Z3×(Z7⋊Z3) (all order 63).

Together with the cyclic groups these are all the groups of order 47 to 65 that can carry a
tournament of this kind (it needs odd order; see "Which groups" below). So: **no Cayley
tournament on fewer than 67 players is 4-paradoxical.** Below 47 nothing is 4-paradoxical by
the Szekeres bound; the search confirms this for circulants on 5 to 45 players as a sanity check.

On 67 players the search finds exactly two 4-paradoxical circulant connection sets out of
2^33: the squares and the non-squares mod 67. Both give the Paley tournament (the map
x → −x turns one into the other). So the Paley tournament is the only 4-paradoxical circulant
tournament on 67 players.

**What this does not say.** It says nothing about tournaments that are not Cayley tournaments,
which are almost all tournaments (on 47 labelled players there are 2^1081 tournaments, of
which 2^23 are circulant). The true value of f(4) can still be anything from 47 to 67. The
result only rules out the most symmetric candidates.

**Is it new?** Half of it is not. Reid, McRae, Hedetniemi and Hedetniemi (2004) report, as a
private communication from D. Fisher (1996), that "the smallest rotational tournament with
domination number 5 is QRT67". Rotational means circulant. The domination number is the size
of the smallest group of players who between them beat everyone else; it is at least 5 exactly
when the tournament is 4-paradoxical, and it cannot reach 6 below 111 players (the Szekeres
bound for k = 5). So Fisher had already found that no circulant tournament on fewer than 67
players is 4-paradoxical. No method, code or counts were published; this project redoes it
independently with published code. No earlier search of the Cayley tournaments on the
non-cyclic groups was found (see [novelty-log.md](novelty-log.md)).

## What was searched, with counts and times

A *kind of 4-set* below means a 4-set up to shifting: in a Cayley tournament, multiplying every
player by the same group element is a symmetry, so a 4-set and its shifts are all beaten or all
unbeaten, and one representative per kind is tested. Each kind contains exactly n of the
C(n,4) 4-sets. For circulants, the map x → −x turns the connection set S into −S and gives the
same tournament up to relabelling, so only connection sets containing 1 were checked (half of
all of them). To test a 4-set, the program stores S as a 128-bit word, and the players beating
all four members come out of a few shifts and bitwise ANDs. Times are wall-clock on an 8-core
Apple M2.

| Players | Group | Kinds of 4-set | Connection sets checked | 4-paradoxical | Time (s) |
|---|---|---|---|---|---|
| 47 | Z47 (circulant) | 3,795 | 2^22 (those containing 1) | 0 | 0.04 |
| 49 | Z49 (circulant) | 4,324 | 2^23 (those containing 1) | 0 | 0.07 |
| 49 | Z7×Z7 | 4,324 | 2^24 (all) | 0 | 0.26 |
| 51 | Z51 (circulant) | 4,900 | 2^24 (those containing 1) | 0 | 0.16 |
| 53 | Z53 (circulant) | 5,525 | 2^25 (those containing 1) | 0 | 0.31 |
| 55 | Z55 (circulant) | 6,201 | 2^26 (those containing 1) | 0 | 0.62 |
| 55 | Z11⋊Z5 | 6,201 | 2^27 (all) | 0 | 2.30 |
| 57 | Z57 (circulant) | 6,930 | 2^27 (those containing 1) | 0 | 1.44 |
| 57 | Z19⋊Z3 | 6,930 | 2^28 (all) | 0 | 4.39 |
| 59 | Z59 (circulant) | 7,714 | 2^28 (those containing 1) | 0 | 2.63 |
| 61 | Z61 (circulant) | 8,555 | 2^29 (those containing 1) | 0 | 5.20 |
| 63 | Z63 (circulant) | 9,455 | 2^30 (those containing 1) | 0 | 10.09 |
| 63 | Z3×Z21 | 9,455 | 2^31 (all) | 0 | 37.35 |
| 63 | Z7⋊Z9 | 9,455 | 2^31 (all) | 0 | 38.47 |
| 63 | Z3×(Z7⋊Z3) | 9,455 | 2^31 (all) | 0 | 36.62 |
| 65 | Z65 (circulant) | 10,416 | 2^31 (those containing 1) | 0 | 20.27 |

In all, about 1.1 × 10^10 connection sets in under three minutes. Most sets fail fast: the
program tests first the 4-sets that most recently caught a failure, and a typical set is
rejected after about four tests. Logs:
[results/circ_k4_47_65.txt](compute/results/circ_k4_47_65.txt),
[results/groups_k4.txt](compute/results/groups_k4.txt).

Also run: circulants on every odd n from 5 to 45 (none 4-paradoxical, as the Szekeres bound
requires; [results/circ_k4_below47.txt](compute/results/circ_k4_below47.txt)), and on 67 players
(2^32 sets containing 1, 40 s, one hit: the Paley set;
[results/circ_k4_67.txt](compute/results/circ_k4_67.txt)).

## How close did they come?

For each family, the search also found the connection set leaving the fewest kinds of 4-set
unbeaten. A 4-paradoxical tournament would leave none. Here the work was cut by symmetry: a
group automorphism (for Z_n, a multiplier x → u·x with u coprime to n) carries one connection
set to another with the same count, so one set per orbit was tested. The automorphism groups
were computed by the program.

| Players | Group | Symmetries used | Fewest unbeaten kinds of 4-set | Same, as 4-sets | Connection sets achieving it | Time (s) |
|---|---|---|---|---|---|---|
| 47 | Z47 (circulant) | 46 | 46 of 3,795 | 2,162 | 2 | 0.27 |
| 49 | Z49 (circulant) | 42 | 101 of 4,324 | 4,949 | 42 | 0.80 |
| 49 | Z7×Z7 | 2,016 | 116 of 4,324 | 5,684 | 672 | 1.03 |
| 51 | Z51 (circulant) | 32 | 89 of 4,900 | 4,539 | 32 | 1.79 |
| 53 | Z53 (circulant) | 52 | 65 of 5,525 | 3,445 | 4 | 2.34 |
| 55 | Z55 (circulant) | 40 | 80 of 6,201 | 4,400 | 40 | 5.90 |
| 55 | Z11⋊Z5 | 110 | 61 of 6,201 | 3,355 | 440 | 4.95 |
| 57 | Z57 (circulant) | 36 | 57 of 6,930 | 3,249 | 4 | 11.20 |
| 57 | Z19⋊Z3 | 342 | 48 of 6,930 | 2,736 | 684 | 10.28 |
| 59 | Z59 (circulant) | 58 | 58 of 7,714 | 3,422 | 60 | 17.44 |
| 61 | Z61 (circulant) | 60 | 51 of 8,555 | 3,111 | 60 | 38.75 |
| 63 | Z63 (circulant) | 36 | 42 of 9,455 | 2,646 | 72 | 76.73 |
| 63 | Z3×Z21 | 288 | 43 of 9,455 | 2,709 | 96 | 95.43 |
| 63 | Z7⋊Z9 | 126 | **30** of 9,455 | 1,890 | 126 | 89.94 |
| 63 | Z3×(Z7⋊Z3) | 252 | 31 of 9,455 | 1,953 | 504 | 113.28 |
| 65 | Z65 (circulant) | 48 | 38 of 10,416 | 2,470 | 48 | 134.95 |

"Symmetries used" is the size of the automorphism group; its values agree with the known ones
(for example 2,016 = |GL(2,7)| for Z7×Z7, and 110 = 11·10 and 342 = 19·18 for the two groups
Zp⋊Zq). The counts in the last-but-one column are over all connection sets (both halves for the
circulants). Log: [results/nearmiss_k4.txt](compute/results/nearmiss_k4.txt), about ten minutes.

None of these comes close. The best of all, on the group Z7⋊Z9 with 63 players, still leaves
30 kinds of 4-set (1,890 of the 595,665 4-sets) beaten by nobody. The shortfall shrinks roughly
as n grows, from 46 to 116 kinds at 47 to 49 players to 30 to 43 at 63 to 65, and reaches 0 at 67
with the Paley tournament. On 47 players the best circulant is the Paley tournament on 47, and on
59 players the Paley tournament ties for best.

## A heuristic attempt at 66 players (not exhaustive, nothing found)

After the exhaustive search, one cheap long shot was tried: look for a 4-paradoxical
tournament on 66 players, which would show f(4) ≤ 66, starting from the Paley tournament on 67
with one player deleted.

**The starting point (exact computation, C and Python agree).** In the Paley tournament on 67,
22,110 of the 766,480 4-sets are beaten by exactly one player. Deleting a player therefore
leaves exactly 22,110 / 67 = 330 of the 720,720 4-sets beaten by nobody, whichever player is
deleted. That is far closer than any Cayley tournament (the best on 65 players leaves 2,470).

**What the search did** ([compute/local_search.c](compute/local_search.c)). It reverses the
result of one game at a time and keeps an exact running count of unbeaten 4-sets (checked
against a fresh recount at the end of every run).

* Every one of the 2,145 possible single reversals from the start makes things worse, by 29
  to 53 unbeaten 4-sets. Paley-minus-one is a deep local minimum.
* Repairing one unbeaten 4-set per step (a tabu search) drifted up to about 1,200 within
  30 seconds.
* Simulated annealing (uphill moves accepted with a probability that falls as the
  "temperature" drops) has a sharp threshold: at temperature 5 or below the search never
  leaves the start; at 6 to 7 it wanders nearby (about 360 to 420 unbeaten); at 8 or above it
  "melts" into disordered tournaments with about 4,000 unbeaten.
* One batch of 8 independent annealing runs, 20 minutes each (about 5.4 × 10^8 proposed
  reversals in all; [compute/run_local_search.sh](compute/run_local_search.sh), log
  [results/local_search_66.txt](compute/results/local_search_66.txt)). The six runs started
  just below the threshold all slid back to the starting 330 as they cooled and never went
  below it. The two that melted first re-cooled only to about 1,750.

**Outcome.** Nothing below 330 was found. This is a heuristic search, so it proves nothing
about whether a 4-paradoxical tournament on 66 players exists. It only shows that the obvious
route (small edits to Paley-minus-one) does not lead to one. It was run once, as the single
batch above, and not pursued further.

## How the code was checked

All checks pass. [compute/check.py](compute/check.py) shares no code with the search and tests
every k-set of players directly, with no symmetry; its output is
[results/check.txt](compute/results/check.txt) (it takes a few seconds).

* The Paley tournaments on 7, 19 and 67 players are 2-, 3- and 4-paradoxical; the one on 59 is
  not 4-paradoxical (58 kinds of 4-set, that is 3,422 4-sets, are beaten by nobody); those on 7
  and 19 are not 3- and 4-paradoxical. The Python and C counts of unbeaten k-sets agree.
* The same circulant search run for k = 2 finds nothing below 7 players and for k = 3 nothing
  below 19, matching f(2) = 7 and f(3) = 19; on 7 and 19 players its only hits are the Paley
  tournaments ([results/small_k.txt](compute/results/small_k.txt)). Python brute force over all
  connection sets agrees with the C counts for every circulant with k = 2 up to 15 players and
  k = 3 up to 27 players.
* The general group code, run on cyclic groups with no symmetry, gives exactly twice the
  circulant counts (k = 3 for 19 to 31 players; k = 4 for 47, 49, 51 and 67 players, the last
  over all 2^33 sets) ([results/crosscheck.txt](compute/results/crosscheck.txt)).
* For each non-cyclic group, random connection sets give the same number of unbeaten 4-sets in
  Python and C; all 1,024 Cayley tournaments on the non-abelian group of order 21 give the same
  2- and 3-paradoxical counts in both.
* The program checks each group table (identity, inverses, associativity) and prints invariants
  (abelian or not, number of elements of each order) showing the four groups of order 63 are
  different from each other and the groups of order 49, 55 and 57 are not cyclic.
* The example connection set behind each near-miss number is recounted from scratch in Python.
  (That checks the example, not that no better set exists; the minimum itself rests on the C
  search.)

## Which groups

A Cayley tournament needs a group of odd order: an element of order 2 equals its own inverse,
so it cannot be put on just one side of the pair {s, s⁻¹}. The odd orders from 47 to 65 are
47, 53, 59, 61 (prime: only the cyclic group), 51 = 3·17 and 65 = 5·13 (only cyclic, since
3 does not divide 16 and 5 does not divide 12), 49 = 7² (Z49 and Z7×Z7), 55 = 5·11 and
57 = 3·19 (cyclic, and one non-abelian group each since 5 divides 10 and 3 divides 18), and
63 = 3²·7 (four groups: Z63, Z3×Z21, Z7⋊Z9 and Z3×(Z7⋊Z3)). This list is standard group
theory and was not machine-checked here. In the names, Zn is the numbers mod n under addition,
× is the ordinary product (pairs, added coordinate by coordinate), and ⋊ is a twisted product
in which the second factor acts on the first by multiplication; the exact multiplication rules
used are in the comment at the top of [compute/search.c](compute/search.c).

## Lean

Nothing was found, so there is no new tournament to verify. A Lean proof of the negative
result would need a certificate (an unbeaten 4-set) for each of about 10^10 connection sets,
checked inside Lean; that is not practical, so the negative result stays an exact computation.

## Files

* [compute/search.c](compute/search.c) - the search (C, POSIX threads, 128-bit bitsets). The
  comment at the top explains the method; `./search` with no arguments prints usage pointers.
* [compute/check.py](compute/check.py) - the independent checker; `python3 check.py verify FILE`
  checks a tournament given as rows of 0/1.
* [compute/local_search.c](compute/local_search.c) and
  [compute/run_local_search.sh](compute/run_local_search.sh) - the heuristic attempt at 66
  players (about 20 minutes).
* [compute/run_all.sh](compute/run_all.sh) - reruns every search above (about six minutes);
  [compute/run_nearmiss.sh](compute/run_nearmiss.sh) - the near-miss runs.
* [compute/results/](compute/results/) - the logs quoted in this README.
* [novelty-log.md](novelty-log.md) - what was searched for and read on prior work.

To reproduce (needs `clang` and Python 3):

```bash
cd paradoxical-tournaments/compute && ./run_all.sh && ./run_nearmiss.sh && python3 check.py
```
