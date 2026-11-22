#!/bin/sh
# Runs every search reported in ../README.md and writes the logs to results/.
# Takes about six minutes on an 8-core Apple M2. The slower near-miss runs are in run_nearmiss.sh.
set -e
cd "$(dirname "$0")"
clang -O3 -mcpu=native -Wall -Wextra -o search search.c -lpthread
mkdir -p results
T=${THREADS:-8}

{
  echo "# Paley tournaments (x beats y when y - x is a nonzero square mod p)"
  ./search paley 7 2; ./search paley 7 3
  ./search paley 19 3; ./search paley 19 4
  ./search paley 23 4; ./search paley 43 4; ./search paley 47 4; ./search paley 59 4
  ./search paley 67 4; ./search paley 67 5
} > results/paley.txt

{
  echo "# Sanity runs: k = 1, 2, 3 on small cyclic groups"
  for n in 3 5 7; do ./search circ $n 1 $T; done
  for n in 3 5 7 9 11; do ./search circ $n 2 $T; done
  for n in 3 5 7 9 11 13 15 17 19 21 23; do ./search circ $n 3 $T; done
} > results/small_k.txt

{
  echo "# k = 4, circulant tournaments on Z_n, n odd, 5 <= n <= 45 (ruled out by the Szekeres bound)"
  n=5; while [ $n -le 45 ]; do ./search circ $n 4 $T | grep -v '^HIT'; n=$((n + 2)); done
} > results/circ_k4_below47.txt

{
  echo "# k = 4, circulant tournaments on Z_n, n odd, 47 <= n <= 65 (the main search)"
  n=47; while [ $n -le 65 ]; do ./search circ $n 4 $T; n=$((n + 2)); done
} > results/circ_k4_47_65.txt

{
  echo "# k = 4, circulant tournaments on Z_67 (all hits listed, 1 in S)"
  ./search circ 67 4 $T
} > results/circ_k4_67.txt

{
  echo "# k = 4, Cayley tournaments on the non-cyclic groups of odd order 47..65"
  for g in Z7xZ7 Z11:Z5 Z19:Z3 Z3xZ21 Z7:Z9 'Z3x(Z7:Z3)'; do ./search group "$g" 4 $T; done
} > results/groups_k4.txt

{
  echo "# Cross-check: the general group code run on cyclic groups (all S, no symmetry)"
  echo "# must give exactly twice the circulant counts (which assume 1 in S)."
  for n in 19 23 25 27 29 31; do ./search group Z$n 3 $T | grep -v '^HIT'; done
  for n in 47 49 51; do ./search group Z$n 4 $T; done
  ./search group Z67 4 $T
} > results/crosscheck.txt
echo done
