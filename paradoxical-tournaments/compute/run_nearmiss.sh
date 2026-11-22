#!/bin/sh
# "How close" runs: for each family, the smallest number of 4-set classes left undominated by
# any connection set. Uses the automorphism group of each group to test one set per orbit.
# Writes results/nearmiss_k4.txt. Takes about ten minutes on an 8-core Apple M2.
set -e
cd "$(dirname "$0")"
clang -O3 -mcpu=native -Wall -Wextra -o search search.c -lpthread
mkdir -p results
T=${THREADS:-8}
{
  echo "# k = 4, smallest number of undominated 4-set classes (min mode)"
  ./search paley 47 4; ./search paley 59 4
  n=47; while [ $n -le 65 ]; do ./search circ $n 4 $T min; n=$((n + 2)); done
  for g in Z7xZ7 Z11:Z5 Z19:Z3 Z3xZ21 Z7:Z9 'Z3x(Z7:Z3)'; do ./search group "$g" 4 $T min; done
} > results/nearmiss_k4.txt
echo done
