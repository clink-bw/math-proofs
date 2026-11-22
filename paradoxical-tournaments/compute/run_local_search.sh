#!/bin/sh
# One batch of 8 independent heuristic runs (20 minutes each, in parallel) looking for a
# 4-paradoxical tournament on 66 players, starting from the Paley tournament on 67 players
# with one player deleted. Writes results/local_search_66.txt. Not an exhaustive search.
set -e
cd "$(dirname "$0")"
clang -O3 -mcpu=native -Wall -Wextra -o local_search local_search.c
mkdir -p results
SECS=${SECS:-1200}
TMP=$(mktemp -d)
i=0
for cfg in "11 7.5 1" "12 7.5 1" "13 7.5 1" "14 7 2" "15 7 2" "16 6.5 2" "17 9 1" "18 12 1"; do
  set -- $cfg
  ./local_search anneal "$1" "$2" "$3" "$SECS" "found_66_seed$1.txt" > "$TMP/run$1.txt" &
done
wait
{
  echo "# 8 simulated-annealing runs, $SECS s each, from Paley 67 minus one player (330 unbeaten 4-sets)"
  ./local_search scan
  for f in "$TMP"/run*.txt; do cat "$f"; done
} > results/local_search_66.txt
rm -r "$TMP"
grep FINAL results/local_search_66.txt
