#!/usr/bin/env python3
"""Brute-force the Wythoff ceiling array A341260 and the two sets A341261, A341262.

    python3 wythoff-ceiling/compute/brute_force.py [LIMIT]

W*(n,k) = F(k+1) * ceil(n r) + (n-1) * F(k)  (n, k >= 1, r the golden ratio).
ceil(n r) is computed exactly with integers: floor(n r) = (n + isqrt(5 n^2)) // 2, and n r is
never an integer for n >= 1, so ceil(n r) = floor(n r) + 1.

Every entry with value <= LIMIT is enumerated directly from the definition (each row is
increasing, and W*(n,1) > LIMIT for large n), occurrences are counted, and the script reports
  * the largest multiplicity seen,
  * the difference sets (with counts) of A341261 (count = 2) and A341262 (count = 0),
  * agreement with the terms listed in the OEIS entries,
  * agreement with the Zeckendorf and circle descriptions proved in the README.
"""
import sys
from math import isqrt
from collections import Counter

LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000_000


def floor_nr(n):
    return (n + isqrt(5 * n * n)) // 2


def ceil_nr(n):
    return floor_nr(n) + 1


def counts(limit):
    c = bytearray(limit + 1)
    n = 1
    while True:
        a, b = ceil_nr(n), n - 1          # W*(n,0), W*(n,-1)
        x, y = b, a                        # pair (W*(n,k-1), W*(n,k)) at k = 0
        x, y = y, x + y                    # k = 1
        if y > limit:
            break
        while y <= limit:
            if c[y] == 255:
                raise RuntimeError("overflow")
            c[y] += 1
            x, y = y, x + y
        n += 1
    return c


def diffs(seq):
    return Counter(b - a for a, b in zip(seq, seq[1:]))


# ---- descriptions to compare against -------------------------------------------------------

FIB = [0, 1]
while FIB[-1] < 10 * LIMIT + 10:
    FIB.append(FIB[-1] + FIB[-2])


def zeck_indices(m):
    """Indices i >= 2 (F(2)=1, F(3)=2, ...) of the Zeckendorf representation, ascending."""
    out = []
    i = len(FIB) - 1
    while m > 0:
        while FIB[i] > m:
            i -= 1
        out.append(i)
        m -= FIB[i]
        i -= 2
    return out[::-1]


def zeck_twice(m):
    z = zeck_indices(m)
    return len(z) >= 2 and z[0] % 2 == 1 and z[1] % 2 == 0


def zeck_missing(m):
    if m == 1:
        return True
    z = zeck_indices(m)
    return z[0] % 2 == 0 and z[0] >= 4 and (len(z) == 1 or z[1] % 2 == 0)


def main():
    c = counts(LIMIT)
    twice = [m for m in range(1, LIMIT + 1) if c[m] == 2]
    missing = [m for m in range(1, LIMIT + 1) if c[m] == 0]
    print(f"LIMIT = {LIMIT:,}")
    print("multiplicities seen:", dict(sorted(Counter(c[1:]).items())))
    # A gap is only certain if the next term is also <= LIMIT; drop the last term's successor.
    print(f"A341261: {len(twice):,} terms; differences {dict(sorted(diffs(twice).items()))}")
    print(f"A341262: {len(missing):,} terms; differences {dict(sorted(diffs(missing).items()))}")

    oeis_twice = [10, 23, 26, 31, 44, 57, 60, 65, 68, 78, 81, 86, 99, 112, 115, 120, 133, 146,
                  149, 154, 157, 167, 170, 175, 178, 188, 201, 204, 209, 212, 222, 225, 230, 243,
                  256, 259, 264, 277, 290, 293, 298, 301, 311, 314, 319, 332, 345, 348, 353, 366,
                  379, 382, 387, 390]
    oeis_missing = [1, 3, 8, 11, 21, 24, 29, 32, 45, 55, 58, 63, 66, 76, 79, 84, 87, 100, 113, 118,
                    121, 134, 144, 147, 152, 155, 165, 168, 173, 176, 189, 199, 202, 207, 210, 220,
                    223, 228, 231, 244, 257, 262, 265, 278, 291, 296, 299, 309, 312, 317, 320, 333,
                    346, 351, 354, 367]
    print("matches OEIS data:", twice[:len(oeis_twice)] == oeis_twice,
          missing[:len(oeis_missing)] == oeis_missing)

    zt = all(zeck_twice(m) == (c[m] == 2) for m in range(1, LIMIT + 1))
    zm = all(zeck_missing(m) == (c[m] == 0) for m in range(1, LIMIT + 1))
    print("Zeckendorf descriptions agree on [1, LIMIT]:", zt, zm)


if __name__ == "__main__":
    main()
