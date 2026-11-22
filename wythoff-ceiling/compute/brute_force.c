/* Brute force for the Wythoff ceiling array A341260, to larger limits than brute_force.py.

     cc -O2 -o /tmp/wc wythoff-ceiling/compute/brute_force.c && /tmp/wc 1000000000

   Counts how often each m <= LIMIT occurs as W*(n,k) = F(k+1) ceil(n r) + (n-1) F(k), n,k >= 1,
   then prints the multiplicities seen, the difference sets of A341261 (count 2) and A341262
   (count 0) with how often each difference occurs, and checks the Zeckendorf descriptions:
     count 2  <=>  lowest Zeckendorf index odd and second-lowest index even   (F(2)=1, F(3)=2,...)
     count 0  <=>  m = 1, or lowest index even >= 4 and second-lowest index even or absent.
   ceil(n r) is exact: floor(n r) = (n + isqrt(5 n^2)) / 2 and n r is never an integer. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

static uint64_t isqrt64(uint64_t v) {
    uint64_t s = (uint64_t)sqrtl((long double)v);
    while (s * s > v) s--;
    while ((s + 1) * (s + 1) <= v) s++;
    return s;
}

int main(int argc, char **argv) {
    uint64_t L = argc > 1 ? strtoull(argv[1], 0, 10) : 1000000000ULL;
    unsigned char *c = calloc(L + 1, 1);
    if (!c) { fprintf(stderr, "out of memory\n"); return 1; }
    for (uint64_t n = 1;; n++) {
        uint64_t a = (n + isqrt64(5 * n * n)) / 2 + 1;   /* ceil(n r) = W*(n,0) */
        uint64_t x = a, y = a + (n - 1);                 /* W*(n,0), W*(n,1) */
        if (y > L) break;
        while (y <= L) { c[y]++; uint64_t z = x + y; x = y; y = z; }
    }
    uint64_t fib[100]; int nf = 2; fib[0] = 0; fib[1] = 1;
    while (fib[nf - 1] <= 4 * L) { fib[nf] = fib[nf - 1] + fib[nf - 2]; nf++; }

    uint64_t mult[256] = {0}, d2[64] = {0}, d0[64] = {0}, big2 = 0, big0 = 0, bad = 0;
    uint64_t last2 = 0, last0 = 0;
    for (uint64_t m = 1; m <= L; m++) {
        mult[c[m]]++;
        if (c[m] == 2) { if (last2) { uint64_t g = m - last2; if (g < 64) d2[g]++; else big2++; } last2 = m; }
        if (c[m] == 0) { if (last0) { uint64_t g = m - last0; if (g < 64) d0[g]++; else big0++; } last0 = m; }
        /* Zeckendorf: lowest two indices */
        uint64_t v = m; int i0 = -1, i1 = -1, i = nf - 1;
        while (v) { while (fib[i] > v) i--; v -= fib[i]; i1 = i0; i0 = i; i -= 2; }
        int twice = (i1 >= 0 && i0 % 2 == 1 && i1 % 2 == 0);
        int missing = (m == 1) || (i0 % 2 == 0 && i0 >= 4 && (i1 < 0 || i1 % 2 == 0));
        if (twice != (c[m] == 2) || missing != (c[m] == 0)) bad++;
    }
    printf("LIMIT = %llu\nmultiplicities:", (unsigned long long)L);
    for (int k = 0; k < 256; k++) if (mult[k]) printf(" %d:%llu", k, (unsigned long long)mult[k]);
    printf("\nA341261 differences:");
    for (int g = 0; g < 64; g++) if (d2[g]) printf(" %d:%llu", g, (unsigned long long)d2[g]);
    printf("  (>=64: %llu)\nA341262 differences:", (unsigned long long)big2);
    for (int g = 0; g < 64; g++) if (d0[g]) printf(" %d:%llu", g, (unsigned long long)d0[g]);
    printf("  (>=64: %llu)\nZeckendorf description mismatches: %llu\n",
           (unsigned long long)big0, (unsigned long long)bad);
    return 0;
}
