/*
 * local_search.c - heuristic search for a 4-paradoxical tournament on 66 players.
 *
 * Start: the Paley tournament on 67 players (x beats y when y - x is a nonzero square mod 67)
 * with player 66 deleted. That leaves 330 of the C(66,4) = 720,720 4-sets beaten by nobody
 * ("unbeaten"). The search changes the result of one game at a time (x beats y becomes y beats
 * x) and tries to drive the number of unbeaten 4-sets to zero.
 *
 * Two methods.
 *
 * "tabu" (min-conflicts tabu search). One step:
 *   pick an unbeaten 4-set A at random; for every player x outside A that beats three of the
 *   four members of A, flipping the one remaining game makes x beat all of A. Among these
 *   candidate flips, take the one giving the fewest unbeaten 4-sets afterwards (or, with
 *   probability NOISE, a random one), skipping games flipped in the last TENURE steps unless
 *   the flip would beat the best count seen so far. If no player beats three members, use
 *   players beating two (two flips).
 *
 * "anneal" (simulated annealing). Each step proposes one flip: half the time a repair flip as
 *   above (a random unbeaten 4-set, a random outsider beating three of its members), otherwise
 *   a random game. A flip that does not increase the count is always made; one that increases
 *   it by d is made with probability exp(-d/T). The temperature T falls geometrically from T0
 *   to T1 over the run.
 *
 * For every 4-set the program keeps the number of players beating all four, and updates it
 * after a flip by looking only at the 4-sets the flip can affect. If the count of unbeaten
 * 4-sets reaches zero, the tournament is written out and should be checked with check.py.
 * This search is NOT exhaustive: if it fails, that says nothing about whether such a
 * tournament exists.
 *
 * Usage: local_search tabu   SEED NOISE TENURE SECONDS [OUTFILE]
 *        local_search anneal SEED T0 T1 SECONDS [OUTFILE]
 *        local_search scan                  (effect of every single flip from the start)
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef unsigned __int128 u128;
#define N 66
#define P 67
#define BIT(i) (((u128)1) << (i))
#define NSETS 720720                 /* C(66,4) */

static u128 OUT[N], IN[N];           /* OUT[x]: players x beats; IN[x]: players beating x */
static uint8_t D[NSETS];             /* number of players beating all of the 4-set */
static int UL[NSETS], UPOS[NSETS];   /* list of unbeaten 4-sets, position in list or -1 */
static uint32_t UM[NSETS];           /* members of list entries, packed 4 x 8 bits */
static int NU;                       /* number of unbeaten 4-sets */
static int C[N + 1][5];
static long TABU[N][N];

static uint64_t rng_s = 88172645463325252ULL;
static uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static inline int idx4(int a, int b, int c, int d) { return C[a][1] + C[b][2] + C[c][3] + C[d][4]; }

/* index of the sorted triple a<b<c with x inserted; also returns the packed members */
static inline int idx_ins(int a, int b, int c, int x, uint32_t *pk) {
    int s0, s1, s2, s3;
    if (x < a) { s0 = x; s1 = a; s2 = b; s3 = c; }
    else if (x < b) { s0 = a; s1 = x; s2 = b; s3 = c; }
    else if (x < c) { s0 = a; s1 = b; s2 = x; s3 = c; }
    else { s0 = a; s1 = b; s2 = c; s3 = x; }
    *pk = (uint32_t)s0 | (uint32_t)s1 << 8 | (uint32_t)s2 << 16 | (uint32_t)s3 << 24;
    return idx4(s0, s1, s2, s3);
}

static inline void ul_add(int i, uint32_t pk) { UPOS[i] = NU; UL[NU] = i; UM[NU] = pk; NU++; }
static inline void ul_del(int i) {
    int p = UPOS[i], last = UL[NU - 1];
    UL[p] = last; UM[p] = UM[NU - 1]; UPOS[last] = p; UPOS[i] = -1; NU--;
}

static int list_bits(u128 m, int *e) {
    int k = 0;
    uint64_t lo = (uint64_t)m, hi = (uint64_t)(m >> 64);
    while (lo) { e[k++] = __builtin_ctzll(lo); lo &= lo - 1; }
    while (hi) { e[k++] = 64 + __builtin_ctzll(hi); hi &= hi - 1; }
    return k;
}

/* change in the number of unbeaten 4-sets if the game u -> w (u beats w) is reversed */
static int delta_flip(int u, int w) {
    int e[N], k, d = 0;
    uint32_t pk;
    /* 4-sets {w} + B, B in OUT[u] \ {w}: u stops beating them */
    k = list_bits(OUT[u] & ~BIT(w), e);
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) for (int l = j + 1; l < k; l++)
        if (D[idx_ins(e[i], e[j], e[l], w, &pk)] == 1) d++;
    /* 4-sets {u} + B, B in OUT[w]: w starts beating them */
    k = list_bits(OUT[w], e);
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) for (int l = j + 1; l < k; l++)
        if (D[idx_ins(e[i], e[j], e[l], u, &pk)] == 0) d--;
    return d;
}

/* reverse the game u -> w and update all counts */
static void apply_flip(int u, int w) {
    int e[N], k;
    uint32_t pk;
    k = list_bits(OUT[u] & ~BIT(w), e);
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) for (int l = j + 1; l < k; l++) {
        int s = idx_ins(e[i], e[j], e[l], w, &pk);
        if (--D[s] == 0) ul_add(s, pk);
    }
    k = list_bits(OUT[w], e);
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) for (int l = j + 1; l < k; l++) {
        int s = idx_ins(e[i], e[j], e[l], u, &pk);
        if (D[s]++ == 0) ul_del(s);
    }
    OUT[u] ^= BIT(w); IN[w] ^= BIT(u);
    OUT[w] ^= BIT(u); IN[u] ^= BIT(w);
}

/* recompute all counts from scratch; returns number of unbeaten 4-sets */
static int recount(int check) {
    int bad = 0, n0 = 0;
    for (int d = 3; d < N; d++) for (int c = 2; c < d; c++) for (int b = 1; b < c; b++) for (int a = 0; a < b; a++) {
        u128 m = IN[a] & IN[b] & IN[c] & IN[d];
        int cnt = __builtin_popcountll((uint64_t)m) + __builtin_popcountll((uint64_t)(m >> 64));
        int s = idx4(a, b, c, d);
        if (check) { if (D[s] != cnt) bad++; }
        else {
            D[s] = (uint8_t)cnt;
            UPOS[s] = -1;
            if (!cnt) ul_add(s, (uint32_t)a | (uint32_t)b << 8 | (uint32_t)c << 16 | (uint32_t)d << 24);
        }
        if (!cnt) n0++;
    }
    if (check && bad) { fprintf(stderr, "count mismatch in %d sets\n", bad); exit(1); }
    return n0;
}

int main(int argc, char **argv) {
    int scan = argc >= 2 && !strcmp(argv[1], "scan");
    if (!scan && (argc < 6 || (strcmp(argv[1], "tabu") && strcmp(argv[1], "anneal")))) {
        fprintf(stderr, "usage: local_search tabu|anneal SEED P1 P2 SECONDS [OUTFILE]\n");
        return 1;
    }
    int anneal = !scan && !strcmp(argv[1], "anneal");
    long seed = scan ? 1 : atol(argv[2]);
    double noise = scan ? 0 : atof(argv[3]), T0 = noise;
    int tenure = scan ? 0 : atoi(argv[4]);
    double T1 = scan ? 0 : atof(argv[4]);
    double seconds = scan ? 0 : atof(argv[5]);
    const char *outfile = argc > 6 ? argv[6] : "found_66.txt";
    rng_s ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 20; i++) rnd();

    for (int n = 0; n <= N; n++) for (int k = 0; k <= 4; k++) {
        long v = 1;
        for (int i = 0; i < k; i++) v = v * (n - i) / (i + 1);
        C[n][k] = n >= k ? (int)v : 0;
    }
    if (C[N][4] != NSETS) { fprintf(stderr, "binomial\n"); return 1; }

    /* Paley 67 minus player 66 */
    int sq[P] = {0};
    for (int x = 1; x < P; x++) sq[x * x % P] = 1;
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++)
        if (x != y && sq[((y - x) % P + P) % P]) { OUT[x] |= BIT(y); IN[y] |= BIT(x); }
    NU = 0;
    recount(0);
    int best = NU;
    printf("start: Paley 67 minus one player, %d unbeaten 4-sets of %d\n", NU, NSETS);
    fflush(stdout);

    if (scan) {                        /* report the effect of every single flip from the start */
        int hist[2000] = {0}, mn = 1 << 30;
        for (int u = 0; u < N; u++) for (int w = 0; w < N; w++)
            if ((OUT[u] >> w) & 1) { int d = delta_flip(u, w); if (d < mn) mn = d; hist[d + 1000]++; }
        printf("single flips from the start: best change %+d; changes:", mn);
        for (int i = 0; i < 2000; i++) if (hist[i]) printf(" %+d:%d", i - 1000, hist[i]);
        printf("\n");
        return 0;
    }
    double t0 = now(), last = t0;
    long step = 0;
    u128 BEST_OUT[N];
    memcpy(BEST_OUT, OUT, sizeof OUT);
    if (anneal) {
        double T = T0;
        long accepted = 0;
        while (NU > 0) {
            step++;
            int u, w;
            int e[N];
            if ((rnd() & 1) && NU > 0) {
                uint32_t pk = UM[rnd() % (uint64_t)NU];
                int A[4] = {pk & 255, (pk >> 8) & 255, (pk >> 16) & 255, (int)(pk >> 24)};
                u128 Am = BIT(A[0]) | BIT(A[1]) | BIT(A[2]) | BIT(A[3]);
                int xs[N], nx = 0;
                for (int x = 0; x < N; x++) {
                    if (Am & BIT(x)) continue;
                    u128 m = IN[x] & Am;
                    if (__builtin_popcountll((uint64_t)m) + __builtin_popcountll((uint64_t)(m >> 64)) == 1) xs[nx++] = x;
                }
                if (!nx) continue;
                w = xs[rnd() % (uint64_t)nx];
                list_bits(IN[w] & Am, e);
                u = e[0];
            } else {
                u = (int)(rnd() % N);
                int k = list_bits(OUT[u], e);
                if (!k) continue;
                w = e[rnd() % (uint64_t)k];
            }
            int d = delta_flip(u, w);
            if (d <= 0 || rnd01() < exp(-d / T)) {
                apply_flip(u, w);
                accepted++;
                if (NU < best) { best = NU; memcpy(BEST_OUT, OUT, sizeof OUT); }
            }
            if ((step & 1023) == 0 || NU == 0) {
                double t = now();
                T = T0 * pow(T1 / T0, (t - t0) / seconds);
                if (t - last > 60 || NU == 0) {
                    printf("t=%.0fs steps=%ld T=%.3f unbeaten=%d best=%d accepted=%ld\n", t - t0, step, T, NU, best, accepted);
                    fflush(stdout);
                    last = t;
                }
                if (t - t0 > seconds) break;
            }
        }
    }
    while (!anneal && NU > 0) {
        step++;
        int pick = (int)(rnd() % (uint64_t)NU);
        uint32_t pk = UM[pick];
        int A[4] = {pk & 255, (pk >> 8) & 255, (pk >> 16) & 255, (int)(pk >> 24)};
        u128 Am = BIT(A[0]) | BIT(A[1]) | BIT(A[2]) | BIT(A[3]);
        /* candidates: (u, w, u2, w2) flips; u2 < 0 when a single flip */
        int cu[N][4], nc = 0, need = 1;
        for (int pass = 0; pass < 2 && nc == 0; pass++, need++) {
            for (int x = 0; x < N; x++) {
                if (Am & BIT(x)) continue;
                u128 m = IN[x] & Am;          /* members of A that beat x */
                int k = __builtin_popcountll((uint64_t)m) + __builtin_popcountll((uint64_t)(m >> 64));
                if (k != need) continue;
                int e[4];
                list_bits(m, e);
                cu[nc][0] = e[0]; cu[nc][1] = x;
                cu[nc][2] = need == 2 ? e[1] : -1; cu[nc][3] = x;
                nc++;
            }
        }
        if (nc == 0) {                   /* every outsider loses to 3+ members: pick again */
            if (now() - t0 > seconds) break;
            continue;
        }
        int bestc = -1, bestd = 1 << 30, ties = 0;
        for (int c = 0; c < nc; c++) {
            int d;
            if (cu[c][2] < 0) d = delta_flip(cu[c][0], cu[c][1]);
            else {
                int d1 = 0;
                apply_flip(cu[c][0], cu[c][1]);
                d1 = delta_flip(cu[c][2], cu[c][3]);
                apply_flip(cu[c][1], cu[c][0]);  /* undo */
                d = delta_flip(cu[c][0], cu[c][1]) + d1;
            }
            int tabu = TABU[cu[c][0]][cu[c][1]] > step || (cu[c][2] >= 0 && TABU[cu[c][2]][cu[c][3]] > step);
            if (tabu && NU + d >= best) continue;
            if (d < bestd) { bestd = d; bestc = c; ties = 1; }
            else if (d == bestd && rnd() % (uint64_t)(++ties) == 0) bestc = c;
        }
        if (bestc < 0 || rnd01() < noise) bestc = (int)(rnd() % (uint64_t)nc);
        int c = bestc;
        apply_flip(cu[c][0], cu[c][1]);
        TABU[cu[c][0]][cu[c][1]] = TABU[cu[c][1]][cu[c][0]] = step + tenure;
        if (cu[c][2] >= 0) {
            apply_flip(cu[c][2], cu[c][3]);
            TABU[cu[c][2]][cu[c][3]] = TABU[cu[c][3]][cu[c][2]] = step + tenure;
        }
        if (NU < best) { best = NU; memcpy(BEST_OUT, OUT, sizeof OUT); }
        double t = now();
        if (t - last > 30 || NU == 0) {
            printf("t=%.0fs steps=%ld unbeaten=%d best=%d\n", t - t0, step, NU, best);
            fflush(stdout);
            last = t;
        }
        if (t - t0 > seconds) break;
    }
    recount(1);                        /* the maintained counts must match a fresh count */
    if (anneal)
        printf("FINAL anneal seed=%ld T0=%.3f T1=%.3f steps=%ld seconds=%.0f best=%d current=%d\n",
               seed, T0, T1, step, now() - t0, best, NU);
    else
        printf("FINAL tabu seed=%ld noise=%.3f tenure=%d steps=%ld seconds=%.0f best=%d current=%d\n",
               seed, noise, tenure, step, now() - t0, best, NU);
    if (best == 0) {
        FILE *f = fopen(outfile, "w");
        for (int x = 0; x < N; x++) {
            for (int y = 0; y < N; y++) fputc((BEST_OUT[x] >> y) & 1 ? '1' : '0', f);
            fputc('\n', f);
        }
        fclose(f);
        printf("FOUND: tournament written to %s (row x, column y is 1 when x beats y)\n", outfile);
    }
    return 0;
}
