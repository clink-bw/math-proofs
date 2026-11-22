/* Exact {2}-domination numbers of the m x n grid for larger heights m.

     cc -O2 -o fast fast.c -lpthread
     ./fast M NMAX [THREADS [WMAX]]

   With WMAX, also prints for every n <= WMAX one optimal list of columns ("word n weight: c_1
   ... c_n", each column a base-3 number, digit i = weight in row i).  check_words.py verifies
   those lists directly against the definition, so the upper bounds do not depend on this
   program being correct.

   Same column automaton as strip.py and lean/GridDomination/Automaton.lean:
   a state is (b, nu), b the last column and nu what the next column must still supply, both
   vectors in {0,1,2}^M written in base 3; reading column d >= nu leads to (d, need(b, d)).

   v_n[s] = least weight of n columns leading from the start to state s.  One step is
       v_{n+1}[(d, need(b,d))] = weight(d) + min { v_n[(b, nu)] : nu <= d }.
   For each b the inner minimum is computed for all d at once by running minima along each of
   the M coordinates, so a step costs about M * 9^M operations.

   The program prints gamma(n) = min over final states (nu = 0) of v_n, and reports the first
   N and the least p for which v_{N+p} = v_N + q entrywise.  Since a step commutes with adding
   a constant to every entry, that identity gives v_{n+p} = v_n + q for all n >= N, hence
   gamma(n+p) = gamma(n) + q for all n >= N. */

#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXM 10
#define INF 1000000000
#ifndef RING
#define RING 96
#endif

static int M, NCOL, NST, NTHREADS = 1;
static int pow3[MAXM + 1];
static int *offs;        /* offs[d]: index of the first state with last column d            */
static int *wtcol;       /* weight of column d                                              */
static int8_t *tauv;     /* tauv[d*M+i] = min(2, own + vertical neighbours of row i)        */
static int *radp;        /* radp[d*M+i] = product of the radices of rows < i for column d   */
static inline int dg(int c, int i) { return c / pow3[i] % 3; }

static int32_t *cur, *nxt;
static int32_t **nxt_thr;
static int16_t **histw;  /* histw[j] = v_j (capped), kept for j <= WMAX to recover optimal lists */
#define INF16 32767

/* Recover one optimal list of n columns by walking back from the best final state. */
static void print_word(int n) {
    int t = -1, best = INF16;
    for (int d = 0; d < NCOL; d++)
        if (histw[n][offs[d]] < best) { best = histw[n][offs[d]]; t = offs[d]; }
    int *cols = malloc(sizeof(int) * (n + 1));
    for (int j = n; j >= 1; j--) {
        int lo = 0, hi = NCOL - 1;                 /* column d of state t: offs[d] <= t */
        while (lo < hi) {
            int mid = (lo + hi + 1) / 2;
            if (offs[mid] <= t) lo = mid; else hi = mid - 1;
        }
        int d = lo, found = -1;
        cols[j] = d;
        for (int b = 0; b < NCOL && found < 0; b++) {
            int tt = offs[d];
            for (int i = 0; i < M; i++) {
                int need = 2 - dg(b, i) - tauv[d * M + i];
                if (need > 0) tt += need * radp[d * M + i];
            }
            if (tt != t) continue;
            int cnt = offs[b + 1] - offs[b];
            for (int r = 0; r < cnt && found < 0; r++) {
                int val = histw[j - 1][offs[b] + r];
                if (val >= INF16 || val + wtcol[d] != histw[j][t]) continue;
                int rr = r, ok = 1;
                for (int i = 0; i < M && ok; i++) {
                    int rad = 3 - tauv[b * M + i];
                    if (rr % rad > dg(d, i)) ok = 0;
                    rr /= rad;
                }
                if (ok) found = offs[b] + r;
            }
        }
        if (found < 0) { fprintf(stderr, "backtrack failed at n=%d j=%d\n", n, j); exit(3); }
        t = found;
    }
    printf("word %d %d:", n, best);
    for (int j = 1; j <= n; j++) printf(" %d", cols[j]);
    printf("\n");
    free(cols);
}


static void setup(void) {
    pow3[0] = 1;
    for (int i = 1; i <= MAXM; i++) pow3[i] = pow3[i - 1] * 3;
    NCOL = pow3[M];
    offs = malloc(sizeof(int) * (NCOL + 1));
    wtcol = malloc(sizeof(int) * NCOL);
    tauv = malloc((size_t)NCOL * M);
    radp = malloc(sizeof(int) * (size_t)NCOL * M);
    int total = 0;
    for (int d = 0; d < NCOL; d++) {
        offs[d] = total;
        int w = 0, prod = 1;
        for (int i = 0; i < M; i++) {
            int t = dg(d, i) + (i > 0 ? dg(d, i - 1) : 0) + (i + 1 < M ? dg(d, i + 1) : 0);
            if (t > 2) t = 2;
            tauv[d * M + i] = (int8_t)t;
            radp[d * M + i] = prod;
            prod *= 3 - t;
            w += dg(d, i);
        }
        wtcol[d] = w;
        total += prod;
    }
    offs[NCOL] = total;
    NST = total;
}

typedef struct { int tid; } job_t;

/* Process all last columns b with b % NTHREADS == tid, writing into nxt_thr[tid]. */
static void *worker(void *arg) {
    int tid = ((job_t *)arg)->tid;
    int32_t *out = nxt_thr[tid];
    int32_t *A = malloc(sizeof(int32_t) * NCOL);
    int bd[MAXM];
    for (int s = 0; s < NST; s++) out[s] = INF;
    for (int b = tid; b < NCOL; b += NTHREADS) {
        /* A[nu] = cur[(b, nu)] if nu is a possible need vector after b, else INF */
        for (int x = 0; x < NCOL; x++) A[x] = INF;
        int cnt = offs[b + 1] - offs[b];
        int any = 0;
        for (int r = 0; r < cnt; r++) {
            int32_t val = cur[offs[b] + r];
            if (val >= INF) continue;
            any = 1;
            int nu = 0, rr = r;
            for (int i = 0; i < M; i++) {
                int rad = 3 - tauv[b * M + i];
                nu += (rr % rad) * pow3[i];
                rr /= rad;
            }
            A[nu] = val;
        }
        if (!any) continue;
        /* running minimum along each coordinate: A[d] = min over nu <= d */
        for (int i = 0; i < M; i++) {
            int step = pow3[i];
            for (int x = 0; x < NCOL; x++) {
                if (x / step % 3 != 0) {
                    int32_t y = A[x - step];
                    if (y < A[x]) A[x] = y;
                }
            }
        }
        for (int i = 0; i < M; i++) bd[i] = dg(b, i);
        for (int d = 0; d < NCOL; d++) {
            int32_t val = A[d];
            if (val >= INF) continue;
            int t = offs[d];
            const int8_t *tv = tauv + (size_t)d * M;
            const int *rp = radp + (size_t)d * M;
            for (int i = 0; i < M; i++) {
                int need = 2 - bd[i] - tv[i];
                if (need > 0) t += need * rp[i];
            }
            val += wtcol[d];
            if (val < out[t]) out[t] = val;
        }
    }
    free(A);
    return NULL;
}

static void step(void) {
    pthread_t th[64];
    job_t jobs[64];
    for (int t = 0; t < NTHREADS; t++) {
        jobs[t].tid = t;
        pthread_create(&th[t], NULL, worker, &jobs[t]);
    }
    for (int t = 0; t < NTHREADS; t++) pthread_join(th[t], NULL);
    for (int s = 0; s < NST; s++) {
        int32_t best = INF;
        for (int t = 0; t < NTHREADS; t++)
            if (nxt_thr[t][s] < best) best = nxt_thr[t][s];
        nxt[s] = best;
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: fast M NMAX [THREADS]\n"); return 1; }
    M = atoi(argv[1]);
    int nmax = atoi(argv[2]);
    if (argc > 3) NTHREADS = atoi(argv[3]);
    int wmax = argc > 4 ? atoi(argv[4]) : 0;
    if (wmax > nmax) wmax = nmax;
    if (M < 1 || M > MAXM || NTHREADS < 1 || NTHREADS > 64) return 1;
    setup();
    fprintf(stderr, "m=%d: %d states\n", M, NST);
    cur = malloc(sizeof(int32_t) * NST);
    nxt = malloc(sizeof(int32_t) * NST);
    nxt_thr = malloc(sizeof(int32_t *) * NTHREADS);
    for (int t = 0; t < NTHREADS; t++) nxt_thr[t] = malloc(sizeof(int32_t) * NST);
    int32_t **ring = malloc(sizeof(int32_t *) * RING);
    for (int i = 0; i < RING; i++) ring[i] = malloc(sizeof(int32_t) * NST);
    int *gam = malloc(sizeof(int) * (nmax + 1));
    for (int s = 0; s < NST; s++) cur[s] = INF;
    cur[0] = 0;                                   /* the start state (0, 0) has index 0 */
    memcpy(ring[0], cur, sizeof(int32_t) * NST);
    gam[0] = 0;
    if (wmax > 0) {
        histw = malloc(sizeof(int16_t *) * (wmax + 1));
        for (int j = 0; j <= wmax; j++) histw[j] = malloc(sizeof(int16_t) * NST);
        for (int s = 0; s < NST; s++) histw[0][s] = cur[s] >= INF16 ? INF16 : (int16_t)cur[s];
    }
    int foundN = -1, foundp = 0, foundq = 0;
    printf("m=%d states=%d\ngamma:", M, NST);
    for (int n = 1; n <= nmax; n++) {
        step();
        int32_t *tmp = cur; cur = nxt; nxt = tmp;
        memcpy(ring[n % RING], cur, sizeof(int32_t) * NST);
        if (n <= wmax)
            for (int s = 0; s < NST; s++) histw[n][s] = cur[s] >= INF16 ? INF16 : (int16_t)cur[s];
        int best = INF;
        for (int d = 0; d < NCOL; d++)            /* final states: (d, 0), index offs[d] */
            if (cur[offs[d]] < best) best = cur[offs[d]];
        gam[n] = best;
        printf(" %d", best);
        fflush(stdout);
        if (foundN < 0) {
            for (int p = 1; p < RING && p <= n && foundN < 0; p++) {
                int32_t *old = ring[(n - p) % RING];
                if (old[0] >= INF) continue;
                int32_t q = cur[0] - old[0];
                int ok = 1;
                for (int s = 0; s < NST && ok; s++)
                    if (old[s] >= INF || cur[s] - old[s] != q) ok = 0;
                if (ok) { foundN = n - p; foundp = p; foundq = q; }
            }
            if (foundN >= 0 && n + 2 * foundp < nmax)                         /* a little extra */
                nmax = n + 2 * foundp > wmax ? n + 2 * foundp : wmax;
        }
    }
    printf("\n");
    for (int n = 1; n <= wmax; n++) print_word(n);
    if (foundN < 0) { printf("no periodicity found up to n=%d\n", nmax); return 0; }
    printf("periodicity: N=%d p=%d q=%d   (v_{n+p} = v_n + q for all n >= N)\n", foundN, foundp,
           foundq);
    /* p*gamma(n) - q*n over one period */
    int lo = INF, hi = -INF;
    printf("p*gamma - q*n for n = N .. N+p-1:");
    for (int n = foundN; n < foundN + foundp; n++) {
        int r = foundp * gam[n] - foundq * n;
        printf(" %d", r);
        if (r < lo) lo = r;
        if (r > hi) hi = r;
    }
    printf("\n");
    if (hi - lo < foundp) {
        printf("so gamma(n) = ceil((%d n + %d) / %d) for all n >= N; exceptions below N:", foundq,
               lo, foundp);
        for (int n = 1; n < foundN; n++) {
            int num = foundq * n + lo;
            int f = (num + foundp - 1) / foundp;
            if (gam[n] != f) printf(" %d(%+d)", n, gam[n] - f);
        }
        printf("\n");
    } else {
        printf("not a single ceiling formula (spread %d >= p)\n", hi - lo);
    }
    return 0;
}
