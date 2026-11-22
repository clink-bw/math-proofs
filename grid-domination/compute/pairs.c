/* Independent check of fast.c by a different dynamic programme.

     cc -O2 -o pairs pairs.c
     ./pairs M NMAX [N P Q]

   For nine rows the table has 9^9 entries; compile with -DSMALL to store one byte per entry
   (enough while all values stay below 255, which the program checks).

   Here a state is simply the pair (a, b) of the last two columns; nothing is compressed.
   V_n[a][b] = least weight of n columns ending in a, b such that columns 1..n-1 are dominated.
   Column b (between a and c) is dominated exactly when a >= r(b, c) in every row, where
       r(b, c)_i = max(0, 2 - c_i - b_i - b_{i-1} - b_{i+1}),
   so   V_{n+1}[b][c] = weight(c) + min { V_n[a][b] : a >= r(b, c) },
   and  gamma(n)      = min over b of     min { V_n[a][b] : a >= r(b, 0) }.
   For each b the minima over all upper sets are computed by running minima along each row.

   Prints gamma(1..NMAX).  If N P Q are given (as reported by fast.c), also checks that
   V_{N+1+P} = V_{N+1} + Q in every entry, which is the same periodicity statement for this
   programme (V_{n+1} is a function of the vector v_n of fast.c, and conversely). */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXM 9
#ifdef SMALL
typedef uint8_t cell_t;
#define INF 255
#else
typedef uint16_t cell_t;
#define INF 65535
#endif

static int M, NCOL;
static int pow3[MAXM + 1];

static inline int dg(int c, int i) { return c / pow3[i] % 3; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: pairs M NMAX [N P Q]\n"); return 1; }
    M = atoi(argv[1]);
    int nmax = atoi(argv[2]);
    int chkN = -1, chkP = 0, chkQ = 0;
    if (argc >= 6) { chkN = atoi(argv[3]); chkP = atoi(argv[4]); chkQ = atoi(argv[5]); }
    if (M < 1 || M > MAXM) return 1;
    pow3[0] = 1;
    for (int i = 1; i <= MAXM; i++) pow3[i] = pow3[i - 1] * 3;
    NCOL = pow3[M];
    size_t SZ = (size_t)NCOL * NCOL;
    /* V[b * NCOL + a] */
    cell_t *V = malloc(SZ * sizeof(cell_t)), *W = malloc(SZ * sizeof(cell_t)), *snap = NULL;
    cell_t *T = malloc((size_t)NCOL * sizeof(cell_t));
    int *wt = malloc(sizeof(int) * NCOL);
    int8_t *tau = malloc((size_t)NCOL * M);
    if (chkN >= 0) snap = malloc(SZ * sizeof(cell_t));
    if (!V || !W || !T || (chkN >= 0 && !snap)) { fprintf(stderr, "out of memory\n"); return 2; }
    for (int d = 0; d < NCOL; d++) {
        int w = 0;
        for (int i = 0; i < M; i++) {
            int t = dg(d, i) + (i > 0 ? dg(d, i - 1) : 0) + (i + 1 < M ? dg(d, i + 1) : 0);
            tau[d * M + i] = (int8_t)(t > 2 ? 2 : t);
            w += dg(d, i);
        }
        wt[d] = w;
    }
    for (size_t k = 0; k < SZ; k++) V[k] = INF;
    for (int b = 0; b < NCOL; b++) V[(size_t)b * NCOL + 0] = (cell_t)wt[b];     /* n = 1, a = 0 */
    printf("m=%d\ngamma:", M);
    int cd[MAXM];
    for (int n = 1; n <= nmax; n++) {
        if (n == chkN + 1 && snap) memcpy(snap, V, SZ * sizeof(cell_t));
        if (n == chkN + 1 + chkP && snap) {
            int ok = 1;
            for (size_t k = 0; k < SZ && ok; k++) {
                if (snap[k] == INF || V[k] == INF) ok = (snap[k] == V[k]);
                else ok = (V[k] == snap[k] + chkQ);
            }
            fprintf(stderr, "periodicity check V_%d = V_%d + %d: %s\n", n, chkN + 1, chkQ,
                    ok ? "OK" : "FAILED");
        }
        int gam = INF;
        for (size_t k = 0; k < SZ; k++) W[k] = INF;
        for (int b = 0; b < NCOL; b++) {
            memcpy(T, V + (size_t)b * NCOL, (size_t)NCOL * sizeof(cell_t));
            /* T[x] = min over a >= x */
            for (int i = 0; i < M; i++) {
                int step = pow3[i];
                for (int x = NCOL - 1; x >= 0; x--)
                    if (x / step % 3 != 2 && T[x + step] < T[x]) T[x] = T[x + step];
            }
            const int8_t *tb = tau + (size_t)b * M;
            /* c = 0: the grid ends after column b */
            {
                int r = 0;
                for (int i = 0; i < M; i++) r += (2 - tb[i]) * pow3[i];
                if (T[r] < gam) gam = T[r];
            }
            for (int c = 0; c < NCOL; c++) {
                int cc = c, r = 0;
                for (int i = 0; i < M; i++) { cd[i] = cc % 3; cc /= 3; }
                for (int i = 0; i < M; i++) {
                    int need = 2 - cd[i] - tb[i];
                    if (need > 0) r += need * pow3[i];
                }
                if (T[r] != INF) {
                    int val = T[r] + wt[c];
                    if (val >= INF) { fprintf(stderr, "overflow\n"); return 2; }
                    W[(size_t)c * NCOL + b] = (cell_t)val;
                }
            }
        }
        printf(" %d", gam);
        fflush(stdout);
        cell_t *tmp = V; V = W; W = tmp;
    }
    printf("\n");
    return 0;
}
