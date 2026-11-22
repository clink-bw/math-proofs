/*
 * search.c - exhaustive search for k-paradoxical Cayley tournaments on small groups.
 *
 * A tournament is k-paradoxical (has Schutte's property S_k) if every set of k players is
 * beaten by some single other player.
 *
 * A Cayley tournament on a group G of odd order n is given by a connection set S that contains
 * exactly one element of each pair {s, s^-1} with s != e. Player x beats player y when
 * x^-1 y is in S. Left multiplication by any group element is an automorphism, so every
 * k-set can be moved to one containing the identity e, and two k-sets that are left
 * translates of each other are both dominated or both not. The search therefore tests one
 * representative k-set (containing e) from each translation class.
 *
 * For a k-set A = {e, a_1, ..., a_{k-1}}: x beats a iff a^-1 x is in S^-1, so the players
 * beating all of A form the set  T & a_1 T & ... & a_{k-1} T,  where T = S^-1 is the set of
 * players beating e. A is dominated iff that intersection is nonempty.
 *
 * Two code paths:
 *   circ  - cyclic group Z_n (circulant tournaments). Here x beats y iff y - x is in S, and
 *           A = {0, a_1, ...} is dominated iff some y has y, y + a_1, ... all in S, i.e.
 *           S & rot(S, a_1) & ... != 0 with rot(S, a) = {y : y + a in S}. The multiplier -1
 *           (x -> -x, an automorphism of Z_n) maps S to -S, so we may assume 1 is in S.
 *   group - any group of odd order given by a multiplication table; the bitsets gT for all
 *           g are updated incrementally. No symmetry is used.
 *
 * Every connection set is visited by a Gray code (one pair {s, s^-1} flips per step) and
 * tested against the representative k-sets, most-recently-failing first. Work is split into
 * jobs over the top bits and run on POSIX threads.
 *
 * Usage:
 *   search circ   N K [threads] [min]  all circulant tournaments on Z_N with 1 in S
 *   search group  NAME K [threads] [min]  all Cayley tournaments on a named group (see below)
 *   search paley  P K                  the Paley tournament on Z_P (P prime, 3 mod 4)
 *   search set    N K s1,s2,...        one circulant tournament on Z_N given by S
 *   search gset   NAME K i1,i2,...     one Cayley tournament on a named group, S given by
 *                                      element indices (used by check.py)
 *   search groups                      print the built-in groups and their invariants
 * Group names: Z7xZ7, Z3xZ21, Z11:Z5, Z19:Z3, Z7:Z9, Z3x(Z7:Z3), Z7:Z3, and Zn (the cyclic
 * group through the general code path, for cross-checks). Element indices: for Zp x Zq the
 * pair (a,b) is a*q+b; for Zp:Zq (a in Zp, b in Zq) it is b*p+a, with
 * (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1 + b2), r = 3, 7, 2 for Z11:Z5, Z19:Z3, Z7:Z9 (and r = 2
 * for Z7:Z3); for Z3x(Z7:Z3) the triple (c,a,b) is c*21 + b*7 + a.
 * With "min", the search also finds the smallest number of undominated k-set classes over all
 * connection sets (a measure of how close the family comes), and how many sets attain it.
 *
 * Bitsets are unsigned __int128, so N <= 127.
 */
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef unsigned __int128 u128;
#define MAXN 127
#define MAXK 6
#define BIT(i) (((u128)1) << (i))

/* ---------------------------------------------------------------- the group */
static int N;                       /* group order                            */
static int K;                       /* k in "k-paradoxical"                    */
static int CYCLIC;                  /* 1 = use the circulant fast path         */
static uint8_t MUL[MAXN][MAXN];     /* MUL[x][y] = x*y; identity is element 0 */
static uint8_t INV[MAXN];
static char GNAME[64];
static char ELEMNAME[MAXN][16];

/* pair classes {u, u^-1}; bit 1 in the code means u in S, bit 0 means u^-1 in S */
static int NCLS;
static int CLS_U[MAXN], CLS_V[MAXN];
static int NFREE;                   /* classes enumerated (the rest are fixed) */
static int FREE[MAXN];
static int FIXED_ON[MAXN];          /* classes fixed with bit 1                */
static int NFIXED;

/* representative k-sets: KM1 = k-1 non-identity elements each */
static int KM1;
static int NREPS;
static uint8_t *REPS;

/* group path: FLIP[c][g] = bits {g*u_c, g*v_c}, toggled in gT when class c flips */
static u128 (*FLIP)[MAXN];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static void die(const char *msg) { fprintf(stderr, "error: %s\n", msg); exit(1); }

static void set_cyclic(int n) {
    if (n < 1 || n > MAXN) die("n must be between 1 and 127");
    N = n; CYCLIC = 1;
    snprintf(GNAME, sizeof GNAME, "Z%d", n);
    for (int x = 0; x < n; x++) {
        INV[x] = (uint8_t)((n - x) % n);
        snprintf(ELEMNAME[x], 16, "%d", x);
        for (int y = 0; y < n; y++) MUL[x][y] = (uint8_t)((x + y) % n);
    }
}

static int ipow(int b, int e, int m) { int r = 1 % m; while (e-- > 0) r = r * b % m; return r; }

/* semidirect product Z_p x| Z_q with generator of Z_q acting by a -> r a; element (a,b) has
   index b*p + a; (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1 + b2).  Requires r^q = 1 mod p. */
static void set_semidirect(const char *name, int p, int q, int r) {
    if (ipow(r, q, p) != 1) die("bad semidirect parameter");
    N = p * q; CYCLIC = 0;
    snprintf(GNAME, sizeof GNAME, "%s", name);
    for (int b1 = 0; b1 < q; b1++)
        for (int a1 = 0; a1 < p; a1++) {
            int x = b1 * p + a1;
            snprintf(ELEMNAME[x], 16, "(%d,%d)", a1, b1);
            for (int b2 = 0; b2 < q; b2++)
                for (int a2 = 0; a2 < p; a2++) {
                    int a = (a1 + ipow(r, b1, p) * a2) % p, b = (b1 + b2) % q;
                    MUL[x][b2 * p + a2] = (uint8_t)(b * p + a);
                }
        }
}

/* direct product Z_p x Z_q, element (a,b) index a*q + b */
static void set_abelian2(const char *name, int p, int q) {
    N = p * q; CYCLIC = 0;
    snprintf(GNAME, sizeof GNAME, "%s", name);
    for (int a1 = 0; a1 < p; a1++)
        for (int b1 = 0; b1 < q; b1++) {
            int x = a1 * q + b1;
            snprintf(ELEMNAME[x], 16, "(%d,%d)", a1, b1);
            for (int a2 = 0; a2 < p; a2++)
                for (int b2 = 0; b2 < q; b2++)
                    MUL[x][a2 * q + b2] = (uint8_t)(((a1 + a2) % p) * q + (b1 + b2) % q);
        }
}

/* Z_3 x (Z_7 x| Z_3): element (c,a,b) index c*21 + b*7 + a */
static void set_z3_x_f21(void) {
    N = 63; CYCLIC = 0;
    snprintf(GNAME, sizeof GNAME, "Z3x(Z7:Z3)");
    for (int c1 = 0; c1 < 3; c1++) for (int b1 = 0; b1 < 3; b1++) for (int a1 = 0; a1 < 7; a1++) {
        int x = c1 * 21 + b1 * 7 + a1;
        snprintf(ELEMNAME[x], 16, "(%d,%d,%d)", c1, a1, b1);
        for (int c2 = 0; c2 < 3; c2++) for (int b2 = 0; b2 < 3; b2++) for (int a2 = 0; a2 < 7; a2++) {
            int c = (c1 + c2) % 3, a = (a1 + ipow(2, b1, 7) * a2) % 7, b = (b1 + b2) % 3;
            MUL[x][c2 * 21 + b2 * 7 + a2] = (uint8_t)(c * 21 + b * 7 + a);
        }
    }
}

static void set_group_by_name(const char *name) {
    if (name[0] == 'Z' && strspn(name + 1, "0123456789") == strlen(name + 1)) {
        /* "Zn": cyclic group through the general (table) code path, for cross-checking */
        set_cyclic(atoi(name + 1));
        CYCLIC = 0;
        snprintf(GNAME, sizeof GNAME, "%s(table)", name);
    } else if (!strcmp(name, "Z7xZ7")) set_abelian2(name, 7, 7);
    else if (!strcmp(name, "Z3xZ21")) set_abelian2(name, 3, 21);
    else if (!strcmp(name, "Z11:Z5")) set_semidirect(name, 11, 5, 3);   /* 3^5 = 1 mod 11 */
    else if (!strcmp(name, "Z19:Z3")) set_semidirect(name, 19, 3, 7);   /* 7^3 = 1 mod 19 */
    else if (!strcmp(name, "Z7:Z9")) set_semidirect(name, 7, 9, 2);     /* 2^3 = 1 mod 7  */
    else if (!strcmp(name, "Z7:Z3")) set_semidirect(name, 7, 3, 2);
    else if (!strcmp(name, "Z3x(Z7:Z3)")) set_z3_x_f21();
    else die("unknown group name");
}

/* check the group axioms, fill INV, and print invariants that pin down the isomorphism type */
static void check_group(int verbose) {
    if (N < 1 || N > MAXN || N % 2 == 0) die("group order must be odd and <= 127");
    for (int x = 0; x < N; x++)
        if (MUL[0][x] != x || MUL[x][0] != x) die("element 0 is not the identity");
    for (int x = 0; x < N; x++) {
        int seen[MAXN] = {0};
        for (int y = 0; y < N; y++) { if (seen[MUL[x][y]]++) die("not a Latin square"); }
    }
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) for (int z = 0; z < N; z++)
        if (MUL[MUL[x][y]][z] != MUL[x][MUL[y][z]]) die("not associative");
    for (int x = 0; x < N; x++) {
        int found = 0;
        for (int y = 0; y < N; y++) if (MUL[x][y] == 0) { INV[x] = (uint8_t)y; found++; }
        if (found != 1) die("inverse");
    }
    if (!verbose) return;
    int abelian = 1;
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (MUL[x][y] != MUL[y][x]) abelian = 0;
    int cnt[MAXN + 1] = {0};
    for (int x = 0; x < N; x++) {
        int o = 1, y = x;
        while (y != 0) { y = MUL[y][x]; o++; }
        cnt[x == 0 ? 1 : o]++;
    }
    printf("group %s: order %d, %s, element orders:", GNAME, N, abelian ? "abelian" : "non-abelian");
    for (int o = 1; o <= N; o++) if (cnt[o]) printf(" %d^%d", o, cnt[o]);
    printf("\n");
}

static void build_classes(int use_minus_one) {
    NCLS = 0;
    int done[MAXN] = {0};
    for (int x = 1; x < N; x++) {
        if (done[x]) continue;
        if (INV[x] == x) die("element of order 2");
        CLS_U[NCLS] = x; CLS_V[NCLS] = INV[x];
        done[x] = done[INV[x]] = 1;
        NCLS++;
    }
    NFREE = 0; NFIXED = 0;
    for (int c = 0; c < NCLS; c++) {
        /* circulant path: the multiplier -1 lets us assume 1 is in S (class of 1 is class 0) */
        if (use_minus_one && c == 0) { FIXED_ON[NFIXED++] = c; continue; }
        FREE[NFREE++] = c;
    }
}

/* representatives of k-sets up to left translation, each containing the identity */
static int cmp_u8(const void *a, const void *b) { return *(const uint8_t *)a - *(const uint8_t *)b; }

static void build_reps(void) {
    KM1 = K - 1;
    int cap = 1 << 16;
    REPS = malloc((size_t)cap * (KM1 > 0 ? KM1 : 1));
    NREPS = 0;
    if (KM1 == 0) { NREPS = 1; return; }       /* k = 1: the single set {e} */
    int idx[MAXK];
    for (int i = 0; i < KM1; i++) idx[i] = i + 1;
    for (;;) {
        /* A = {0, idx[0..KM1-1]} as a sorted K-tuple */
        uint8_t A[MAXK], best[MAXK], T[MAXK];
        A[0] = 0;
        for (int i = 0; i < KM1; i++) A[i + 1] = (uint8_t)idx[i];
        memcpy(best, A, K);
        for (int j = 1; j < K; j++) {           /* translate by A[j]^-1 */
            for (int i = 0; i < K; i++) T[i] = MUL[INV[A[j]]][A[i]];
            qsort(T, K, 1, cmp_u8);
            if (memcmp(T, best, K) < 0) memcpy(best, T, K);
        }
        if (!memcmp(best, A, K)) {
            if (NREPS == cap) { cap *= 2; REPS = realloc(REPS, (size_t)cap * KM1); }
            memcpy(REPS + (size_t)NREPS * KM1, A + 1, KM1);
            NREPS++;
        }
        int i = KM1 - 1;
        while (i >= 0 && idx[i] == N - KM1 + i) i--;
        if (i < 0) break;
        idx[i]++;
        for (int j = i + 1; j < KM1; j++) idx[j] = idx[j - 1] + 1;
    }
}

/* ---------------------------------------------------------------- testing */
static inline u128 rot(u128 S, int a) { return (S >> a) | (S << (N - a)); }

/* bitset of S (as a subset of G) from the class bits */
static u128 S_from_bits(const uint8_t *bits) {
    u128 S = 0;
    for (int c = 0; c < NCLS; c++) S |= bits[c] ? BIT(CLS_U[c]) : BIT(CLS_V[c]);
    return S;
}

/* is representative r dominated?  circulant path */
static inline int dom_circ(u128 S, int r) {
    const uint8_t *a = REPS + (size_t)r * KM1;
    u128 acc = S;                     /* bits >= N vanish because S has none */
    for (int i = 0; i < KM1; i++) acc &= rot(S, a[i]);
    return acc != 0;
}

/* group path: L[g] = g T where T = S^-1 */
static inline int dom_group(const u128 *L, int r) {
    const uint8_t *a = REPS + (size_t)r * KM1;
    u128 acc = L[0];
    for (int i = 0; i < KM1; i++) acc &= L[a[i]];
    return acc != 0;
}

static void build_translates(u128 S, u128 *L) {
    for (int g = 0; g < N; g++) {
        u128 x = 0;
        for (int s = 1; s < N; s++) if ((S >> s) & 1) x |= BIT(MUL[g][INV[s]]);
        L[g] = x;
    }
}

/* full count of undominated classes (no ordering tricks) */
static int count_undominated(u128 S, int *first_bad) {
    u128 L[MAXN];
    if (!CYCLIC) build_translates(S, L);
    int cnt = 0;
    if (first_bad) *first_bad = -1;
    for (int r = 0; r < NREPS; r++) {
        int ok = CYCLIC ? dom_circ(S, r) : dom_group(L, r);
        if (!ok) { if (first_bad && *first_bad < 0) *first_bad = r; cnt++; }
    }
    return cnt;
}

/* ---------------------------------------------------------------- automorphisms
 * Used only in "min" mode. An automorphism a of G maps Cay(G,S) isomorphically onto
 * Cay(G,a(S)), so the number of undominated classes is constant on Aut(G)-orbits of
 * connection sets and it suffices to test one set per orbit: the numerically smallest bitset
 * (among sets containing 1, in the circulant path). For Z_n the automorphisms are the
 * multipliers x -> u x with gcd(u, n) = 1.  Aut(G) is computed by brute force: try every
 * assignment of images to a generating set and keep the ones that extend to a bijective
 * homomorphism. */
static int NAUT;
static uint8_t (*AUT)[MAXN];

static void build_automorphisms(void) {
    int gens[8], ng = 0, ord[MAXN];
    uint8_t in[MAXN];
    int queue[MAXN];
    for (int x = 0; x < N; x++) {
        int o = 1, y = x;
        while (y != 0) { y = MUL[y][x]; o++; }
        ord[x] = x == 0 ? 1 : o;
    }
    int size = 1;
    memset(in, 0, sizeof in); in[0] = 1;
    for (int x = 1; x < N && size < N; x++) {
        if (in[x]) continue;
        if (ng == 8) die("too many generators");
        gens[ng++] = x;
        memset(in, 0, sizeof in); in[0] = 1; size = 1;
        int qh = 0, qt = 0; queue[qt++] = 0;
        while (qh < qt) {
            int g = queue[qh++];
            for (int i = 0; i < ng; i++) {
                int h = MUL[g][gens[i]];
                if (!in[h]) { in[h] = 1; queue[qt++] = h; size++; }
            }
        }
    }
    int cap = 1024;
    AUT = malloc(sizeof(*AUT) * (size_t)cap);
    NAUT = 0;
    int img[8] = {0};
    for (;;) {
        int okord = 1;
        for (int i = 0; i < ng; i++) if (ord[img[i]] != ord[gens[i]]) okord = 0;
        if (okord) {
            uint8_t phi[MAXN], set[MAXN] = {0}, used[MAXN] = {0};
            int qh = 0, qt = 0, good = 1;
            phi[0] = 0; set[0] = 1; queue[qt++] = 0;
            while (qh < qt && good) {
                int g = queue[qh++];
                for (int i = 0; i < ng && good; i++) {
                    int h = MUL[g][gens[i]], v = MUL[phi[g]][img[i]];
                    if (!set[h]) { set[h] = 1; phi[h] = (uint8_t)v; queue[qt++] = h; }
                    else if (phi[h] != v) good = 0;
                }
            }
            for (int x = 0; x < N && good; x++) { if (used[phi[x]]++) good = 0; }
            if (good) {
                if (NAUT == cap) { cap *= 2; AUT = realloc(AUT, sizeof(*AUT) * (size_t)cap); }
                memcpy(AUT[NAUT++], phi, (size_t)N);
            }
        }
        int i = 0;
        while (i < ng && ++img[i] == N) img[i++] = 0;
        if (i == ng) break;
    }
}

static inline u128 apply_aut(const uint8_t *a, u128 S) {
    u128 T = 0;
    uint64_t lo = (uint64_t)S, hi = (uint64_t)(S >> 64);
    while (lo) { T |= BIT(a[__builtin_ctzll(lo)]); lo &= lo - 1; }
    while (hi) { T |= BIT(a[64 + __builtin_ctzll(hi)]); hi &= hi - 1; }
    return T;
}

static inline int respects_fixed(u128 T) {
    for (int i = 0; i < NFIXED; i++) if (!((T >> CLS_U[FIXED_ON[i]]) & 1)) return 0;
    return 1;
}

/* is S the smallest set in its orbit (among sets respecting the fixed classes)? */
static inline int is_canonical(u128 S) {
    for (int i = 0; i < NAUT; i++) {
        u128 T = apply_aut(AUT[i], S);
        if (T < S && respects_fixed(T)) return 0;
    }
    return 1;
}

/* number of distinct images of S under Aut(G) (the full orbit, ignoring fixed classes) */
static long orbit_size(u128 S) {
    long stab = 0;
    for (int i = 0; i < NAUT; i++) if (apply_aut(AUT[i], S) == S) stab++;
    return NAUT / stab;
}

/* ---------------------------------------------------------------- search */
static int MINMODE;
static int JOBBITS;
static atomic_long NEXTJOB;
static long NJOBS;
static atomic_int BEST;             /* min mode: smallest undominated count seen */
static pthread_mutex_t LOCK = PTHREAD_MUTEX_INITIALIZER;
static long BEST_COUNT;             /* min mode: number of orbits attaining BEST */
static long BEST_SETS;              /* min mode: number of sets attaining BEST   */
static u128 BEST_EXAMPLE;
static long HITS;                   /* sets with 0 undominated classes          */
static long TESTED;                 /* sets tested (min mode: orbit representatives) */
static long VISITED;                /* sets visited by the enumeration                */
static long TESTS_DONE;             /* number of (set, representative) checks   */

static void print_set(FILE *f, u128 S) {
    int first = 1;
    fprintf(f, "{");
    for (int x = 0; x < N; x++)
        if ((S >> x) & 1) { fprintf(f, first ? "%s" : ",%s", CYCLIC ? ELEMNAME[x] : ELEMNAME[x]); first = 0; }
    fprintf(f, "}");
}

typedef struct { int *order; long tested, hits, tests; } Thread;

/* move order[p] to the front */
static inline void mtf(int *order, int p) {
    int r = order[p];
    memmove(order + 1, order, (size_t)p * sizeof(int));
    order[0] = r;
}

static void record(u128 S, int cnt) {
    long osz = MINMODE ? orbit_size(S) : 1;
    pthread_mutex_lock(&LOCK);
    if (cnt == 0) {
        HITS++;
        if (HITS <= 2000) { printf("HIT %s k=%d S=", GNAME, K); print_set(stdout, S); printf("\n"); fflush(stdout); }
    }
    if (MINMODE) {
        int b = atomic_load(&BEST);
        if (cnt < b) { atomic_store(&BEST, cnt); BEST_COUNT = 1; BEST_SETS = osz; BEST_EXAMPLE = S; }
        else if (cnt == b) { BEST_COUNT++; BEST_SETS += osz; }
    }
    pthread_mutex_unlock(&LOCK);
}

/* process one connection set. Exists mode: stop at the first undominated class. Min mode:
   skip sets that are not the canonical member of their Aut(G)-orbit, and stop counting once
   the count exceeds the best found so far. */
static inline void process(Thread *t, u128 S, const u128 *L) {
    if (MINMODE && !is_canonical(S)) return;
    int limit = MINMODE ? atomic_load_explicit(&BEST, memory_order_relaxed) : 0;
    int cnt = 0;
    int *order = t->order;
    for (int p = 0; p < NREPS; p++) {
        int r = order[p];
        t->tests++;
        int ok = CYCLIC ? dom_circ(S, r) : dom_group(L, r);
        if (!ok) {
            mtf(order, p);
            if (++cnt > limit) break;
        }
    }
    t->tested++;
    if (cnt <= limit) record(S, cnt);
}

static void *worker(void *arg) {
    Thread *t = arg;
    int low = NFREE - JOBBITS;
    u128 L[MAXN];
    uint8_t bits[MAXN];
    for (;;) {
        long job = atomic_fetch_add(&NEXTJOB, 1);
        if (job >= NJOBS) break;
        memset(bits, 0, sizeof bits);
        for (int i = 0; i < NFIXED; i++) bits[FIXED_ON[i]] = 1;
        for (int j = 0; j < JOBBITS; j++) bits[FREE[low + j]] = (uint8_t)((job >> j) & 1);
        u128 S = S_from_bits(bits);
        if (!CYCLIC) build_translates(S, L);
        unsigned long long steps = 1ULL << low;
        for (unsigned long long i = 0; i < steps; i++) {
            if (i) {
                int c = FREE[__builtin_ctzll(i)];
                S ^= BIT(CLS_U[c]) | BIT(CLS_V[c]);
                if (!CYCLIC) { const u128 *F = FLIP[c]; for (int g = 0; g < N; g++) L[g] ^= F[g]; }
            }
            process(t, S, L);
        }
    }
    return NULL;
}

static void run_search(int nthreads) {
    build_reps();
    if (MINMODE) build_automorphisms();
    if (!CYCLIC) {
        FLIP = malloc(sizeof(*FLIP) * (size_t)NCLS);
        for (int c = 0; c < NCLS; c++)
            for (int g = 0; g < N; g++)
                FLIP[c][g] = BIT(MUL[g][CLS_U[c]]) | BIT(MUL[g][CLS_V[c]]);
    }
    JOBBITS = NFREE < 12 ? NFREE / 2 : 10;
    NJOBS = 1L << JOBBITS;
    atomic_store(&NEXTJOB, 0);
    atomic_store(&BEST, MINMODE ? 1 << 30 : 0);
    BEST_COUNT = 0; HITS = 0;
    double t0 = now();
    pthread_t th[64];
    Thread T[64];
    for (int i = 0; i < nthreads; i++) {
        T[i].order = malloc(sizeof(int) * (size_t)NREPS);
        for (int r = 0; r < NREPS; r++) T[i].order[r] = r;
        T[i].tested = T[i].hits = T[i].tests = 0;
        pthread_create(&th[i], NULL, worker, &T[i]);
    }
    TESTED = 0; TESTS_DONE = 0;
    for (int i = 0; i < nthreads; i++) {
        pthread_join(th[i], NULL);
        TESTED += T[i].tested; TESTS_DONE += T[i].tests;
    }
    double dt = now() - t0;
    VISITED = 1L << NFREE;
    if (!MINMODE) {
        printf("RESULT group=%s n=%d k=%d classes_of_k_sets=%d connection_sets_tested=%ld "
               "(2^%d%s) k_paradoxical=%ld set_checks=%ld seconds=%.2f threads=%d\n",
               GNAME, N, K, NREPS, TESTED, NFREE, NFIXED ? ", 1 in S" : "", HITS, TESTS_DONE, dt, nthreads);
    } else {
        printf("MIN group=%s n=%d k=%d classes_of_k_sets=%d connection_sets_visited=%ld (2^%d%s) "
               "automorphisms=%d orbits_tested=%ld min_undominated_classes=%d attained_by_orbits=%ld "
               "attained_by_sets=%ld (of 2^%d) k_paradoxical_orbits=%ld set_checks=%ld seconds=%.2f threads=%d\n",
               GNAME, N, K, NREPS, VISITED, NFREE, NFIXED ? ", 1 in S" : "", NAUT, TESTED,
               atomic_load(&BEST), BEST_COUNT, BEST_SETS, NCLS, HITS, TESTS_DONE, dt, nthreads);
        printf("MINEXAMPLE group=%s n=%d k=%d undominated_classes=%d S=", GNAME, N, K, atomic_load(&BEST));
        print_set(stdout, BEST_EXAMPLE);
        printf("\n");
    }
    fflush(stdout);
}

static int is_prime(int p) { if (p < 2) return 0; for (int d = 2; d * d <= p; d++) if (p % d == 0) return 0; return 1; }

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "see the comment at the top of search.c for usage\n"); return 1; }
    const char *mode = argv[1];
    if (!strcmp(mode, "groups")) {
        const char *names[] = {"Z7xZ7", "Z11:Z5", "Z19:Z3", "Z3xZ21", "Z7:Z9", "Z3x(Z7:Z3)", "Z63", "Z7:Z3"};
        for (unsigned i = 0; i < sizeof names / sizeof *names; i++) { set_group_by_name(names[i]); check_group(1); }
        return 0;
    }
    if (argc < 4) die("missing arguments");
    K = atoi(argv[3]);
    if (K < 1 || K > MAXK) die("k out of range");
    int searching = !strcmp(mode, "circ") || !strcmp(mode, "group");
    int nthreads = searching && argc > 4 && strcmp(argv[4], "min") ? atoi(argv[4]) : 8;
    MINMODE = searching && argc > 4 && !strcmp(argv[argc - 1], "min");
    if (nthreads < 1 || nthreads > 64) die("threads");
    if (!strcmp(mode, "circ")) {
        set_cyclic(atoi(argv[2]));
        check_group(0);
        build_classes(1);
        run_search(nthreads);
    } else if (!strcmp(mode, "group")) {
        set_group_by_name(argv[2]);
        check_group(1);
        build_classes(0);
        run_search(nthreads);
    } else if (!strcmp(mode, "paley") || !strcmp(mode, "set")) {
        int n = atoi(argv[2]);
        set_cyclic(n);
        check_group(0);
        build_classes(1);
        build_reps();
        u128 S = 0;
        if (!strcmp(mode, "paley")) {
            if (!is_prime(n) || n % 4 != 3) die("Paley needs a prime = 3 mod 4");
            for (int x = 1; x < n; x++) S |= BIT(x * x % n);
        } else {
            if (argc < 5) die("missing set");
            char *s = argv[4];
            while (*s) { S |= BIT(atoi(s) % n); while (*s && *s != ',') s++; if (*s) s++; }
            for (int x = 1; x < n; x++)
                if (((S >> x) & 1) == ((S >> (n - x)) & 1)) die("S must contain exactly one of x, -x");
            if (S & 1) die("0 in S");
        }
        int bad;
        int cnt = count_undominated(S, &bad);
        printf("CHECK n=%d k=%d S=", n, K);
        print_set(stdout, S);
        printf(" classes=%d undominated_classes=%d -> %s", NREPS, cnt, cnt ? "NOT k-paradoxical" : "k-paradoxical");
        if (bad >= 0) {
            printf(" (e.g. {0");
            for (int i = 0; i < KM1; i++) printf(",%d", REPS[(size_t)bad * KM1 + i]);
            printf("} is beaten by nobody)");
        }
        printf("\n");
    } else if (!strcmp(mode, "gset")) {
        /* one Cayley tournament on a named group; S given by element indices */
        set_group_by_name(argv[2]);
        check_group(0);
        build_classes(0);
        build_reps();
        if (argc < 5) die("missing set");
        u128 S = 0;
        char *s = argv[4];
        while (*s) {
            int x = atoi(s);
            if (x <= 0 || x >= N) die("element index out of range");
            S |= BIT(x);
            while (*s && *s != ',') s++;
            if (*s) s++;
        }
        for (int c = 0; c < NCLS; c++)
            if (((S >> CLS_U[c]) & 1) == ((S >> CLS_V[c]) & 1)) die("S must contain exactly one of x, x^-1");
        printf("GSET group=%s n=%d k=%d classes=%d undominated_classes=%d\n", GNAME, N, K, NREPS,
               count_undominated(S, NULL));
    } else die("unknown mode");
    return 0;
}
