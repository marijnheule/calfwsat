/*
 * ntil-encode.c  —  CNF encoder for the No-Three-In-Line problem
 *
 * Produces a DIMACS CNF file encoding:
 *   Variables : p[i][j], shell-numbered: s=max(i,j), var=s²+pos+1 where
 *               pos=i if j==s (top of L), pos=2s-j if i==s (bottom, r-to-l)
 *   No-triple : ¬p[A] ∨ ¬p[B] ∨ ¬p[C]  for every collinear triple
 *   Row/col   : for each row/col and each cell j, ∨_{k≠j} p[k]  (≥2 per line)
 *   Symmetry  : (--sym) orbit variable reduction; first ⌈n²/4⌉ vars suffice
 *
 *   --alt     : "at-least-two" relaxation — no-triple constraints are emitted
 *               for rows (di=0) AND oblique lines (di>0, dj≠0), but NOT for
 *               columns (dj=0).  Combined with the ≥2 per row/col constraints:
 *               every row has exactly 2 points; every column has at least 2.
 *   --far     : distance constraint — for every pair of cells at Chebyshev
 *               distance 1 (horizontal, vertical, or diagonal neighbours),
 *               add ¬p[i][j] ∨ ¬p[i'][j'].  No two selected points may touch.
 *   --amo     : at-most-one constraint on each of the four quadrants (split
 *               at h=⌊n/2⌋): at most one selected cell per row and per column
 *               within each quadrant.  Encoded as pairwise ¬p[a] ∨ ¬p[b]
 *               clauses.  With --sym, only the top-left quadrant is encoded
 *               explicitly (symmetry forces the other three to follow).
 *   --off K   : force all cells within Chebyshev distance K of the grid centre
 *               to be false, except cells on the main diagonal (i==j).
 *               The centre is ((n-1)/2, (n-1)/2); distance is measured exactly
 *               (max(|2i-(n-1)|, |2j-(n-1)|) <= 2K in integer arithmetic).
 *               Note: with --sym and even n, anti-diagonal cells (i+j==n-1)
 *               share an orbit with diagonal cells and are therefore also
 *               exempted to avoid inadvertently forcing diagonal cells false.
 *
 * Usage: ntil-encode [n] [--sym] [--cnf|--knf|--aux|--end] [--alt] [--far] [--amo] [--off K] [--color]
 * Build: cc -O2 -o ntil-encode ntil-encode.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 1000

static int N, SYM, KNF, ALT, FAR, AMO, OFF, CUT, COLOR, K, AUX, END, POS;
static int rep[MAXN][MAXN];   /* orbit representative variable for each cell */
static int norbs;              /* number of distinct orbits */
static int aux_var_count;      /* highest variable index allocated; new_aux() bumps this */

static int new_aux(void) { return ++aux_var_count; }

static int gcd(int a, int b) { return b ? gcd(b, a % b) : a; }

/* Variable numbering.
 *
 * The top-left h×h quadrant (h=N/2) is numbered row-major: var=i*h+j+1.
 * For cells outside the quadrant, L-shaped shells expand outward:
 *   shell k (s=h+k): new column s (rows 0..s-1, top to bottom)
 *                    then new row s (cols s..0, right to left).
 *   base for shell k = h² + k*(2h+k).
 *
 * This guarantees the minimum variable in every 90°-rotation orbit is
 * a quadrant cell, so --sym uses only variables 1..⌊n²/4⌋ (even n)
 * or 1..(n²+3)/4 (odd n).  Example for n=4:
 *
 *    1  2  5 10       (quadrant: row-major)
 *    3  4  6 11
 *    9  8  7 12
 *   16 15 14 13
 */
static int var(int i, int j) {
    int h = N / 2;
    if (i < h && j < h)
        return i * h + j + 1;
    int s = i > j ? i : j;
    int k = s - h;
    int base = h * h + k * (2 * h + k);
    return base + (j == s ? i : s + (s - j)) + 1;
}

/* Fill rep[i][j] = orbit representative variable (min var in orbit).
 *
 * Even N: standard 90°-rotation orbit (size 4); rep is always a quadrant cell.
 *
 * Odd N: the centre (c,c) with c=(N-1)/2 lies on BOTH diagonals.  Any 90°
 * orbit touching the main diagonal also touches the anti-diagonal, so a
 * strictly 90°-symmetric set of size 2N (≡2 mod 4) is impossible.  We use:
 *   - Anti-diagonal cells (i+j == N-1), incl. centre: rep = 0  (forced false)
 *   - Main-diagonal cells (i == j, i ≠ c):            180°-orbit {(i,i),(N-1-i,N-1-i)}
 *   - All other cells:                                 standard 90°-orbit
 * This lets the encoding achieve exactly 2N points. */
static void compute_reps(void) {
    for (int i = 0; i < N; i++)
    for (int j = 0; j < N; j++) {
        if ((N & 1) && i + j == N - 1) {
            rep[i][j] = 0;              /* anti-diagonal (+ centre): forced false */
        } else if ((N & 1) && i == j) {
            /* 180°-orbit partner: (N-1-i, N-1-i) */
            int vi = var(i, i), vp = var(N-1-i, N-1-i);
            rep[i][j] = vi < vp ? vi : vp;
        } else {
            int mn = N*N+1, ci = i, cj = j;
            do {
                int v = var(ci, cj); if (v < mn) mn = v;
                int ni = cj, nj = N-1-ci; ci = ni; cj = nj;
            } while (ci != i || cj != j);
            rep[i][j] = mn;
        }
    }
    norbs = 0;
    for (int i = 0; i < N; i++)
    for (int j = 0; j < N; j++)
        if (rep[i][j] > norbs) norbs = rep[i][j];
}

/* Literal variable: orbit representative when --sym, cell var otherwise. */
static int vlit(int i, int j) { return SYM ? rep[i][j] : var(i,j); }

/* Color variable: cell (i,j) coloured with color c (0-based).
 * These are per actual cell (never shared between orbit members), numbered
 * after all occupancy variables: cvar(i,j,c) = N²+(i·N+j)·K+c+1. */
static int cvar(int i, int j, int c) {
    return N * N + (i * N + j) * K + c + 1;
}

/* ---------- cell helpers ------------------------------------------------ */

static int cell_cmp(const void *a, const void *b) {
    const int *ca = (const int *)a, *cb = (const int *)b;
    return ca[0] != cb[0] ? ca[0] - cb[0] : ca[1] - cb[1];
}

static int int_cmp(const void *a, const void *b) {
    return *(const int *)a - *(const int *)b;
}

/* Return 1 if line pts[0..np-1] is the canonical representative of its
 * 90°-rotation orbit and should be emitted.
 *
 * di/dj: canonical direction of the current line (used to track each rotation's
 *   direction so we can detect --alt-skipped rotations).
 *
 * Even N: all four rotations produce the same vlit sequence (every 90°-orbit
 *   is complete), so we use sorted cell coordinates as the canonical key.
 *
 * Odd N: different rotations may filter out different anti-diagonal (vlit=0)
 *   cells, yielding genuinely different vlit sequences = different constraints.
 *   We may only skip a rotation when another produces the IDENTICAL vlit
 *   sequence (a true duplicate).  Among duplicates we keep the one with the
 *   lex-smallest sorted cell coordinates.  Rotations with distinct vlit
 *   sequences are always emitted regardless of cell-coordinate order.
 *
 * --alt interaction: if a rotation's direction would be skipped by --alt
 *   (dj=0, i.e. a column), it will not be emitted and therefore cannot serve
 *   as the canonical representative — we ignore it in the comparison so it
 *   does not suppress the current line. */
static int line_canonical(int pts[MAXN][2], int np, int di, int dj) {
    /* Sorted cell coords of current rotation (tie-breaking key). */
    int base[MAXN][2];
    memcpy(base, pts, np * sizeof base[0]);
    qsort(base, np, sizeof base[0], cell_cmp);

    /* Sorted vlit sequence of the current rotation (odd-N: non-zero only). */
    int vseq0[MAXN], vlen0 = 0;
    for (int p = 0; p < np; p++) {
        int v = vlit(pts[p][0], pts[p][1]);
        if (v) vseq0[vlen0++] = v;
    }
    if (N & 1) qsort(vseq0, vlen0, sizeof(int), int_cmp);

    int cur[MAXN][2];
    memcpy(cur, pts, np * sizeof cur[0]);
    int rdi = di, rdj = dj;

    for (int k = 0; k < 3; k++) {
        /* Rotate cur and direction 90°: (i,j)→(j,N-1-i), (di,dj)→(dj,-di). */
        for (int p = 0; p < np; p++) {
            int ni = cur[p][1], nj = N - 1 - cur[p][0];
            cur[p][0] = ni; cur[p][1] = nj;
        }
        { int nrdi = rdj, nrdj = -rdi; rdi = nrdi; rdj = nrdj; }

        /* --alt: a rotation with rdj==0 (vertical/column direction) would be
         * skipped by the outer --alt filter and will never be emitted.  It
         * cannot act as the canonical representative, so ignore it. */
        if (ALT && rdj == 0) continue;

        if (N & 1) {
            /* Odd N: compare vlit sequences first.
             * If this rotation's sequence differs from ours it's a different
             * constraint — don't let it suppress us. */
            int vseqr[MAXN], vlenr = 0;
            for (int p = 0; p < np; p++) {
                int v = vlit(cur[p][0], cur[p][1]);
                if (v) vseqr[vlenr++] = v;
            }
            qsort(vseqr, vlenr, sizeof(int), int_cmp);
            if (vlenr != vlen0) continue;
            int same = 1;
            for (int i = 0; i < vlen0; i++)
                if (vseqr[i] != vseq0[i]) { same = 0; break; }
            if (!same) continue;   /* different clauses — always emit both */
        }

        /* Same vlit sequence (or even N): use sorted cell coords to break ties.
         * If this rotation's sorted cells are lex-smaller, we are not canonical. */
        int rot[MAXN][2];
        memcpy(rot, cur, np * sizeof rot[0]);
        qsort(rot, np, sizeof rot[0], cell_cmp);
        for (int p = 0; p < np; p++)
            for (int q = 0; q < 2; q++) {
                if (rot[p][q] < base[p][q]) return 0;
                if (rot[p][q] > base[p][q]) goto next;
            }
        next:;
    }
    return 1;
}

/* ---------- clause store ------------------------------------------------ */

static int lit_cmp(const void *a, const void *b) {
    int la = *(const int *)a, lb = *(const int *)b;
    int va = la < 0 ? -la : la, vb = lb < 0 ? -lb : lb;
    return va != vb ? va - vb : la - lb;
}

typedef struct { int *lits; int len; int bound; } Clause;
static Clause *cstore;
static int cstore_n, cstore_cap;

/* Sort lits and (for CNF only) dedup, then append to clause store.
 * bound < 0 → CNF clause; bound >= 0 → KNF klause "k bound ...".
 *
 * Dedup is correct for CNF (a literal repeated in a disjunction is redundant)
 * but NOT for KNF: in "k b l1 l2 ... 0" each occurrence contributes 1 to the
 * count, so a duplicate carries real weight.  Example: the no-triple klause
 * for a 4-point line where two points share orbit a and two share orbit b is
 * "k 2 -a -a -b -b 0" = "2(1-a)+2(1-b)≥2" ≡ "a+b≤1", which is NOT the same
 * as "k 2 -a -b 0" = "both a and b must be false". */
static void add_clause(int *lits, int n, int bound) {
    qsort(lits, n, sizeof(int), lit_cmp);
    if (bound < 0) {                 /* CNF: remove genuinely redundant dups */
        int m = 0;
        for (int i = 0; i < n; i++)
            if (m == 0 || lits[i] != lits[m-1]) lits[m++] = lits[i];
        n = m;
    }
    if (cstore_n == cstore_cap) {
        cstore_cap = cstore_cap ? cstore_cap * 2 : 4096;
        cstore = realloc(cstore, cstore_cap * sizeof(Clause));
        if (!cstore) { fputs("out of memory\n", stderr); exit(1); }
    }
    Clause *c = &cstore[cstore_n++];
    c->lits = malloc(n * sizeof(int));
    if (!c->lits) { fputs("out of memory\n", stderr); exit(1); }
    memcpy(c->lits, lits, n * sizeof(int));
    c->len = n; c->bound = bound;
}

/* Effective bound for subsumption: CNF clause (bound=-1) behaves as bound=1. */
static int eff_bound(int b) { return b < 0 ? 1 : b; }

/* Return 1 if clause a subsumes clause b:
 *   lits(a) ⊆ lits(b)  AND  eff_bound(a) >= eff_bound(b).
 * Both literal lists are sorted by variable (abs value). */
static int subsumes(const Clause *a, const Clause *b) {
    if (a->len > b->len) return 0;
    if (eff_bound(a->bound) < eff_bound(b->bound)) return 0;
    int bi = 0;
    for (int ai = 0; ai < a->len; ai++) {
        int va = a->lits[ai] < 0 ? -a->lits[ai] : a->lits[ai];
        while (bi < b->len) {
            int vb = b->lits[bi] < 0 ? -b->lits[bi] : b->lits[bi];
            if (vb == va) break;
            if (vb > va)  return 0;
            bi++;
        }
        if (bi >= b->len || b->lits[bi] != a->lits[ai]) return 0;
        bi++;
    }
    return 1;
}

static int clause_store_cmp(const void *a, const void *b) {
    const Clause *ca = (const Clause *)a, *cb = (const Clause *)b;
    /* shorter first; among equal length, higher bound first (stronger) */
    if (ca->len != cb->len) return ca->len - cb->len;
    return eff_bound(cb->bound) - eff_bound(ca->bound);
}

static void eliminate_subsumed(void) {
    /* Without --sym, var() is a bijection so every clause is already
     * unique and no subsumptions can exist — skip entirely. */
    if (!SYM) return;

    /* Sort shortest-first so i < j guarantees cstore[i].len <= cstore[j].len.
     * Among equal lengths, higher effective bound comes first (stronger clauses
     * first so they subsume weaker ones of the same literal set). */
    qsort(cstore, cstore_n, sizeof(Clause), clause_store_cmp);

#define LIT_IDX(l) ((l) > 0 ? 2*((l)-1) : 2*(-(l)-1)+1)

    int max_var = 0;
    for (int i = 0; i < cstore_n; i++)
        for (int j = 0; j < cstore[i].len; j++) {
            int v = cstore[i].lits[j];
            if (v < 0) v = -v;
            if (v > max_var) max_var = v;
        }
    int nslots = 2 * max_var;

    /* Pass 1: count occurrences per literal slot (stored at cnt[idx+1]). */
    int *cnt = calloc(nslots + 2, sizeof(int));
    if (!cnt) { fputs("out of memory\n", stderr); exit(1); }
    for (int i = 0; i < cstore_n; i++)
        for (int j = 0; j < cstore[i].len; j++)
            cnt[LIT_IDX(cstore[i].lits[j]) + 1]++;

    /* Prefix sum → CSR row pointers: list for slot idx is cnt[idx]..cnt[idx+1]. */
    for (int i = 1; i <= nslots; i++) cnt[i] += cnt[i-1];

    /* Pass 2: fill clause-index array. */
    int *data = malloc(cnt[nslots] * sizeof(int));
    int *pos  = calloc(nslots, sizeof(int));
    if (!data || !pos) { fputs("out of memory\n", stderr); exit(1); }
    for (int i = 0; i < cstore_n; i++)
        for (int j = 0; j < cstore[i].len; j++) {
            int idx = LIT_IDX(cstore[i].lits[j]);
            data[cnt[idx] + pos[idx]++] = i;
        }
    free(pos);

    char *dead = calloc(cstore_n, 1);
    if (!dead) { fputs("out of memory\n", stderr); exit(1); }

    for (int i = 0; i < cstore_n; i++) {
        if (dead[i]) continue;
        /* Find the literal in clause i that occurs in the fewest clauses. */
        int best = LIT_IDX(cstore[i].lits[0]);
        for (int j = 1; j < cstore[i].len; j++) {
            int idx = LIT_IDX(cstore[i].lits[j]);
            if (cnt[idx+1] - cnt[idx] < cnt[best+1] - cnt[best])
                best = idx;
        }
        /* Clause i can only subsume j if j contains that rarest literal. */
        for (int k = cnt[best]; k < cnt[best+1]; k++) {
            int j = data[k];
            if (j <= i || dead[j]) continue;
            if (subsumes(&cstore[i], &cstore[j]))
                dead[j] = 1;
        }
    }

    /* Compact. */
    int m = 0;
    for (int i = 0; i < cstore_n; i++) {
        if (!dead[i]) cstore[m++] = cstore[i];
        else          free(cstore[i].lits);
    }
    cstore_n = m;

    free(cnt); free(data); free(dead);
#undef LIT_IDX
}

/* ---------- KNF at-most-two helper -------------------------------------- */

/* Encode "at most 2 of vlits[0..m-1] are true" in KNF+binary style.
 *
 * vlits is a *multiset* of positive vlit values; with --sym a single orbit
 * variable can appear multiple times (two cells in the same line share one
 * orbit representative).  Such duplicates carry structural weight:
 *
 *   If literal l appears k >= 2 times, setting l=1 already contributes k
 *   units to the at-most-2 budget, leaving room for at most 2-k others.
 *   For k >= 2 that means every other literal must be false.
 *
 * Algorithm:
 *   While some literal l appears >= 2 times in the current multiset:
 *     1. Add binary CNF clause  -l OR -l'  for every distinct other literal l'.
 *     2. Remove ALL occurrences of l from the multiset.
 *   Then, if |remaining| >= 3, add a KNF klause k(|remaining|-2) over -l1...-lm.
 *
 * This preserves every binary clause that the full CNF expansion would produce
 * (via triple-deduplication) and replaces the remaining at-most-2 sub-problem
 * with one KNF line.
 */
static void add_atmost2_knf(int *vlits_in, int m) {
    int cur[MAXN], n = m;
    memcpy(cur, vlits_in, m * sizeof(int));

    for (;;) {
        qsort(cur, n, sizeof(int), int_cmp);
        /* Find the first literal that appears >= 2 times. */
        int dup = -1;
        for (int i = 0; i < n - 1; i++)
            if (cur[i] == cur[i+1]) { dup = cur[i]; break; }
        if (dup < 0) break;   /* no duplicates — done */

        /* Add binary clause  -dup OR -l'  for each distinct other literal l'. */
        int prev_other = -1;
        for (int j = 0; j < n; j++) {
            if (cur[j] == dup || cur[j] == prev_other) continue;
            prev_other = cur[j];
            int bin[2] = {-dup, -cur[j]};
            add_clause(bin, 2, -1);
        }
        /* Remove all occurrences of dup. */
        int m2 = 0;
        for (int j = 0; j < n; j++)
            if (cur[j] != dup) cur[m2++] = cur[j];
        n = m2;
    }

    /* Remaining literals are all distinct → one KNF klause (if non-trivial). */
    if (n >= 3) {
        int lits[MAXN];
        for (int i = 0; i < n; i++) lits[i] = -cur[i];
        add_clause(lits, n, n - 2);
    }
}

/* ---------- AUX recursive at-most-two helper ---------------------------- */

/* Encode "at most 2 of vlits[0..m-1] are true" using recursive auxiliary
 * variables.  vlits must contain DISTINCT positive variable numbers (call
 * add_atmost2_aux_wrapper if duplicates are possible).
 *
 * Base case (m <= 5): emit all C(m,3) ternary CNF clauses ¬a ∨ ¬b ∨ ¬c.
 *
 * Recursive case (m > 5):
 *   x1..x4 = vlits[0..3];  fresh y1, y2 = new_aux().
 *   AMT(x1,x2,x3,x4)                   (recursive)
 *   ¬x1 ∨ y1,  ¬x3 ∨ y1               (x1 or x3 true  → y1 true)
 *   ¬x2 ∨ y2,  ¬x4 ∨ y2               (x2 or x4 true  → y2 true)
 *   ¬x1 ∨ ¬x3 ∨ y2                    (x1 ∧ x3 true   → y2 true)
 *   ¬x2 ∨ ¬x4 ∨ y1                    (x2 ∧ x4 true   → y1 true)
 *   AMT(y1,y2,x5,…,xm)                 (recursive, m-2 vars)
 *
 * Correctness sketch: y1 is true iff ≥1 of {x1,x3} is true (or both, via the
 * ternary clause); y2 iff ≥1 of {x2,x4}.  The tail AMT then ensures at most 2
 * of {y1,y2,x5,…,xm} are true, which propagates the budget correctly. */
static void add_atmost2_aux(int *vlits, int m) {
    if (m < 3) return;   /* ≤2 vars: constraint trivially satisfied */

    if (m <= 5) {
        /* Base case: all C(m,3) ternary clauses. */
        int cl[3];
        for (int a = 0; a < m-2; a++)
        for (int b = a+1; b < m-1; b++)
        for (int e = b+1; e < m;   e++) {
            cl[0] = -vlits[a]; cl[1] = -vlits[b]; cl[2] = -vlits[e];
            add_clause(cl, 3, -1);
        }
        return;
    }

    /* Recursive case. */
    int x1 = vlits[0], x2 = vlits[1], x3 = vlits[2], x4 = vlits[3];
    int y1 = new_aux(), y2 = new_aux();

    /* AMT(x1,x2,x3,x4) — base case (m=4 ≤ 5). */
    int head[4] = {x1, x2, x3, x4};
    add_atmost2_aux(head, 4);

    /* Implication clauses. */
    int cl2[2], cl3[3];
    cl2[0] = -x1; cl2[1] = y1; add_clause(cl2, 2, -1);
    cl2[0] = -x3; cl2[1] = y1; add_clause(cl2, 2, -1);
    cl2[0] = -x2; cl2[1] = y2; add_clause(cl2, 2, -1);
    cl2[0] = -x4; cl2[1] = y2; add_clause(cl2, 2, -1);
    cl3[0] = -x1; cl3[1] = -x3; cl3[2] = y2; add_clause(cl3, 3, -1);
    cl3[0] = -x2; cl3[1] = -x4; cl3[2] = y1; add_clause(cl3, 3, -1);

    /* AMT(y1,y2,x5,…,xm)  --aux: y1,y2 first
     * AMT(x5,…,xm,y1,y2)  --end: y1,y2 last  */
    int tail_n = m - 2;          /* y1,y2 replace x1..x4, keep x5..xm */
    int *tail = malloc(tail_n * sizeof(int));
    if (!tail) { fputs("out of memory\n", stderr); exit(1); }
    if (END) {
        for (int i = 4; i < m; i++) tail[i - 4] = vlits[i];
        tail[tail_n - 2] = y1; tail[tail_n - 1] = y2;
    } else {
        tail[0] = y1; tail[1] = y2;
        for (int i = 4; i < m; i++) tail[i - 2] = vlits[i];
    }
    add_atmost2_aux(tail, tail_n);
    free(tail);
}

/* Wrapper: handle duplicate vlit values first (same logic as add_atmost2_knf),
 * then delegate the remaining distinct literals to add_atmost2_aux. */
static void add_atmost2_aux_wrapper(int *vlits_in, int m) {
    int cur[MAXN], n = m;
    memcpy(cur, vlits_in, m * sizeof(int));

    for (;;) {
        qsort(cur, n, sizeof(int), int_cmp);
        /* Find first literal appearing >= 2 times. */
        int dup = -1;
        for (int i = 0; i < n - 1; i++)
            if (cur[i] == cur[i+1]) { dup = cur[i]; break; }
        if (dup < 0) break;   /* no duplicates */

        /* Binary clause -dup ∨ -l' for every distinct other literal l'. */
        int prev_other = -1;
        for (int j = 0; j < n; j++) {
            if (cur[j] == dup || cur[j] == prev_other) continue;
            prev_other = cur[j];
            int bin[2] = {-dup, -cur[j]};
            add_clause(bin, 2, -1);
        }
        /* Remove all occurrences of dup. */
        int m2 = 0;
        for (int j = 0; j < n; j++)
            if (cur[j] != dup) cur[m2++] = cur[j];
        n = m2;
    }

    if (n >= 3)
        add_atmost2_aux(cur, n);
}

/* ---------- main pass --------------------------------------------------- */

/* Collect all clauses into the clause store. */
static void pass(void) {
    int ci, cj, np, pts[MAXN][2];
    int rpts[MAXN][2], rp;   /* pts filtered to those with vlit != 0 */
    int lits[MAXN];

    /* --- No-triple constraints ---
     * CNF: C(rp,3) clauses of length 3  per line
     * KNF: 1 klause  "k (rp-2) -v1..-vrp"  per line  (at-most-2 of rp real cells)
     *
     * With --sym: line_canonical() skips a rotation unless it is the canonical
     * representative of its orbit (see function comment for even/odd N details). */
    for (int di = 0; di < N; di++)
    for (int dj = (di ? -(N-1) : 1); dj < N; dj++) {
        if (gcd(di, dj < 0 ? -dj : dj) != 1) continue;
        /* --alt: skip vertical lines (dj=0, columns) only; rows (di=0) keep
         * their no-triple constraint, so each row has exactly 2 points. */
        if (ALT && dj == 0) continue;

        for (int i0 = 0; i0 < N; i0++)
        for (int j0 = 0; j0 < N; j0++) {
            int pi = i0 - di, pj = j0 - dj;
            if (pi >= 0 && pi < N && pj >= 0 && pj < N) continue;

            for (np = 0, ci = i0, cj = j0;
                 ci >= 0 && ci < N && cj >= 0 && cj < N;
                 ci += di, cj += dj) {
                pts[np][0] = ci; pts[np][1] = cj; np++;
            }
            if (np < 3) continue;
            /* --color: colour vars are per actual cell, so every rotation of a
             * line yields a distinct constraint — skip line_canonical entirely. */
            if (SYM && !COLOR && !line_canonical(pts, np, di, dj)) continue;

            /* Filter to real (non-forced-false) cells. */
            rp = 0;
            for (int p = 0; p < np; p++)
                if (vlit(pts[p][0], pts[p][1]) != 0) {
                    rpts[rp][0] = pts[p][0]; rpts[rp][1] = pts[p][1]; rp++;
                }
            if (rp < 3) continue;   /* ≤2 real cells on this line: trivially OK */

            if (COLOR) {
                /* For each colour c: at most 2 cells on this line have colour c.
                 * Applies to ALL np cells (coloring is grid-wide, not occupancy-based).
                 * cvar variables are always distinct (per cell per colour). */
                for (int c = 0; c < K; c++) {
                    if (KNF) {
                        int vlits[MAXN];
                        for (int p = 0; p < np; p++)
                            vlits[p] = cvar(pts[p][0], pts[p][1], c);
                        add_atmost2_knf(vlits, np);
                    } else {
                        for (int a = 0; a < np-2; a++)
                        for (int b = a+1; b < np-1; b++)
                        for (int e = b+1; e < np;   e++) {
                            lits[0] = -cvar(pts[a][0], pts[a][1], c);
                            lits[1] = -cvar(pts[b][0], pts[b][1], c);
                            lits[2] = -cvar(pts[e][0], pts[e][1], c);
                            add_clause(lits, 3, -1);
                        }
                    }
                }
            } else if (KNF) {
                /* Extract vlit multiset (may contain duplicates with --sym),
                 * emit binary CNF clauses for duplicates, then one KNF klause. */
                int vlits[MAXN];
                for (int p = 0; p < rp; p++)
                    vlits[p] = vlit(rpts[p][0], rpts[p][1]);
                add_atmost2_knf(vlits, rp);
            } else if (AUX || END) {
                /* Recursive auxiliary-variable encoding of at-most-two.
                 * Handles duplicates (--sym) then encodes the remaining
                 * distinct literals with add_atmost2_aux.
                 * --aux: tail order [y1,y2,x5,...]; --end: [x5,...,y1,y2]. */
                int vlits[MAXN];
                for (int p = 0; p < rp; p++)
                    vlits[p] = vlit(rpts[p][0], rpts[p][1]);
                add_atmost2_aux_wrapper(vlits, rp);
            } else {
                for (int a = 0; a < rp-2; a++)
                for (int b = a+1; b < rp-1; b++)
                for (int e = b+1; e < rp;   e++) {
                    lits[0] = -vlit(rpts[a][0], rpts[a][1]);
                    lits[1] = -vlit(rpts[b][0], rpts[b][1]);
                    lits[2] = -vlit(rpts[e][0], rpts[e][1]);
                    add_clause(lits, 3, -1);
                }
            }
        }
    }

    /* --- Row/col at-least-2 constraints ---
     * For each real cell (i,j) in a row/col, one CNF clause:
     *   "at least one of the other real cells in this row/col is occupied."
     * Same encoding for both CNF and KNF — duplicates from --sym are deduped
     * inside add_clause (correct for CNF disjunctions).
     *
     * Cells with vlit=0 (forced-false anti-diagonal, odd N + --sym) are excluded. */
    for (int i = 0; i < N; i++)
    for (int j = 0; j < N; j++) {
        if (!vlit(i, j)) continue;
        int m = 0;
        for (int k = 0; k < N; k++) {
            if (k == j) continue;
            int v = vlit(i, k); if (v) lits[m++] = v;
        }
        if (m >= 1) add_clause(lits, m, -1);
    }
    for (int j = 0; j < N; j++)
    for (int i = 0; i < N; i++) {
        if (!vlit(i, j)) continue;
        int m = 0;
        for (int k = 0; k < N; k++) {
            if (k == i) continue;
            int v = vlit(k, j); if (v) lits[m++] = v;
        }
        if (m >= 1) add_clause(lits, m, -1);
    }

    /* --- Adjacency (--far) constraints ---
     * For every unordered pair of cells at Chebyshev distance 1 add
     * ¬p[i][j] ∨ ¬p[i'][j'].  We enumerate each pair once via the four
     * "forward" directions: E, SW, S, SE.
     *
     * Edge case with --sym: if two adjacent cells share the same orbit
     * representative (both controlled by the same variable), the clause
     * collapses to the unit clause ¬v, forcing that orbit to be unoccupied. */
    /* --- AMO (--amo) constraints ---
     * Four quadrants split at h = N/2:
     *   TL: rows [0,h)  × cols [0,h)     TR: rows [0,h)  × cols [h,N)
     *   BL: rows [h,N)  × cols [0,h)     BR: rows [h,N)  × cols [h,N)
     * At most one selected cell per row and per column within each quadrant,
     * encoded as pairwise ¬p[a] ∨ ¬p[b] for every pair in each line.
     * With --sym, only the top-left quadrant is needed (symmetry implies the rest). */
    if (AMO) {
        int h = N / 2;
        int quads[4][4] = {
            {0, h, 0, h},   /* top-left  */
            {0, h, h, N},   /* top-right */
            {h, N, 0, h},   /* bot-left  */
            {h, N, h, N},   /* bot-right */
        };
        int nq = SYM ? 1 : 4;
        for (int q = 0; q < nq; q++) {
            int r0 = quads[q][0], r1 = quads[q][1];
            int c0 = quads[q][2], c1 = quads[q][3];
            /* Rows. */
            for (int i = r0; i < r1; i++)
            for (int j = c0; j < c1; j++) {
                int va = vlit(i, j); if (!va) continue;
                for (int k = j + 1; k < c1; k++) {
                    int vb = vlit(i, k); if (!vb) continue;
                    if (va == vb) { lits[0] = -va; add_clause(lits, 1, -1); }
                    else          { lits[0] = -va; lits[1] = -vb; add_clause(lits, 2, -1); }
                }
            }
            /* Columns. */
            for (int j = c0; j < c1; j++)
            for (int i = r0; i < r1; i++) {
                int va = vlit(i, j); if (!va) continue;
                for (int k = i + 1; k < r1; k++) {
                    int vb = vlit(k, j); if (!vb) continue;
                    if (va == vb) { lits[0] = -va; add_clause(lits, 1, -1); }
                    else          { lits[0] = -va; lits[1] = -vb; add_clause(lits, 2, -1); }
                }
            }
        }
    }

    if (FAR) {
        /* --far: forward half of Chebyshev-1 neighbourhood (4 directions). */
        static const int dirs1[4][2] = {
            {0,1},
            {1,-1},{1,0},{1,1}
        };
        const int (*dirs)[2] = dirs1;
        int ndirs             = 4;

        for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) {
            int va = vlit(i, j);
            if (!va) continue;
            for (int d = 0; d < ndirs; d++) {
                int i2 = i + dirs[d][0], j2 = j + dirs[d][1];
                if (i2 < 0 || i2 >= N || j2 < 0 || j2 >= N) continue;
                int vb = vlit(i2, j2);
                if (!vb) continue;
                if (va == vb) {
                    /* Same orbit variable — occupying it would place two
                     * cells within the blocked distance: force it false. */
                    lits[0] = -va;
                    add_clause(lits, 1, -1);
                } else {
                    lits[0] = -va; lits[1] = -vb;
                    add_clause(lits, 2, -1);
                }
            }
        }
    }

    /* --- Off-zone (--off K) constraints ---
     * Force every cell within Chebyshev distance K of the grid centre to be
     * false, except cells on the main diagonal (i==j).
     *
     * Centre is at ((N-1)/2, (N-1)/2); distance is computed exactly using
     * integer arithmetic: cell (i,j) is in the zone iff
     *   max(|2i-(N-1)|, |2j-(N-1)|) <= 2*OFF.
     *
     * With --sym and even N, anti-diagonal cells (i+j==N-1) share a 90°-orbit
     * with diagonal cells; forcing such an orbit to false would also eliminate
     * the diagonal cells that are meant to be kept.  Those cells are therefore
     * also exempted.  (For odd N + --sym the anti-diagonal already has vlit=0
     * and is handled by the "!v" guard below.) */
    /* --- Corner zone (--cut K) constraints ---
     * Force every cell within taxicab distance K of any corner to be false.
     * The four corners are (0,0), (0,N-1), (N-1,0), (N-1,N-1).
     * A cell (i,j) is in the zone iff
     *   min(i+j, i+(N-1-j), (N-1-i)+j, (N-1-i)+(N-1-j)) <= CUT.
     * No diagonal exemption — all cells in the zone are forced off. */
    if (CUT) {
        for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) {
            int d0 = i + j;
            int d1 = i + (N-1-j);
            int d2 = (N-1-i) + j;
            int d3 = (N-1-i) + (N-1-j);
            int dmin = d0;
            if (d1 < dmin) dmin = d1;
            if (d2 < dmin) dmin = d2;
            if (d3 < dmin) dmin = d3;
            if (dmin > CUT) continue;
            int v = vlit(i, j);
            if (!v) continue;
            lits[0] = -v;
            add_clause(lits, 1, -1);
        }
    }

    if (OFF) {
        for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) {
            /* Distance from centre (in 2x integer units, avoids fractions). */
            int di = 2 * i - (N - 1), dj = 2 * j - (N - 1);
            int cheb2 = (di < 0 ? -di : di) > (dj < 0 ? -dj : dj)
                        ? (di < 0 ? -di : di) : (dj < 0 ? -dj : dj);
            if (cheb2 > 2 * OFF) continue;          /* outside the zone */
            if (i == j) continue;                    /* main diagonal: exempt */
            /* Even N + --sym: anti-diagonal cell shares orbit with diagonal. */
            if (SYM && !(N & 1) && i + j == N - 1) continue;
            int v = vlit(i, j);
            if (!v) continue;                        /* already forced false */
            lits[0] = -v;
            add_clause(lits, 1, -1);
        }
    }

    /* --- Colour (--color) constraints ---
     *
     * Every cell (i,j) is assigned exactly one of K=ceil(N/2) colours,
     * independently of whether it is occupied.  The no-3-same-colour per line
     * constraints (emitted above in the no-triple section) apply to all cells.
     *
     * Per cell: exactly one colour variable is true.
     *   at-least-one: cvar(i,j,0) ∨ … ∨ cvar(i,j,K-1)
     *   at-most-one : pairwise ¬cvar ∨ ¬cvar (CNF) or k(K-1) (KNF). */
    if (COLOR) {
        for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) {
            /* at-least-one colour */
            for (int c = 0; c < K; c++) lits[c] = cvar(i, j, c);
            add_clause(lits, K, -1);
            /* at-most-one colour */
            if (KNF && K >= 2) {
                for (int c = 0; c < K; c++) lits[c] = -cvar(i, j, c);
                add_clause(lits, K, K - 1);
            } else {
                for (int a = 0; a < K; a++)
                for (int b = a + 1; b < K; b++) {
                    lits[0] = -cvar(i, j, a); lits[1] = -cvar(i, j, b);
                    add_clause(lits, 2, -1);
                }
            }
        }
    }
}

/* ---------- main -------------------------------------------------------- */

int main(int argc, char *argv[]) {
    N = 8; SYM = 0; KNF = 0; ALT = 0; FAR = 0; AMO = 0; OFF = 0; CUT = 0;
    COLOR = 0; K = 0; AUX = 0; END = 0; POS = 1;

    for (int i = 1; i < argc; i++) {
        if      (!strcmp(argv[i], "--sym"))   SYM = 1;
        else if (!strcmp(argv[i], "--knf"))   KNF = 1;
        else if (!strcmp(argv[i], "--cnf"))   KNF = 0;
        else if (!strcmp(argv[i], "--alt"))   ALT = 1;
        else if (!strcmp(argv[i], "--far"))   FAR  = 1;
        else if (!strcmp(argv[i], "--amo"))   AMO  = 1;
        else if (!strcmp(argv[i], "--color"))                   COLOR = 1;
        else if (!strcmp(argv[i], "--colors") && i + 1 < argc) { COLOR = 1; K = atoi(argv[++i]); }
        else if (!strcmp(argv[i], "--aux"))   AUX = 1;
        else if (!strcmp(argv[i], "--end"))   END = 1;
        else if (!strcmp(argv[i], "--off") && i + 1 < argc) OFF = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--cut") && i + 1 < argc) CUT = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--pos") && i + 1 < argc) POS = atoi(argv[++i]);
        else                                  N = atoi(argv[i]);
    }

    if (N < 2 || N > MAXN) { fprintf(stderr, "n must be 2..%d\n", MAXN); return 1; }

    if (COLOR && K == 0) K = (N + 1) / 2;   /* default: ceil(N/2) colours */

    if (SYM) compute_reps();

    /* --aux/--end: auxiliary variables are allocated above the base occupancy vars. */
    aux_var_count = SYM ? norbs : N * N;

    pass();                    /* collect all clauses into store */
    eliminate_subsumed();      /* remove subsumed clauses */

    /* nvars: for --aux/--end the count grows during pass() as aux vars are allocated. */
    int nvars = ((AUX || END) ? aux_var_count : (SYM ? norbs : N * N))
                + (COLOR ? N * N * K : 0);
    fprintf(stdout, "c No-three-in-line, %dx%d grid\n", N, N);
    fprintf(stdout, "c var(i,j): quadrant row-major i*%d+j+1; see source for shell extension\n", N/2);
    if (SYM) fprintf(stdout, "c symmetry: 90°-rotation — %d orbits (%d occupancy variables, down from %d)\n", norbs, SYM ? norbs : N*N, N*N);
    if (COLOR) fprintf(stdout, "c coloring:   --color — %d colors (ceil(n/2)); every cell colored, no line has 3 cells of the same color\n", K);
    if (COLOR) fprintf(stdout, "c             color vars: cvar(i,j,c) = %d + (i*%d+j)*%d + c + 1  (vars %d..%d)\n",
                       N*N, N, K, N*N+1, N*N+N*N*K);
    if (AUX || END) fprintf(stdout, "c encoding:   --%s — recursive aux-variable AMT encoding (tail order: %s); %d base vars + %d aux vars\n",
                     END ? "end" : "aux", END ? "x5…xm,y1,y2" : "y1,y2,x5…xm",
                     SYM ? norbs : N * N, aux_var_count - (SYM ? norbs : N * N));
    if (ALT) fprintf(stdout, "c relaxation: --alt — rows exactly 2, columns at-least-2 (no-triple skipped for columns)\n");
    if (FAR)  fprintf(stdout, "c distance:   --far  — no two selected points within Chebyshev distance 1\n");
    if (AMO)  fprintf(stdout, "c amo:        --amo  — at most one per row/col per quadrant%s\n",
                      SYM ? " (top-left only; symmetry covers the rest)" : " (all four quadrants)");
    if (OFF)  fprintf(stdout, "c off-zone:   --off %d — cells within Chebyshev distance %d of centre forced false (diagonal exempt)\n", OFF, OFF);
    if (CUT)  fprintf(stdout, "c corners:    --cut %d — cells within taxicab distance %d of any corner forced false\n", CUT, CUT);

    /* --pos P: count how many all-positive CNF clauses there are so the header
     * can report the correct total (each such clause is emitted POS times). */
    int nclauses = cstore_n;
    if (POS > 1) {
        for (int i = 0; i < cstore_n; i++) {
            Clause *c = &cstore[i];
            if (c->bound >= 0) continue;      /* KNF klause — not duplicated */
            int all_pos = 1;
            for (int j = 0; j < c->len; j++)
                if (c->lits[j] < 0) { all_pos = 0; break; }
            if (all_pos) nclauses += POS - 1;
        }
    }
    if (POS > 1) fprintf(stdout, "c pos:        --pos %d — all-positive clauses duplicated %d times\n", POS, POS);
    fprintf(stdout, "p %s %d %d\n", KNF ? "knf" : "cnf", nvars, nclauses);

    for (int i = 0; i < cstore_n; i++) {
        Clause *c = &cstore[i];
        /* Determine repetition count: all-positive CNF clauses are emitted POS times. */
        int times = 1;
        if (POS > 1 && c->bound < 0) {
            int all_pos = 1;
            for (int j = 0; j < c->len; j++)
                if (c->lits[j] < 0) { all_pos = 0; break; }
            if (all_pos) times = POS;
        }
        for (int t = 0; t < times; t++) {
            if (c->bound > 1) fprintf(stdout, "k %d", c->bound);
            for (int j = 0; j < c->len; j++) fprintf(stdout, " %d", c->lits[j]);
            fprintf(stdout, " 0\n");
        }
        free(c->lits);
    }
    free(cstore);

    return 0;
}
