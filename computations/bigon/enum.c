/*
 * enum.c -- enumerate arrangements of n pseudolines in the real projective
 * plane up to isomorphism, as reorientation classes of rank-3 oriented
 * matroids on a simple matroid (no loops, no parallel elements).
 *
 * Method.  Level n+1 is obtained from level n by all single-element
 * extensions: for a representative chirotope chi on {0..n-1} we backtrack
 * over the values chi(a,b,n) in {+,0,-} (in {+,-} in "simple" mode),
 * pruning with
 *   - the 3-term Grassmann-Pluecker relations (all that contain the new
 *     value), and
 *   - the matroid condition for a simple rank-3 matroid: in every 4-set the
 *     number of zero triples is 0, 1 or 4.
 * By Bjoerner-Las Vergnas-Sturmfels-White-Ziegler, Thm 3.6.2, an alternating
 * map whose support is the set of bases of a matroid and which satisfies the
 * 3-term GP relations is a chirotope.  Every arrangement of n+1 >= 4
 * pseudolines has a pseudoline whose deletion is still of rank 3, so
 * extending one representative of every class at level n reaches every
 * class at level n+1.
 *
 * Isomorphism.  Each extension is put in canonical form through its cell
 * decomposition of the sphere (the double cover of the projective
 * arrangement): the flag graph (vertex, edge, face) with its three
 * involutions s0, s1, s2 is built from the cocircuits; a breadth-first
 * search from a start flag orders the pseudolines (first appearance) and
 * fixes a reorientation (the start face becomes the all-positive tope);
 * the resulting chirotope, normalised up to global sign, is the code of
 * that start flag.  The canonical form is the least code over the start
 * flags of maximal invariant (vertex degree, face size, ...).  Two
 * chirotopes get the same canonical form iff they differ by relabelling,
 * reorientation and global sign, i.e. iff the projective arrangements are
 * isomorphic (reflections allowed).
 *
 * Modes:
 *   all    : every class (simple and non-simple arrangements)
 *   simple : uniform chirotopes only (simple arrangements)
 *   avoid  : the deletion-closed class of arrangements containing no
 *            sub-arrangement II_5, II'_{3,2} or III_6 (see README)
 *
 * Usage:  ./enum MODE NMAX OUTDIR
 * For each n it prints counts and writes OUTDIR/MODE_n.txt with one line
 * per bigon-free class: its multiple points (flats with >= 3 pseudolines),
 * pseudolines written as hex digits, separated by commas; then a tab and
 * the canonical chirotope (one of + 0 - per triple a<b<c, lex order).
 * In avoid mode every class is written, with a third field bigonal or
 * bigon-free.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 16
#define MAXF 128           /* flats of rank 2: at most C(16,2)=120 */
#define MAXCO (2 * MAXF)
#define MAXE (2 * MAXN * MAXN)
#define MAXFL (4 * MAXE)

typedef signed char s8;

static int N;                       /* number of elements of current chi */
static s8 chi[MAXN][MAXN][MAXN];    /* 2 = unassigned */
static int mode;                    /* 0 all, 1 simple, 2 avoid */

static void setchi(int a, int b, int c, int v) {
  chi[a][b][c] = chi[b][c][a] = chi[c][a][b] = v;
  int w = (v == 2) ? 2 : -v;
  chi[b][a][c] = chi[a][c][b] = chi[c][b][a] = w;
}

static void decode(const char *s, int n) {
  N = n;
  int t = 0;
  for (int a = 0; a < n; a++)
    for (int b = a + 1; b < n; b++)
      for (int c = b + 1; c < n; c++) {
        char ch = s[t++];
        setchi(a, b, c, ch == '+' ? 1 : ch == '-' ? -1 : 0);
      }
}

/* ---------------- canonical form ---------------- */

typedef struct { uint32_t P, M; } SV;

static int nfl;
static uint32_t flat[MAXF];
static int pf[MAXN][MAXN];      /* flat index of pair */
static SV co[MAXCO];            /* co[2f], co[2f+1] = -co[2f] */
static int ne;
static int eline[MAXE], eend[MAXE][2];
static SV esv[MAXE];
static int vinc[MAXCO][2 * MAXN], nvinc[MAXCO];
static int fs1[MAXFL], fface[MAXFL];

static SV neg(SV y) { SV z = {y.M, y.P}; return z; }

static void computeflats(void) {
  int n = N;
  nfl = 0;
  for (int a = 0; a < n; a++)
    for (int b = a + 1; b < n; b++) pf[a][b] = -1;
  for (int a = 0; a < n; a++)
    for (int b = a + 1; b < n; b++) {
      if (pf[a][b] >= 0) continue;
      uint32_t m = (1u << a) | (1u << b);
      for (int c = 0; c < n; c++)
        if (c != a && c != b && chi[a][b][c] == 0) m |= 1u << c;
      int f = nfl++;
      flat[f] = m;
      for (int x = 0; x < n; x++)
        if (m >> x & 1)
          for (int y = x + 1; y < n; y++)
            if (m >> y & 1) pf[x][y] = f;
      SV y = {0, 0};
      for (int e = 0; e < n; e++) {
        if (chi[a][b][e] > 0) y.P |= 1u << e;
        else if (chi[a][b][e] < 0) y.M |= 1u << e;
      }
      co[2 * f] = y;
      co[2 * f + 1] = neg(y);
    }
}

static int PF(int a, int b) { return a < b ? pf[a][b] : pf[b][a]; }

/* cocircuit id of s*chi(i,j,.) */
static int coid(int i, int j, int s) {
  int f = PF(i, j);
  SV y = co[2 * f];
  /* find e with chi(i,j,e) != 0 and compare */
  for (int e = 0; e < N; e++) {
    int v = chi[i][j][e];
    if (v) {
      int yv = (y.P >> e & 1) ? 1 : -1;
      return (s * v == yv) ? 2 * f : 2 * f + 1;
    }
  }
  return -1;
}

static void build(void) {
  int n = N;
  computeflats();
  ne = 0;
  for (int v = 0; v < 2 * nfl; v++) nvinc[v] = 0;
  for (int i = 0; i < n; i++) {
    /* representatives of flats through i */
    int rep[MAXN] = {0}, m = 0;
    for (int f = 0; f < nfl; f++)
      if (flat[f] >> i & 1) {
        uint32_t r = flat[f] & ~(1u << i);
        rep[m++] = __builtin_ctz(r);
      }
    int r = rep[0];
    /* upper half: directions (s,j) with s*chi(i,r,j) > 0 */
    int us[MAXN], uj[MAXN], k = 0;
    for (int t = 1; t < m; t++) {
      int j = rep[t];
      us[k] = chi[i][r][j] > 0 ? 1 : -1;
      uj[k] = j;
      k++;
    }
    /* insertion sort: u before w iff det(u,w) > 0 */
    for (int x = 1; x < k; x++) {
      int s = us[x], j = uj[x], y = x - 1;
      while (y >= 0 && s * us[y] * chi[i][uj[y]][j] < 0) {
        us[y + 1] = us[y]; uj[y + 1] = uj[y]; y--;
      }
      us[y + 1] = s; uj[y + 1] = j;
    }
    int cyc[2 * MAXN], L = 0;
    cyc[L++] = coid(i, r, 1);
    for (int x = 0; x < k; x++) cyc[L++] = coid(i, uj[x], us[x]);
    cyc[L++] = coid(i, r, -1);
    for (int x = 0; x < k; x++) cyc[L++] = coid(i, uj[x], -us[x]);
    for (int x = 0; x < L; x++) {
      int Y = cyc[x], Z = cyc[(x + 1) % L];
      int e = ne++;
      eline[e] = i;
      eend[e][0] = Y;
      eend[e][1] = Z;
      SV y = co[Y], z = co[Z], c;
      uint32_t ysup = y.P | y.M;
      c.P = y.P | (z.P & ~ysup);
      c.M = y.M | (z.M & ~ysup);
      esv[e] = c;
      vinc[Y][nvinc[Y]++] = e;
      vinc[Z][nvinc[Z]++] = e;
    }
  }
  /* s1 */
  int F = 4 * ne;
  for (int f = 0; f < F; f++) {
    int e = f >> 2, side = (f >> 1) & 1, sg = f & 1; /* sg 0:+ 1:- */
    int i = eline[e], Y = eend[e][side];
    SV T = esv[e];
    if (sg == 0) T.P |= 1u << i; else T.M |= 1u << i;
    int found = -1;
    for (int t = 0; t < nvinc[Y]; t++) {
      int e2 = vinc[Y][t];
      if (e2 == e) continue;
      int j = eline[e2];
      uint32_t bj = 1u << j;
      if (esv[e2].P == (T.P & ~bj) && esv[e2].M == (T.M & ~bj)) {
        int side2 = (eend[e2][0] == Y) ? 0 : 1;
        int sg2 = (T.P & bj) ? 0 : 1;
        found = e2 * 4 + side2 * 2 + sg2;
        break;
      }
    }
    if (found < 0) { fprintf(stderr, "s1 not found\n"); exit(1); }
    fs1[f] = found;
  }
  /* face sizes */
  for (int f = 0; f < F; f++) fface[f] = -1;
  static int orb[MAXFL];
  for (int f = 0; f < F; f++) {
    if (fface[f] >= 0) continue;
    int L = 0, x = f;
    do {
      orb[L++] = x; x ^= 2;
      orb[L++] = x; x = fs1[x];
    } while (x != f);
    for (int t = 0; t < L; t++) fface[orb[t]] = L / 2;
  }
}

static int flagkey(int f, int part) {
  int e = f >> 2, side = (f >> 1) & 1;
  switch (part) {
    case 0: return __builtin_popcount(flat[eend[e][side] >> 1]);
    case 1: return fface[f];
    case 2: return __builtin_popcount(flat[eend[e][side ^ 1] >> 1]);
    default: return fface[f ^ 1];
  }
}

static void codefrom(int f0, char *out) {
  int n = N, F = 4 * ne;
  static int vis[MAXFL], q[MAXFL];
  int lab[MAXN], nl = 0;
  for (int x = 0; x < n; x++) lab[x] = -1;
  for (int x = 0; x < F; x++) vis[x] = 0;
  int h = 0, t = 0;
  q[t++] = f0; vis[f0] = 1;
  while (h < t && nl < n) {
    int x = q[h++];
    int li = eline[x >> 2];
    if (lab[li] < 0) lab[li] = nl++;
    int nb[3] = {x ^ 2, fs1[x], x ^ 1};
    for (int k = 0; k < 3; k++)
      if (!vis[nb[k]]) { vis[nb[k]] = 1; q[t++] = nb[k]; }
  }
  /* tope of f0 */
  int e = f0 >> 2, sg = f0 & 1, i0 = eline[e];
  SV T = esv[e];
  if (sg == 0) T.P |= 1u << i0; else T.M |= 1u << i0;
  int sig[MAXN];
  for (int x = 0; x < n; x++) sig[x] = (T.P >> x & 1) ? 1 : -1;
  int inv[MAXN];
  for (int x = 0; x < n; x++) inv[lab[x]] = x;
  int k = 0, gs = 0;
  for (int a = 0; a < n; a++)
    for (int b = a + 1; b < n; b++)
      for (int c = b + 1; c < n; c++) {
        int A = inv[a], B = inv[b], C = inv[c];
        int v = sig[A] * sig[B] * sig[C] * chi[A][B][C];
        if (gs == 0 && v) gs = v;
        v *= gs ? gs : 1;
        out[k++] = v > 0 ? '+' : v < 0 ? '-' : '0';
      }
  out[k] = 0;
}

static void canon(char *best) {
  build();
  int F = 4 * ne;
  int bestkey[4] = {-1, -1, -1, -1};
  static int cand[MAXFL];
  int nc = 0;
  for (int f = 0; f < F; f++) {
    int key[4], c = 0;
    for (int p = 0; p < 4; p++) key[p] = flagkey(f, p);
    for (int p = 0; p < 4 && c == 0; p++)
      c = (key[p] > bestkey[p]) - (key[p] < bestkey[p]);
    if (c > 0) { memcpy(bestkey, key, sizeof key); nc = 0; }
    if (c >= 0) cand[nc++] = f;
  }
  char cur[600];
  best[0] = 0;
  for (int t = 0; t < nc; t++) {
    codefrom(cand[t], cur);
    if (best[0] == 0 || strcmp(cur, best) < 0) strcpy(best, cur);
  }
}

/* ---------------- hash set of strings ---------------- */

typedef struct { char **slot; size_t cap, cnt; int len; } Set;

static uint64_t hsh(const char *s) {
  uint64_t h = 1469598103934665603ULL;
  for (; *s; s++) h = (h ^ (unsigned char)*s) * 1099511628211ULL;
  return h;
}
static void setinit(Set *S, int len) {
  S->cap = 1 << 16; S->cnt = 0; S->len = len;
  S->slot = calloc(S->cap, sizeof(char *));
}
static int setadd(Set *S, const char *s);
static void grow(Set *S) {
  char **old = S->slot; size_t oc = S->cap;
  S->cap *= 2; S->cnt = 0;
  S->slot = calloc(S->cap, sizeof(char *));
  for (size_t i = 0; i < oc; i++)
    if (old[i]) {
      size_t j = hsh(old[i]) & (S->cap - 1);
      while (S->slot[j]) j = (j + 1) & (S->cap - 1);
      S->slot[j] = old[i]; S->cnt++;
    }
  free(old);
}
static int setadd(Set *S, const char *s) {
  if (2 * (S->cnt + 1) > S->cap) grow(S);
  size_t j = hsh(s) & (S->cap - 1);
  while (S->slot[j]) {
    if (strcmp(S->slot[j], s) == 0) return 0;
    j = (j + 1) & (S->cap - 1);
  }
  S->slot[j] = strdup(s); S->cnt++;
  return 1;
}

/* ---------------- extension ---------------- */

static int npairs, pa[MAXN * MAXN], pb[MAXN * MAXN];
static Set *target;
static long nleaves;

static int gp(int p, int x1, int x2, int x3, int x4) {
  int a = chi[p][x1][x2], b = chi[p][x3][x4];
  int c = chi[p][x1][x3], d = chi[p][x2][x4];
  int e = chi[p][x1][x4], f = chi[p][x2][x3];
  if (a == 2 || b == 2 || c == 2 || d == 2 || e == 2 || f == 2) return 1;
  int t1 = a * b, t2 = -c * d, t3 = e * f;
  int pos = t1 > 0 || t2 > 0 || t3 > 0, ng = t1 < 0 || t2 < 0 || t3 < 0;
  if (!t1 && !t2 && !t3) return 1;
  return pos && ng;
}

static void sort4(int *x) {
  for (int i = 1; i < 4; i++) {
    int v = x[i], j = i - 1;
    while (j >= 0 && x[j] > v) { x[j + 1] = x[j]; j--; }
    x[j + 1] = v;
  }
}

static int consistent(int a, int b) {
  int n = N; /* new element index n, total n+1 elements */
  int nw = n;
  int tri[3] = {a, b, nw};
  /* 4-set matroid condition */
  for (int c = 0; c < n; c++) {
    if (c == a || c == b) continue;
    int v[4] = {chi[a][b][nw], chi[a][b][c], chi[a][c][nw], chi[b][c][nw]};
    int z = 0, nz = 0;
    for (int k = 0; k < 4; k++) {
      if (v[k] == 0) z++;
      else if (v[k] != 2) nz++;
    }
    if (z >= 2 && nz >= 1) return 0;
  }
  /* GP relations containing the triple {a,b,new} */
  for (int pi = 0; pi < 3; pi++) {
    int p = tri[pi], u = tri[(pi + 1) % 3], w = tri[(pi + 2) % 3];
    for (int c = 0; c <= n; c++) {
      if (c == a || c == b || c == nw) continue;
      for (int d = c + 1; d <= n; d++) {
        if (d == a || d == b || d == nw) continue;
        int x[4] = {u, w, c, d};
        sort4(x);
        if (!gp(p, x[0], x[1], x[2], x[3])) return 0;
      }
    }
  }
  return 1;
}

/* pattern check for avoid mode: subsets containing the new element */
static int conc(int a, int b, int c) { return chi[a][b][c] == 0; }

static int has_pattern_with_new(void) {
  int n = N + 1, nw = N;
  int idx[6];
  /* 5-subsets containing nw */
  for (int a = 0; a < nw; a++)
    for (int b = a + 1; b < nw; b++)
      for (int c = b + 1; c < nw; c++)
        for (int d = c + 1; d < nw; d++) {
          idx[0] = a; idx[1] = b; idx[2] = c; idx[3] = d; idx[4] = nw;
          int k = 0;
          for (int i = 0; i < 5; i++)
            for (int j = i + 1; j < 5; j++)
              for (int l = j + 1; l < 5; l++) k += conc(idx[i], idx[j], idx[l]);
          if (k == 0 || k == 1) return 1; /* II_5 or II'_{3,2} */
        }
  /* 6-subsets containing nw: III_6 */
  for (int a = 0; a < nw; a++)
    for (int b = a + 1; b < nw; b++)
      for (int c = b + 1; c < nw; c++)
        for (int d = c + 1; d < nw; d++)
          for (int e = d + 1; e < nw; e++) {
            idx[0] = a; idx[1] = b; idx[2] = c; idx[3] = d; idx[4] = e; idx[5] = nw;
            int k = 0, deg[6] = {0};
            for (int i = 0; i < 6; i++)
              for (int j = i + 1; j < 6; j++)
                for (int l = j + 1; l < 6; l++)
                  if (conc(idx[i], idx[j], idx[l])) { k++; deg[i]++; deg[j]++; deg[l]++; }
            if (k == 4) {
              int ok = 1;
              for (int i = 0; i < 6; i++) ok &= deg[i] == 2;
              if (ok) return 1;
            }
          }
  (void)n;
  return 0;
}

static void leaf(void) {
  nleaves++;
  if (mode == 2 && has_pattern_with_new()) return;
  int n0 = N;
  N = n0 + 1;
  char buf[600];
  canon(buf);
  N = n0;
  setadd(target, buf);
}

static void bt(int t) {
  if (t == npairs) { leaf(); return; }
  int a = pa[t], b = pb[t];
  static const int vals[3] = {1, -1, 0};
  int nv = (mode == 1) ? 2 : 3;
  for (int k = 0; k < nv; k++) {
    setchi(a, b, N, vals[k]);
    if (consistent(a, b)) bt(t + 1);
  }
  setchi(a, b, N, 2);
}

static void extend(const char *rep, int n, Set *out) {
  decode(rep, n);
  for (int a = 0; a < n; a++)
    for (int b = a + 1; b < n; b++) setchi(a, b, n, 2);
  npairs = 0;
  for (int a = 0; a < n; a++)
    for (int b = a + 1; b < n; b++) { pa[npairs] = a; pb[npairs] = b; npairs++; }
  target = out;
  bt(0);
}

/* ---------------- reporting ---------------- */

static void describe(const char *s, int n, FILE *fp, long *bf, long *bfns,
                     long *simple) {
  decode(s, n);
  computeflats();
  int pts[MAXN] = {0};
  int ns = 1;
  for (int f = 0; f < nfl; f++) {
    if (__builtin_popcount(flat[f]) > 2) ns = 0;
    for (int x = 0; x < n; x++)
      if (flat[f] >> x & 1) pts[x]++;
  }
  if (ns) (*simple)++;
  int bigon = 0;
  for (int x = 0; x < n; x++) if (pts[x] <= 2) bigon = 1;
  if (bigon && mode != 2) return;
  if (!bigon) {
    (*bf)++;
    if (!ns) (*bfns)++;
  }
  if (fp) {
    int first = 1;
    for (int f = 0; f < nfl; f++)
      if (__builtin_popcount(flat[f]) > 2) {
        if (!first) fputc(',', fp);
        first = 0;
        for (int x = 0; x < n; x++)
          if (flat[f] >> x & 1) fputc("0123456789abcdef"[x], fp);
      }
    fprintf(fp, "\t%s", s);
    if (mode == 2) fprintf(fp, "\t%s", bigon ? "bigonal" : "bigon-free");
    fputc('\n', fp);
  }
}

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: enum all|simple|avoid NMAX OUTDIR\n"); return 1; }
  mode = !strcmp(argv[1], "all") ? 0 : !strcmp(argv[1], "simple") ? 1 : 2;
  int nmax = atoi(argv[2]);
  if (nmax > MAXN) nmax = MAXN;
  const char *outdir = argv[3];
  Set cur;
  setinit(&cur, 1);
  setadd(&cur, "+");
  printf("mode=%s\n%3s %10s %10s %10s %10s %12s\n", argv[1], "n", "classes",
         "simple", "bigonfree", "bf-nonsimp", "extensions");
  for (int n = 3;; n++) {
    char path[512];
    snprintf(path, sizeof path, "%s/%s_%d.txt", outdir, argv[1], n);
    FILE *fp = fopen(path, "w");
    long bf = 0, bfns = 0, simple = 0;
    for (size_t i = 0; i < cur.cap; i++)
      if (cur.slot[i]) describe(cur.slot[i], n, fp, &bf, &bfns, &simple);
    if (fp) fclose(fp);
    printf("%3d %10zu %10ld %10ld %10ld %12ld\n", n, cur.cnt, simple, bf, bfns,
           nleaves);
    fflush(stdout);
    if (n == nmax || cur.cnt == 0) break;
    Set nxt;
    setinit(&nxt, 1);
    nleaves = 0;
    for (size_t i = 0; i < cur.cap; i++)
      if (cur.slot[i]) extend(cur.slot[i], n, &nxt);
    for (size_t i = 0; i < cur.cap; i++) free(cur.slot[i]);
    free(cur.slot);
    cur = nxt;
  }
  return 0;
}
