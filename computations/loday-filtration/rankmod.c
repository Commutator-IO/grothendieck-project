/* rank mod p of G_i[c,c'] = f_i(type(c^{-1} c')), c, c' n-cycles of S_n, for i = 1..n.
   usage: rankmod table_n.txt p [i]   */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int n, np, T[64][12]; static long long F[64][12];
static int cyc[50000][12], N;
static void gen(int *seq, int k, int used) {
  if (k == n) { int *p = cyc[N++]; for (int j = 0; j < n; j++) p[seq[j]] = seq[(j+1)%n]; return; }
  for (int v = 1; v < n; v++) if (!(used >> v & 1)) { seq[k] = v; gen(seq, k+1, used | 1<<v); }
}
static int typeidx(const int *a, const int *b) { /* type of a^{-1} b */
  int ai[12], q[12], seen[12] = {0}, t[12], L = 0;
  for (int j = 0; j < n; j++) ai[a[j]] = j;
  for (int j = 0; j < n; j++) q[j] = ai[b[j]];
  for (int j = 0; j < n; j++) if (!seen[j]) { int l = 0, x = j; while (!seen[x]) { seen[x] = 1; x = q[x]; l++; } t[L++] = l; }
  for (int u = 0; u < L; u++) for (int v = u+1; v < L; v++) if (t[v] > t[u]) { int w = t[u]; t[u] = t[v]; t[v] = w; }
  for (int j = L; j < n; j++) t[j] = 0;
  for (int k = 0; k < np; k++) if (!memcmp(t, T[k], n * sizeof(int))) return k;
  fprintf(stderr, "type not found\n"); exit(1);
}
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); uint64_t p = strtoull(argv[2], 0, 10); int only = argc > 3 ? atoi(argv[3]) : 0;
  fscanf(f, "%d %d", &n, &np);
  for (int k = 0; k < np; k++) { for (int j = 0; j < n; j++) fscanf(f, "%d", &T[k][j]); for (int i = 0; i < n; i++) fscanf(f, "%lld", &F[k][i]); }
  int seq[12]; seq[0] = 0; gen(seq, 1, 1);
  unsigned char *ty = malloc((size_t)N * N);
  for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) ty[(size_t)a*N+b] = typeidx(cyc[a], cyc[b]);
  uint64_t *M = malloc(sizeof(uint64_t) * (size_t)N * N);
  for (int i = 1; i <= n; i++) {
    if (only && i != only) continue;
    for (size_t e = 0; e < (size_t)N*N; e++) { long long v = F[ty[e]][i-1] % (long long)p; if (v < 0) v += p; M[e] = v; }
    int r = 0;
    for (int col = 0; col < N && r < N; col++) {
      int pv = -1; for (int k = r; k < N; k++) if (M[(size_t)k*N+col]) { pv = k; break; }
      if (pv < 0) continue;
      if (pv != r) for (int j = 0; j < N; j++) { uint64_t w = M[(size_t)r*N+j]; M[(size_t)r*N+j] = M[(size_t)pv*N+j]; M[(size_t)pv*N+j] = w; }
      uint64_t x = M[(size_t)r*N+col], inv = 1, e = p-2; while (e) { if (e&1) inv = inv*x%p; x = x*x%p; e >>= 1; }
      uint64_t *R = M + (size_t)r*N;
      for (int j = col; j < N; j++) R[j] = R[j]*inv%p;
      for (int k = r+1; k < N; k++) { uint64_t *K = M + (size_t)k*N; uint64_t c = K[col]; if (!c) continue; c = p - c;
        for (int j = col; j < N; j++) K[j] = (K[j] + c*R[j]) % p; }
      r++;
    }
    printf("n=%d i=%d N=%d rank mod %llu = %d  => dim F_i k(U_n) <= %d\n", n, i, N, (unsigned long long)p, r, N - r); fflush(stdout);
  }
  return 0;
}
