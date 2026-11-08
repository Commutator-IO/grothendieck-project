# Loday filtration test, Gram-matrix form.
# For x in the span of the n-cycles in Q[S_n] and a set Lam of shapes, rho_lam(x) = 0 for all lam in Lam
# iff G x = 0, where G[c,c'] = sum_{lam in Lam} dim(lam) chi_lam(c^{-1} c')  (G is PSD: x^T G x =
# n! * sum_lam ||rho_lam(x)||^2_HS / dim(lam) ... up to positive factors).  F_i k(U_n) = kernel of G for
# Lam = {lam : len(lam) > i}.
import sys
from common import *
def gram(n, Lam):
    C = ncycles(n); Ci = [inverse(c) for c in C]
    f = {}
    G = []
    for a in range(len(C)):
        row = []
        for b in range(len(C)):
            t = cyctype(compose(Ci[a], C[b]))
            if t not in f: f[t] = sum(dim(l) * chi(l, t) for l in Lam)
            row.append(f[t])
        G.append(row)
    return C, G
def rank_mod(G, p):
    M = [[x % p for x in r] for r in G]; n = len(M); m = len(M[0]); r = 0
    for col in range(m):
        piv = next((i for i in range(r, n) if M[i][col]), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][col], p - 2, p); M[r] = [x * inv % p for x in M[r]]
        for i in range(n):
            if i != r and M[i][col]:
                f = M[i][col]; Mi = M[i]; Mr = M[r]
                M[i] = [(u - f * v) % p for u, v in zip(Mi, Mr)]
        r += 1
    return r
if __name__ == '__main__':
    n = int(sys.argv[1]); check_table(n)
    for i in range(1, n + 1):
        Lam = [l for l in partitions(n) if len(l) > i]
        if not Lam: print(n, i, 'dim', len(ncycles(n))); continue
        C, G = gram(n, Lam)
        rs = [rank_mod(G, p) for p in (1000003, 998244353)]
        print(n, i, 'ranks mod p', rs, 'dim F_i k(U_n) <=', len(C) - max(rs), flush=True)
