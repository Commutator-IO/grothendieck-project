# Exact dimension of F_i k(U_n) = k(U_n) ∩ (blocks with len <= i), and its decomposition as an S_n-module
# under conjugation, without eliminating on the full (n-1)! x (n-1)! Gram matrix.
#
# K = kernel of G (G as in gram.py) is stable under conjugation. For a Young subgroup S_nu and
# eps in {trivial, sign}, dim K^{(S_nu, eps)} = sum_mu k_mu <chi_mu ⊗ eps, Ind_{S_nu} 1>
#   = sum_mu k_mu K_{mu nu} (eps trivial)  or  sum_mu k_mu K_{mu' nu} (eps = sign),
# and dim K^{(S_nu, eps)} = (number of eps-orbit sums) - rank_Q(G restricted to them), computed exactly
# by fraction-free (Bareiss) elimination over Z. Solving for the multiplicities k_mu gives
# dim K = sum_mu k_mu dim(mu) exactly.
import sys, math
from fractions import Fraction
from common import *
n, i = int(sys.argv[1]), int(sys.argv[2])
mode = sys.argv[3] if len(sys.argv) > 3 else 'R'
check_table(n)
P = list(partitions(n))
Lam = [l for l in P if (len(l) > i if mode == 'R' else len(l) <= i)]
C = ncycles(n); pos = {c: k for k, c in enumerate(C)}; Ci = [inverse(c) for c in C]
fcache = {}
def f(t):
    if t not in fcache: fcache[t] = sum(dim(l) * chi(l, t) for l in Lam)
    return fcache[t]
def conj(g, c): return compose(compose(g, c), inverse(g))
def sgn(p): return (-1) ** (len(p) - len(cyctype(p)))
def gens(nu):
    out = []; s = 0
    for part in nu:
        for a in range(s, s + part - 1):
            g = list(range(n)); g[a], g[a + 1] = g[a + 1], g[a]; out.append(tuple(g))
        s += part
    return out
def orbits(nu, eps):
    gs = gens(nu); seen = {}; orbs = []
    for k in range(len(C)):
        if k in seen: continue
        orb = {k: 1}; stack = [k]; ok = True
        while stack:
            a = stack.pop()
            for g in gs:
                b = pos[conj(g, C[a])]; s = orb[a] * (-1 if eps == 'sgn' else 1)
                if b in orb:
                    if orb[b] != s: ok = False
                else:
                    orb[b] = s; stack.append(b)
        for b in orb: seen[b] = 1
        if ok: orbs.append(orb)
    return orbs
def rank_bareiss(M):
    M = [r[:] for r in M]; rows = len(M); cols = len(M[0]) if M else 0; r = 0; prev = 1
    for col in range(cols):
        p = next((k for k in range(r, rows) if M[k][col]), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        for k in range(r + 1, rows):
            M[k] = [(M[r][col] * M[k][j] - M[k][col] * M[r][j]) // prev for j in range(cols)]
        prev = M[r][col]; r += 1
        if r == rows: break
    return r
def fixed_kernel_dim(nu, eps):
    orbs = orbits(nu, eps)
    if not orbs: return 0, 0
    M = []
    for a in orbs:
        a0, sa = next(iter(a.items()))
        row = []
        for b in orbs:
            row.append(len(a) * sum(sa * sb * f(cyctype(compose(Ci[a0], C[c]))) for c, sb in b.items()))
        M.append(row)
    return len(orbs), len(orbs) - rank_bareiss(M)
def kostka_like(mu, nu):   # <chi_mu, Ind_{S_nu} 1> = (1/|S_nu|) sum_{g in S_nu} chi_mu(g), via cycle-type counts
    # enumerate cycle types of S_nu as products of cycle types of the factors
    def zinv(t): return Fraction(1, math.prod(m ** t.count(m) * math.factorial(t.count(m)) for m in set(t)))
    tot = Fraction(0)
    def rec(k, acc, w):
        nonlocal tot
        if k == len(nu):
            tot += w * chi(mu, tuple(sorted(acc, reverse=True))); return
        for t in partitions(nu[k]): rec(k + 1, acc + list(t), w * zinv(t))
    rec(0, [], Fraction(1)); return tot
def conjp(l): return tuple(sum(1 for x in l if x > j) for j in range(l[0]))
size = lambda nu: math.prod(math.factorial(x) for x in nu)
eqs = []
for nu in P:
    for eps in ('triv', 'sgn'):
        if size(nu) < (int(sys.argv[4]) if len(sys.argv) > 4 else 24): continue
        N, d = fixed_kernel_dim(nu, eps)
        row = [kostka_like(mu if eps == 'triv' else conjp(mu), nu) for mu in P]
        eqs.append((row, Fraction(d))); print('nu', nu, eps, 'orbit sums', N, 'kernel', d, flush=True)
# solve the (overdetermined, consistent) system exactly
A = [r + [b] for r, b in eqs]; m = len(P); piv = []; r = 0
for col in range(m):
    p = next((k for k in range(r, len(A)) if A[k][col] != 0), None)
    if p is None: continue
    A[r], A[p] = A[p], A[r]; v = A[r][col]; A[r] = [x / v for x in A[r]]
    for k in range(len(A)):
        if k != r and A[k][col] != 0:
            fct = A[k][col]; A[k] = [x - fct * y for x, y in zip(A[k], A[r])]
    piv.append(col); r += 1
assert len(piv) == m, 'system not of full rank: %d of %d' % (len(piv), m)
assert all(all(x == 0 for x in row) for row in A[r:]), 'inconsistent'
k = {P[c]: A[j][m] for j, c in enumerate(piv)}
assert all(v.denominator == 1 and v >= 0 for v in k.values())
print('multiplicities:', {mu: int(v) for mu, v in k.items() if v})
print('EXACT dim =', sum(int(v) * dim(mu) for mu, v in k.items()))
