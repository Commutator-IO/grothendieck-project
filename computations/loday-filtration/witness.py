# Exact kernel of the Gram matrix over Q for (n, i), an independent check in the group algebra, and
# the S_n-character (conjugation action) of F_i k(U_n).
import sys, itertools, math
from fractions import Fraction
from common import *
from gram import gram
n, i = int(sys.argv[1]), int(sys.argv[2])
Lam = [l for l in partitions(n) if len(l) > i]
C, G = gram(n, Lam); N = len(C); pos = {c: k for k, c in enumerate(C)}
# RREF over Q
M = [[Fraction(x) for x in r] for r in G]; pivcols = []; r = 0
for col in range(N):
    p = next((k for k in range(r, N) if M[k][col] != 0), None)
    if p is None: continue
    M[r], M[p] = M[p], M[r]; v = M[r][col]; M[r] = [x / v for x in M[r]]
    for k in range(N):
        if k != r and M[k][col] != 0:
            f = M[k][col]; M[k] = [a - f * b for a, b in zip(M[k], M[r])]
    pivcols.append(col); r += 1
free = [c for c in range(N) if c not in pivcols]
basis = []
for fc in free:
    v = [Fraction(0)] * N; v[fc] = Fraction(1)
    for row, pc in zip(M, pivcols): v[pc] = -row[fc]
    den = math.lcm(*[x.denominator for x in v]); v = [int(x * den) for x in v]
    g = math.gcd(*v); basis.append([x // g for x in v])
print('rank over Q', r, 'dim F_%d k(U_%d) =' % (i, n), len(basis))
# independent check: x * (sum_g chi_lam(g) g) = 0 in Q[S_n] for every lam in Lam
G_all = list(itertools.permutations(range(n)))
def times_central(x, lam):
    out = {}
    for c, a in x.items():
        if a == 0: continue
        for g in G_all:
            h = compose(c, g); out[h] = out.get(h, 0) + a * chi(lam, cyctype(g))
    return {h: v for h, v in out.items() if v}
for v in basis:
    x = {C[k]: v[k] for k in range(N) if v[k]}
    for lam in Lam: assert not times_central(x, lam)
# also: each basis vector is NOT killed by some lam with len <= i (sanity: nonzero element)
print('group-algebra check passed for', len(basis), 'vectors')
# character of conjugation action on the kernel
def coords(w):  # w in kernel; coordinates in basis = values at free columns
    return [w[fc] / 1 for fc in free]
B = [[Fraction(x) for x in v] for v in basis]
# normalise: basis has value at its free column = scale s_k
scale = [B[k][free[k]] for k in range(len(B))]
reps = {}
for g in G_all: reps.setdefault(cyctype(g), g)
charK = {}
for t, g in reps.items():
    gi = inverse(g); tr = Fraction(0)
    for k, v in enumerate(B):
        w = [Fraction(0)] * N
        for j in range(N):
            if v[j]: w[pos[compose(compose(g, C[j]), gi)]] += v[j]
        tr += w[free[k]] / scale[k]
    charK[t] = tr
mult = {}
z = lambda t: math.prod(m ** t.count(m) * math.factorial(t.count(m)) for m in set(t))
for lam in partitions(n):
    m = sum(charK[t] * chi(lam, t) / z(t) for t in charK)
    if m: mult[lam] = m
print('character of F_i k(U_n) (conjugation):', {''.join(map(str, t)): int(v) for t, v in charK.items()})
print('decomposition:', mult)
# sparsest basis vector
best = min(basis, key=lambda v: sum(1 for x in v if x))
print('sparsest RREF vector: support', sum(1 for x in best if x), 'max |coef|', max(abs(x) for x in best))
with open('witness_n%d_i%d.txt' % (n, i), 'w') as fh:
    for v in basis:
        fh.write(' '.join('%d:%s' % (x, ''.join(map(str, C[k]))) for k, x in enumerate(v) if x) + '\n')
