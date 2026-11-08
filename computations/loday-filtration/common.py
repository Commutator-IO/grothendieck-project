# Shared tools: partitions, Murnaghan-Nakayama characters, cycle types, n-cycles of S_n.
import itertools
from functools import lru_cache
def partitions(n, m=None):
    if m is None: m = n
    if n == 0: yield (); return
    for k in range(min(n, m), 0, -1):
        for p in partitions(n - k, k): yield (k,) + p
@lru_cache(None)
def chi(lam, mu):
    """character of the irreducible S_n-module of shape lam at cycle type mu (Murnaghan-Nakayama)"""
    if not mu: return 1 if sum(lam) == 0 else 0
    r, rest = mu[0], mu[1:]
    L = len(lam); beta = [lam[i] + L - 1 - i for i in range(L)]
    tot = 0
    for b in beta:
        nb = b - r
        if nb < 0 or nb in beta: continue
        sign = (-1) ** sum(1 for c in beta if nb < c < b)
        newb = sorted([c for c in beta if c != b] + [nb], reverse=True)
        Ln = len(newb); newlam = tuple(x for x in (newb[j] - (Ln - 1 - j) for j in range(Ln)) if x > 0)
        tot += sign * chi(newlam, rest)
    return tot
def cyctype(p):
    n = len(p); seen = [0] * n; t = []
    for i in range(n):
        if not seen[i]:
            l = 0; j = i
            while not seen[j]: seen[j] = 1; j = p[j]; l += 1
            t.append(l)
    return tuple(sorted(t, reverse=True))
def compose(a, b): return tuple(a[b[k]] for k in range(len(a)))   # (a b)(k) = a(b(k))
def inverse(a):
    r = [0] * len(a)
    for i, x in enumerate(a): r[x] = i
    return tuple(r)
def ncycles(n):
    """all n-cycles of S_n, as tuples p with p[k] = image of k; sorted"""
    out = []
    for rest in itertools.permutations(range(1, n)):
        seq = (0,) + rest; p = [0] * n
        for k in range(n): p[seq[k]] = seq[(k + 1) % n]
        out.append(tuple(p))
    return sorted(out)
def dim(lam): return chi(lam, (1,) * sum(lam))
def check_table(n):
    P = list(partitions(n)); import math
    assert sum(dim(l) ** 2 for l in P) == math.factorial(n)
    # column orthogonality at identity vs n-cycle
    assert sum(dim(l) * chi(l, (n,)) for l in P) == 0
