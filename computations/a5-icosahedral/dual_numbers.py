"""Folder 85, p. 40, the scheme structure in characteristic 5.

Spec Z[T]/(T^2+T-1) is not reduced at 5 (T^2+T-1 = (T-2)^2 mod 5). Field points do not see
this, so test the representability claim on R = F_q[e]/(e^2), a local Artinian ring with
finite residue field (forms of PGL2 over R are split, and Aut(PGL2_R) = PGL2(R)):
    #{homs A5 -> PGL2(R) injective on the closed fibre}
        = |PGL2(R)| * #{x in R : x^2 + x - 1 = 0}.
For q = 5 the right side is 15000 * 5 (every 2 + y e is a root); for q = 4 it is 3840 * 2.
"""
import time
from itertools import product
from gf import GF


def run(p, k):
    F = GF(p, k)
    A, M, N, inv = F.add, F.mul, F.neg, F.inv
    def add(x, y): return (A[x[0]][y[0]], A[x[1]][y[1]])
    def mul(x, y): return (M[x[0]][y[0]], A[M[x[0]][y[1]]][M[x[1]][y[0]]])
    def neg(x): return (N[x[0]], N[x[1]])
    def unit(x): return x[0] != 0
    def rinv(x):
        a = inv[x[0]]
        return (a, N[M[M[a][a]][x[1]]])
    R = [(a, b) for a in range(F.q) for b in range(F.q)]
    one, zero = (1, 0), (0, 0)
    def norm(g):
        for v in g:
            if unit(v):
                i = rinv(v)
                return tuple(mul(i, x) for x in g)
        raise ValueError
    def mm(g, h):
        a, b, c, d = g; e, f, k_, l = h
        return norm((add(mul(a, e), mul(b, k_)), add(mul(a, f), mul(b, l)),
                     add(mul(c, e), mul(d, k_)), add(mul(c, f), mul(d, l))))
    def det(g): return add(mul(g[0], g[3]), neg(mul(g[1], g[2])))
    G = []
    for g in product(R, repeat=4):
        if unit(det(g)) and next(v for v in g if unit(v)) == one:
            G.append(g)
    I = (one, zero, zero, one)
    def pw(g, n):
        h = I
        for _ in range(n): h = mm(h, g)
        return h
    S2 = [g for g in G if mm(g, g) == I]
    S5 = [g for g in G if pw(g, 5) == I]
    def Ainv(g):
        t = add(g[0], g[3])
        return add(mul(mul(t, t), rinv(det(g))), neg((F.from_int(2), 0)))
    def closed(g): return tuple(v[0] for v in g)
    Ic = (1, 0, 0, 1)
    roots = [x for x in R if add(add(mul(x, x), x), neg(one)) == zero]
    per = {}
    for s in S2:
        for q5 in S5:
            if pw(mm(s, q5), 3) != I:
                continue
            if closed(s) == Ic and closed(q5) == Ic:
                continue  # trivial on the closed fibre: not a monomorphism
            per.setdefault(Ainv(q5), 0)
            per[Ainv(q5)] += 1
    n = sum(per.values())
    ok = n == len(G) * len(roots) and set(per) == set(roots) and all(v == len(G) for v in per.values())
    return (f"R = F_{F.q}[e]/(e^2): |PGL2(R)| = {len(G)}, roots of T^2+T-1 in R: {len(roots)}, "
            f"homs A5 -> PGL2(R) injective on the closed fibre: {n}, expected {len(G) * len(roots)}, "
            f"each root hit |PGL2(R)| times: {all(v == len(G) for v in per.values())}  agree: {ok}"), ok


if __name__ == '__main__':
    t = time.time()
    lines, ok = [], True
    for p, k in [(2, 1), (3, 1), (2, 2), (5, 1)]:
        l, o = run(p, k); print(l); lines.append(l); ok &= o
    lines.append(f"ALL OK: {ok}   ({time.time() - t:.1f} s)")
    print(lines[-1])
    open(__import__('os').path.join(__import__('os').path.dirname(__file__) or '.', 'results.txt'), 'a').write('\n--- dual numbers (dual_numbers.py) ---\n' + '\n'.join(lines) + '\n')
