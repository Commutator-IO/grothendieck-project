"""Folder 85, pp. 10 and 40: icosahedral subgroups of PGL2, moduli Spec Z[T]/(T^2+T-1).

(1) Symbolic, in Z[T]/(T^2+T-1) and over Z[zeta5] (sympy):
    - g^5 = x5 g + y5 with x5 = det^2 (A^2 + A - 1)  (generic 2x2 matrix);
    - A(g^2) = A(g)^2 - 2, which is -1 - A(g) mod T^2+T-1;
    - Delta(-1, T) = (T+2)(T-1) = -1 mod T^2+T-1 (discriminant of page 4 at (nu0,nu1) = (3,5));
    - the page-40 model s = [[0,-1],[1,0]], p = [[z,1],[0,z^4]] over Z[z]/(Phi5):
      s^2 = -1, (sp)^3 = -1, p^5 scalar, A(p) root of T^2+T-1.
(2) Finite fields: count homomorphisms A5 = <s,p | s^2, p^5, (sp)^3> -> PGL2(F_q).
    Prediction from the corollary (rigid groupoid, iso classes = F_q-points of
    Spec Z[T]/(T^2+T-1); over F_q every form of PGL2 is split and Aut(PGL2) = PGL2):
        #monomorphisms = |PGL2(F_q)| * #{x in F_q : x^2 + x - 1 = 0},
    each root being the invariant A(phi(p)) of exactly |PGL2(F_q)| of them (free, single orbit).
"""
import time
from gf import GF, pgl2, make_ops
import sympy as sp

FIELDS = [(2, 1), (3, 1), (2, 2), (5, 1), (7, 1), (2, 3), (3, 2), (11, 1), (13, 1), (2, 4),
          (17, 1), (19, 1), (23, 1), (5, 2), (3, 3), (29, 1), (31, 1)]


def symbolic(out):
    a, b, c, d, T, z = sp.symbols('a b c d T z')
    g = sp.Matrix([[a, b], [c, d]])
    t, de = g.trace(), g.det()
    A = sp.together(t**2 / de - 2)
    x5 = t**4 - 3 * de * t**2 + de**2
    y5 = -de * (t**3 - 2 * de * t)
    ok1 = sp.expand(g**5 - x5 * g - y5 * sp.eye(2)) == sp.zeros(2, 2)
    ok2 = sp.simplify(x5 - de**2 * (A**2 + A - 1)) == 0
    g2 = g * g
    A2 = g2.trace()**2 / g2.det() - 2
    ok3 = sp.simplify(A2 - (A**2 - 2)) == 0
    ok4 = sp.rem(sp.expand(T**2 - 2 - (-1 - T)), T**2 + T - 1, T) == 0
    ok5 = sp.rem(sp.expand((-1 + 2) * (T + 2) * (-1 + T)), T**2 + T - 1, T) == -1
    phi5 = z**4 + z**3 + z**2 + z + 1
    red = lambda M: M.applyfunc(lambda e: sp.rem(sp.expand(e), phi5, z))
    s = sp.Matrix([[0, -1], [1, 0]]); p = sp.Matrix([[z, 1], [0, z**4]])
    ok6 = red(s**2) == -sp.eye(2) and red((s * p)**3) == -sp.eye(2)
    p5 = red(p**5)
    ok7 = p5[0, 1] == 0 and p5[1, 0] == 0 and sp.expand(p5[0, 0] - p5[1, 1]) == 0
    Ap = sp.rem(sp.expand(p.trace()**2 / 1 - 2), phi5, z)  # det p = z^5 = 1
    ok8 = sp.rem(sp.expand(p.det()), phi5, z) == 1 and sp.rem(sp.expand(Ap**2 + Ap - 1), phi5, z) == 0
    line = (f"symbolic: g^5 = x5 g + y5: {ok1}; x5 = det^2(A^2+A-1): {ok2}; A(g^2) = A^2-2: {ok3}; "
            f"= -1-A mod T^2+T-1: {ok4}; Delta(-1,T) = -1 mod T^2+T-1: {ok5}; "
            f"model s^2=-1,(sp)^3=-1: {ok6}; p^5 scalar: {ok7}; det p = 1, A(p) = {Ap} root: {ok8}")
    print(line); out.append(line)
    return all([ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8])


def run_field(p, k, out):
    F = GF(p, k)
    G = pgl2(F)
    norm, mul, tr, det, A = make_ops(F)
    I = (1, 0, 0, 1)
    def pw(g, n):
        h = I
        for _ in range(n):
            h = mul(h, g)
        return h
    S2 = [g for g in G if mul(g, g) == I]
    S5 = [g for g in G if pw(g, 5) == I]
    roots = [x for x in F.elements() if F.sub(F.add[F.mul[x][x]][x], 1) == 0]
    per_root = {}
    trivial = 0
    for s in S2:
        for pp in S5:
            sp_ = mul(s, pp)
            if pw(sp_, 3) != I:
                continue
            if s == I and pp == I:
                trivial += 1
                continue
            # A5 is simple and 60 = order of <s,p| s^2,p^5,(sp)^3>, so any non-trivial hom is injective
            per_root.setdefault(A(pp), []).append((s, pp))
    nmono = sum(map(len, per_root.values()))
    expected = len(G) * len(roots)
    ok = (nmono == expected and set(per_root) == set(roots)
          and all(len(v) == len(G) for v in per_root.values()) and trivial == 1)
    # single free orbit per root
    for r, v in per_root.items():
        s, pp = v[0]
        orb = set()
        for g in G:
            gi = norm((g[3], F.neg[g[1]], F.neg[g[2]], g[0]))
            orb.add((mul(mul(g, s), gi), mul(mul(g, pp), gi)))
        ok &= orb == set(v)
    line = (f"q={F.q:4d} (p={p}) |PGL2|={len(G):6d}  roots of T^2+T-1 in F_q: {len(roots)}  "
            f"monomorphisms A5->PGL2: {nmono:6d}  expected |PGL2|*#roots = {expected:6d}  "
            f"invariants hit: {sorted(per_root)} (roots {sorted(roots)})  agree: {ok}")
    print(line); out.append(line)
    return ok


if __name__ == '__main__':
    t0 = time.time()
    out = []
    ok = symbolic(out)
    for p, k in FIELDS:
        ok &= run_field(p, k, out)
    out.append(f"ALL OK: {ok}   ({time.time() - t0:.1f} s)")
    print(out[-1])
    open(__import__('os').path.join(__import__('os').path.dirname(__file__) or '.', 'results.txt'), 'w').write('\n'.join(out) + '\n')
