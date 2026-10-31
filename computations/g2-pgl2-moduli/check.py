"""Folder 85, pp. 4-7: homomorphisms of G2 = <t0,t1,t2 | ti^2, (t0 t2)^2> into PGL2(F_q).

Tests, for each finite field F_q in the list:
 (a) every homomorphism satisfying (*) (rho0^2 != 1, rho1^2 != 1, rho0 rho1 != rho1 rho0)
     has Delta = (a0+2)(a1+2)(a0+a1) != 0;
 (b) every pair (a0, a1) in F_q^2 with Delta != 0 is the invariant of exactly
     |PGL2(F_q)| such homomorphisms, forming one conjugacy orbit with trivial stabiliser
     (= rigid + "the isomorphism-class functor is the complement of three lines", on F_q-points;
     over a finite field every form of PGL2 is split, Lang);
 (c) the order criterion: for g != 1 in PGL2(F_q) and nu >= 2, ord(g) = nu
     iff Psi_nu(A(g)) = 0, under the proviso "nu prime or nu invertible";
 plus (d) symbolic identities with sympy (the discriminant as a product of traces).
"""
import sys, time
from math import gcd
from gf import GF, pgl2, make_ops
import sympy as sp

FIELDS = [(2, 1), (3, 1), (2, 2), (5, 1), (7, 1), (2, 3), (3, 2), (11, 1), (13, 1)]
NU_MAX = 30


def psi_int(nu):
    x = sp.Symbol('x')
    if nu == 1:
        return sp.Poly(x - 2, x)
    if nu == 2:
        return sp.Poly(x + 2, x)
    return sp.Poly(sp.minimal_polynomial(2 * sp.cos(2 * sp.pi / nu), x), x)


PSI = {nu: [int(c) for c in psi_int(nu).all_coeffs()] for nu in range(1, NU_MAX + 1)}


def ev(F, coeffs, a):
    r = 0
    for c in coeffs:
        r = F.add[F.mul[r][a]][F.from_int(c)]
    return r


def run_field(p, k, out):
    F = GF(p, k)
    q = F.q
    G = pgl2(F)
    norm, mul, tr, det, A = make_ops(F)
    I = (1, 0, 0, 1)
    S = [g for g in G if mul(g, g) == I]          # elements with g^2 = 1 (incl. identity)
    two = F.from_int(2)
    def Delta(a0, a1):
        return F.mul[F.mul[F.add[a0][two]][F.add[a1][two]]][F.add[a0][a1]]
    counts = {}
    bad_a = 0
    ndeg = 0
    for t0 in S:
        for t2 in S:
            if mul(mul(t0, t2), mul(t0, t2)) != I:
                continue
            for t1 in S:
                r0, r1 = mul(t0, t1), mul(t1, t2)
                star = mul(r0, r0) != I and mul(r1, r1) != I and mul(r0, r1) != mul(r1, r0)
                if not star:
                    ndeg += 1
                    continue
                a0, a1 = A(r0), A(r1)
                if Delta(a0, a1) == 0:
                    bad_a += 1
                counts.setdefault((a0, a1), []).append((t0, t1, t2))
    admissible = [(x, y) for x in F.elements() for y in F.elements() if Delta(x, y) != 0]
    exp_N = q * q - 3 * q + (2 if p == 2 else 3)
    ok_b = (set(counts) == set(admissible) and all(len(v) == len(G) for v in counts.values()))
    # one orbit, trivial stabiliser: conjugating a representative by all of PGL2 gives |G| distinct triples
    ok_orbit = True
    for key, v in counts.items():
        t0, t1, t2 = v[0]
        orb = set()
        for g in G:
            gi = None
            # inverse in PGL2: adjugate
            a, b, c, d = g
            gi = norm((d, F.neg[b], F.neg[c], a))
            orb.add(tuple(mul(mul(g, t), gi) for t in (t0, t1, t2)))
        if orb != set(v):
            ok_orbit = False
            break
    # (c) order criterion
    def order(g):
        h, n = g, 1
        while h != I:
            h, n = mul(h, g), n + 1
        return n
    bad_c = []
    proviso_needed = set()
    for g in G:
        if g == I:
            continue
        o, a = order(g), A(g)
        for nu in range(2, NU_MAX + 1):
            allowed = sp.isprime(nu) or gcd(nu, p) == 1
            zero = ev(F, PSI[nu], a) == 0
            if nu == o and not zero:
                bad_c.append((g, o, nu, 'order but Psi != 0'))
            if allowed and zero and nu != o:
                bad_c.append((g, o, nu, 'Psi = 0 but order differs'))
            if not allowed and zero and nu != o:
                proviso_needed.add(nu)
    line = (f"q={q:3d} |PGL2|={len(G):5d}  homs with (*): {sum(map(len, counts.values())):8d} "
            f"= |PGL2| x {len(counts):3d} (expected #pairs {exp_N}, admissible {len(admissible)})  "
            f"(*) => Delta!=0 violations: {bad_a}  per-pair count = |PGL2|: {ok_b}  "
            f"single free orbit: {ok_orbit}  order-criterion violations: {len(bad_c)}  "
            f"nu where the proviso is needed: {sorted(proviso_needed)}")
    print(line); out.append(line)
    for b in bad_c[:5]:
        out.append(f"   order-criterion counterexample: {b}")
    return bad_a == 0 and ok_b and ok_orbit and len(admissible) == exp_N and not bad_c


def symbolic(out):
    a = sp.symbols('a0:3'); b = sp.symbols('b0:3'); c = sp.symbols('c0:3')
    tau = [sp.Matrix([[a[i], b[i]], [c[i], -a[i]]]) for i in range(3)]
    d = [t.det() for t in tau]
    t01 = (tau[0] * tau[1]).trace(); t12 = (tau[1] * tau[2]).trace()
    t02 = (tau[0] * tau[2]).trace(); T = (tau[0] * tau[1] * tau[2]).trace()
    al0 = t01**2 / (d[0] * d[1]) - 2; al1 = t12**2 / (d[1] * d[2]) - 2
    Dl = (al0 + 2) * (al1 + 2) * (al0 + al1)
    # Delta * d0^2 d1^3 d2^2 + t01^2 t12^2 T^2 must lie in the ideal (t02)
    expr = sp.together(Dl * d[0]**2 * d[1]**3 * d[2]**2 + t01**2 * t12**2 * T**2)
    num = sp.expand(sp.numer(expr) * 1)
    den = sp.denom(expr)
    rem = sp.reduced(num, [t02], *a, *b, *c)[1]
    # reduced() w.r.t. a single generator is a valid ideal-membership test (principal ideal)
    ok1 = sp.expand(rem) == 0
    comm = sp.expand(tau[0]*tau[1]*tau[1]*tau[2] - tau[1]*tau[2]*tau[0]*tau[1] + T * tau[1])
    ok2 = comm == sp.zeros(2, 2)
    line = (f"symbolic: Delta*d0^2 d1^3 d2^2 = -t01^2 t12^2 T^2 mod t02: {ok1} (denominator {den}); "
            f"rho0 rho1 - rho1 rho0 = -T tau1: {ok2}")
    print(line); out.append(line)
    return ok1 and ok2


if __name__ == '__main__':
    t = time.time()
    out = []
    ok = symbolic(out)
    for p, k in FIELDS:
        ok &= run_field(p, k, out)
    out.append(f"ALL OK: {ok}   ({time.time() - t:.1f} s)")
    print(out[-1])
    open(__import__('os').path.join(__import__('os').path.dirname(__file__) or '.', 'results.txt'), 'w').write('\n'.join(out) + '\n')
