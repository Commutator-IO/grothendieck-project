"""Folder 153, pp. 3 and 9: co-operations of relative Int, over k0 = Z.

For K0 = Z[1/S] (S a set of inverted primes; S = all primes gives Q, S = {} gives Z),
Omega = {F in K0[T] : F(Z) in Z} = Int(Z) cap K0[T].  For each degree bound d we
compute a Z-basis (e_0..e_d) of Omega_{<=d}, then for every basis element F we write
F(X+Y) and F(XY) in the K0-basis e_i(X) e_j(Y) of K0[X,Y]_{<=d,<=d} (unique, since the
e_i are Q-independent) and check that all coefficients are integers, i.e. that
F(X+Y), F(XY) come from (unique) elements of Omega (x) Omega.
Second part: the non-flat K0 = Z/n x Z[1/n] (for which K0 (x) K0 = K0) gives a
torsion element of Omega, so the freeness hypothesis fails there.
"""
import random, sys, time
from sympy import Matrix, Rational, binomial, symbols, Poly, expand, factorint, primerange, ZZ, eye, zeros
from sympy.matrices.normalforms import smith_normal_decomp

T, X, Y = symbols('T X Y')

def binom_poly_coeffs(i, d):
    p = Poly(expand(binomial(T, i).expand(func=True)), T)
    v = [Rational(0)] * (d + 1)
    for (k,), c in p.terms():
        v[k] = Rational(c)
    return v

def in_ZS(q, S):
    """q rational with denominator only divisible by primes of S (S=None: all primes)."""
    if S is None:
        return True
    return all(p in S for p in factorint(Rational(q).q))

def prime_to_S(n, S):
    if S is None:
        return 1
    n = abs(int(n))
    if n == 0:
        return 0
    r = 1
    for p, e in factorint(n).items():
        if p not in S:
            r *= p ** e
    return r

def omega_basis(d, S):
    """Columns: monomial coefficient vectors of a Z-basis of Omega_{<=d}."""
    Bin = Matrix(d + 1, d + 1, lambda r, c: binom_poly_coeffs(c, d)[r])  # binomial -> monomial
    B = Bin.inv()  # monomial -> binomial, integer matrix
    assert all(x.is_integer for x in B)
    s, D, t = None, None, None
    Dm, s, t = smith_normal_decomp(B, domain=ZZ)  # Dm = s*B*t
    Dp = [prime_to_S(Dm[i, i], S) for i in range(d + 1)]
    Lbin = s.inv() * Matrix.diag(*Dp)  # basis of L in binomial coordinates
    assert all(x.is_integer for x in Lbin)
    return Bin * Lbin

def coeff_matrix(expr, d):
    P = Poly(expand(expr), X, Y)
    M = zeros(d + 1, d + 1)
    for (a, b), c in P.terms():
        M[a, b] = c
    return M

def check(d, S, rng):
    E = omega_basis(d, S)
    Einv = E.inv()
    # sanity: basis elements lie in Omega (Z_S coefficients, integer values on 0..d)
    for j in range(d + 1):
        col = E[:, j]
        assert all(in_ZS(c, S) for c in col)
        for m in range(d + 1):
            assert sum(col[k] * m ** k for k in range(d + 1)).is_integer
    # independent check that the lattice is all of Omega_{<=d}: a degree-j element of
    # Omega has leading coefficient in (1/j!)Z cap Z_S = (1/a_j)Z, a_j = S-part of j!,
    # so covol(Omega_{<=d}) >= prod 1/a_j; our lattice lies in Omega, so equality of
    # |det E| with prod 1/a_j forces lattice = Omega_{<=d}.
    from math import factorial
    target = Rational(1)
    for j in range(d + 1):
        f = factorial(j)
        target /= (f // prime_to_S(f, S)) if S is not None else f
    hits = abs(E.det()) == target
    assert hits, "basis does not span Omega"
    bad = []
    for j in range(d + 1):
        F = sum(E[k, j] * T ** k for k in range(d + 1))
        for name, sub in (("X+Y", X + Y), ("XY", X * Y)):
            P = coeff_matrix(F.subs(T, sub), d)
            C = Einv * P * Einv.T
            if not all(x.is_integer for x in C):
                bad.append((j, name))
    return E, hits, bad

def main():
    rng = random.Random(153)
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    cases = [("Q (Int(Z))", None), ("Z", set()), ("Z[1/2]", {2}), ("Z[1/3]", {3}),
             ("Z[1/5]", {5}), ("Z[1/6]", {2, 3}), ("Z[1/30]", {2, 3, 5})]
    total_bad = 0
    print("Part 1: co-operations, k0 = Z, K0 = Z[1/S], degrees 0..%d" % dmax)
    for name, S in cases:
        t0 = time.time()
        E, hits, bad = check(dmax, S, rng)
        lead = [E[j, j] for j in range(dmax + 1)] if all(E[i, j] == 0 for j in range(dmax+1) for i in range(j+1, dmax+1)) else None
        print(f"  K0 = {name:12s} basis of Omega_<=%d found; |det| = prod 1/a_j: {hits} (lattice = Omega); "
              f"non-integral coproduct coefficients: {len(bad)}  [{time.time()-t0:.1f}s]" % dmax)
        total_bad += len(bad)
    print("  TOTAL failures:", total_bad)
    # negative control: the test must reject a lattice that is not Omega
    d = 4
    Ectl = Matrix(d + 1, d + 1, lambda r, c: binom_poly_coeffs(c, d)[r] * (2 if c == 2 else 1))
    Ei = Ectl.inv(); badctl = 0
    for j in range(d + 1):
        F = sum(Ectl[k, j] * T ** k for k in range(d + 1))
        C = Ei * coeff_matrix(F.subs(T, X + Y), d) * Ei.T
        badctl += not all(x.is_integer for x in C)
    print(f"  negative control (span of binom(T,i), i != 2, and 2*binom(T,2); deg <= 4): "
          f"{badctl} basis elements with non-integral X+Y coproduct (expected > 0)")
    print()
    print("Part 2: non-flat K0 = Z/n x Z[1/n] (K0 (x)_Z K0 = K0 since Z/n (x) Z[1/n] = 0)")
    for n in (2, 3, 4, 6, 10, 12):
        p = min(factorint(n))
        f1 = (n // p) * (T ** p - T)  # coefficients read mod n, second component 0
        nonzero = any(int(c) % n for c in Poly(f1, T).coeffs())
        vanishes = all(int(f1.subs(T, m)) % n == 0 for m in range(-30, 31))
        print(f"  n = {n:2d}: F = ({n//p}(T^{p} - T) mod {n}, 0) is nonzero: {nonzero}; "
              f"F(m) = image of 0 for |m|<=30: {vanishes}; n*F = 0 -> Omega has torsion, not free")

main()
