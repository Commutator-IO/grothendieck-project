"""Folder 2, p. 13: a non-zero class with total Chern class 1.

Model (splitting principle, as in the reading and in Lean's Folder2.lean):
X a curve, p, q the classes in A^1(X) of the points 0 and a (p^2 = q^2 = 0),
A(X x P^r) = A(X)[eta]/(eta^{r+1}), i_!(x) = sum_i (-1)^i C(r,i) ([O(-0) L^-i] - [O(-a) L^-i]),
c(O(-0) L^-i) = 1 - p - i eta, c(O(-a) L^-i) = 1 - q - i eta.
Route A: expand the product of total Chern classes.
Route B (independent): ch(i_! x) = (e^-p - e^-q)(1 - e^-eta)^r, then log c = sum_k (-1)^(k-1) (k-1)! ch_k.
Both give c(i_! x) = 1 + kappa_r (p - q) eta^r with an integer kappa_r; c = 1 iff kappa_r (p - q) = 0
in A^1(X), and p - q has the order N of the point a in Pic^0.
"""
from sympy import symbols, binomial, factorial, expand, Poly, exp, series, S
import sys

p, q, e, t = symbols('p q eta t')

def reduce(expr, r):
    """Truncate in Q[p,q,eta]: p^2 = q^2 = 0, eta^(r+1) = 0."""
    P = Poly(expand(expr), p, q, e)
    out = S(0)
    for (a, b, c), coef in P.terms():
        if a < 2 and b < 2 and c <= r:
            out += coef * p**a * q**b * e**c
    return expand(out)

def inv(u, r):
    """Inverse of 1 - u, u nilpotent of order <= r+3 in the truncated ring."""
    s, pw = S(1), S(1)
    for _ in range(r + 3):
        pw = reduce(pw * u, r)
        s += pw
    return reduce(s, r)

def chern_A(r):
    c = S(1)
    for i in range(r + 1):
        k = (-1)**i * binomial(r, i)
        a, b = 1 - p - i*e, 1 - q - i*e
        f = reduce(a * inv(q + i*e, r), r) if k > 0 else reduce(b * inv(p + i*e, r), r)
        for _ in range(abs(k)):
            c = reduce(c * f, r)
    return c

def chern_B(r):
    # ch(i_! x) = (e^-p - e^-q)(1 - e^-eta)^r, truncated (p^2 = q^2 = 0, eta^(r+1) = 0)
    ch = reduce((series(exp(-p), p, 0, 2).removeO() - series(exp(-q), q, 0, 2).removeO())
                * series((1 - exp(-t))**r, t, 0, r + 1).removeO().subs(t, e), r)
    # split ch by total degree, log c = sum_k (-1)^(k-1) (k-1)! ch_k
    P = Poly(ch, p, q, e)
    chk = {}
    for (a, b, c), coef in P.terms():
        chk[a + b + c] = chk.get(a + b + c, 0) + coef * p**a * q**b * e**c
    L = sum((-1)**(k - 1) * factorial(k - 1) * v for k, v in chk.items() if k >= 1)
    c, term = S(1), S(1)
    for n in range(1, r + 4):
        term = reduce(term * L, r) / n
        c += term
    return reduce(c, r)

def main():
    rmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    print("c(i_! x) - 1 in Z[p,q,eta]/(p^2, q^2, eta^(r+1)), x = [O(-0)] - [O(-a)]")
    kap = {}
    for r in range(1, rmax + 1):
        A, B = chern_A(r), chern_B(r)
        assert expand(A - B) == 0, (r, A, B)
        d = expand(A - 1)
        k = Poly(d, p, q, e).coeff_monomial(p * e**r)
        assert expand(d - k * (p - q) * e**r) == 0, d
        assert k == (-1)**(r - 1) * factorial(r)
        kap[r] = k
        print(f"  r = {r}: route A = route B = 1 + ({k})*(p - q)*eta^{r}")
    print()
    print("c(i_! x) = 1  iff  r! (p - q) = 0 in A^1(X); p - q has order N (a of order N in Pic^0)")
    for N in range(2, 9):
        rs = [r for r in range(1, rmax + 1) if kap[r] % N == 0]
        print(f"  N = {N}: total Chern class 1 for r in {rs}  (smallest r = {min(rs) if rs else None})")
    print()
    print("Counterexample to 'only possible for r >= 3': N = 2 (the page's own a + a = 0), r = 2:")
    c2 = chern_A(2)
    print(f"  c(i_! x) = {c2} ; minus 1 = {expand(c2 - 1)} = -2(p - q) eta^2 = 0 since 2(p - q) = 0")
    print("  so c(i_! x) = 1 in A(X x P^2), while i_! x = x . xi^2 != 0 in K(X x P^2) (x != 0).")
    print("  For r = 1: c(i_! x) = 1 + (p - q) eta != 1 since p - q != 0.")

main()
