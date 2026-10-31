"""Folder 82, p. 78, (61): in characteristic 2, for a quaternion algebra M,
P(g~/O_S) ~= X^(2), and the map (60) X -> P(g~/O_S), L |-> L^perp, is the
relative Frobenius X -> X^(2) followed by that isomorphism.
Tested on the algebras [a,b): i^2 = i + a, j^2 = b, ji = (i+1)j, b a unit:
 (1) symbolically over F_2[a, b, 1/b] (the universal such algebra);
 (2) exhaustively on R-points, R = F_2, F_4, F_8, F_2[e]/(e^2), F_2[e]/(e^3),
     F_4[e]/(e^2), every (a, b) in R x R^*."""
import itertools
from sympy import symbols, Poly, expand

a, b = symbols('a b')
X = symbols('x0:4'); Y = symbols('y0:4'); Z = symbols('z0:4')
def zero(e, gens): return Poly(expand(e), *gens, modulus=2).is_zero

# basis 1, i, j, k = ij (computed by hand from the three relations, char 2)
T = {(0,0):(1,0,0,0),(0,1):(0,1,0,0),(0,2):(0,0,1,0),(0,3):(0,0,0,1),
     (1,0):(0,1,0,0),(1,1):(a,1,0,0),(1,2):(0,0,0,1),(1,3):(0,0,a,1),   # i.ij = (i+a)j
     (2,0):(0,0,1,0),(2,1):(0,0,1,1),(2,2):(b,0,0,0),(2,3):(b,b,0,0),   # j.ij = (ij+j)j = b(i+1)
     (3,0):(0,0,0,1),(3,1):(0,0,a,0),(3,2):(0,b,0,0),(3,3):(a*b,0,0,0)} # ij.i = aj, ij.j = bi, ij.ij = ab
def mul(u, v, tab=T):
    w = [0]*4
    for s in range(4):
        for t in range(4):
            for k in range(4): w[k] += u[s]*v[t]*tab[(s,t)][k]
    return [expand(x) for x in w]
G = (a, b) + X + Y + Z
ok = True
def report(name, val):
    global ok; ok &= bool(val); print(f"{name}: {val}")
report("associativity of [a,b) over F_2[a,b]", all(zero(l-r, G) for l, r in zip(mul(mul(X,Y),Z), mul(X,mul(Y,Z)))))
report("relations i^2=i+a, j^2=b, ji=ij+j",
       mul((0,1,0,0),(0,1,0,0)) == [a,1,0,0] and mul((0,0,1,0),(0,0,1,0)) == [b,0,0,0] and mul((0,0,1,0),(0,1,0,0)) == [0,0,1,1])
Trd = X[1]
Nrd = X[0]**2 + X[0]*X[1] + a*X[1]**2 + b*(X[2]**2 + X[2]*X[3] + a*X[3]**2)
sq = mul(X, X)
report("x^2 = Trd(x) x + Nrd(x) (so Trd, Nrd are the reduced trace and norm)",
       all(zero(sq[k] - Trd*X[k] - (Nrd if k == 0 else 0), G) for k in range(4)))
NY = Nrd.subs(dict(zip(X, Y)), simultaneous=True)
NXY = Nrd.subs(dict(zip(X, mul(X, Y))), simultaneous=True)
report("Nrd multiplicative", zero(NXY - Nrd*NY, G))
# g~ = {Trd = 0} = span(1, j, ij), coordinates (x0, x2, x3); q = -det = Nrd on g~; phi(u,v) = Trd(uv)
x0, x2, x3 = X[0], X[2], X[3]
q = Nrd.subs(X[1], 0)
phi = mul([X[0],0,X[2],X[3]], [Y[0],0,Y[2],Y[3]])[1]
qs = lambda c: q.subs({X[0]: c[0], X[2]: c[1], X[3]: c[2]}, simultaneous=True)
report("phi = Trd(uv) is the polar form of q on g~", zero(qs((x0+Y[0], x2+Y[2], x3+Y[3])) - q - qs((Y[0],Y[2],Y[3])) - phi, G))
print("   phi(x, y) =", phi, " -> kernel of phi = O.1 (b a unit), as (58)")
report("Trd(1) = 0, so 1 is in g~", True)
# (60): L = (x0:x2:x3) on X = {q = 0} |-> L^perp = {y : b(x2 y3 + x3 y2) = 0}, contains 1;
# as a point of P(g~/O) (linear forms in (y2, y3) up to units): (x3 : x2), i.e. the projection (x2 : x3).
# X^(2): q2 = U0^2 + b^2 (U2^2 + U2 U3 + a^2 U3^2); F(x) = (x0^2, x2^2, x3^2).
U0, U2, U3, s, t = symbols('U0 U2 U3 s t')
q2 = U0**2 + b**2*(U2**2 + U2*U3 + a**2*U3**2)
report("F maps X into X^(2): q2(F(x)) = q(x)^2", zero(q2.subs({U0: x0**2, U2: x2**2, U3: x3**2}, simultaneous=True) - q**2, G))
# psi : X^(2) -> P^1, two charts (u2 : B) and (B : u3), B = U0/b + U2 + a U3, i.e. bB = U0 + bU2 + abU3
bB = U0 + b*U2 + a*b*U3
report("psi's charts agree on X^(2): (bB)^2 = b^2 U2 U3 + q2", zero(bB**2 - b**2*U2*U3 - q2, (a, b, U0, U2, U3)))
report("psi(F(x)) = (x2 : x3): b B(F(x)) = b x2 x3 + q(x)",
       zero(bB.subs({U0: x0**2, U2: x2**2, U3: x3**2}, simultaneous=True) - b*x2*x3 - q, G))
# inverse of psi: (s : t) |-> (b(s^2 + s t + a t^2) : s^2 : t^2)
inv = {U0: b*(s**2 + s*t + a*t**2), U2: s**2, U3: t**2}
report("inverse lands on X^(2)", zero(q2.subs(inv, simultaneous=True), (a, b, s, t)))
report("psi(inv(s:t)) = (s:t): bB(inv) = b s t", zero(bB.subs(inv, simultaneous=True) - b*s*t, (a, b, s, t)))
# inv(psi(U)) = U on X^(2), chart (U2 : B): inv(U2, B) = (b(U2^2 + U2 B + a B^2), U2^2, B^2) should be U2 * U (mod q2)
B = bB / b
cand = [b*(U2**2 + U2*B + a*B**2), U2**2, B**2]
# compare cand ~ U2 * (U0, U2, U3) using B^2 = U2 U3 + q2/b^2
r = [expand(b**2*(c - U2*u)) for c, u in zip(cand, (U0, U2, U3))]
red2 = lambda e: Poly(expand(e), U0, U2, U3, a, b, modulus=2).rem(Poly(q2, U0, U2, U3, a, b, modulus=2)).is_zero
report("inv(psi(U)) = U on X^(2) (chart U2 != 0, times U2)", all(red2(e) for e in r))

# ---- (2) exhaustive check on points over small char-2 rings -----------------------------
def ring_GF2n(n, mod):   # F_2[x]/(mod), elements as bitmasks
    els = list(range(2**n))
    def m(x, y):
        r = 0
        for k in range(n):
            if (y >> k) & 1: r ^= x << k
        for k in range(2*n-2, n-1, -1):
            if (r >> k) & 1: r ^= mod << (k-n)
        return r
    return els, (lambda x, y: x ^ y), m
def ring_trunc(base, d):   # base[e]/(e^d), tuples
    bels, badd, bmul = base
    els = list(itertools.product(bels, repeat=d))
    add = lambda x, y: tuple(badd(p, q) for p, q in zip(x, y))
    def m(x, y):
        r = [0]*d
        for i in range(d):
            for j in range(d-i): r[i+j] = badd(r[i+j], bmul(x[i], y[j]))
        return tuple(r)
    return els, add, m
F2 = ring_GF2n(1, 0b11); F4 = ring_GF2n(2, 0b111); F8 = ring_GF2n(3, 0b1011)
rings = {"F2": F2, "F4": F4, "F8": F8, "F2[e]/e^2": ring_trunc(F2, 2),
         "F2[e]/e^3": ring_trunc(F2, 3), "F4[e]/e^2": ring_trunc(F4, 2)}
for name, (els, add, m) in rings.items():
    zero_ = els[0]; one = next(x for x in els if all(m(x, y) == y for y in els))
    units = [x for x in els if any(m(x, y) == one for y in els)]
    inv_ = {x: next(y for y in els if m(x, y) == one) for x in units}
    def S(*xs):
        r = zero_
        for x in xs: r = add(r, x)
        return r
    def M(*xs):
        r = one
        for x in xs: r = m(r, x)
        return r
    def unimod(v):   # over a local ring: some coordinate is a unit
        return any(x in units for x in v)
    def proj_eq(v, w):  # same point of P^n(R) (R local): v = c w with c a unit
        return any(all(M(c, y) == x for x, y in zip(v, w)) for c in units)
    good = True; npts = 0; nP1 = 0
    P1 = [v for v in itertools.product(els, repeat=2) if unimod(v)]
    for A_, B_ in itertools.product(els, units):
        qf = lambda x0, x2, x3: S(M(x0,x0), M(B_, S(M(x2,x2), M(x2,x3), M(A_,x3,x3))))
        q2f = lambda u0, u2, u3: S(M(u0,u0), M(B_,B_, S(M(u2,u2), M(u2,u3), M(A_,A_,u3,u3))))
        Xpts = [v for v in itertools.product(els, repeat=3) if unimod(v) and qf(*v) == zero_]
        X2pts = [v for v in itertools.product(els, repeat=3) if unimod(v) and q2f(*v) == zero_]
        binv = inv_[B_]
        def psi(u):
            Bv = S(M(u[0], binv), u[1], M(A_, u[2]))
            c1, c2 = (u[1], Bv), (Bv, u[2])
            outs = [c for c in (c1, c2) if unimod(c)]
            assert outs, (name, u)
            assert all(proj_eq(outs[0], c) for c in outs)   # charts agree
            return outs[0]
        for x in Xpts:
            npts += 1
            if not unimod((x[1], x[2])): good = False; continue     # (60) defined
            fx = tuple(M(c, c) for c in x)
            if not proj_eq(psi(fx), (x[1], x[2])): good = False      # (60) = psi o F
        # psi bijective X^(2)(R)/units -> P^1(R)/units
        def classes(pts):
            reps = []
            for p in pts:
                if not any(proj_eq(p, r) for r in reps): reps.append(p)
            return reps
        X2c = classes(X2pts); P1c = classes(P1)
        images = [psi(u) for u in X2c]
        bij = len(X2c) == len(P1c) and all(any(proj_eq(im, p) for im in images) for p in P1c)
        good &= bij
    print(f"{name}: all (a,b) with b a unit: (60) = psi o Frobenius on X(R), psi : X^(2)(R) -> P^1(R) bijective: {good}")
    ok &= good
print("ALL OK" if ok else "SOME FAIL")
