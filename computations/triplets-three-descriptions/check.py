"""Folder 62, pp. 41-53: triples (X, X', s) -- a conic, an etale trisection, a section
disjoint from it -- over a base where 6 is invertible, described
  (A) by an S3-torsor T with t in Gamma(T, O), t and t-1 invertible, g.t = g(t) (p. 49);
  (B) by an invertible sheaf M with an etale trisection of V(M) of sum zero (p. 53),
      locally x^3 + b x + c, disc invertible;
  (C) by the invariant j = q(s) (pp. 41-43), formula (11), which determines the triple
      where j(j-1) is invertible.
Finite check over S = Spec F_p, p = 5..31: groupoids of iso classes, with automorphism
groups, computed four ways:
  (D) the definition: X = P^1 (s is a point), s = infinity, X' = squarefree cubic,
      modulo the affine group;
  (A) S3-orbits of pairs (sigma, t0), sigma in S3 (Frobenius cocycle), t0 in
      P^1(F_pbar) - {0,1,inf} with Frob(t0) = sigma(t0);
  (B) (b, c), 4b^3 + 27c^2 != 0, modulo (b, c) ~ (u^2 b, u^3 c);
and compares the multisets of (j, |Aut|). Also checks symbolically that, for a cubic with
roots r1 + r2 + r3 = 0 and t = (r2 - r3)/(r2 - r1), formula (11) gives
j(t) = 27c^2/(4b^3 + 27c^2), and records which normalisation, (u^2, u^3) or (u^4, u^6),
matches (D)."""
import itertools
from collections import Counter
from sympy import symbols, simplify, Rational, factor

# ---------- symbolic bridge A <-> B ----------
r1, r2 = symbols('r1 r2'); r3 = -r1 - r2
b_ = r1*r2 + r1*r3 + r2*r3; c_ = -r1*r2*r3
t = (r2 - r3)/(r2 - r1)
j11 = -Rational(1, 27)*((t + 1)*(2*t - 1)*(t - 2)/(t*(t - 1)))**2
bridge = simplify(j11 - 27*c_**2/(4*b_**3 + 27*c_**2)) == 0
print("formula (11) at t = (r2-r3)/(r2-r1) equals 27c^2/(4b^3+27c^2):", bridge)

# ---------- finite fields F_{p^n} ----------
def irreducible(p, n):
    for coeffs in itertools.product(range(p), repeat=n):
        f = list(coeffs) + [1]           # monic, low degree first
        if f[0] == 0: continue
        # no roots in any F_{p^d}, d | n, d < n: brute force via no factor of degree <= n/2
        if all(not divides(g, f, p) for d in range(1, n//2 + 1) for g in monics(p, d)):
            return f
def monics(p, d):
    for cs in itertools.product(range(p), repeat=d): yield list(cs) + [1]
def divides(g, f, p):
    f = f[:]
    while len(f) >= len(g):
        c = f[-1]
        if c:
            s = len(f) - len(g)
            for i, x in enumerate(g): f[s + i] = (f[s + i] - c*x) % p
        f.pop()
    return not any(f)
class GF:
    def __init__(self, p, n):
        self.p, self.n = p, n; self.f = irreducible(p, n) if n > 1 else [0, 1]
    def mul(self, x, y):
        p, n = self.p, self.n; r = [0]*(2*n - 1)
        for i, a in enumerate(x):
            if a:
                for k, b in enumerate(y): r[i + k] = (r[i + k] + a*b) % p
        for k in range(2*n - 2, n - 1, -1):
            c = r[k]
            if c:
                for i in range(n + 1): r[k - n + i] = (r[k - n + i] - c*self.f[i]) % p
        return tuple(r[:n])
    def add(self, x, y): return tuple((a + b) % self.p for a, b in zip(x, y))
    def neg(self, x): return tuple((-a) % self.p for a in x)
    def const(self, c): return tuple([c % self.p] + [0]*(self.n - 1))
    def power(self, x, e):
        r = self.const(1)
        while e:
            if e & 1: r = self.mul(r, x)
            x = self.mul(x, x); e >>= 1
        return r
    def inv(self, x): return self.power(x, self.p**self.n - 2)
    def elements(self): return itertools.product(range(self.p), repeat=self.n)

# anharmonic group as Mobius matrices (a, b, c, d): t -> (a t + b)/(c t + d)
S3 = {'id': (1,0,0,1), 'l': (0,1,1,0), 'm': (-1,1,0,1), 'lm': (0,1,-1,1), 'ml': (1,-1,1,0), 'lml': (1,0,1,-1)}
def mob_mul(A, B):
    a, b, c, d = A; e, f, g, h = B
    M = (a*e + b*g, a*f + b*h, c*e + d*g, c*f + d*h)
    return M
def norm(M):
    for k, v in S3.items():
        # projective equality
        if all(M[i]*v[j] == M[j]*v[i] for i in range(4) for j in range(4)): return k
    raise ValueError(M)
G = list(S3)
MUL = {(x, y): norm(mob_mul(S3[x], S3[y])) for x in G for y in G}
INV = {x: next(y for y in G if MUL[(x, y)] == 'id') for x in G}
def act(F, g, x):
    a, b, c, d = S3[g]
    return F.mul(F.add(F.mul(F.const(a), x), F.const(b)), F.inv(F.add(F.mul(F.const(c), x), F.const(d))))
def jfun(F, x):   # formula (11)
    one = F.const(1)
    num = F.mul(F.mul(F.add(x, one), F.add(F.mul(F.const(2), x), F.neg(one))), F.add(x, F.const(-2)))
    den = F.mul(x, F.add(x, F.neg(one)))
    v = F.mul(num, F.inv(den))
    return F.mul(F.const(-pow(27, -1, F.p)), F.mul(v, v))

def descA(p):
    fields = {1: GF(p, 1), 2: GF(p, 2), 3: GF(p, 3)}
    order = {g: next(k for k in range(1, 7) if (lambda h: h == 'id')(power_g(g, k))) for g in G}
    objs = []
    for s in G:
        F = fields[order[s]]
        for x in F.elements():
            x = tuple(x)
            if x == F.const(0) or x == F.const(1): continue
            if F.power(x, p) == act(F, s, x): objs.append((s, x, order[s]))
    seen = set(); classes = []
    for (s, x, o) in objs:
        if (s, x) in seen: continue
        F = fields[o]; orbit = set(); stab = 0
        for g in G:
            s2 = MUL[(MUL[(g, s)], INV[g])]; x2 = act(F, g, x)
            orbit.add((s2, x2))
            if (s2, x2) == (s, x): stab += 1
        seen |= orbit
        jv = jfun(F, x); assert all(c == 0 for c in jv[1:])   # j is in F_p
        classes.append((jv[0], stab))
    return Counter(classes)
def power_g(g, k):
    r = 'id'
    for _ in range(k): r = MUL[(r, g)]
    return r

def descB(p, w2=2, w3=3):
    pts = [(b, c) for b in range(p) for c in range(p) if (4*b**3 + 27*c**2) % p]
    seen = set(); out = Counter()
    for (b, c) in pts:
        if (b, c) in seen: continue
        orb = {((pow(u, w2, p)*b) % p, (pow(u, w3, p)*c) % p) for u in range(1, p)}
        stab = sum(1 for u in range(1, p) if (pow(u, w2, p)*b - b) % p == 0 and (pow(u, w3, p)*c - c) % p == 0)
        seen |= orb
        j = 27*c*c*pow(4*b**3 + 27*c**2, -1, p) % p
        out[(j, stab)] += 1
    return out

def descD(p):
    # monic squarefree cubics x^3 + A x^2 + B x + C modulo x -> l x + m (renormalised)
    def sqfree(A, B, C):
        disc = (A*A*B*B - 4*B**3 - 4*A**3*C - 27*C*C + 18*A*B*C) % p
        return disc != 0
    def transform(f, l, m):
        A, B, C = f  # g(x) = l^-3 f(l x + m)
        il = pow(l, -1, p)
        A2 = (3*m + A) * il % p
        B2 = (3*m*m + 2*A*m + B) * il * il % p
        C2 = (m**3 + A*m*m + B*m + C) * il**3 % p
        return (A2, B2, C2)
    cubics = [(A, B, C) for A in range(p) for B in range(p) for C in range(p) if sqfree(A, B, C)]
    seen = set(); out = Counter()
    for f in cubics:
        if f in seen: continue
        orb = set(); stab = 0
        for l in range(1, p):
            for m in range(p):
                g = transform(f, l, m); orb.add(g)
                if g == f: stab += 1
        seen |= orb
        # j via depressed form: shift x -> x - A/3
        A, B, C = f; m = (-A * pow(3, -1, p)) % p
        _, b, c = transform(f, 1, m)
        j = 27*c*c*pow(4*b**3 + 27*c**2, -1, p) % p
        out[(j, stab)] += 1
    return out

allok = bridge
for p in [5, 7, 11, 13, 17, 19, 23, 29, 31]:
    D = descD(p); A = descA(p); B = descB(p); B46 = descB(p, 4, 6)
    perj = Counter(j for (j, _) in D.elements())
    uniq = all(perj[j] == 1 for j in range(p) if j not in (0, 1))
    ok = (A == D) and (B == D) and uniq
    allok &= ok
    print(f"p={p}: classes D={sum(D.values())} A={sum(A.values())} B={sum(B.values())} | "
          f"A==D: {A == D}, B==D: {B == D}, one class per j with j(j-1)!=0: {uniq} | "
          f"classes over j=0: {perj[0]}, j=1: {perj[1]} | (u^4,u^6) normalisation gives {sum(B46.values())} classes, == D: {B46 == D}")
    if p == 7:
        print("   p=7, (j, |Aut|) multiset:", sorted(D.items()))
print("ALL OK" if allok else "SOME FAIL")
