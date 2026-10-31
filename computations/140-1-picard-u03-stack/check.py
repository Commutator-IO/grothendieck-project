"""Folder 140-1, pp. 22, 24, 29: Picard group of the stack [U_{0,3}/S_3].

What Lean (lean/Grothendieck/Folder140_1.lean) leaves open and is finite:

E. Equivariance of the identification O(U_{0,3})^* = k^* x V(J).
   S_3 acts on P^1 by the Mobius maps permuting p_0 = 0, p_1 = 1, p_2 = oo,
   and on functions by sigma.u = u o h with h inducing sigma^{-1} on the
   three points (the convention of Folder140_1's docstring of sgnExp).
   For every sigma and every u = lambda^a (1-lambda)^b with |a|, |b| <= 4,
   sympy checks that sigma.u = (+-1) lambda^a' (1-lambda)^b' with divisor
   sigma.v ((sigma.v)_i = v_{sigma^-1 i}, v = (a, b, -a-b)) and sign
   (-1)^{sgnExp sigma v}, wt as in Lean.  Over Z, hence over every ring.
   It also checks that this is a left action (sigma.(tau.u) = (sigma tau).u).

O. The page's generator O(1).  On Sigma_J = P(V_J) with the natural
   S_3-linearisation, Sigma_J^* (complement of the zeros of e_i - e_j) is
   U_{0,3}, with lambda = (x1-x2)/(x1-x3); the induced action on lambda is
   checked to be the six anharmonic substitutions.  Invertible sections of
   O(n) on Sigma_J^* are c prod (x_j - x_k)^{a_jk}, sum a = n (unique
   factorisation in k[x]).  O(n) is equivariantly trivial iff one of them is
   S_3-invariant.  For n = 1..12 and |a_jk| <= 12, sympy computes
   sigma(f)/f for the generators of S_3 and checks whether it is 1 in
   characteristic 0, 2, 3, 5, 7.  The order of [O(1)] is the least such n.
"""
from itertools import permutations, product
from sympy import symbols, simplify, together, factor, Rational, cancel, Poly, S

lam = symbols('lambda')
PTS = [S(0), S(1), S.Infinity]

def mobius_from_images(imgs):
    """the Mobius map sending 0,1,oo to imgs[0], imgs[1], imgs[2]"""
    # enumerate the six anharmonic maps and pick the one with these images
    cands = [lam, 1/lam, 1-lam, lam/(lam-1), 1/(1-lam), (lam-1)/lam]
    for h in cands:
        ims = []
        for p in PTS:
            num, den = together(h).as_numer_denom()
            if p is S.Infinity:
                pn, pd = Poly(num, lam), Poly(den, lam)
                v = S.Infinity if pn.degree() > pd.degree() else (
                    pn.LC()/pd.LC() if pn.degree() == pd.degree() else S(0))
            else:
                v = S.Infinity if den.subs(lam, p) == 0 else h.subs(lam, p)
            ims.append(S.Infinity if v in (S.Infinity, -S.Infinity, S.ComplexInfinity) else v)
        if ims == list(imgs):
            return h
    raise ValueError(imgs)

G3 = list(permutations(range(3)))   # sigma as tuple: sigma[j] = image of j
def inv(s): return tuple(s.index(j) for j in range(3))
def mul(s, t): return tuple(s[t[j]] for j in range(3))   # (s t)(j) = s(t(j))

_H = {}
def h_for(sigma):
    """h inducing sigma^{-1} on the points: h(p_j) = p_{sigma^{-1} j}"""
    if sigma not in _H:
        si = inv(sigma)
        _H[sigma] = mobius_from_images([PTS[si[j]] for j in range(3)])
    return _H[sigma]

def wt(sigma, j):
    si = inv(sigma)
    return 1 if (si[2] == 1 and j == 0) or (si[2] == 0 and j == 1) else 0

def act(sigma, u):
    return cancel(together(u.subs(lam, h_for(sigma))))

def check_E(B=4):
    bad = 0; total = 0
    for sigma in G3:
        for a, b in product(range(-B, B+1), repeat=2):
            u = lam**a * (1-lam)**b
            w = act(sigma, u)
            v = (a, b, -a-b)
            sv = tuple(v[inv(sigma)[i]] for i in range(3))
            sign = (-1)**(sum(wt(sigma, j)*v[j] for j in range(3)) % 2)
            target = sign * lam**sv[0] * (1-lam)**sv[1]
            total += 1
            if cancel(w - target) != 0: bad += 1
    # left action on generators
    badact = 0
    for s, t in product(G3, repeat=2):
        for u in (lam, 1-lam):
            if cancel(act(s, act(t, u)) - act(mul(s, t), u)) != 0: badact += 1
    return total, bad, badact

x1, x2, x3 = X = symbols('x1 x2 x3')
PAIRS = [(0, 1), (0, 2), (1, 2)]

def perm_x(sigma, f):
    # sigma acts on V_J by e_i -> e_{sigma i}; on coordinates x_i -> x_{sigma i}
    return f.subs({X[i]: symbols('y%d' % sigma[i]) for i in range(3)}, simultaneous=True) \
            .subs({symbols('y%d' % i): X[i] for i in range(3)}, simultaneous=True)

def check_lambda_action():
    L = (x1-x2)/(x1-x3)
    subs = set()
    for sigma in G3:
        Ls = perm_x(sigma, L)
        # express Ls as a function of L: solve via x1=1? use x = (0? ) generic: set x3=0, x1=1, x2 = 1-l
        expr = cancel(Ls.subs({x1: 1, x3: 0, x2: 1-lam}))
        subs.add(str(expr))
    return subs

def unit_section(a):
    f = S(1)
    for (j, k), e in zip(PAIRS, a):
        f *= (X[j]-X[k])**e
    return f

def ratio_constant(sigma, a):
    f = unit_section(a)
    r = cancel(perm_x(sigma, f) / f)
    return r   # a rational function; invariant iff r == 1

def check_O(nmax=12, B=12, chars=(0, 2, 3, 5, 7)):
    gens = [(1, 0, 2), (1, 2, 0)]      # a transposition and a 3-cycle
    first = {}
    for p in chars:
        first[p] = None
    for n in range(1, nmax+1):
        for a in product(range(-B, B+1), repeat=2):
            a3 = n - a[0] - a[1]
            if abs(a3) > B: continue
            vec = (a[0], a[1], a3)
            # screen: sigma(f)/f is constant only if the exponent vector is
            # invariant under the induced permutation of the pairs (unique
            # factorisation); sympy then computes the constant
            ok_exp = True
            for g in gens:
                for (j, k), e in zip(PAIRS, vec):
                    jj, kk = sorted((g[j], g[k]))
                    if vec[PAIRS.index((jj, kk))] != e: ok_exp = False
            if not ok_exp:
                continue
            rs = [ratio_constant(g, vec) for g in gens]
            if any(not r.is_number for r in rs):   # exponents not invariant
                continue
            for p in chars:
                if first[p] is not None: continue
                ok = all((r == 1) if p == 0 else ((Rational(r).p - Rational(r).q) % p == 0) for r in rs)
                if ok: first[p] = (n, vec)
    return first

def main():
    out = []
    total, bad, badact = check_E()
    out.append(f"E. sigma.(lambda^a (1-lambda)^b) = (-1)^sgnExp lambda^a' (1-lambda)^b' with divisor sigma.v:")
    out.append(f"   {total - bad}/{total} (6 elements x |a|,|b| <= 4); left-action failures on generators: {badact}/72")
    out.append("   Mobius maps used: " + ", ".join(f"{s}->{h_for(s)}" for s in G3))
    out.append("O. induced action of S_3 on lambda = (x1-x2)/(x1-x3): " + ", ".join(sorted(check_lambda_action())))
    first = check_O()
    for p, v in first.items():
        name = "char 0" if p == 0 else f"char {p}"
        out.append(f"   {name}: least n with an S_3-invariant invertible section of O(n) on Sigma_J^*: "
                   + (f"n = {v[0]}, exponents (a12, a13, a23) = {v[1]}" if v else "none for n <= 12"))
    print("\n".join(out))

if __name__ == "__main__":
    main()
