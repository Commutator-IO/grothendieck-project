"""Folder 138, pp. 122-127: operations on maps as compositions with a clean
Belyi-extending phi.  Forward direction on explicit small cases.

For a rational function g = P/Q on P^1 the script computes, exactly,
the ramification profile over 0, 1, oo (multiplicities of the roots of
P, P - Q, Q, plus the point oo), checks by Riemann-Hurwitz that there is
no other branching (sum (e - 1) over the three fibres = 2 deg - 2), and
reads the map g^{-1}([0,1]) off the profile: vertex degrees = profile
over 0, edges = deg/2, face degrees = profile over oo; g is clean when
every index over 1 is 2.

Operations phi:
  sub  = 4z(1-z)        A = [0,1], vertices 0, 1, edge midpoint 1/2
  med  = -(z-1)^2/(4z)  A = loop at 1 round 0 (faces centred at 0, oo)
  sub2 = sub o sub
Each phi is checked: clean, branched over {0,1,oo} only,
phi({0,1,oo}) in {0,1,oo}, and 1 not in phi^{-1}(1).
Then for small clean maps f (f = 4 b (1 - b), b a small Belyi function,
and f = med), phi o f is checked to be clean and branched over {0,1,oo},
and its passport is compared with the passport the operation predicts
from that of f (sub: new vertices of degree 2 at edge midpoints, faces
doubled; med: medial map, vertices of degree 4 at edge midpoints, faces
= vertices and faces of f).
Finally a clean phi with phi(1) = 1 (z(2 - z)) is composed with f to show
that phi o f is then not clean (index 4 over 1).
"""
from sympy import symbols, together, Poly, factor_list, cancel, S, Rational

z = symbols('z')

def profile(g):
    g = cancel(together(g))
    P, Q = [Poly(t, z) for t in g.as_numer_denom()]
    d = max(P.degree(), Q.degree())
    def mults(R, at_inf):
        out = []
        _, fl = factor_list(R.as_expr(), z)
        for fac, m in fl:
            out += [m] * Poly(fac, z).degree()
        if at_inf > 0: out.append(at_inf)
        return sorted(out, reverse=True)
    over0 = mults(P, d - P.degree())
    over1 = mults(P - Q, d - (P - Q).degree())
    overinf = mults(Q, d - Q.degree())
    return d, over0, over1, overinf

def value_at(g, p):
    g = cancel(together(g))
    P, Q = [Poly(t, z) for t in g.as_numer_denom()]
    if p is S.Infinity:
        if P.degree() > Q.degree(): return S.Infinity
        if P.degree() < Q.degree(): return S(0)
        return P.LC() / Q.LC()
    q = Q.eval(p)
    return S.Infinity if q == 0 else P.eval(p) / q

def info(g):
    d, a, b, c = profile(g)
    rh = sum(e - 1 for e in a + b + c) == 2*d - 2
    clean = all(e == 2 for e in b)
    return dict(deg=d, V=a, mid=b, F=c, belyi=rh, clean=clean)

sub = 4*z*(1 - z)
med = -(z - 1)**2 / (4*z)
OPS = {'sub': sub, 'med': med, 'sub2': sub.subs(z, sub)}

def predict(op, fi):
    V, F, E = fi['V'], fi['F'], fi['deg'] // 2
    if op == 'sub':
        return sorted(V + [2]*E, reverse=True), sorted([2*x for x in F], reverse=True)
    if op == 'med':
        return [4]*E, sorted(V + F, reverse=True)
    if op == 'sub2':
        v1, f1 = sorted(V + [2]*E, reverse=True), [2*x for x in F]
        return sorted(v1 + [2]*(2*E), reverse=True), sorted([2*x for x in f1], reverse=True)

def main():
    out = []
    out.append("Operations phi:")
    for name, phi in OPS.items():
        i = info(phi)
        imgs = [value_at(phi, p) for p in (S(0), S(1), S.Infinity)]
        ok_imgs = all(v in (S(0), S(1), S.Infinity) for v in imgs)
        out.append(f"  {name:5s} deg {i['deg']}: over0 {i['V']} over1 {i['mid']} overoo {i['F']} "
                   f"belyi={i['belyi']} clean={i['clean']} phi(0,1,oo)={imgs} in {{0,1,oo}}: {ok_imgs}; "
                   f"1 in phi^-1(1): {imgs[1] == 1}")
    bs = [z, z**2, z**3, z**2*(3 - 2*z), z**2/(2*z - 1), 1 - (1 - z)**3]
    fs = [('4b(1-b), b=' + str(b), 4*b*(1 - b)) for b in bs] + [('med', med)]
    out.append("Compositions phi o f:")
    nok = ntot = 0
    for fname, f in fs:
        fi = info(f)
        if not (fi['belyi'] and fi['clean']):
            out.append(f"  f = {fname}: not a clean Belyi map, skipped ({fi})"); continue
        for name, phi in OPS.items():
            gi = info(cancel(phi.subs(z, f)))
            pv, pf = predict(name, fi)
            match = gi['belyi'] and gi['clean'] and gi['V'] == pv and gi['F'] == pf
            ntot += 1; nok += match
            out.append(f"  f = {fname:24s} [V {fi['V']}, F {fi['F']}]  {name:4s}: V {gi['V']} F {gi['F']} "
                       f"clean={gi['clean']} belyi={gi['belyi']} matches prediction={match}")
    out.append(f"  {nok}/{ntot} compositions clean, branched over 0,1,oo only, with the predicted passport")
    bad = z*(2 - z)
    bi = info(bad)
    out.append(f"phi = z(2-z): clean={bi['clean']} belyi={bi['belyi']}, phi(1) = {value_at(bad, S(1))}")
    gi = info(cancel(bad.subs(z, 4*z*(1 - z))))
    out.append(f"  phi o 4z(1-z): over1 {gi['mid']} clean={gi['clean']}  (index 4 over 1: not a map)")
    print("\n".join(out))

if __name__ == "__main__":
    main()
