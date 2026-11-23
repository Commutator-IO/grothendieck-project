"""Grothendieck's second question to Kostant: the classes of quadruples (T, B, T', B') and
the action of the exterior automorphisms.  See section "The second question" of
docs/kostant/article.tex.

Usage:
    python3 -I computations/kostant/kostant_quadruples.py A2 A3 A4 B3 C3 D4
        lists the orbits of Phi = N(T) cap N(T') on Q x Q' explicitly and prints, per type,
        h, |W|, z, the number of classes and the letter's |W|^2/(h z phi(h)), the number of
        chambers met by the Coxeter plane (2h), the number of classes in the pair D_+-, and
        for each exterior automorphism its sign eps on e_{-theta}, the number of classes it
        fixes and its action on D_+-.
    FAST=1 python3 -I computations/kostant/kostant_quadruples.py A5 A6 D5
        counts the classes fixed by each exterior automorphism by Burnside's lemma instead.

Floating point (numpy) in the adjoint representation of a matrix model of g (types A, B, C,
D; G2 is not wired); the outcome is combinatorial.  Phi acts through the pairs (w, w') with
w P w^-1 = P^k and w' c' w'^-1 = c'^k for the same unit k.
"""
import itertools, math, sys
import numpy as np

TOL = 1e-7


def E(N, i, j):
    m = np.zeros((N, N), dtype=complex)
    m[i, j] = 1
    return m


def model(typ, n):
    """Return (N, e_list, diagram automorphisms as permutations of simple indices)."""
    if typ == 'A':
        N = n + 1
        es = [E(N, i, i + 1) for i in range(n)]
        outs = [tuple(range(n))[::-1]] if n >= 2 else []
    elif typ == 'B':
        N = 2 * n + 1
        es = [E(N, i, i + 1) - E(N, N - 2 - i, N - 1 - i) for i in range(n - 1)]
        es.append(E(N, n - 1, n) - E(N, n, n + 1))
        outs = []
    elif typ == 'C':
        N = 2 * n
        es = [E(N, i, i + 1) - E(N, N - 2 - i, N - 1 - i) for i in range(n - 1)]
        es.append(E(N, n - 1, n))
        outs = []
    elif typ == 'D':
        N = 2 * n
        es = [E(N, i, i + 1) - E(N, N - 2 - i, N - 1 - i) for i in range(n - 1)]
        es.append(E(N, n - 2, n) - E(N, n - 1, n + 1))
        sw = list(range(n)); sw[n - 2], sw[n - 1] = n - 1, n - 2
        outs = [tuple(sw)]
        if n == 4:
            outs = [tuple(p) for p in ([0, 1, 3, 2], [3, 1, 0, 2], [2, 1, 3, 0], [3, 1, 2, 0], [2, 1, 0, 3])]
    elif typ == 'G':
        N = 7
        X = lambda i, j: E(N, i, j) - E(N, N - 1 - j, N - 1 - i)
        a1 = X(0, 1); a2 = X(1, 2); a3 = X(2, 3)
        es = [a1 + a3, a2]   # short, long  (a scale fixed below by search)
        outs = []
    return N, es, outs


def bracket(x, y):
    return x @ y - y @ x


def lie_closure(gens):
    """Basis (list of matrices) and words (tuples of generator indices, left-nested)."""
    basis, words = [], []
    def add(m, w):
        v = m.reshape(-1)
        if basis:
            B = np.array([b.reshape(-1) for b in basis]).T
            c, *_ = np.linalg.lstsq(B, v, rcond=None)
            if np.linalg.norm(B @ c - v) < 1e-8 * max(1, np.linalg.norm(v)):
                return False
        basis.append(m); words.append(w)
        return True
    frontier = []
    for i, g in enumerate(gens):
        if add(g, (i,)):
            frontier.append(len(basis) - 1)
    while frontier:
        new = []
        for k in frontier:
            for i, g in enumerate(gens):
                m = bracket(g, basis[k])
                if np.linalg.norm(m) > 1e-9 and add(m, words[k] + (i,)):
                    new.append(len(basis) - 1)
        frontier = new
    return basis, words


class Lie:
    def __init__(self, typ, n, es=None):
        N, es0, outs = model(typ, n)
        es = es if es is not None else es0
        self.typ, self.n, self.outs = typ, n, outs
        fs = [e.T.copy() for e in es]
        self.gens = es + fs
        self.basis, self.words = lie_closure(self.gens)
        self.dim = len(self.basis)
        self.Bmat = np.array([b.reshape(-1) for b in self.basis]).T
        self.Bpinv = np.linalg.pinv(self.Bmat)
        self.l = len(es)
        self.es, self.fs = es, fs
        self.hs = [bracket(e, f) for e, f in zip(es, fs)]

    def coords(self, m):
        return self.Bpinv @ m.reshape(-1)

    def ad(self, x):
        return np.array([self.coords(bracket(x, b)) for b in self.basis]).T

    def mat(self, v):
        return (self.Bmat @ v).reshape(self.basis[0].shape)


def setup(L):
    l = L.l
    adh = [L.ad(h) for h in L.hs]
    rng = np.random.default_rng(1)
    gen = sum(r * a for r, a in zip(rng.normal(size=l), adh))
    vals, vecs = np.linalg.eig(gen)
    roots, rvecs = [], []
    for k in range(L.dim):
        if abs(vals[k]) > 1e-6:
            v = vecs[:, k]
            roots.append(np.array([(a @ v)[np.argmax(abs(v))] / v[np.argmax(abs(v))] for a in adh]))
            rvecs.append(v)
    roots = np.array(roots).real   # values alpha(h_j)
    # simple roots: values of alpha_i on h_j = Cartan matrix rows
    simple = np.array([[L.coords(bracket(h, e)) @ L.coords(e) / (L.coords(e) @ L.coords(e)) for h in L.hs] for e in L.es]).real
    # express each root in simple roots
    coef = np.linalg.solve(simple.T, roots.T).T
    coef = np.rint(coef).astype(int)
    hts = coef.sum(axis=1)
    h = hts.max() + 1
    ith = int(np.argmin(hts))     # -theta
    e_mth = L.mat(rvecs[ith])
    return dict(roots=roots, coef=coef, hts=hts, h=h, rvecs=rvecs, e_mth=e_mth, simple=simple)


def weyl_perms(roots):
    """roots: array of root vectors (rows) in some coordinates with a W-invariant form.
    Returns simple reflections as permutations, using a generic chamber."""
    R = len(roots)
    # form: use standard dot after symmetrising via sum of outer products of roots
    M = roots.T @ roots
    Minv = np.linalg.inv(M)
    dot = lambda a, b: a @ Minv @ b
    rng = np.random.default_rng(7)
    g = rng.normal(size=roots.shape[1])
    pos = [i for i in range(R) if dot(roots[i], g) > 0]
    # simple roots: positive roots not sum of two positive roots
    posset = set(pos)
    def find(v):
        for j in range(R):
            if np.linalg.norm(roots[j] - v) < 1e-6:
                return j
        return None
    simple = []
    for i in pos:
        dec = False
        for j in pos:
            k = find(roots[i] - roots[j])
            if k is not None and k in posset:
                dec = True; break
        if not dec:
            simple.append(i)
    refl = []
    for s in simple:
        a = roots[s]
        perm = []
        for j in range(R):
            b = roots[j]
            perm.append(find(b - 2 * dot(b, a) / dot(a, a) * a))
        refl.append(tuple(perm))
    return refl, frozenset(pos), dot


def compose(p, q):  # p after q
    return tuple(p[i] for i in q)


def group(gens, R):
    ident = tuple(range(R))
    G = {ident}; frontier = [ident]
    while frontier:
        new = []
        for g in frontier:
            for s in gens:
                x = compose(s, g)
                if x not in G:
                    G.add(x); new.append(x)
        frontier = new
    return G


def analyse(typ, n, es=None, verbose=True):
    L = Lie(typ, n, es)
    S = setup(L)
    h = S['h']; roots = S['roots']; R = len(roots)
    l = L.l
    # Cyclic element and t'
    Ep = sum(L.es) + S['e_mth']
    adE = L.ad(Ep)
    u, sv, vh = np.linalg.svd(adE)
    tp = vh[-l:].conj()        # basis of kernel (rows)
    assert sv[-l] < 1e-8 and sv[-l - 1] > 1e-6, sv[-l - 2:]
    tpm = [L.mat(v) for v in tp]
    adtp = [L.ad(m) for m in tpm]
    rng = np.random.default_rng(3)
    gen = sum(complex(*rng.normal(size=2)) * a for a in adtp)
    vals, vecs = np.linalg.eig(gen)
    proots, pvecs = [], []
    for k in range(L.dim):
        if abs(vals[k]) > 1e-6:
            v = vecs[:, k]; j = np.argmax(abs(v))
            proots.append(np.array([(a @ v)[j] / v[j] for a in adtp]))
            pvecs.append(v)
    proots = np.array(proots)
    assert len(proots) == R
    # real coordinates for t'-roots: values on a real basis of t'_R; use coefficients w.r.t. a
    # Q-basis of roots instead: express in terms of l independent roots
    idx = []
    for i in range(R):
        cand = idx + [i]
        if np.linalg.matrix_rank(proots[cand], tol=1e-6) == len(cand):
            idx.append(i)
        if len(idx) == l:
            break
    pcoef = np.linalg.lstsq(proots[idx].T, proots.T, rcond=None)[0].T.real
    rcoef = S['coef'].astype(float)
    W_s, posW, _ = weyl_perms(rcoef)
    Wp_s, posWp, _ = weyl_perms(pcoef)
    W = group(W_s, R); Wp = group(Wp_s, R)
    # P action: on t-roots trivial in W; on t'-roots: Ad P maps root vector v_b to root c'(b)
    zeta = np.exp(2j * np.pi / h)
    # Ad P diagonal on t-root spaces with zeta^ht, identity on t
    # build Ad P in basis: eigen-decompose via generic h
    adh = [L.ad(x) for x in L.hs]
    rho = np.linalg.solve(S['simple'], np.ones(l))   # coefficients so that alpha_i(rho_vee)=1, in h_j basis
    adrho = sum(c * a for c, a in zip(rho, adh))
    ev, V = np.linalg.eig(adrho)
    AdP = V @ np.diag(np.exp(2j * np.pi * ev / h)) @ np.linalg.inv(V)
    def match_root(v, vecs, roots_vals, adbasis):
        j = np.argmax(abs(v))
        val = np.array([(a @ v)[j] / v[j] for a in adbasis])
        for k in range(len(roots_vals)):
            if np.linalg.norm(roots_vals[k] - val) < 1e-5:
                return k
        raise ValueError(val)
    cprime = tuple(match_root(AdP @ pvecs[b], pvecs, proots, adtp) for b in range(R))
    assert cprime in Wp
    # orders
    def power(p, k):
        r = tuple(range(R))
        for _ in range(k % h if k >= 0 else k % h):
            r = compose(p, r)
        return r
    cpow = [power(cprime, k) for k in range(h)]
    assert cpow[0] == tuple(range(R)) and len(set(cpow)) == h
    hts = S['hts']
    units = [k for k in range(1, h) if math.gcd(k, h) == 1] if h > 1 else [0]
    def kof_w(w):
        # w as permutation of t-roots; need ht(w^-1 a) = k ht(a) mod h
        inv = [0] * R
        for i, j in enumerate(w):
            inv[j] = i
        for k in units:
            if all((hts[inv[a]] - k * hts[a]) % h == 0 for a in range(R)):
                return k
        return None
    def kof_wp(wp):
        inv = [0] * R
        for i, j in enumerate(wp):
            inv[j] = i
        conj = compose(wp, compose(cprime, tuple(inv)))
        for k in units:
            if conj == cpow[k % h]:
                return k
        return None
    Wk = {}
    for w in W:
        k = kof_w(w)
        if k is not None:
            Wk.setdefault(k, []).append(w)
    Wpk = {}
    for wp in Wp:
        k = kof_wp(wp)
        if k is not None:
            Wpk.setdefault(k, []).append(wp)
    Phi = [(w, wp) for k in Wk for w in Wk[k] for wp in Wpk.get(k, [])]
    z = len(Wk.get(1, []))
    # chambers
    def chamber(w, pos):
        return frozenset(w[i] for i in pos)
    Q = {chamber(w, posW) for w in W}
    Qp = {chamber(w, posWp) for w in Wp}
    def act(perm, C):
        return frozenset(perm[i] for i in C)
    # orbits
    import os
    if os.environ.get('FAST'):
        Qlist, Qplist = list(Q), list(Qp)
        res = dict(typ=f"{typ}{n}", h=h, W=len(W), z=len(Wk.get(1, [])), Phi=len(Phi),
                   classes=len(W) ** 2 // len(Phi), out=[])
        for d in L.outs:
            psi_t, psi_tp, eps = outer_action(L, S, d, Ep, pvecs, proots, adtp, h)
            def inv(p):
                r = [0] * R
                for i, j in enumerate(p):
                    r[j] = i
                return tuple(r)
            tot = 0
            for w, wp in Phi:
                g = compose(inv(w), psi_t); gp = compose(inv(wp), psi_tp)
                a = sum(1 for C in Qlist if act(g, C) == C)
                if a == 0:
                    continue
                b = sum(1 for C in Qplist if act(gp, C) == C)
                tot += a * b
            res['out'].append((d, round(eps[0].real), tot / len(Phi)))
        print(res, flush=True)
        return res
    Ql, Qpl = sorted(Q, key=sorted), sorted(Qp, key=sorted)
    seen, classes = {}, []
    for C in Ql:
        for Cp in Qpl:
            if (C, Cp) in seen:
                continue
            orb = {(act(w, C), act(wp, Cp)) for w, wp in Phi}
            for x in orb:
                seen[x] = len(classes)
            classes.append(orb)
    phi_h = len(units)
    expected = len(W) ** 2 // (h * z * phi_h) if h * z * phi_h else None
    info = dict(typ=f"{typ}{n}", h=h, W=len(W), z=z, phi=phi_h, Phi=len(Phi), classes=len(classes),
                expected=expected)
    # adapted Borels B: chambers w C0 with w in Phi-image
    std = frozenset(i for i in range(R) if hts[i] > 0)
    assert std in Q
    adaptedW = {act(w, std) for w in Wk[1]}
    # Coxeter chambers in t': {b : Re(mu * b(E')) > 0}
    bE = np.array([match_val(L, Ep, pvecs[b]) for b in range(R)])
    cox = set()
    for t in np.linspace(0, 2 * np.pi, 4000, endpoint=False):
        mu = np.exp(1j * (t + 1e-3))
        vals = (mu * bE).real
        if np.min(abs(vals)) < 1e-9:
            continue
        cox.add(frozenset(i for i in range(R) if vals[i] > 0))
    cox &= Qp
    D = {seen[(C, Cp)] for C in adaptedW for Cp in cox}
    info['coxeter_chambers'] = len(cox)
    info['D_classes'] = len(D)
    # Out action
    out_info = []
    for d in L.outs:
        psi_t, psi_tp, eps = outer_action(L, S, d, Ep, pvecs, proots, adtp, h)
        img = {}
        for ci, orb in enumerate(classes):
            C, Cp = next(iter(orb))
            img[ci] = seen[(act(psi_t, C), act(psi_tp, Cp))]
        fixed = [ci for ci in img if img[ci] == ci]
        out_info.append(dict(perm=d, eps=eps, fixed=len(fixed), D_fixed=sorted(c for c in D if img[c] == c),
                             D_img={c: img[c] for c in D}))
    info['out'] = out_info
    info['D'] = sorted(D)
    if verbose:
        print(info)
    return info


def match_val(L, x, v):
    adx = L.ad(x)
    j = np.argmax(abs(v))
    return (adx @ v)[j] / v[j]


def outer_action(L, S, d, Ep, pvecs, proots, adtp, h):
    """Pinned automorphism delta permuting simple indices by d, composed with Ad(t) so that
    psi(E') is proportional to E'.  Returns its permutations of t-roots and t'-roots."""
    l = L.l
    # matrix of delta on g via words
    gens_img = [L.es[d[i]] for i in range(l)] + [L.fs[d[i]] for i in range(l)]
    D = np.zeros((L.dim, L.dim), dtype=complex)
    for k, w in enumerate(L.words):
        m = gens_img[w[0]]
        for i in w[1:]:
            m = bracket(gens_img[i], m)
        D[:, k] = L.coords(m)
    # check homomorphism on a random pair
    dE = L.mat(D @ L.coords(Ep))
    s = sum(L.es) - dE + S['e_mth'] * 0
    # coefficient of e_{-theta} in delta(E')
    em = S['e_mth']
    resid = dE - sum(L.es)
    eps = (L.coords(resid) @ L.coords(em).conj()) / (L.coords(em) @ L.coords(em).conj())
    eps = complex(eps)
    assert np.linalg.norm(resid - eps * em) < 1e-6
    assert abs(abs(eps) - 1) < 1e-6
    # Ad(t): scales g_alpha by lam^ht(alpha); want -> lam * (sum e_i + eps lam^{-h} e_-theta) prop. E'
    lam = np.exp(1j * np.angle(eps) / h)    # lam^h = eps  -> eps * lam^{-(h-1)} = lam
    adh = [L.ad(x) for x in L.hs]
    rho = np.linalg.solve(S['simple'], np.ones(l))
    adrho = sum(c * a for c, a in zip(rho, adh))
    ev, V = np.linalg.eig(adrho)
    Adt = V @ np.diag(lam ** ev) @ np.linalg.inv(V)
    Psi = Adt @ D
    PE = L.mat(Psi @ L.coords(Ep))
    ratio = (L.coords(PE) @ L.coords(Ep).conj()) / (L.coords(Ep) @ L.coords(Ep).conj())
    assert np.linalg.norm(PE - ratio * Ep) < 1e-6, "psi(E') not prop. to E'"
    # action on t-roots: root vectors rvecs
    R = len(proots)
    def perm_from(vecs, adbasis, rootvals):
        out = []
        for b in range(R):
            v = Psi @ vecs[b]
            j = np.argmax(abs(v))
            val = np.array([(a @ v)[j] / v[j] for a in adbasis])
            k = next(k for k in range(R) if np.linalg.norm(rootvals[k] - val) < 1e-5)
            out.append(k)
        return tuple(out)
    adh_list = adh
    psi_t = perm_from(S['rvecs'], adh_list, S['roots'])
    psi_tp = perm_from(pvecs, adtp, proots)
    return psi_t, psi_tp, (eps, ratio)


if __name__ == '__main__':
    for spec in sys.argv[1:]:
        i = analyse(spec[0], int(spec[1:]), verbose=False)
        if 'expected' not in i: continue
        print(i['typ'], 'h', i['h'], '|W|', i['W'], 'z', i['z'], 'classes', i['classes'], 'exp', i['expected'],
              'coxCh', i['coxeter_chambers'], 'D', i['D_classes'],
              [(o['perm'], round(o['eps'][0].real), 'fixed', o['fixed'], 'Dfixed', o['D_fixed'], o['D_img']) for o in i['out']],
              flush=True)
