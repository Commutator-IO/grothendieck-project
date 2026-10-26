#!/usr/bin/env python3
"""Count G(F_q)-orbits of Kostant rigidifications (T, B, T', B') for the split
adjoint groups of type A2, B2, G2 over prime fields F_q with q = 1 mod h.

Standard library only.  See README.md for the conventions and the reduction.
"""
import itertools, json, math, sys, time

# ---------------------------------------------------------------- linear algebra mod p

def rref(rows, p):
    """Reduced row echelon form of a list of vectors mod p; returns tuple of rows."""
    m = [list(r) for r in rows]
    out, ncol, piv_row = [], (len(m[0]) if m else 0), 0
    for c in range(ncol):
        sel = None
        for i in range(piv_row, len(m)):
            if m[i][c] % p:
                sel = i
                break
        if sel is None:
            continue
        m[piv_row], m[sel] = m[sel], m[piv_row]
        inv = pow(m[piv_row][c], p - 2, p)
        m[piv_row] = [(x * inv) % p for x in m[piv_row]]
        for i in range(len(m)):
            if i != piv_row and m[i][c] % p:
                f = m[i][c]
                m[i] = [(a - f * b) % p for a, b in zip(m[i], m[piv_row])]
        piv_row += 1
        if piv_row == len(m):
            break
    return tuple(tuple(r) for r in m[:piv_row])

def kernel(A, p):
    """Basis of {x : A x = 0} for a matrix A given as list of rows."""
    if not A:
        return []
    n = len(A[0])
    R = rref(A, p)
    pivots = []
    for r in R:
        pivots.append(next(i for i, x in enumerate(r) if x))
    free = [j for j in range(n) if j not in pivots]
    basis = []
    for f in free:
        v = [0] * n
        v[f] = 1
        for r, pc in zip(R, pivots):
            v[pc] = (-r[f]) % p
        basis.append(v)
    return basis

def matmul(A, B, p):
    Bt = list(zip(*B))
    return [[sum(a * b for a, b in zip(row, col)) % p for col in Bt] for row in A]

def matvec(A, v, p):
    return [sum(a * b for a, b in zip(row, v)) % p for row in A]

def inv_mat(A, p):
    n = len(A)
    M = [list(A[i]) + [int(i == j) for j in range(n)] for i in range(n)]
    R = rref(M, p)
    assert len(R) == n and all(R[i][i] == 1 for i in range(n)), "singular"
    return [list(r[n:]) for r in R]

def span(vectors, p):
    return rref(vectors, p)

# ---------------------------------------------------------------- the Lie algebras

def setup(typ, p):
    """Matrix realisation, as the Lie algebra of the stabiliser of a tensor whose
    weights for a diagonal torus are given.  Returns the Lie algebra data."""
    if typ == 'A2':
        W = [(1, 0), (0, 1), (-1, -1)]                 # weights of the 3-dim rep
        cons = 'trace'
    elif typ == 'B2':
        W = [(0, 0), (1, 0), (0, 1), (-1, 0), (0, -1)]  # so(5), Q = v0^2 + v1 v-1 + v2 v-2
        cons = 'quad'
    elif typ == 'G2':
        W = [(0, 0), (1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)]
        cons = 'cubic'
    n = len(W)
    neg = {i: W.index(tuple(-x for x in W[i])) for i in range(n) if tuple(-x for x in W[i]) in W}

    if cons == 'quad':
        M = [[0] * n for _ in range(n)]
        M[0][0] = 2
        for i in range(1, n):
            M[i][neg[i]] = 1
    if cons == 'cubic':
        # split octonion 3-form: v0^vi^v-i (i=1,2,3) + v1^v2^v3 + v-1^v-2^v-3
        phi = {}
        def add(a, b, c, s):
            for perm, sg in ((a, b, c), 1), ((b, c, a), 1), ((c, a, b), 1), \
                            ((b, a, c), -1), ((a, c, b), -1), ((c, b, a), -1):
                phi[perm] = (phi.get(perm, 0) + s * sg) % p
        for i in (1, 2, 3):
            add(0, i, neg[i], 1)
        add(1, 2, 3, 1)
        add(4, 5, 6, 1)

    def constraint(X):
        if cons == 'trace':
            return [sum(X[i][i] for i in range(n)) % p]
        if cons == 'quad':
            XtM = matmul([list(r) for r in zip(*X)], M, p)
            MX = matmul(M, X, p)
            return [(XtM[i][j] + MX[i][j]) % p for i in range(n) for j in range(n)]
        out = []
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    s = 0
                    for k in range(n):
                        s += X[k][a] * phi.get((k, b, c), 0) + X[k][b] * phi.get((a, k, c), 0) \
                             + X[k][c] * phi.get((a, b, k), 0)
                    out.append(s % p)
        return out

    # weight blocks of gl(V)
    blocks = {}
    for i in range(n):
        for j in range(n):
            w = tuple(a - b for a, b in zip(W[i], W[j]))
            blocks.setdefault(w, []).append((i, j))
    cartan, roots = [], {}
    for w, ents in blocks.items():
        cols = []
        for (i, j) in ents:
            E = [[0] * n for _ in range(n)]
            E[i][j] = 1
            cols.append(constraint(E))
        A = [list(r) for r in zip(*cols)]
        K = kernel(A, p)
        mats = []
        for v in K:
            X = [[0] * n for _ in range(n)]
            for c, (i, j) in zip(v, ents):
                X[i][j] = c
            mats.append(X)
        if w == (0, 0):
            cartan = mats
        elif mats:
            assert len(mats) == 1, (typ, w, len(mats))
            roots[w] = mats[0]
    r = 2
    assert len(cartan) == r, (typ, len(cartan))
    rootlist = sorted(roots)
    basis = cartan + [roots[w] for w in rootlist]
    d = len(basis)
    expected = {'A2': 8, 'B2': 10, 'G2': 14}[typ]
    assert d == expected, (typ, d)

    # coordinates
    flat = [[X[i][j] for i in range(n) for j in range(n)] for X in basis]
    cols = list(zip(*flat))  # n^2 rows, d cols
    # choose pivot rows
    piv, cur = [], []
    for idx, row in enumerate(cols):
        test = cur + [list(row)]
        if len(rref(test, p)) > len(cur):
            cur.append(list(row))
            piv.append(idx)
        if len(piv) == d:
            break
    sub = [list(cols[i]) for i in piv]
    subinv = inv_mat(sub, p)
    def coords(Y):
        fl = [Y[i][j] for i in range(n) for j in range(n)]
        v = matvec(subinv, [fl[i] for i in piv], p)
        # verify
        recon = [sum(v[k] * flat[k][t] for k in range(d)) % p for t in range(n * n)]
        assert recon == [x % p for x in fl], "not in L"
        return v
    def bracket(X, Y):
        XY, YX = matmul(X, Y, p), matmul(Y, X, p)
        return [[(a - b) % p for a, b in zip(r1, r2)] for r1, r2 in zip(XY, YX)]
    # structure constants
    sc = [[coords(bracket(basis[a], basis[b])) for b in range(d)] for a in range(d)]

    # root system combinatorics (in Z^2 weight coordinates)
    fpos = lambda w: w[0] * 1000 + w[1] * 1001 + 0.5 * w[1]
    pos = [w for w in rootlist if fpos(w) > 0]
    simple = [w for w in pos if not any(tuple(a - b for a, b in zip(w, u)) in pos for u in pos)]
    assert len(simple) == 2
    det = simple[0][0] * simple[1][1] - simple[0][1] * simple[1][0]
    def simple_coords(w):
        a = (w[0] * simple[1][1] - w[1] * simple[1][0])
        b = (simple[0][0] * w[1] - simple[0][1] * w[0])
        assert a % det == 0 and b % det == 0
        return (a // det, b // det)
    rootcoef = {w: simple_coords(w) for w in rootlist}
    return dict(typ=typ, p=p, d=d, r=r, roots=rootlist, rootcoef=rootcoef, sc=sc,
                simple=simple, pos=pos)

def bracket_vec(L, x, y):
    p, d, sc = L['p'], L['d'], L['sc']
    out = [0] * d
    for a in range(d):
        if x[a]:
            for b in range(d):
                if y[b]:
                    f = x[a] * y[b]
                    row = sc[a][b]
                    for k in range(d):
                        if row[k]:
                            out[k] += f * row[k]
    return [v % p for v in out]

def ad(L, x):
    d = L['d']
    cols = [bracket_vec(L, x, [int(i == k) for i in range(d)]) for k in range(d)]
    return [list(r) for r in zip(*cols)]

def root_vec(L, w):
    d = L['d']
    v = [0] * d
    v[L['r'] + L['roots'].index(w)] = 1
    return v

# ---------------------------------------------------------------- group elements (as automorphisms of L)

def torus_elements(L):
    p, d, r = L['p'], L['d'], L['r']
    for s in itertools.product(range(1, p), repeat=r):
        diag = [1] * r + [pow(s[0], L['rootcoef'][w][0] % (p - 1), p) *
                          pow(s[1], L['rootcoef'][w][1] % (p - 1), p) % p for w in L['roots']]
        yield s, diag

def apply_diag(diag, space, p):
    return rref([[a * b % p for a, b in zip(diag, v)] for v in space], p)

def exp_nil(A, p):
    d = len(A)
    I = [[int(i == j) for j in range(d)] for i in range(d)]
    out, term, k = [row[:] for row in I], I, 1
    while True:
        term = matmul(term, A, p)
        if not any(any(r) for r in term):
            return out
        inv = pow(math.factorial(k), p - 2, p)
        out = [[(o + t * inv) % p for o, t in zip(ro, rt)] for ro, rt in zip(out, term)]
        k += 1

def weyl_lifts(L):
    """One lift n_w in N(T)(F_p) for every w in W, as automorphism matrices of L,
    together with the induced permutation of roots."""
    p = L['p']
    gens = []
    for a in L['simple']:
        e = root_vec(L, a)
        f0 = root_vec(L, tuple(-x for x in a))
        h = bracket_vec(L, e, f0)
        he = bracket_vec(L, h, e)
        c = he[L['r'] + L['roots'].index(a)]
        f = [x * 2 * pow(c, p - 2, p) % p for x in f0]
        E, F = exp_nil(ad(L, e), p), exp_nil(ad(L, [(-x) % p for x in f]), p)
        gens.append(matmul(matmul(E, F, p), E, p))
    def perm(Mx):
        out = []
        for w in L['roots']:
            img = [row[L['r'] + L['roots'].index(w)] for row in Mx]
            nz = [k for k, x in enumerate(img) if x]
            assert len(nz) == 1 and nz[0] >= L['r']
            out.append(L['roots'][nz[0] - L['r']])
        return tuple(out)
    d = L['d']
    I = [[int(i == j) for j in range(d)] for i in range(d)]
    lifts = {perm(I): I}
    frontier = [I]
    while frontier:
        nf = []
        for Mx in frontier:
            for g in gens:
                N = matmul(g, Mx, p)
                k = perm(N)
                if k not in lifts:
                    lifts[k] = N
                    nf.append(N)
        frontier = nf
    return lifts

def apply_mat(Mx, space, p):
    return rref([matvec(Mx, v, p) for v in space], p)

# ---------------------------------------------------------------- tori, Borels

def positive_systems(L):
    """All positive systems of the root system of t0, as (base, highest root)."""
    roots = L['roots']
    res = []
    for b1, b2 in itertools.permutations(roots, 2):
        if b1 > b2:
            continue
        det = b1[0] * b2[1] - b1[1] * b2[0]
        if det == 0:
            continue
        ok, P = True, []
        for w in roots:
            a = (w[0] * b2[1] - w[1] * b2[0]); b = (b1[0] * w[1] - b1[1] * w[0])
            if a % det or b % det:
                ok = False; break
            a //= det; b //= det
            if a >= 0 and b >= 0:
                P.append((a + b, w))
            elif not (a <= 0 and b <= 0):
                ok = False; break
        if ok:
            res.append(((b1, b2), max(P)[1], [w for _, w in P]))
    return res

def borels_containing(L, t, x):
    """Borel subalgebras b ⊃ t for a Cartan subalgebra t = centraliser of the regular
    semisimple element x, via the eigenspaces of ad x.  Returns None if t is not split
    over F_p (some eigenvalue of ad x not in F_p)."""
    p, d = L['p'], L['d']
    A = ad(L, x)
    best, total = {}, 0
    for lam in range(1, p):
        K = kernel([[(A[i][j] - (lam if i == j else 0)) % p for j in range(d)] for i in range(d)], p)
        if K:
            best[lam] = K
            total += len(K)
    if total != d - len(t):
        return None
    # refine eigenspaces of ad x that are not lines by the other elements of t
    spaces = list(best.values())
    for y in t:
        Ay, new = ad(L, y), []
        for S in spaces:
            if len(S) == 1:
                new.append(S); continue
            AS = [matvec(Ay, v, p) for v in S]           # images, as vectors
            got = 0
            for lam in range(p):
                M = [[(AS[k][i] - lam * S[k][i]) % p for k in range(len(S))] for i in range(d)]
                K = kernel(M, p)
                if K:
                    new.append([[sum(a * S[k][i] for k, a in enumerate(c)) % p for i in range(d)] for c in K])
                    got += len(K)
            if got != len(S):
                return None
        spaces = new
    assert all(len(K) == 1 for K in spaces), "t not split by its basis"
    vecs = [K[0] for K in spaces]
    nroot = len(vecs)
    # pair opposite roots: [v_a, v_b] in t
    tsp = rref(t, p)
    def in_space(v, S):
        return len(rref(list(S) + [v], p)) == len(S)
    opp = {}
    for i in range(nroot):
        for j in range(nroot):
            if i != j and in_space(bracket_vec(L, vecs[i], vecs[j]), tsp) and any(bracket_vec(L, vecs[i], vecs[j])):
                opp[i] = j
    assert len(opp) == nroot
    pairs = sorted({tuple(sorted((i, opp[i]))) for i in range(nroot)})
    out = []
    for choice in itertools.product((0, 1), repeat=len(pairs)):
        P = [pr[c] for pr, c in zip(pairs, choice)]
        b = rref(list(t) + [vecs[i] for i in P], p)
        closed = all(in_space(bracket_vec(L, vecs[i], vecs[j]), b) for i in P for j in P)
        if closed:
            out.append(b)
    return out

def centraliser(L, x):
    return rref(kernel(ad(L, x), p=L['p']), L['p'])

# ---------------------------------------------------------------- the count

def count(typ, p):
    t0 = time.time()
    L = setup(typ, p)
    d, r = L['d'], L['r']
    nW = {'A2': 6, 'B2': 8, 'G2': 12}[typ]
    h = {'A2': 3, 'B2': 4, 'G2': 6}[typ]
    z = {'A2': 3, 'B2': 2, 'G2': 1}[typ]
    phi = sum(1 for k in range(1, h + 1) if math.gcd(k, h) == 1)
    assert (p - 1) % h == 0
    tcart = rref([[int(i == k) for i in range(d)] for k in range(r)], p)
    PS = positive_systems(L)
    assert len(PS) == nW
    torus = list(torus_elements(L))
    # representatives of tori in apposition: e = e_b1 + e_b2 + c e_{-theta}; every
    # other choice of nonzero coefficients is a T(F_q)-translate of a multiple of one of these.
    reps = {}
    nonreg = 0
    for (b1, b2), theta, _ in PS:
        for c in range(1, p):
            e = [(x + y + c * z_) % p for x, y, z_ in
                 zip(root_vec(L, b1), root_vec(L, b2), root_vec(L, tuple(-x for x in theta)))]
            tp = centraliser(L, e)
            if len(tp) != r:
                nonreg += 1
                continue
            reps.setdefault(tp, e)
    # orbits of T(F_q) on {(t', b') : t' in apposition with t0, t' split, b' ⊃ t'}
    split_reps, nonsplit = [], 0
    for tp, e in reps.items():
        Bs = borels_containing(L, tp, e)
        if Bs is None:
            nonsplit += 1
            continue
        assert len(Bs) == nW, (typ, p, len(Bs))
        split_reps.append((tp, Bs))
    seen, orbits, stabs = set(), [], []
    all_tp = set()
    for tp, Bs in split_reps:
        for bp in Bs:
            if (tp, bp) in seen:
                continue
            orb = set()
            for s, diag in torus:
                img = (apply_diag(diag, tp, p), apply_diag(diag, bp, p))
                orb.add(img)
                all_tp.add(img[0])
            seen |= orb
            orbits.append((tp, bp))
            stabs.append(len(torus) // len(orb))
    free = all(s == 1 for s in stabs) and all(len(torus) % 1 == 0 for _ in stabs)
    # sizes check: each orbit must have exactly |T| elements for freeness
    sizes_ok = len(seen) == len(orbits) * len(torus)
    # groups attached to one pair (t0, t'1)
    tp1 = split_reps[0][0]
    T_cap_NT = [s for s, diag in torus if apply_diag(diag, tp1, p) == tp1]
    T_cap_T = [s for s, diag in torus if all([a * b % p for a, b in zip(diag, v)] == list(v) for v in tp1)]
    # order of the cyclic group T ∩ N(T')
    def order(s):
        k, cur = 1, s
        while cur != (1,) * r:
            cur = tuple(a * b % p for a, b in zip(cur, s)); k += 1
        return k
    cyclic = any(order(s) == len(T_cap_NT) for s in T_cap_NT)
    lifts = weyl_lifts(L)
    assert len(lifts) == nW
    stab_pair, image_W = 0, set()
    for wkey, n_w in lifts.items():
        for s, diag in torus:
            Mx = [[diag[i] * n_w[i][j] % p for j in range(d)] for i in range(d)]
            if apply_mat(Mx, tp1, p) == tp1:
                stab_pair += 1
                image_W.add(wkey)
    # general position of B and B' (letter's question): dim(b ∩ b') for each orbit rep
    def inter_dim(U, V):
        return len(U) + len(V) - len(rref(list(U) + list(V), p))
    b0 = rref(list(tcart) + [root_vec(L, w) for w in L['pos']], p)
    # orbits of N(T)(F_q) on triples (b, t', b') are those of T(F_q) on (t', b') with b = b0;
    # rather than conjugating, record dim(b ∩ b') for b = b0 directly.
    gp = sorted(inter_dim(b0, bp) for tp, bp in orbits)
    res = dict(type=typ, q=p, h=h, z=z, phi_h=phi, W=nW,
               predicted=nW * nW // (h * z * phi), predicted_with_generator=nW * nW // (h * z),
               orbits=len(orbits), orbits_with_generator=len(orbits) * phi if cyclic and len(T_cap_NT) == h else None,
               action_free=bool(free and sizes_ok),
               apposition_tori_rational_split=len(all_tp),
               apposition_reps_nonsplit=nonsplit, nonregular_e=nonreg,
               T_cap_NTp=len(T_cap_NT), T_cap_NTp_cyclic=cyclic, T_cap_Tp=len(T_cap_T),
               NT_cap_NTp=stab_pair, NT_cap_NTp_image_in_W=len(image_W),
               predicted_NT_cap_NTp=h * z * phi,
               dim_b_cap_bprime=gp, seconds=round(time.time() - t0, 1))
    return res

if __name__ == '__main__':
    plan = {'A2': [7, 13, 19, 31, 37], 'B2': [5, 13, 17, 29, 37], 'G2': [7, 13, 19, 31, 37]}
    if len(sys.argv) > 1:
        plan = {k: v for k, v in plan.items() if k in sys.argv[1:]}
    results = []
    for typ, qs in plan.items():
        for q in qs:
            res = count(typ, q)
            print(json.dumps(res), flush=True)
            results.append(res)
    if len(sys.argv) == 1:
        with open(__file__.rsplit('/', 1)[0] + '/results.json', 'w') as f:
            json.dump(results, f, indent=1)
