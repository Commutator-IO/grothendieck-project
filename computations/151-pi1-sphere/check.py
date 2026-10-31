"""Folder 151 (modern reading pp. 37-41): the Pi_1 level of the tube gluing
is too coarse on P^1_C = S^2, and the gerbe level recovers H^2(S^2, A) = A.

1. Groupoid level.  Pushout of fundamental groups of the pieces
   (S^2 with k marked points: X* = S^2 minus k points, pi_1 = F_{k-1};
    k discs D_i, pi_1 = 1; k punctured discs, pi_1 = Z):
   order of the amalgamated group, by sympy's coset enumeration.
2. Categories.  Homology over Q and F_p (degrees 0..4) of the nerve of
   (a) the category  .->.  of the page (two objects, one arrow);
   (b) the category the definition of p. 37 gives for the three groupoids
       A = Pi_1(V*), B = Pi_1(V), C = Pi_1(X*): objects a, b, c, End(a) = G,
       one arrow a->b and one a->c;
   (c) the two-object category End(a) = G, one arrow a->b (the first case,
       X = C, of p. 38).
   G = Z/m (m = 2..4) stands in for Z, so that each chain group is finite;
   hocolim(* <- BG -> *) = Sigma BG has H_2 = H_1(G) = G.
3. Simplicial homotopy pushout * <- S^1 -> * (S^1 a 3-cycle): homology of S^2.
4. Gerbe count.  Classes of gluing data (trivial extensions on the pieces,
   an automorphism Hom(Z, A) per boundary circle, modulo Hom(F_{k-1}, A)
   acting through the boundary loops c_1..c_k, c_1...c_k = 1), by brute force,
   compared with |H^2(S^2; A)| from simplicial cochains of the boundary of
   a tetrahedron, for several finite abelian A and k = 1..3.
"""
import itertools
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form  # small matrices only
from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup

def snf_diag(M):
    if M.rows == 0 or M.cols == 0: return []
    S = smith_normal_form(M, domain=ZZ)
    return [abs(S[i, i]) for i in range(min(S.rows, S.cols)) if S[i, i] != 0]

def homology(boundaries, dims, top):
    """boundaries[k]: matrix C_k -> C_{k-1} (rows = dim C_{k-1}); H_0..H_top"""
    res = []
    for k in range(top+1):
        dk = boundaries.get(k)
        rank_k = len(snf_diag(dk)) if dk is not None else 0
        dk1 = boundaries.get(k+1)
        d = snf_diag(dk1) if dk1 is not None else []
        free = dims[k] - rank_k - len(d)
        tors = [x for x in d if x > 1]
        res.append((free, tors))
    return res

def fmt(h):
    out = []
    for free, tors in h:
        parts = (["Z^%d" % free] if free > 1 else (["Z"] if free == 1 else [])) + ["Z/%d" % t for t in tors]
        out.append(" + ".join(parts) if parts else "0")
    return "[" + ", ".join(out) + "]"

# ---------- 2. nerves of small categories (normalised chains) ----------
def nerve_homology(objects, arrows, compose, ident, top=4):
    """arrows: list of (src, tgt, name) non-identity; compose(g, f) = g o f
    returns a name or ident(obj). Normalised chain complex: strings of
    composable non-identity arrows."""
    by_src = {}
    for a in arrows: by_src.setdefault(a[0], []).append(a)
    chains = {0: [(o,) for o in objects]}
    simp = {0: [((o,), ()) for o in objects]}
    for k in range(1, top+2):
        nxt = []
        for (objs, arr) in simp[k-1]:
            last = objs[-1]
            for a in by_src.get(last, []):
                nxt.append((objs + (a[1],), arr + (a[2],)))
        simp[k] = nxt
    index = {k: {s: i for i, s in enumerate(simp[k])} for k in simp}
    B = {}
    for k in range(1, top+2):
        M = [[0]*len(simp[k]) for _ in range(len(simp[k-1]))]
        for j, (objs, arr) in enumerate(simp[k]):
            for i in range(k+1):
                if i == 0:
                    face = (objs[1:], arr[1:])
                elif i == k:
                    face = (objs[:-1], arr[:-1])
                else:
                    c = compose(arr[i], arr[i-1])
                    if c is None:      # identity: degenerate face, 0 in normalised complex
                        continue
                    face = (objs[:i] + objs[i+1:], arr[:i-1] + (c,) + arr[i+1:])
                M[index[k-1][face]][j] += (-1)**i
        B[k] = M
    dims = {k: len(simp[k]) for k in simp}
    return B, dims

def rank_mod(M, p):
    rows = [[x % p for x in r] for r in M]
    rank, ncols = 0, (len(rows[0]) if rows else 0)
    for c in range(ncols):
        piv = next((r for r in range(rank, len(rows)) if rows[r][c]), None)
        if piv is None: continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][c], p-2, p)
        rows[rank] = [x*inv % p for x in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][c]:
                f = rows[r][c]
                rows[r] = [(x - f*y) % p for x, y in zip(rows[r], rows[rank])]
        rank += 1
    return rank

def betti_mod(B, dims, p, top=4):
    """dim H_k(nerve; F_p), k = 0..top (p = 1000003 stands for Q)"""
    rk = {k: rank_mod(B[k], p) for k in B}
    return [dims[k] - rk.get(k, 0) - rk.get(k+1, 0) for k in range(top+1)]

def cat_span(m, legs):
    """objects a (End = Z/m), and one leg object per name in legs."""
    objs = ['a'] + legs
    arrows = [('a', 'a', ('g', r)) for r in range(1, m)] + [('a', x, ('to', x)) for x in legs]
    def compose(g, f):   # g o f
        if g[0] == 'g' and f[0] == 'g':
            r = (g[1] + f[1]) % m
            return None if r == 0 else ('g', r)
        if g[0] == 'to' and f[0] == 'g':
            return g
        raise ValueError
    return objs, arrows, compose

def arrow_cat():
    return ['a', 'b'], [('a', 'b', 'u')], lambda g, f: (_ for _ in ()).throw(ValueError)

# ---------- 3. simplicial suspension of a 3-cycle ----------
def suspension_homology():
    # vertices 0,1,2 (circle), N, S cones
    V = [0, 1, 2, 'N', 'S']
    E = [(0, 1), (1, 2), (0, 2)] + [(i, 'N') for i in range(3)] + [(i, 'S') for i in range(3)]
    T = [(0, 1, 'N'), (1, 2, 'N'), (0, 2, 'N'), (0, 1, 'S'), (1, 2, 'S'), (0, 2, 'S')]
    vi = {v: i for i, v in enumerate(V)}; ei = {e: i for i, e in enumerate(E)}
    d1 = [[0]*len(E) for _ in V]
    for j, (u, v) in enumerate(E): d1[vi[v]][j] += 1; d1[vi[u]][j] -= 1
    d2 = [[0]*len(T) for _ in E]
    for j, (u, v, w) in enumerate(T):
        d2[ei[(v, w)]][j] += 1; d2[ei[(u, w)]][j] -= 1; d2[ei[(u, v)]][j] += 1
    return homology({1: Matrix(d1), 2: Matrix(d2)}, {0: 5, 1: 9, 2: 6}, 2)

# ---------- 4. gerbe gluing data vs H^2(S^2; A) ----------
def abelian(ms):
    return list(itertools.product(*[range(m) for m in ms]))
def add(x, y, ms): return tuple((a+b) % m for a, b, m in zip(x, y, ms))
def neg(x, ms): return tuple((-a) % m for a, m in zip(x, ms))

def gerbe_classes(ms, k):
    A = abelian(ms)
    data = list(itertools.product(A, repeat=k))          # Hom(Z,A)^k
    # image of Hom(F_{k-1}, A): f(x_1..x_{k-1}) free, f(c_k) = -sum
    im = set()
    for vals in itertools.product(A, repeat=k-1):
        s = tuple(0 for _ in ms)
        for v in vals: s = add(s, v, ms)
        im.add(tuple(vals) + (neg(s, ms),))
    seen, classes = set(), 0
    for d in data:
        if d in seen: continue
        classes += 1
        for h in im:
            seen.add(tuple(add(a, b, ms) for a, b in zip(d, h)))
    return classes

def h2_sphere_order(ms):
    """|H^2(boundary of tetrahedron; A)| = |coker(d: C^1 -> C^2)| with A = prod Z/m."""
    V = range(4)
    E = list(itertools.combinations(V, 2)); T = list(itertools.combinations(V, 3))
    ei = {e: i for i, e in enumerate(E)}
    # coboundary C^1 -> C^2 as integer matrix (rows T, cols E)
    D = [[0]*len(E) for _ in T]
    for r, (u, v, w) in enumerate(T):
        D[r][ei[(v, w)]] += 1; D[r][ei[(u, w)]] -= 1; D[r][ei[(u, v)]] += 1
    diag = snf_diag(Matrix(D)) + [0]*(len(T) - len(snf_diag(Matrix(D))))
    import math
    order = 1
    for m in ms:
        for dd in diag:  # coker of Z^E -> Z^T tensored with Z/m: Z/gcd(dd, m)
            order *= math.gcd(dd, m) if dd else m
    return order

def main():
    out = []
    out.append("1. Amalgamated pi_1 of the pieces of S^2 with k marked points")
    for k in range(1, 5):
        if k == 1:
            out.append("   k=1: 1 *_Z 1 = trivial group (both legs kill the generator)")
            continue
        F = free_group(",".join("x%d" % i for i in range(1, k)))
        gens = F[1:]
        prod = gens[0]
        for g in gens[1:]: prod = prod * g
        rels = list(gens) + [prod**-1]          # boundary loops c_1..c_k killed by the discs
        G = FpGroup(F[0], rels)
        out.append(f"   k={k}: F_{k-1} / <<c_1..c_k>> has order {G.order()}")
    out.append("   -> the 1-type obtained by gluing groupoids is contractible; pi_1(S^2) = 1 agrees, pi_2 is lost")
    out.append("2. Homology H_0..H_4 of nerves of small categories (G = Z/m in place of Z)")
    out.append("   dims of H_0..H_4 with coefficients in Q (mod 1000003) and in F_p, p | m")
    o, a, _ = arrow_cat()
    B, d = nerve_homology(o, a, None, None)
    out.append("   (a) .->.                    : Q " + str(betti_mod(B, d, 1000003)) + "  F_2 " + str(betti_mod(B, d, 2)))
    for m in (2, 3, 4, 5):
        p = min(q for q in (2, 3, 5) if m % q == 0)
        for label, legs in (("(c) End(a)=Z/%d, a->b      " % m, ['b']), ("(b) End(a)=Z/%d, a->b, a->c" % m, ['b', 'c'])):
            o, a, c = cat_span(m, legs)
            B, d = nerve_homology(o, a, c, None)
            out.append(f"   {label}: Q " + str(betti_mod(B, d, 1000003)) + f"  F_{p} " + str(betti_mod(B, d, p)))
    out.append("   expected: (c) contractible [1,0,0,0,0]; (b) = Sigma B(Z/m): Q [1,0,0,0,0], F_p [1,0,1,1,1]")
    out.append("3. Simplicial homotopy pushout * <- S^1 -> *: H_0..H_2 = " + fmt(suspension_homology()))
    out.append("4. Gerbe gluing classes vs |H^2(S^2; A)|")
    for ms in [(2,), (3,), (4,), (5,), (6,), (7,), (8,), (2, 2), (2, 4), (3, 3)]:
        h2 = h2_sphere_order(ms)
        row = []
        for k in (1, 2, 3):
            if len(abelian(ms))**(2*k-1) > 300000: row.append(f"k={k}: skipped"); continue
            row.append(f"k={k}: {gerbe_classes(ms, k)}")
        name = " x ".join("Z/%d" % m for m in ms)
        out.append(f"   A = {name:10s} |A| = {len(abelian(ms)):2d}  |H^2(S^2;A)| = {h2:2d}  gluing classes " + ", ".join(row))
    print("\n".join(out))

if __name__ == "__main__":
    main()
