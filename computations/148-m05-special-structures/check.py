"""Folder 148, pp. 30-35: the chart of « special » structures on five points.

Counts, with an explicit definition, the special structures of modular
dimension <= 2 on a set K of five labelled points of the Riemann sphere,
their S_5-orbits, and for each orbit the groups G (holomorphic) and G~
(holomorphic and antiholomorphic) of automorphisms of one structure, to
compare with the chart of page 30 (12 + 20 + 30, 60 + 60 + 120,
60 + 120 + 60; total 542 in nine orbits).

Definition used (the edition's; the page gives none in words):

  level 2  a point p of M_{0,5}(C) that is an isolated fixed point of its
           stabiliser in S_5 (a finite group of order > 2 is needed: a
           single involution fixes a curve);
  level 1  a point p of a boundary divisor D_{ab} = M_{0,3} x M_{0,4} whose
           stabiliser permutes the three points c, d, e of the four-holed
           piece non-trivially (an isolated fixed point in D_{ab}), together
           with a ray t in the normal line N = T_n(triangle) (x) T_n(piece)
           at the node n;
  level 0  a point of a 0-dimensional stratum (three triangles), together
           with a pair of rays (t1, t2) in the normal lines at its two nodes;
and the rays are « real »: t is an isolated fixed point, in the space of
rays over p, of an antiholomorphic automorphism of the marked stable curve
that fixes p and each node (it may permute the labels).  This is the
reading of « sommets-repères » as tangential base points, and of the NB of
page 30 (« sauf I_4, toutes ces structures sont réelles »).

Everything is computed numerically (complex floating point, tolerance
1e-9) from Möbius transformations; nothing about the answer is put in by
hand.  Run: python3 check.py > results.txt
"""
import cmath
import math
from itertools import permutations, combinations

EPS = 1e-9
INF = None  # the point at infinity
LABELS = range(5)
S5 = list(permutations(LABELS))


# --- projective line -------------------------------------------------------

def hom(z):
    return (1 + 0j, 0j) if z is INF else (complex(z), 1 + 0j)


def aff(v):
    x, y = v
    return INF if abs(y) < EPS * max(1.0, abs(x)) else x / y


def same(z, w):
    (a, b), (c, d) = hom(z), hom(w)
    return abs(a * d - b * c) < 1e-7 * max(1.0, abs(a), abs(b)) * max(1.0, abs(c), abs(d))


def conj(z):
    return INF if z is INF else z.conjugate()


def mat_apply(M, z):
    (a, b), (c, d) = M
    x, y = hom(z)
    return aff((a * x + b * y, c * x + d * y))


def mat_mul(A, B):
    return ((A[0][0] * B[0][0] + A[0][1] * B[1][0], A[0][0] * B[0][1] + A[0][1] * B[1][1]),
            (A[1][0] * B[0][0] + A[1][1] * B[1][0], A[1][0] * B[0][1] + A[1][1] * B[1][1]))


def mat_inv(M):
    (a, b), (c, d) = M
    return ((d, -b), (-c, a))


def mat_conj(M):
    return tuple(tuple(x.conjugate() for x in row) for row in M)


def to_01inf(p1, p2, p3):
    """The Möbius map sending p1, p2, p3 to 0, 1, infinity."""
    v1, v2, v3 = hom(p1), hom(p2), hom(p3)
    r1 = (v1[1], -v1[0])
    r2 = (v3[1], -v3[0])
    s1 = r1[0] * v2[0] + r1[1] * v2[1]
    s2 = r2[0] * v2[0] + r2[1] * v2[1]
    return ((r1[0] / s1, r1[1] / s1), (r2[0] / s2, r2[1] / s2))


def mobius_3(src, dst):
    """The Möbius map sending the three points src to the three points dst."""
    return mat_mul(mat_inv(to_01inf(*dst)), to_01inf(*src))


def deriv0(M):
    """f'(0) for a Möbius map f with f(0) = 0."""
    (a, b), (c, d) = M
    assert abs(b) < 1e-7 * max(abs(a), abs(d)), "map does not fix 0"
    return a / d


def chart(z):
    """A Möbius chart sending z to 0."""
    if z is INF:
        return ((0j, 1 + 0j), (1 + 0j, 0j))
    return ((1 + 0j, -complex(z)), (0j, 1 + 0j))


def ang(x):
    return cmath.phase(x) % (2 * math.pi)


def same_angle(a, b):
    d = (a - b) % (2 * math.pi)
    return min(d, 2 * math.pi - d) < 1e-7


# --- marked stable curves ---------------------------------------------------
# A curve is a list of components; a component is a dict  label -> point,
# where a label is an int (a point of K) or a string (a node).  Each node
# label occurs in exactly two components.

def nodes_of(curve):
    return sorted({l for comp in curve for l in comp if isinstance(l, str)})


def automorphism(curve, g, anti):
    """If the relabelling g (with complex conjugation if anti) is an
    automorphism of the curve, return (node map, {node: (A, B)}) where the
    action on the normal line at node n, sent to node n', is
    theta -> (+-theta) + arg A + arg B; else None."""
    marks = [frozenset(l for l in comp if isinstance(l, int)) for comp in curve]
    comp_image = []
    for m in marks:
        target = frozenset(g[l] for l in m)
        if target not in marks:
            return None
        comp_image.append(marks.index(target))
    if len(set(comp_image)) != len(curve):
        return None
    node_map = {}
    for n in nodes_of(curve):
        cs = [i for i, comp in enumerate(curve) if n in comp]
        img = {comp_image[i] for i in cs}
        cand = [m for m in nodes_of(curve) if {i for i, comp in enumerate(curve) if m in comp} == img]
        if len(cand) != 1:
            return None
        node_map[n] = cand[0]
    derivs = {}
    for i, comp in enumerate(curve):
        tgt = curve[comp_image[i]]
        lab = list(comp)
        img = [g[l] if isinstance(l, int) else node_map[l] for l in lab]
        src = [conj(comp[l]) if anti else comp[l] for l in lab]
        dst = [tgt[l] for l in img]
        M = mobius_3(src[:3], dst[:3])
        if not all(same(mat_apply(M, s), d) for s, d in zip(src, dst)):
            return None
        for l in lab:
            if isinstance(l, str):
                cs = chart(comp[l])
                cinv = mat_inv(cs)
                if anti:
                    cinv = mat_conj(cinv)
                h = mat_mul(chart(tgt[node_map[l]]), mat_mul(M, cinv))
                derivs.setdefault(l, []).append(deriv0(h))
    return node_map, {n: tuple(v) for n, v in derivs.items()}


def stabiliser(curve):
    out = []
    for g in S5:
        for anti in (False, True):
            a = automorphism(curve, g, anti)
            if a is not None:
                out.append((g, anti, a[0], a[1]))
    return out


def act(elem, rays, nodes):
    g, anti, nmap, d = elem
    new = {}
    for n, th in zip(nodes, rays):
        A, B = d[n]
        new[nmap[n]] = ((-th if anti else th) + ang(A) + ang(B)) % (2 * math.pi)
    return tuple(new[n] for n in nodes)


def same_rays(r, s):
    return all(same_angle(a, b) for a, b in zip(r, s))


def real_rays(stab, nodes):
    """Ray tuples isolated-fixed by a node-fixing antiholomorphic element."""
    found = []
    for g, anti, nmap, d in stab:
        if not anti or any(nmap[n] != n for n in nodes):
            continue
        choices = []
        for n in nodes:
            c = (ang(d[n][0]) + ang(d[n][1])) / 2
            choices.append([c % (2 * math.pi), (c + math.pi) % (2 * math.pi)])
        tuples = [()]
        for ch in choices:
            tuples = [t + (x,) for t in tuples for x in ch]
        for t in tuples:
            if not any(same_rays(t, s) for s in found):
                found.append(t)
    return found


# --- the strata -------------------------------------------------------------

def key5(pts):
    """Normal form of a labelled 5-point configuration: send 0, 1, 2 to
    0, 1, infinity and read off the images of 3 and 4."""
    M = to_01inf(pts[0], pts[1], pts[2])
    out = []
    for i in (3, 4):
        w = mat_apply(M, pts[i])
        out.append((round(w.real, 6), round(w.imag, 6)))
    return tuple(out)


def level2_points():
    """Points of M_{0,5} fixed by an element of order >= 3 (up to Möbius,
    z -> zeta z with fixed points 0, infinity), deduplicated."""
    seen = {}
    for g in S5:
        cycles, done = [], set()
        for i in LABELS:
            if i in done:
                continue
            c, j = [], i
            while j not in done:
                done.add(j)
                c.append(j)
                j = g[j]
            cycles.append(c)
        long = [c for c in cycles if len(c) > 1]
        fixed = [c[0] for c in cycles if len(c) == 1]
        if len(long) != 1 or len(long[0]) < 3 or len(fixed) > 2:
            continue  # order >= 3 needs one cycle of length nu and <= 2 fixed points
        nu = len(long[0])
        for k in range(1, nu):
            if math.gcd(k, nu) != 1:
                continue
            zeta = cmath.exp(2j * math.pi * k / nu)
            for fixpos in permutations([0j, INF], len(fixed)):
                pts = [None] * 5
                for j, l in enumerate(long[0]):
                    pts[l] = zeta ** j
                for l, z in zip(fixed, fixpos):
                    pts[l] = z
                seen.setdefault(key5(pts), pts)
    return list(seen.values())


def level1_points():
    """For each circle {a, b}: the curve (triangle a, b, n) + (piece c, d,
    e, n), with lambda a fixed point of a non-trivial permutation of c, d, e."""
    out = []
    for a, b in combinations(LABELS, 2):
        c, d, e = [l for l in LABELS if l not in (a, b)]

        def renorm(lam, s):
            # piece: n = 0, c = 1, d = inf, e = lam; relabel by s; read lambda again
            pos = {'n': 0j, c: 1 + 0j, d: INF, e: lam}
            new = {'n': pos['n'], s[c]: pos[c], s[d]: pos[d], s[e]: pos[e]}
            M = to_01inf(new['n'], new[c], new[d])
            return mat_apply(M, new[e])

        lams = []
        for s3 in permutations((c, d, e)):
            s = dict(zip((c, d, e), s3))
            if s3 == (c, d, e):
                continue
            # the induced map on lambda is Möbius: fit it at three values
            xs = [0.3 + 0.7j, -1.7 + 0.2j, 2.1 - 1.3j]
            T = mobius_3(xs, [renorm(x, s) for x in xs])
            (p, q), (r, t) = T
            # fixed points: r z^2 + (t - p) z - q = 0
            if abs(r) < EPS:
                roots = [q / (t - p)] if abs(p - t) > EPS else []  # z = (p z + q) / t
            else:
                disc = cmath.sqrt((t - p) ** 2 + 4 * r * q)
                roots = [((p - t) + disc) / (2 * r), ((p - t) - disc) / (2 * r)]
            for z in roots:
                if abs(z) < 1e-6 or abs(z - 1) < 1e-6 or abs(z) > 1e6:
                    continue
                if not any(abs(z - w) < 1e-6 for w in lams):
                    lams.append(z)
        for lam in lams:
            tri = {a: 1 + 0j, b: INF, 'n': 0j}
            piece = {'n': 0j, c: 1 + 0j, d: INF, e: lam}
            out.append(((a, b), lam, [tri, piece]))
    return out


def level0_points():
    out = []
    for mid in LABELS:
        rest = [l for l in LABELS if l != mid]
        for pair in combinations(rest, 2):
            if rest[0] not in pair:
                continue
            other = tuple(l for l in rest if l not in pair)
            e1 = {pair[0]: 1 + 0j, pair[1]: INF, 'n1': 0j}
            m = {'n1': 0j, mid: 1 + 0j, 'n2': INF}
            e2 = {other[0]: 1 + 0j, other[1]: INF, 'n2': 0j}
            out.append(((pair, mid, other), [e1, m, e2]))
    return out


# --- orbits -----------------------------------------------------------------

def orbit_types(structures):
    """structures: list of (point_id, curve, stab, rays).  The S_5-orbits of
    (point, rays) are the S_5-orbits of points times the Stab(p)-orbits on
    rays; returns one line per orbit."""
    rows = []
    for pid, curve, stab, rays, npoints in structures:
        nodes = nodes_of(curve)
        left = list(rays)
        while left:
            t = left[0]
            orb = []
            for el in stab:
                u = act(el, t, nodes)
                if not any(same_rays(u, s) for s in orb):
                    orb.append(u)
            left = [s for s in left if not any(same_rays(s, o) for o in orb)]
            G = [el for el in stab if not el[1] and same_rays(act(el, t, nodes), t)]
            Gt = [el for el in stab if same_rays(act(el, t, nodes), t)]
            labfix = any(el[1] and all(el[0][i] == i for i in LABELS) for el in Gt)
            antis = [''.join(str(x) for x in el[0]) for el in Gt if el[1]]
            rows.append((pid, npoints * len(orb), len(G), len(Gt), labfix, t, len(orb), antis))
    return rows


def group_name(stab):
    hol = [el for el in stab if not el[1]]
    n = len(hol)
    orders = []
    for g, *_ in hol:
        k, h = 1, g
        while h != tuple(LABELS):
            h = tuple(g[i] for i in h)
            k += 1
        orders.append(k)
    return n, max(orders)


def main():
    print("Folder 148, pp. 30-35 -- special structures on five points\n")
    total, orbits = 0, 0

    # level 2
    pts = level2_points()
    classes = {}
    for p in pts:
        stab = stabiliser([dict(enumerate(p))])
        n, mo = group_name(stab)
        classes.setdefault((n, mo), []).append((p, stab))
    print("Level 2 (points of M_{0,5} with stabiliser of order > 2):")
    names = {(10, 5): 'D_5 (pentagonal, I_10)', (6, 3): 'S_3 = D_3 (bitetrahedral, I_6)', (4, 4): 'Z/4 (square pyramid, I_4)'}
    for (n, mo), lst in sorted(classes.items(), key=lambda x: -x[0][0]):
        # one S_5-orbit per class?  orbit size is 120 / |G|
        anti = len([el for el in lst[0][1] if el[1]])
        print(f"  |G| = {n:2d}, max order {mo}: {len(lst):3d} labelled points = 120/{n}; "
              f"|G~| = {n + anti}  -> {names.get((n, mo), '?')}")
        total += len(lst)
        orbits += 1
        assert len(lst) == 120 // n
    print(f"  level 2 total: {sum(len(l) for l in classes.values())}\n")

    # level 1
    pts1 = level1_points()
    by_type = {}
    for ab, lam, curve in pts1:
        stab = stabiliser(curve)
        n, mo = group_name(stab)
        by_type.setdefault(n, []).append((ab, lam, curve, stab))
    print("Level 1 (boundary divisor D_ab, special point of the four-holed piece, real normal ray):")
    lvl1 = 0
    for mo, lst in sorted(by_type.items()):
        kind = {4: 'harmonic (square)', 6: 'equianharmonic (tetrahedral)'}[mo]
        ab, lam, curve, stab = lst[0]
        rays = real_rays(stab, nodes_of(curve))
        print(f"  {kind}: {len(lst)} labelled points over the 10 circles "
              f"(|Stab| = {len([e for e in stab if not e[1]])}), {len(rays)} real rays at each")
        rows = orbit_types([(kind, curve, stab, rays, len(lst))])
        for pid, size, g, gt, labfix, t, norb, antis in rows:
            th = ', '.join(f"{x / math.pi:.3f}pi" for x in t)
            print(f"     orbit of {size:3d} = 120/{g}: |G| = {g}, |G~| = {gt}, "
                  f"a label-fixing real structure: {labfix}; ray {th} ({norb} rays per point); "
                  f"antiholomorphic symmetries as relabellings {antis}")
            total += size
            lvl1 += size
            orbits += 1
            assert size * g == 120
    print(f"  level 1 total: {lvl1}\n")

    # level 0
    pts0 = level0_points()
    print("Level 0 (pants decompositions, real pair of normal rays):")
    pid, curve = pts0[0]
    stab = stabiliser(curve)
    rays = real_rays(stab, nodes_of(curve))
    print(f"  {len(pts0)} decompositions, |Stab| = {len([e for e in stab if not e[1]])}, "
          f"{len(rays)} real ray pairs at each")
    rows = orbit_types([('level0', curve, stab, rays, len(pts0))])
    lvl0 = 0
    for pid, size, g, gt, labfix, t, norb, antis in rows:
        th = ', '.join(f"{x / math.pi:.3f}pi" for x in t)
        print(f"     orbit of {size:3d} = 120/{g}: |G| = {g}, |G~| = {gt}, "
              f"a label-fixing real structure: {labfix}; rays ({th}); antiholomorphic symmetries as relabellings {antis}")
        total += size
        lvl0 += size
        orbits += 1
        assert size * g == 120
    print(f"  level 0 total: {lvl0}\n")

    print(f"TOTAL: {total} structures in {orbits} S_5-orbits")
    print("(level 1 representative: circle {0, 1}, triangle 0 = 1, 1 = inf, node 0; "
          "level 0: ends {0, 1} and {3, 4}, middle point 2; a relabelling is written as the images of 0..4)")
    print("Page 30: 12 + 20 + 30 | 60 + 60 + 120 | 60 + 120 + 60 = 542 in 9 orbits")


if __name__ == '__main__':
    main()
