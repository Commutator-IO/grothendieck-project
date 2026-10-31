#!/usr/bin/env python3
"""Face-width test of the three-pencil case of Problem 14 (folder 80,
pp. 39-54; MathOverflow question 516410).

The route tested: if the skeleton graph G of a bigon-free arrangement is
3-connected and its embedding in RP^2 has large enough face-width, a
uniqueness-of-embedding theorem would make every automorphism of G (labelled
or not) map facial walks to facial walks, hence come from a homeomorphism.

For every three-pencil bigon-free class of out/all_n.txt (the 132 classes of
three_pencil.py for n <= 9; run run.py first) this script computes:

  * the graph G: vertices = points of the arrangement, edges = segments of
    the pseudolines between consecutive points.  It is checked to be a
    simple graph (no loop, no parallel edge): a pseudoline with k >= 3 points
    gives k distinct edges, and two points lie on at most one pseudoline;
  * kappa(G), the vertex connectivity (Menger, unit-capacity max-flow on the
    vertex-split digraph, over all non-adjacent pairs);
  * fw, the face-width of the embedding in RP^2, i.e. the least number of
    points in which a non-contractible closed curve meets G.  Method: the
    double cover of the arrangement is the cell decomposition of the sphere
    given by the covectors of the oriented matroid (vertices = cocircuits,
    edges = covectors with one zero, faces = topes; all covectors are got by
    composing cocircuits).  Its radial graph R~ joins a cocircuit X to a tope
    T when X <= T.  A non-contractible closed curve of RP^2 meeting G only in
    vertices lifts to a path from a lift x of a vertex to its antipode -x,
    and conversely; so fw = min over cocircuits X of dist_R~(X, -X) / 2
    (Mohar 1997, sect. 3: fw = ew(radial graph) / 2, where ew is the least
    length of a non-contractible cycle; a shortest non-contractible closed
    walk is a cycle);
  * tau, the least number of points meeting every pseudoline.  Any
    non-contractible closed curve meets every pseudoline (two
    non-contractible curves of RP^2 have intersection number 1 mod 2), so
    fw >= tau: an independent lower bound;
  * polyhedrality as in Mohar 1997, Prop. 3.9 (d): every facial walk is a
    cycle and two faces meet in nothing, one vertex or one edge.  By that
    proposition this holds iff kappa >= 3 and fw >= 3: an independent check
    of the two computations above;
  * whether a non-contractible curve meets G in exactly the three corners of
    a triangle without a fourth pseudoline;
  * the automorphism groups: Aut(G) of the bare graph, the label-respecting
    ones (permuting the pseudolines; compared with three_pencil.py), and the
    map automorphisms (those carrying facial cycles to facial cycles, i.e.
    induced by homeomorphisms of RP^2).  If Aut(G) is larger than the map
    group, G has an embedding in RP^2 not equivalent to the given one with
    the same face-width, and no uniqueness theorem can apply to it.

Usage: python3 three_pencil_facewidth.py [NMAX]   (default 9)
"""
import os
import sys
from collections import Counter, defaultdict, deque
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from three_pencil import Arr, chi, parse, skeleton_isos  # noqa: E402


# ---------------------------------------------------------------- graph

def skeleton_graph(A):
    """vertices 0..V-1 (points), adjacency sets, edge -> line"""
    pts = sorted(A.points, key=lambda p: sorted(p))
    idx = {p: k for k, p in enumerate(pts)}
    adj = [set() for _ in pts]
    eline = {}
    for i in range(A.n):
        cyc = A.cycle[i]
        k = len(cyc)
        assert k >= 3                                   # bigon-free
        for t in range(k):
            x, y = idx[cyc[t]], idx[cyc[(t + 1) % k]]
            assert x != y                               # no loop
            e = frozenset((x, y))
            assert e not in eline                       # no parallel edge
            eline[e] = i
            adj[x].add(y)
            adj[y].add(x)
    return pts, idx, adj, eline


def local_connectivity(adj, s, t):
    """max number of internally disjoint s-t paths (s, t non-adjacent)"""
    V = len(adj)
    # vertex v -> v_in = 2v, v_out = 2v+1; capacity 1 on v_in -> v_out
    cap = defaultdict(int)
    nbr = defaultdict(set)

    def arc(a, b, c):
        cap[a, b] += c
        nbr[a].add(b)
        nbr[b].add(a)
    for v in range(V):
        arc(2 * v, 2 * v + 1, 1 if v not in (s, t) else V)
        for w in adj[v]:
            arc(2 * v + 1, 2 * w, V)
    src, snk = 2 * s + 1, 2 * t
    flow = 0
    while True:
        prev = {src: None}
        q = deque([src])
        while q and snk not in prev:
            a = q.popleft()
            for b in nbr[a]:
                if b not in prev and cap[a, b] > 0:
                    prev[b] = a
                    q.append(b)
        if snk not in prev:
            return flow
        b = snk
        while prev[b] is not None:
            a = prev[b]
            cap[a, b] -= 1
            cap[b, a] += 1
            b = a
        flow += 1


def connectivity(adj):
    V = len(adj)
    best = V - 1
    for s, t in combinations(range(V), 2):
        if t not in adj[s]:
            best = min(best, local_connectivity(adj, s, t))
    return best


# ---------------------------------------------------- sphere cell complex

def compose(X, Y):
    return tuple(x if x else y for x, y in zip(X, Y))


def le(X, T):
    return all(x == 0 or x == t for x, t in zip(X, T))


def neg(X):
    return tuple(-x for x in X)


def sphere_complex(A, pts):
    n = A.n
    coc = {}
    for p in pts:
        a, b = sorted(p)[:2]
        X = tuple(chi(A.sign, a, b, e) for e in range(n))
        assert {e for e in range(n) if X[e] == 0} == set(p)
        coc[X] = p
        coc[neg(X)] = p
    cocs = list(coc)
    S = set(cocs)
    frontier = set(cocs)
    while frontier:
        new = set()
        for X in frontier:
            for C in cocs:
                Z = compose(X, C)
                if Z not in S:
                    new.add(Z)
        S |= new
        frontier = new
    topes = [T for T in S if 0 not in T]
    edges = [Y for Y in S if sum(1 for y in Y if y == 0) == 1]
    return coc, topes, edges


def proj(X):
    """representative of {X, -X}: first non-zero entry positive"""
    for x in X:
        if x:
            return X if x > 0 else neg(X)
    raise ValueError


# ----------------------------------------------------------- face-width

def face_width(coc, topes):
    cocs = list(coc)
    # radial graph on the sphere: nodes ('v', X) and ('f', T)
    R = defaultdict(list)
    for X in cocs:
        for T in topes:
            if le(X, T):
                R['v', X].append(('f', T))
                R['f', T].append(('v', X))
    best, witness = None, None
    for X in cocs:
        start, goal = ('v', X), ('v', neg(X))
        prev = {start: None}
        q = deque([start])
        while q:
            a = q.popleft()
            if a == goal:
                break
            for b in R[a]:
                if b not in prev:
                    prev[b] = a
                    q.append(b)
        path = [goal]
        while prev[path[-1]] is not None:
            path.append(prev[path[-1]])
        d = len(path) - 1
        if best is None or d < best:
            best = d
            witness = [coc[node[1]] for node in path[:-1] if node[0] == 'v']
    assert best % 2 == 0
    return best // 2, witness, R


def corner_curve(A, coc, R):
    """three-pencil triangles (a, b, c) whose corners u, v, w alone are met
    by some non-contractible closed curve"""
    found = []
    for a, b, c in combinations(range(A.n), 3):
        u, v, w = A.pt[a, b], A.pt[b, c], A.pt[a, c]
        if len({u, v, w}) < 3:
            continue
        if not all(d in u or d in v or d in w for d in range(A.n)):
            continue
        allowed = {X for X, p in coc.items() if p in (u, v, w)}
        X0 = next(X for X in allowed if coc[X] == u)
        start, goal = ('v', X0), ('v', neg(X0))
        seen = {start}
        q = deque([start])
        while q:
            node = q.popleft()
            for nb in R[node]:
                if nb[0] == 'v' and nb[1] not in allowed:
                    continue
                if nb not in seen:
                    seen.add(nb)
                    q.append(nb)
        found.append(((a, b, c), goal in seen))
    return found


def parity_check(A, coc, topes, fw, witness):
    """Independent check of fw <= 3 / fw >= 4 by crossing parity.  A closed
    curve through the points p_1..p_k (k = 2, 3), running inside a face F_i
    from p_i to p_{i+1}, is non-contractible iff it crosses a pseudoline l
    an odd number of times; it can cross l only at a p_i on l, and does so
    iff, at a lift x of p_i, the lifts of F_{i-1} and F_i through x have
    opposite signs on l.  The parity must be the same for every l.  Returns
    the least k <= 3 for which such a curve is non-contractible, or None."""
    lift = {}                                   # point -> one cocircuit
    for X, p in coc.items():
        lift.setdefault(p, X)
    faces_at = defaultdict(dict)                # point -> {face: tope at lift}
    for p, X in lift.items():
        for T in topes:
            if le(X, T):
                faces_at[p][proj(T)] = T
    pts = list(lift)
    n = A.n

    def parities(cyc, fs):
        k = len(cyc)
        par = [0] * n
        for i in range(k):
            p = cyc[i]
            Tin, Tout = faces_at[p][fs[i - 1]], faces_at[p][fs[i]]
            for l in p:
                if Tin[l] != Tout[l]:
                    par[l] ^= 1
        return par

    for k in (2, 3):
        for cyc in combinations(pts, k):
            choices = []
            for i in range(k):
                common = set(faces_at[cyc[i]]) & set(faces_at[cyc[(i + 1) % k]])
                choices.append(sorted(common))
            stack = [[]]
            for ch in choices:
                stack = [s + [f] for s in stack for f in ch]
            for fs in stack:
                par = parities(cyc, fs)
                assert len(set(par)) == 1, (cyc, fs, par)
                if par[0]:
                    return k
    return None


def point_cover(A):
    pts = list(A.points)
    for k in range(1, A.n + 1):
        for S in combinations(pts, k):
            if set().union(*S) == set(range(A.n)):
                return k


# ------------------------------------------------------- polyhedrality

def faces_of(topes, edges, coc, idx):
    """faces of RP^2: (vertex set, edge set) of each pair {T, -T}"""
    out = {}
    for T in topes:
        P = proj(T)
        if P in out:
            continue
        vs = [idx[coc[X]] for X in coc if le(X, T)]
        assert len(vs) == len(set(vs))          # facial walk is a cycle
        es = set()
        for Y in edges:
            if le(Y, T):
                ends = [idx[coc[X]] for X in coc if le(X, Y)]
                assert len(ends) == 2
                es.add(frozenset(ends))
        assert len(es) == len(vs)
        out[P] = (frozenset(vs), frozenset(es))
    return list(out.values())


def polyhedral(faces):
    for (V1, E1), (V2, E2) in combinations(faces, 2):
        IV, IE = V1 & V2, E1 & E2
        if len(IE) == 0 and len(IV) <= 1:
            continue
        if len(IE) == 1 and IV == next(iter(IE)):
            continue
        return False
    return True


# -------------------------------------------------------- automorphisms

def graph_automorphisms(adj):
    """all vertex permutations preserving adjacency (backtracking)"""
    V = len(adj)
    deg = [len(a) for a in adj]
    # order: BFS from a vertex of the rarest degree, so that each new vertex
    # has an already mapped neighbour (the graph is connected)
    order, seen = [], set()
    rare = Counter(deg)
    r0 = min(range(V), key=lambda v: (rare[deg[v]], -deg[v]))
    q = deque([r0])
    seen.add(r0)
    while q:
        v = q.popleft()
        order.append(v)
        for w in sorted(adj[v]):
            if w not in seen:
                seen.add(w)
                q.append(w)
    assert len(order) == V
    res = []
    img = {}
    used = set()

    def rec(k):
        if k == V:
            res.append(dict(img))
            return
        v = order[k]
        mapped_nb = [w for w in adj[v] if w in img]
        if mapped_nb:
            cands = set(adj[img[mapped_nb[0]]])
        else:
            cands = set(range(V))
        for x in cands:
            if x in used or deg[x] != deg[v]:
                continue
            if all((img[w] in adj[x]) == (w in adj[v]) for w in img):
                img[v] = x
                used.add(x)
                rec(k + 1)
                del img[v]
                used.discard(x)
    rec(0)
    return res


def classify_auts(auts, eline, faces):
    face_set = {E for _, E in faces}
    lines = defaultdict(set)
    for e, i in eline.items():
        lines[i].add(e)
    line_sets = {frozenset(s) for s in lines.values()}
    n_lab = n_map = n_lab_not_map = 0
    for s in auts:
        def im(E):
            return frozenset(frozenset(s[x] for x in e) for e in E)
        lab = all(im(L) in line_sets for L in line_sets)
        mp = all(im(E) in face_set for E in face_set)
        n_lab += lab
        n_map += mp
        n_lab_not_map += lab and not mp
    return n_lab, n_map, n_lab_not_map


# ----------------------------------------------------------------- main

def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    rows = []
    for n in range(4, nmax + 1):
        path = os.path.join(HERE, 'out', f'all_{n}.txt')
        with open(path) as fp:
            lines = fp.readlines()
        for lineno, line in enumerate(lines):
            flats, sign = parse(line, n)
            A = Arr(n, flats, sign)
            if not A.three_pencil():
                continue
            pts, idx, adj, eline = skeleton_graph(A)
            kappa = connectivity(adj)
            coc, topes, edges = sphere_complex(A, pts)
            V, E, F = len(pts), len(eline), len(topes) // 2
            assert len(coc) == 2 * V and len(edges) == 2 * E
            assert V - E + F == 1                       # Euler, RP^2
            fw, witness, R = face_width(coc, topes)
            tau = point_cover(A)
            faces = faces_of(topes, edges, coc, idx)
            poly = polyhedral(faces)
            assert poly == (kappa >= 3 and fw >= 3)     # Mohar, Prop. 3.9
            assert set().union(*witness) == set(range(n))
            assert fw >= tau
            k = parity_check(A, coc, topes, fw, witness)
            assert k == (fw if fw <= 3 else None), (n, lineno, fw, k)
            corners = corner_curve(A, coc, R)
            auts = graph_automorphisms(adj)
            n_lab, n_map, bad = classify_auts(auts, eline, faces)
            assert n_lab == len(skeleton_isos(A, A))    # three_pencil.py
            rows.append(dict(
                n=n, line=lineno + 1, V=V, E=E, F=F,
                mult=sorted((len(p) for p in A.points if len(p) > 2),
                            reverse=True),
                mindeg=min(len(a) for a in adj), kappa=kappa, fw=fw,
                tau=tau, poly=poly,
                witness=[''.join('%x' % i for i in sorted(p)) for p in witness],
                ncorner=len(corners),
                corner_ok=sum(ok for _, ok in corners),
                aut=len(auts), lab=n_lab, map=n_map, lab_not_map=bad))
    return rows


def report(rows, nmax):
    out = []
    w = out.append
    w('Three-pencil bigon-free classes: connectivity and face-width in RP^2')
    w('(python3 three_pencil_facewidth.py %d)' % nmax)
    w('')
    w('Per class: n, line of out/all_n.txt, V E F, multiple points (sizes),')
    w('min degree, kappa, fw, tau (point cover), polyhedral (Mohar 3.9 d),')
    w('a curve realising fw (points met, as sets of pseudolines),')
    w('three-pencil triangles / those whose corners alone carry a')
    w('non-contractible curve, |Aut G|, label-respecting, map automorphisms.')
    w('')
    for r in rows:
        w('n=%(n)d #%(line)-6d V=%(V)-2d E=%(E)-2d F=%(F)-2d mult=%(mult)s '
          'mindeg=%(mindeg)d kappa=%(kappa)d fw=%(fw)d tau=%(tau)d '
          'poly=%(poly)s witness=%(witness)s corners=%(corner_ok)d/%(ncorner)d '
          'aut=%(aut)d lab=%(lab)d map=%(map)d' % r)
    w('')
    w('Summary by n')
    w('  n  classes  kappa (count)        fw (count)   tau  polyhedral  '
      'corner-curve  Aut(G) > map group')
    by = defaultdict(list)
    for r in rows:
        by[r['n']].append(r)
    for n in sorted(by):
        R = by[n]
        k = Counter(r['kappa'] for r in R)
        f = Counter(r['fw'] for r in R)
        t = Counter(r['tau'] for r in R)
        w('  %d  %7d  %-20s %-12s %-5s %10d  %12d  %d' % (
            n, len(R), dict(sorted(k.items())), dict(sorted(f.items())),
            dict(sorted(t.items())), sum(r['poly'] for r in R),
            sum(r['corner_ok'] > 0 for r in R),
            sum(r['aut'] > r['map'] for r in R)))
    w('  all %5d  %-20s %-12s' % (
        len(rows), dict(sorted(Counter(r['kappa'] for r in rows).items())),
        dict(sorted(Counter(r['fw'] for r in rows).items()))))
    w('')
    w('label-respecting automorphisms not induced by a homeomorphism: %d'
      % sum(r['lab_not_map'] for r in rows))
    w('classes with a graph automorphism not induced by a homeomorphism: '
      '%d of %d' % (sum(r['aut'] > r['map'] for r in rows), len(rows)))
    return '\n'.join(out) + '\n'


if __name__ == '__main__':
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    rows = main()
    text = report(rows, nmax)
    print(text, end='')
    with open(os.path.join(HERE, 'three_pencil_facewidth_results.txt'), 'w') as fp:
        fp.write(text)
