"""Combinatorial encodings (method 3), their checks, and a stable-graph enumerator.

  python3.12 comb.py check <file.json> [...]   recompute every encoding's derived numbers, compare them
                                               with the stored "derived" and with "expected"; exit 1 on a mismatch
  python3.12 comb.py enumerate <g> <n>         count (and with -v list) the stable graphs of type (g, n)
  import comb; comb.check(encoding)            what build.py calls

Schemas (field "schema"):

dessin/1   -- a bicoloured map (dessin d'enfant). Darts = edges, numbered 1..n.
             sigma0, sigma1: permutations given as lists of cycles (rotation of the
             darts around black / white vertices, counter-clockwise as seen on the page).
             Derived: black = #cycles(sigma0), white = #cycles(sigma1),
             faces = #cycles(sigma0 sigma1) (composition: apply sigma1 first),
             genus g from 2 - 2g = black + white - n + faces.
map/1      -- a map (one kind of vertex) by half-edges 1..2m: sigma = rotation at
             vertices (cycles), alpha = edge involution (pairs). Faces = cycles of
             sigma∘alpha. 2 - 2g = V - E + F.
polyhedron/1 -- a face lattice: "faces" is a list of vertex cycles (the boundary of each
             2-cell, vertex names as strings). Edges are derived; V - E + F computed.
             Optional "cells3" for solids (list of face indices).
stable-graph/1 -- a graph with genus labels and legs (Mumford–Deligne graph):
             vertices: {name: genus}, edges: [[u,v],...] (u=v is a loop),
             legs: {name: number of free half-edges}. Derived: type (g, nu) with
             g = b1 + sum genus, nu = #legs; stability 2g_v - 2 + n_v > 0 at each vertex;
             dimension 3g - 3 + nu - #edges of the stratum.
cellular/1 -- a cell decomposition of a closed surface with named edges (allows
             loops and multiple edges, which a vertex-cycle face list cannot):
             edges: {name: [u, v]}, faces: list of edge-name cycles (each face's boundary
             walk). Checked: consecutive edges of a face share a vertex, every edge is
             used exactly twice (closed surface); V - E + F and genus derived.
stable-graph-table/1 -- his tables of stable graphs: rows of {type: [g, n], his_number,
             drawn (his count, as text), graphs: [stable-graph/1 bodies], enumerated}.
             Checked: enumerated = the number of stable graphs of the type, and
             his_number = 3g - 3 + n where he writes one.
segment-config/1 -- points and intervals on a line, left to right: a list of
             {"pt": label, "kind": full|open|paren|bracket|isolated|cross} and
             {"seg": [a, b], "style": ...}.

Every encoding may carry "expected": numbers read on the page (e.g. his
« 6 sommets, 4 faces »), compared with the derived ones by check().
"""
from collections import Counter

def perm_from_cycles(cycles, n=None):
    p = {}
    for cyc in cycles:
        for i, a in enumerate(cyc):
            p[a] = cyc[(i + 1) % len(cyc)]
    if n:
        for a in range(1, n + 1):
            p.setdefault(a, a)
    return p

def cycles_of(p):
    seen, out = set(), []
    for a in sorted(p, key=str):
        if a in seen:
            continue
        cyc, b = [], a
        while b not in seen:
            seen.add(b); cyc.append(b); b = p[b]
        out.append(cyc)
    return out

def compose(p, q):  # p∘q : apply q first
    return {a: p[q[a]] for a in q}

def check(enc):
    s = enc['schema']
    res = {}
    if s == 'dessin/1':
        n = enc['n']
        s0, s1 = perm_from_cycles(enc['sigma0'], n), perm_from_cycles(enc['sigma1'], n)
        sinf = compose(s0, s1)
        b, w, F = len(cycles_of(s0)), len(cycles_of(s1)), len(cycles_of(sinf))
        chi = b + w - n + F
        res = dict(darts=n, black=b, white=w, faces=F, face_degrees=sorted(len(c) for c in cycles_of(sinf)),
                   euler=chi, genus=(2 - chi) / 2, connected=connected(n, [s0, s1]),
                   passport=[sorted(len(c) for c in cycles_of(s0)), sorted(len(c) for c in cycles_of(s1)), sorted(len(c) for c in cycles_of(sinf))])
    elif s == 'map/1':
        n = 2 * len(enc['alpha'])
        sg = perm_from_cycles(enc['sigma'], n); al = perm_from_cycles(enc['alpha'], n)
        V, E, F = len(cycles_of(sg)), n // 2, len(cycles_of(compose(sg, al)))
        res = dict(vertices=V, edges=E, faces=F, euler=V - E + F, genus=(2 - (V - E + F)) / 2,
                   vertex_degrees=sorted(len(c) for c in cycles_of(sg)), face_degrees=sorted(len(c) for c in cycles_of(compose(sg, al))),
                   connected=connected(n, [sg, al]))
    elif s == 'polyhedron/1':
        faces = enc['faces']
        edges = set()
        for f in faces:
            for i in range(len(f)):
                edges.add(frozenset((f[i], f[(i + 1) % len(f)])))
        verts = set(v for f in faces for v in f) | set(enc.get('isolated_vertices', []))
        extra = [frozenset(e) for e in enc.get('extra_edges', [])]
        edges |= set(extra)
        verts |= set(v for e in extra for v in e)
        V, E, F = len(verts), len(edges), len(faces)
        cnt = Counter(e for f in faces for e in (frozenset((f[i], f[(i + 1) % len(f)])) for i in range(len(f))))
        res = dict(vertices=V, edges=E, faces=F, euler=V - E + F, face_sizes=sorted(len(f) for f in faces),
                   closed_surface=all(c == 2 for c in cnt.values()) and not extra)
    elif s == 'stable-graph/1':
        vg = enc['vertices']; legs = enc.get('legs', {}); edges = enc['edges']
        val = Counter()
        for u, v in edges:
            val[u] += 1; val[v] += 1
        for v, k in legs.items():
            val[v] += k
        V, E = len(vg), len(edges)
        comps = components(list(vg), edges)
        b1 = E - V + comps
        symbolic = [str(x) for x in vg.values() if not isinstance(x, int)]
        if symbolic:
            g = '%d + %s' % (b1 + sum(x for x in vg.values() if isinstance(x, int)), ' + '.join(symbolic))
            nu = sum(legs.values())
            res = dict(vertices=V, edges=E, type=[g, nu], b1=b1, connected=comps == 1,
                       stable=all(val[v] >= 3 for v in vg), stable_note='genera symbolic: stability checked as valence >= 3, which holds whatever the genera',
                       valences={v: val[v] for v in vg})
            exp = enc.get('expected', {})
            res['expected_ok'] = all(res.get(k) == v for k, v in exp.items()) if exp else None
            return res
        g = b1 + sum(vg.values())
        nu = sum(legs.values())
        res = dict(vertices=V, edges=E, type=[g, nu], b1=b1, connected=comps == 1,
                   stable=all(2 * vg[v] - 2 + val[v] > 0 for v in vg), stratum_dim=3 * g - 3 + nu - E,
                   valences={v: val[v] for v in vg})
    elif s == 'cellular/1':
        edges = enc['edges']
        verts = set(v for e in edges.values() for v in e) | set(enc.get('isolated_vertices', []))
        cnt = Counter(e for f in enc['faces'] for e in f)
        walk_ok = True
        for f in enc['faces']:
            for i in range(len(f)):
                if not set(edges[f[i]]) & set(edges[f[(i + 1) % len(f)]]):
                    walk_ok = False
        V, E, F = len(verts), len(edges), len(enc['faces'])
        res = dict(vertices=V, edges=E, faces=F, euler=V - E + F, genus=(2 - (V - E + F)) / 2,
                   closed_surface=all(cnt[e] == 2 for e in edges), boundary_walks_ok=walk_ok,
                   face_sizes=sorted(len(f) for f in enc['faces']))
    elif s == 'segment-config/1':
        kinds = {'full', 'open', 'paren', 'bracket', 'isolated', 'cross'}
        res = dict(points=sum(1 for x in enc['items'] if 'pt' in x), segments=sum(1 for x in enc['items'] if 'seg' in x),
                   kinds_ok=all(x.get('kind', 'full') in kinds for x in enc['items'] if 'pt' in x))
    elif s == 'stable-graph-table/1':
        rows = []
        for r in enc['rows']:
            g, n = r['type']
            cnt = len(enumerate_stable(g, n)) if 3 * g - 3 + n <= 4 else None  # larger types: too slow to enumerate here
            rows.append(dict(type=[g, n], enumerated=cnt, enumerated_ok=None if cnt is None or 'enumerated' not in r else cnt == r['enumerated'],
                             his_number_ok=None if r.get('his_number') is None else r['his_number'] == 3 * g - 3 + n,
                             graphs_stable=all(check(dict(schema='stable-graph/1', **gr))['stable'] for gr in r.get('graphs', []))))
        res = dict(rows=rows, all_ok=all(x['enumerated_ok'] is not False and x['his_number_ok'] is not False and x['graphs_stable'] for x in rows))
    exp = enc.get('expected', {})
    res['expected_ok'] = all(res.get(k) == v for k, v in exp.items()) if exp else None
    if exp:
        res['expected_mismatch'] = {k: [v, res.get(k)] for k, v in exp.items() if res.get(k) != v}
    return res

def connected(n, perms):
    seen, stack = {1}, [1]
    while stack:
        a = stack.pop()
        for p in perms:
            for b in (p[a],):
                if b not in seen:
                    seen.add(b); stack.append(b)
    return len(seen) == len(perms[0])

def components(vs, edges):
    parent = {v: v for v in vs}
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for u, v in edges:
        parent[find(u)] = find(v)
    return len({find(v) for v in vs})


def enumerate_stable(g, n):
    """All stable graphs of type (g, n) with unlabelled legs, up to isomorphism.
    Returned as dicts in the stable-graph/1 schema (vertices v0, v1, ...)."""
    from itertools import product, permutations, combinations_with_replacement
    out, seen = [], set()
    vmax = max(1, 2 * g - 2 + n)
    for V in range(1, vmax + 1):
        pairs = [(i, j) for i in range(V) for j in range(i, V)]
        for E in range(V - 1, 3 * g - 3 + n + 1):
            h1 = E - V + 1
            if h1 > g:
                continue
            for edges in combinations_with_replacement(pairs, E):
                if components(list(range(V)), list(edges)) != 1:
                    continue
                for gens in product(range(g - h1 + 1), repeat=V):
                    if sum(gens) != g - h1:
                        continue
                    for legs in product(range(n + 1), repeat=V):
                        if sum(legs) != n:
                            continue
                        val = [legs[i] for i in range(V)]
                        for a, b in edges:
                            val[a] += 1; val[b] += 1
                        if any(2 * gens[i] - 2 + val[i] <= 0 for i in range(V)):
                            continue
                        key = None
                        for p in permutations(range(V)):
                            k = (tuple(gens[p.index(i)] for i in range(V)), tuple(legs[p.index(i)] for i in range(V)),
                                 tuple(sorted(tuple(sorted((p[a], p[b]))) for a, b in edges)))
                            k = (tuple(gens[i] for i in p), tuple(legs[i] for i in p),
                                 tuple(sorted(tuple(sorted((p.index(a), p.index(b)))) for a, b in edges)))
                            key = k if key is None or k < key else key
                        if key in seen:
                            continue
                        seen.add(key)
                        gs, ls, es = key
                        out.append(dict(schema='stable-graph/1', vertices={f'v{i}': gs[i] for i in range(V)},
                                        edges=[[f'v{a}', f'v{b}'] for a, b in es], legs={f'v{i}': ls[i] for i in range(V) if ls[i]}))
    out.sort(key=lambda d: (len(d['edges']), len(d['vertices'])))
    return out



def _main():
    import sys, json, argparse
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    c = sub.add_parser('check'); c.add_argument('files', nargs='+')
    e = sub.add_parser('enumerate'); e.add_argument('g', type=int); e.add_argument('n', type=int); e.add_argument('-v', action='store_true')
    a = ap.parse_args()
    if a.cmd == 'enumerate':
        gs = enumerate_stable(a.g, a.n)
        print(f'type ({a.g},{a.n}): {len(gs)} stable graphs')
        if a.v:
            for x in gs: print(' ', json.dumps(x))
        return 0
    bad = 0
    for f in a.files:
        d = json.load(open(f, encoding='utf8'))
        for enc in d.get('encodings', [d]):
            body = {k: v for k, v in enc.items() if k != 'derived'}
            res = check(body)
            stored = enc.get('derived')
            rj = json.loads(json.dumps(res))
            same = stored is None or all(rj.get(k) == v for k, v in stored.items())  # fields added since are not a mismatch
            ok = res.get('expected_ok') is not False and res.get('all_ok', True) is not False and same
            bad += not ok
            short = {k: v for k, v in res.items() if k in ('black', 'white', 'faces', 'genus', 'passport', 'vertices', 'edges', 'euler',
                                                         'closed_surface', 'boundary_walks_ok', 'type', 'stable', 'stratum_dim', 'points',
                                                         'segments', 'all_ok', 'expected_ok', 'expected_mismatch') and v != {}}
            print(f"{'ok ' if ok else 'BAD'} {f} [{enc['schema']}] {enc.get('name', '')}: {json.dumps(short, ensure_ascii=False)}"
                  + ('' if same else '  (differs from the stored derived block)'))
    return 1 if bad else 0


if __name__ == '__main__':
    raise SystemExit(_main())
