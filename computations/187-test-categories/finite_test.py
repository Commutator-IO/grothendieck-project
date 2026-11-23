#!/usr/bin/env python3
"""Lawvere-object tests for small finite categories (issue #187).

For a small category A, Grothendieck's criterion (Cisinski, Astérisque 308, Th. 4.1.19;
Maltsiniotis, La théorie de l'homotopie de Grothendieck, Th. 6.6) says: A is a local test
category iff its Lawvere object L (the presheaf of sieves, i_A^*(Δ1)) is locally aspherical,
i.e. iff the category of elements A/(a × L) is aspherical for every object a. A weak test
category needs A/L aspherical (Def. 4.1.8 with C = Δ1), and a test category needs A aspherical.

This script computes, for a finite category A, the integral homology in degrees 0..DEG of the
nerves of A, A/L and every A/(a × L), with coefficients Q (rank mod a large prime) and F_2.
A nerve is not aspherical as soon as H_0 has rank != 1 or some H_i (0 < i <= DEG) is non-zero;
homology that vanishes up to DEG proves nothing. The chains are the normalised ones: strings of
non-identity arrows (finite in each degree, though a category with a non-identity
endomorphism has non-degenerate simplices in every degree).

    python3 finite_test.py            # monoids of order <= 4 and posets of size <= 4
    python3 finite_test.py 5          # monoids of order <= 5 (from docs/bridges/atlas)
"""
import itertools
import json
import os
import sys

P = 1_000_003
DEG = 2


class Cat:
    """A finite category: arrows 0..n-1, src, tgt, comp[g][f] = g∘f (or None), ids[obj]."""

    def __init__(self, objs, src, tgt, comp, ids):
        self.objs, self.src, self.tgt, self.comp, self.ids = objs, src, tgt, comp, ids
        self.into = {c: [f for f in range(len(src)) if tgt[f] == c] for c in objs}


def monoid_cat(t):
    n = len(t)
    return Cat([0], [0] * n, [0] * n, [[t[g][f] for f in range(n)] for g in range(n)], {0: 0})


def poset_cat(n, le):
    arrows = [(x, y) for x in range(n) for y in range(n) if le(x, y)]
    idx = {a: i for i, a in enumerate(arrows)}
    src = [a[0] for a in arrows]
    tgt = [a[1] for a in arrows]
    comp = [[idx[(f[0], g[1])] if f[1] == g[0] else None for f in arrows] for g in arrows]
    return Cat(list(range(n)), src, tgt, comp, {x: idx[(x, x)] for x in range(n)})


def sieves(A, c):
    """All sieves on c: sets of arrows into c closed under precomposition."""
    into = A.into[c]
    out = []
    for k in range(len(into) + 1):
        for S in itertools.combinations(into, k):
            S = frozenset(S)
            if all(A.comp[f][g] in S for f in S for g in A.into[A.src[f]]):
                out.append(S)
    return out


def pullback(A, f, S):
    """f^*S = {g : f∘g ∈ S}, a sieve on src f."""
    return frozenset(g for g in A.into[A.src[f]] if A.comp[f][g] in S)


def elements(A, F, act):
    """Category of elements of a presheaf: F[c] a list of elements, act(f, y) = F(f)(y).
    Returns (objects, arrows) with arrows (source, target, f) for non-identity arrows only,
    and a composition function on arrows."""
    objs = [(c, x) for c in A.objs for x in F[c]]
    index = {o: i for i, o in enumerate(objs)}
    arrows = []
    for d in A.objs:
        for y in F[d]:
            for f in A.into[d]:
                x = act(f, y)
                s, t = index[(A.src[f], x)], index[(d, y)]
                if not (f == A.ids[d] and s == t):
                    arrows.append((s, t, f))
    return objs, arrows


def homology(A, objs, arrows):
    """Ranks of H_0..H_DEG of the nerve of the category of elements, over F_P and F_2."""
    by_src = {}
    for i, (s, t, f) in enumerate(arrows):
        by_src.setdefault(s, []).append(i)

    def compose(i, j):  # arrow j after arrow i: s_i -> t_i = s_j -> t_j
        s, _, f = arrows[i]
        _, t, g = arrows[j]
        h = A.comp[g][f]
        return (s, t, h)

    key = {(s, t, f): i for i, (s, t, f) in enumerate(arrows)}
    chains = [[(o,) for o in range(len(objs))], [(i,) for i in range(len(arrows))]]
    for n in range(2, DEG + 2):
        nxt = []
        for ch in chains[-1]:
            for j in by_src.get(arrows[ch[-1]][1], []):
                nxt.append(ch + (j,))
        chains.append(nxt)

    def faces(n, ch):
        """Normalised boundary of an n-chain (n >= 1); n = 1: arrow index."""
        if n == 1:
            s, t, _ = arrows[ch[0]]
            return [((t,), 1), ((s,), -1)]
        out = []
        out.append((ch[1:], 1))  # d_0 drops the first arrow
        for k in range(1, n):  # inner faces compose arrows k-1 and k
            c = compose(ch[k - 1], ch[k])
            if c[0] == c[1] and c[2] == A.ids[A.src[c[2]]]:
                continue  # degenerate face
            out.append((ch[:k - 1] + (key[c],) + ch[k + 1:], (-1) ** k))
        out.append((ch[:-1], (-1) ** n))
        return out

    def rank(n, p):
        if n == 0:
            return 0
        rows = {c: i for i, c in enumerate(chains[n - 1])}
        mat = []
        for ch in chains[n]:
            v = {}
            for c, sgn in faces(n, ch):
                r = rows[c]
                v[r] = (v.get(r, 0) + sgn) % p
            v = {k: x for k, x in v.items() if x}
            if v:
                mat.append(v)
        return elim(mat, p)

    res = {}
    for p in (P, 2):
        rk = [rank(n, p) for n in range(DEG + 2)]
        res[p] = [len(chains[n]) - rk[n] - rk[n + 1] for n in range(DEG + 1)]
    return res


def elim(mat, p):
    pivots = {}
    r = 0
    for v in mat:
        v = dict(v)
        while v:
            k = min(v)
            if k in pivots:
                w = pivots[k]
                c = v[k] * pow(w[k], p - 2, p) % p
                for kk, x in w.items():
                    y = (v.get(kk, 0) - c * x) % p
                    if y:
                        v[kk] = y
                    else:
                        v.pop(kk, None)
            else:
                pivots[k] = v
                r += 1
                break
    return r


def aspherical_so_far(h):
    return all(h[p][0] == 1 and all(x == 0 for x in h[p][1:]) for p in h)


def lawvere(A):
    F = {c: sieves(A, c) for c in A.objs}
    return F, (lambda f, S: pullback(A, f, S))


def report(A):
    """(A aspherical so far, A/L aspherical so far, every A/(a×L) aspherical so far, details)."""
    one = {c: [()] for c in A.objs}
    hA = homology(A, *elements(A, one, lambda f, y: ()))
    L, actL = lawvere(A)
    hL = homology(A, *elements(A, L, actL))
    loc = []
    for a in A.objs:
        F = {c: [(g, S) for g in A.into[a] if A.src[g] == c for S in L[c]] for c in A.objs}
        act = lambda f, y: (A.comp[y[0]][f], pullback(A, f, y[1]))
        loc.append(homology(A, *elements(A, F, act)))
    return aspherical_so_far(hA), aspherical_so_far(hL), all(map(aspherical_so_far, loc)), (hA, hL, loc)


def ore(A):
    return all(any(A.comp[f][h] == A.comp[g][k] for h in A.into[A.src[f]] for k in A.into[A.src[g]]
                   if A.comp[f][h] is not None and A.comp[g][k] is not None)
               for c in A.objs for f in A.into[c] for g in A.into[c])


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    here = os.path.dirname(os.path.abspath(__file__))
    atlas = json.load(open(os.path.join(here, '..', '..', 'docs', 'bridges', 'atlas', 'monoids-6.json')))
    print(f'# Homology of nerves in degrees 0..{DEG}, over Q (mod {P}) and F_2.')
    print('# columns: order, table, Ore, A aspherical?, A/L aspherical?, all A/(a x L) aspherical?,'
          ' H_*(A/(a x L); Q)')
    tally = {}
    for n in range(1, N + 1):
        for m in atlas[str(n)]:
            A = monoid_cat(m['table'])
            o = ore(A)
            assert o == m['ore']
            a, l, loc, (hA, hL, hl) = report(A)
            tally.setdefault((o, a, l, loc), 0)
            tally[(o, a, l, loc)] += 1
            if not o:
                print(n, m['table'], 'Ore' if o else 'non-Ore', a, l, loc, hl[0][P])
    print('# tally (Ore, A asph., A/L asph., local) -> count:', tally)
    ptally = {}
    for n in range(1, min(N, 4) + 1):
        pairs = [(x, y) for x in range(n) for y in range(n) if x < y]
        seen = set()
        for bits in itertools.product([0, 1], repeat=len(pairs)):
            rel = {pr for pr, b in zip(pairs, bits) if b}
            if any((x, y) in rel and (y, z) in rel and (x, z) not in rel
                   for x in range(n) for y in range(n) for z in range(n)):
                continue
            A = poset_cat(n, lambda x, y: x == y or (x, y) in rel)
            r = report(A)[:3]
            ptally[(ore(A),) + r] = ptally.get((ore(A),) + r, 0) + 1
    print('# posets on {0..n-1}, n <= 4, labelled (Ore, A asph., A/L asph., local) -> count:', ptally)


if __name__ == '__main__':
    main()
