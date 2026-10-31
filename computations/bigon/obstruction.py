#!/usr/bin/env python3
"""Sign obstruction for Problem 14 of docs/problems/article.tex (folder 80, pp. 39-54).

An isomorphism of labelled skeleta with permutation s gives, along each pseudoline i, the same
points in the same cyclic order up to reversal; so psi = chi' o s * chi (sign bits over F_2, on the
triples without a common point) is, at each i, a constant plus a cut of the complete multipartite
graph on the points of i, i.e. balanced on its 4-cycles. The argument of the paper says that such a
psi is a coboundary r_i + r_j + r_l, i.e. chi' o s is a reorientation of chi. This script computes,
for each bigon-free intersection lattice found by enum.c (out/all_n.txt, run run.py first),

    dim {psi balanced on the 4-cycles at every line}  -  dim {coboundaries},

which the argument says is 0. It depends only on the lattice (which pseudolines are concurrent).

Usage: python3 obstruction.py [NMAX]     (default 9; about three minutes)
"""
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def rank2(rows):
    """rank over F_2 of a list of bitmasks"""
    piv = {}
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h]
            else:
                piv[h] = v
                break
    return len(piv)


def obstruction(n, points):
    """points: the vertices, as tuples of pseudolines; every pair lies in exactly one"""
    pt = {}
    for k, p in enumerate(points):
        for a, b in itertools.combinations(sorted(p), 2):
            pt[(a, b)] = k
    assert len(pt) == n * (n - 1) // 2

    def P(a, b):
        return pt[(min(a, b), max(a, b))]

    bases = [t for t in itertools.combinations(range(n), 3) if P(t[0], t[1]) != P(t[0], t[2])]
    idx = {t: i for i, t in enumerate(bases)}

    def B(*x):
        return idx[tuple(sorted(x))]

    rows = []
    for i in range(n):
        oth = [j for j in range(n) if j != i]
        cls = {j: P(i, j) for j in oth}
        if len(set(cls.values())) < 3:
            return None  # a bigonal pseudoline
        for j, l, k, m in itertools.permutations(oth, 4):
            if j < k and l < m and len({cls[j], cls[l]}) == 2 and len({cls[l], cls[k]}) == 2 \
                    and len({cls[k], cls[m]}) == 2 and len({cls[m], cls[j]}) == 2:
                r = 0
                for a, b in ((j, l), (l, k), (k, m), (m, j)):
                    r ^= 1 << B(i, a, b)
                rows.append(r)
    cob = [sum(1 << k for t, k in idx.items() if a in t) for a in range(n)]
    return len(bases) - rank2(rows) - rank2(cob)


def lattices(n):
    seen = set()
    with open(os.path.join(HERE, 'out', f'all_{n}.txt')) as f:
        for line in f:
            key = line.split('\t')[0]
            if key in seen:
                continue
            seen.add(key)
            flats = [tuple(sorted(int(c, 16) for c in p)) for p in key.split(',') if p]
            covered = {pr for F in flats for pr in itertools.combinations(F, 2)}
            yield flats + [pr for pr in itertools.combinations(range(n), 2) if pr not in covered]


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    for n in range(4, nmax + 1):
        counts = {}
        for pts in lattices(n):
            o = obstruction(n, pts)
            counts[o] = counts.get(o, 0) + 1
        print(f'n = {n}: {sum(counts.values())} lattices, obstruction counts {counts}', flush=True)


if __name__ == '__main__':
    main()
