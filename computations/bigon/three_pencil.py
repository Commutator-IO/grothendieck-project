#!/usr/bin/env python3
"""Three-pencil test for Problem 14 of docs/problems/article.tex (folder 80,
pp. 39-54): is a bigon-free arrangement determined by its labelled skeleton?

Lean (lean/Grothendieck/Folder80Maps3.lean, full_of_fourth') proves it when
every triangle has a fourth pseudoline through none of its vertices.  A
triangle without one has three multiple vertices and every other pseudoline
through one of them, so the arrangement lies in the three pencils at the
vertices of a triangle; the complete quadrangle III_6 is the first case.
This script tests exactly those arrangements, among the bigon-free classes
that enum.c writes to out/all_n.txt (run run.py first).

The labelled skeleton of an arrangement: vertices are the points (the flats
of the intersection lattice), and each pseudoline i carries the cycle of its
points in their order along i.  An isomorphism of labelled skeleta is a
permutation s of the pseudolines that maps points to points and the cycle on
i to the cycle on s(i), up to rotation and reflection (two points lie on at
most one common pseudoline, so the edges are determined by their ends).
An arrangement isomorphism (homeomorphism, reflections allowed) is a
permutation s with chi(s a, s b, s c) = e * r_a r_b r_c * chi(a, b, c) for a
sign e and a reorientation r.  Every arrangement isomorphism induces a
skeleton isomorphism with the same s.  Two checks, for n <= NMAX:

  1. every skeleton automorphism comes from an arrangement automorphism;
  2. two different classes never have isomorphic labelled skeleta.

Usage: python3 three_pencil.py [NMAX]     (default 9; reads out/all_n.txt)
"""
import os
import sys
from itertools import combinations, product
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))


def parse(line, n):
    pts, chi = line.rstrip('\n').split('\t')[:2]
    flats = [frozenset(int(c, 16) for c in p) for p in pts.split(',') if p]
    sign = {}
    for t, c in zip(combinations(range(n), 3), chi):
        sign[t] = {'+': 1, '-': -1, '0': 0}[c]
    return flats, sign


def chi(sign, a, b, c):
    """chirotope value, alternating in its arguments"""
    if a == b or b == c or a == c:
        return 0
    s, t = 1, [a, b, c]
    for i in range(3):
        for j in range(2 - i):
            if t[j] > t[j + 1]:
                t[j], t[j + 1] = t[j + 1], t[j]
                s = -s
    return s * sign[tuple(t)]


class Arr:
    def __init__(self, n, flats, sign):
        self.n, self.sign = n, sign
        self.pt = {}                      # pair -> point (frozenset of lines)
        for f in flats:
            for i, j in combinations(sorted(f), 2):
                self.pt[i, j] = self.pt[j, i] = f
        for i, j in combinations(range(n), 2):
            if (i, j) not in self.pt:
                self.pt[i, j] = self.pt[j, i] = frozenset((i, j))
        self.points = set(self.pt.values())
        self.cycle = [self.order(i) for i in range(n)]
        for i in range(n):
            assert len(self.cycle[i]) == len({self.pt[i, j] for j in range(n) if j != i})

    def order(self, i):
        """the points on pseudoline i in their (cyclic) order along it, read
        from the rank-2 contraction at i: angles in [0, pi) from a start"""
        others = [j for j in range(self.n) if j != i]
        s0 = others[0]
        upper = [s0]                      # representatives with angle in [0, pi)
        for j in others[1:]:
            v = chi(self.sign, i, s0, j)
            if v > 0:
                upper.append(j)
            elif v < 0:
                pass                      # -j has angle in (0, pi): handled below
            # v == 0: j parallel to s0, same point as s0
        lower = [j for j in others[1:] if chi(self.sign, i, s0, j) < 0]
        # the elements -j for j in lower lie in (0, pi); compare x, y in the
        # open half-plane by chi(x, y) > 0, with -j contributing a sign
        items = [(j, 1) for j in upper if j != s0] + [(j, -1) for j in lower]
        import functools

        def cmp(x, y):
            v = x[1] * y[1] * chi(self.sign, i, x[0], y[0])
            return -1 if v > 0 else (1 if v < 0 else 0)
        items.sort(key=functools.cmp_to_key(cmp))
        seq = [self.pt[i, s0]]
        for j, _ in items:
            p = self.pt[i, j]
            if p != seq[-1] and p != seq[0]:
                seq.append(p)
        return seq

    def three_pencil(self):
        for a, b, c in combinations(range(self.n), 3):
            u, v, w = self.pt[a, b], self.pt[b, c], self.pt[a, c]
            if len({u, v, w}) < 3:
                continue
            if all(d in u or d in v or d in w for d in range(self.n)):
                return (a, b, c)
        return None


def dihedral_eq(seq, target):
    """seq equals target as a cycle up to rotation and reflection"""
    m = len(target)
    if len(seq) != m:
        return False
    if m == 0:
        return True
    try:
        k = target.index(seq[0])
    except ValueError:
        return False
    fwd = all(target[(k + t) % m] == seq[t] for t in range(m))
    bwd = all(target[(k - t) % m] == seq[t] for t in range(m))
    return fwd or bwd


def skeleton_isos(A, B):
    """all permutations s with s(points of A) = points of B and the cycle of
    A on i mapped onto the cycle of B on s(i); backtracking on the lines"""
    n = A.n
    res = []
    s = [None] * n
    used = [False] * n
    degA = [len(c) for c in A.cycle]
    degB = [len(c) for c in B.cycle]

    def ok_partial(k):
        # the point of i and k maps into the point of s(i) and s(k), with
        # the same number of lines
        for i in range(k):
            p, q = A.pt[i, k], B.pt[s[i], s[k]]
            if len(p) != len(q):
                return False
            if any(x <= k and s[x] not in q for x in p):
                return False
        return True

    def rec(k):
        if k == n:
            img = lambda p: frozenset(s[x] for x in p)
            if {img(p) for p in A.points} != B.points:
                return
            if all(dihedral_eq([img(p) for p in A.cycle[i]], B.cycle[s[i]])
                   for i in range(n)):
                res.append(tuple(s))
            return
        for j in range(n):
            if not used[j] and degA[k] == degB[j]:
                s[k], used[j] = j, True
                if ok_partial(k):
                    rec(k + 1)
                used[j] = False
        s[k] = None

    rec(0)
    return res


def realised(A, B, s):
    """is there a sign e and a reorientation r with
    chi_B(s a, s b, s c) = e r_a r_b r_c chi_A(a, b, c) for all triples?"""
    n = A.n
    trip = list(combinations(range(n), 3))
    for e in (1, -1):
        for bits in product((1, -1), repeat=n - 1):
            r = (1,) + bits
            if all(chi(B.sign, s[a], s[b], s[c]) ==
                   e * r[a] * r[b] * r[c] * chi(A.sign, a, b, c)
                   for a, b, c in trip):
                return True
    return False


def invariant(A):
    return (tuple(sorted(len(p) for p in A.points)),
            tuple(sorted(len(c) for c in A.cycle)))


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    total_bad = 0
    for n in range(4, nmax + 1):
        path = os.path.join(HERE, 'out', f'all_{n}.txt')
        arrs = []
        with open(path) as fp:
            for line in fp:
                flats, sign = parse(line, n)
                A = Arr(n, flats, sign)
                if A.three_pencil():
                    arrs.append(A)
        auts_bad = 0
        aut_sizes = []
        for A in arrs:
            isos = skeleton_isos(A, A)
            bad = [s for s in isos if not realised(A, A, s)]
            aut_sizes.append(len(isos))
            if bad:
                auts_bad += 1
                print(f'n={n}: skeleton automorphism not from the arrangement:',
                      bad[0], 'points', sorted(map(sorted, (p for p in A.points if len(p) > 2))))
        by_inv = defaultdict(list)
        for A in arrs:
            by_inv[invariant(A)].append(A)
        pairs_bad, pairs = 0, 0
        for group in by_inv.values():
            for A, B in combinations(group, 2):
                pairs += 1
                isos = skeleton_isos(A, B)
                if isos:
                    pairs_bad += 1
                    print(f'n={n}: two classes with isomorphic labelled skeleta:',
                          'realised' if realised(A, B, isos[0]) else 'NOT realised', isos[0])
        total_bad += auts_bad + pairs_bad
        print(f'n={n}: {len(arrs)} three-pencil bigon-free classes; '
              f'automorphism groups of the skeleta of orders {sorted(set(aut_sizes))}; '
              f'{auts_bad} with a skeleton automorphism not from the arrangement; '
              f'{pairs} pairs of classes with equal invariants compared, '
              f'{pairs_bad} with isomorphic skeleta', flush=True)
    print('counterexamples:', total_bad)


if __name__ == '__main__':
    main()
