#!/usr/bin/env python3
"""Analyse the bigon-free arrangements written by enum.c.

For every bigon-free class (one line of out/all_n.txt or out/simple_n.txt:
its multiple points, then its canonical chirotope) this script checks, from
the intersection lattice alone (everything asked depends only on which
pseudolines are concurrent):

  * that it is indeed bigon-free (every pseudoline carries >= 3 vertices);
  * the dichotomy: it is II_4, or it contains a sub-arrangement II_5
    (5 pseudolines, no 3 concurrent), II'_{3,2} (5 pseudolines with exactly
    one concurrent triple) or III_6 (6 pseudolines with exactly 4
    concurrent triples, each pseudoline in two of them);
  * the numbering (Lemme of folder 80, p. 28): D_1..D_4 of type II_4, or
    D_1..D_6 of type III_6, and for every later i, D_i not bigonal in K_i
    = {D_1..D_i}, i.e. D_i meets D_1..D_{i-1} in >= 3 distinct points.
    Since this condition is monotone in the set already placed, a numbering
    from a given start exists iff the greedy closure of the start is
    everything;
  * the strong numbering: same start, and every K_i from the start on is
    bigon-free as a whole (searched over subsets).

Usage: python3 analyse.py OUTDIR MODE N [N ...]   (writes a summary to stdout)
"""
import sys
from itertools import combinations
from collections import Counter


def parse(line):
    pts = line.split('\t')[0]
    return [tuple(int(c, 16) for c in p) for p in pts.split(',') if p]


class Lattice:
    def __init__(self, n, flats):
        self.n = n
        # point id of the pair {i,j}: index of its multiple point, or the pair
        self.pt = {}
        for k, f in enumerate(flats):
            for i, j in combinations(f, 2):
                self.pt[(i, j)] = self.pt[(j, i)] = ('m', k)
        for i, j in combinations(range(n), 2):
            if (i, j) not in self.pt:
                self.pt[(i, j)] = self.pt[(j, i)] = ('p', i, j)
        self.conc = set()
        for f in flats:
            for t in combinations(f, 3):
                self.conc.add(t)

    def npts(self, i, S):
        """number of vertices of the sub-arrangement S on pseudoline i"""
        return len({self.pt[(i, j)] for j in S if j != i})

    def bigon_free(self, S):
        return all(self.npts(i, S) >= 3 for i in S)

    def nconc(self, S):
        return sum(1 for t in combinations(sorted(S), 3) if t in self.conc)

    def is_III6(self, S):
        ts = [t for t in combinations(sorted(S), 3) if t in self.conc]
        if len(ts) != 4:
            return False
        c = Counter(x for t in ts for x in t)
        return all(c[x] == 2 for x in S)

    def starts(self):
        n = self.n
        s4 = [S for S in combinations(range(n), 4) if self.nconc(S) == 0]
        s6 = [S for S in combinations(range(n), 6) if self.is_III6(S)]
        return s4, s6

    def dichotomy(self):
        n = self.n
        if n == 4 and not self.conc:
            return 'II_4'
        for S in combinations(range(n), 5):
            k = self.nconc(S)
            if k == 0:
                return 'II_5'
            if k == 1:
                return "II'_32"
        for S in combinations(range(n), 6):
            if self.is_III6(S):
                return 'III_6'
        return None

    def closure(self, S):
        S = set(S)
        grew = True
        while grew:
            grew = False
            for d in range(self.n):
                if d not in S and self.npts(d, S) >= 3:
                    S.add(d)
                    grew = True
        return S

    def numbering(self, s4, s6):
        full = set(range(self.n))
        if any(self.closure(S) == full for S in s4):
            return 'II_4'
        if any(self.closure(S) == full for S in s6):
            return 'III_6'
        return None

    def strong(self, s4, s6):
        full = frozenset(range(self.n))
        seen = set()
        stack = [frozenset(S) for S in s4 + s6]
        while stack:
            S = stack.pop()
            if S == full:
                return True
            if S in seen:
                continue
            seen.add(S)
            for d in full - S:
                T = S | {d}
                if self.npts(d, S) >= 3 and self.bigon_free(T):
                    stack.append(T)
        return False


def main():
    outdir, mode, ns = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3:]]
    for n in ns:
        lat = Counter()
        with open(f'{outdir}/{mode}_{n}.txt') as fp:
            for line in fp:
                lat[line.split('\t')[0]] += 1
        stats = Counter()
        bad = []
        for key, mult in lat.items():
            L = Lattice(n, parse(key))
            assert L.bigon_free(range(n)), key
            d = L.dichotomy()
            s4, s6 = L.starts()
            num = L.numbering(s4, s6) if n >= 5 else 'n<5'
            st = L.strong(s4, s6) if n >= 5 else None
            stats[('dichotomy', d)] += mult
            stats[('numbering', num)] += mult
            stats[('strong', st)] += mult
            stats[('lattices',)] += 1
            if d is None or (n >= 5 and num is None):
                bad.append(key)
        print(f'n={n}: {sum(lat.values())} bigon-free classes, '
              f'{stats[("lattices",)]} distinct lattices (as labelled)')
        for k in sorted((k for k in stats if k[0] != 'lattices'), key=str):
            print(f'   {k[0]:10s} {str(k[1]):8s} {stats[k]}')
        for key in bad[:10]:
            print('   FAILS:', key)
        print(f'   failures: {len(bad)}')
        sys.stdout.flush()


if __name__ == '__main__':
    main()
