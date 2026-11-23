#!/usr/bin/env python3
"""Euler characteristic of A/L for every finite poset A on n <= N points (issue #187).

For a finite poset P, the category of elements of the Lawvere object is the finite poset
E = {(x, S) : S a down-set of the down-set of x}, (x, S) <= (y, T) iff x <= y and S = T ∩ ↓x.
Its Euler characteristic is computed from P alone: χ(E) = Σ_x |D(↓x)| c(x), where D(↓x) is the
set of down-sets of ↓x and c(x) = Σ_n (-1)^n #{chains y_0 < … < y_{n-1} < x}. A contractible
finite poset has χ = 1, so χ(E) != 1 shows that E is not contractible, and then P is not a
weak test category (Cisinski, Astérisque 308, Déf. 4.1.8, with C = Δ1).

    python3 posets_euler.py 6
"""
import itertools
import sys
from collections import Counter


def posets(n):
    """Labelled partial orders on range(n) compatible with the natural order (x < y => x <= y
    in the natural order), which gives every isomorphism class at least once."""
    pairs = [(x, y) for x in range(n) for y in range(x + 1, n)]
    for bits in itertools.product([0, 1], repeat=len(pairs)):
        rel = {p for p, b in zip(pairs, bits) if b}
        if all((x, z) in rel for (x, y) in rel for (y2, z) in rel if y == y2):
            yield rel


def euler(n, rel):
    le = lambda x, y: x == y or (x, y) in rel
    down = [[y for y in range(n) if le(y, x)] for x in range(n)]
    c = [0] * n
    for x in range(n):  # chains ending at x, by increasing x (natural order is a linear extension)
        c[x] = 1 - sum(c[y] for y in down[x] if y != x)
    # c[x] above is Σ over chains ending at x of (-1)^length: c(x) = 1 - Σ_{y<x} c(y)
    def ndown(xs):
        cnt = 0
        for k in range(len(xs) + 1):
            for S in itertools.combinations(xs, k):
                S = set(S)
                if all(z in S for y in S for z in down[y]):
                    cnt += 1
        return cnt
    return sum(ndown(down[x]) * c[x] for x in range(n)), sum(c)


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    for n in range(1, N + 1):
        tally = Counter()
        for rel in posets(n):
            chiE, chiP = euler(n, rel)
            tally[(chiP, chiE)] += 1
        ones = sum(v for (p, e), v in tally.items() if e == 1)
        print(f'n={n}: labelled posets (natural-order extensions) by (χ(P), χ(A/L)):',
              dict(sorted(tally.items())), f'| with χ(A/L) = 1: {ones}')


if __name__ == '__main__':
    main()
