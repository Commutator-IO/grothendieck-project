#!/usr/bin/env python3
"""An atlas of the small decks B M: every monoid of order <= N up to isomorphism, with the
invariants of the topos of right M-sets that the arches of the article read on M.

    python3 docs/bridges/atlas/monoids.py 5        # writes monoids-5.json next to this file

Enumeration: multiplication tables on {0, ..., n-1} with 0 the identity, filled cell by cell
with an associativity check on every completed triple, kept up to isomorphism (a canonical form
over the permutations fixing 0). The counts per order are checked against OEIS A058129
(1, 2, 7, 35, 228, 2237 monoids of order 1..6 up to isomorphism).

Invariants, for the topos PSh(B M) of right M-sets (arch of the article in brackets):
  group      M is a group                                    [Boolean, Thm 2.4 of Hemelaer-Rogers]
  ore        aM and bM meet for all a, b (right Ore)         [De Morgan]
  points     number of J-classes of M containing an idempotent: the essential points, idempotents
             up to D = J for finite M                       [essential points]
  subtopoi   number of two-sided ideals I with I = I.I, the empty ideal included
                                                             [subtopoi, Prop. 6.1.2 of Pirashvili]
  commutative, idempotents, regular (every element regular), and the size of the group of units.
"""
import itertools
import json
import os
import sys


def monoids(n):
    """All monoid tables on range(n) with identity 0, up to isomorphism (canonical forms)."""
    cells = [(a, b) for a in range(1, n) for b in range(1, n)]
    t = [[None] * n for _ in range(n)]
    for x in range(n):
        t[0][x] = x
        t[x][0] = x
    seen = set()
    perms = [(0,) + p for p in itertools.permutations(range(1, n))]

    def assoc_ok():
        # check every triple whose three products are defined
        for a in range(n):
            for b in range(n):
                ab = t[a][b]
                if ab is None:
                    continue
                for c in range(n):
                    bc = t[b][c]
                    if bc is None:
                        continue
                    l, r = t[ab][c], t[a][bc]
                    if l is not None and r is not None and l != r:
                        return False
        return True

    def canon():
        best = None
        for p in perms:
            inv = [0] * n
            for i, x in enumerate(p):
                inv[x] = i
            key = tuple(inv[t[p[a]][p[b]]] for a in range(n) for b in range(n))
            if best is None or key < best:
                best = key
        return best

    def rec(k):
        if k == len(cells):
            c = canon()
            if c not in seen:
                seen.add(c)
            return
        a, b = cells[k]
        for v in range(n):
            t[a][b] = v
            if assoc_ok():
                rec(k + 1)
        t[a][b] = None

    rec(0)
    return [tuple(tuple(c[i * n:(i + 1) * n]) for i in range(n)) for c in sorted(seen)]


def invariants(m):
    n = len(m)
    M = range(n)
    mul = lambda a, b: m[a][b]
    units = [a for a in M if any(mul(a, b) == 0 and mul(b, a) == 0 for b in M)]
    idem = [e for e in M if mul(e, e) == e]
    right = {a: frozenset(mul(a, x) for x in M) for a in M}
    left = {a: frozenset(mul(x, a) for x in M) for a in M}
    two = {a: frozenset(mul(mul(x, a), y) for x in M for y in M) for a in M}
    ore = all(right[a] & right[b] for a in M for b in M)
    jclasses = {}
    for a in M:
        jclasses.setdefault(two[a], []).append(a)
    points = sum(1 for cls in jclasses.values() if any(e in cls for e in idem))
    # two-sided ideals: unions of principal ideals closed under the order; enumerate subsets
    ideals = set()
    for r in range(n + 1):
        for s in itertools.combinations(M, r):
            S = frozenset(s)
            if all(mul(x, a) in S and mul(a, x) in S for a in S for x in M):
                ideals.add(S)
    subtopoi = sum(1 for I in ideals if frozenset(mul(a, b) for a in I for b in I) == I)
    regular = all(any(mul(mul(a, x), a) == a for x in M) for a in M)
    return {
        "group": len(units) == n,
        "ore": ore,
        "points": points,
        "subtopoi": subtopoi,
        "commutative": all(mul(a, b) == mul(b, a) for a in M for b in M),
        "idempotents": len(idem),
        "regular": regular,
        "units": len(units),
        "ideals": len(ideals),
    }


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    here = os.path.dirname(os.path.abspath(__file__))
    out = {}
    for n in range(1, N + 1):
        ms = monoids(n)
        out[n] = [{"table": m, **invariants(m)} for m in ms]
        print(f"order {n}: {len(ms)} monoids", flush=True)
    with open(os.path.join(here, f"monoids-{N}.json"), "w") as f:
        json.dump(out, f)


if __name__ == "__main__":
    main()
