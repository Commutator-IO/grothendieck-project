#!/usr/bin/env python3
"""Mechanical check of Caramello's grid of translations (arXiv:1103.3493, section 7.3) on finite
cases: the invariant is computed in the topos itself, and compared with the condition her
propositions state on the structure.

    python3 docs/dualities/grid/caramello_grid.py      # posets with at most 5 elements

For a finite poset Q, the topos [Q, Set] (Caramello's Sh(A_Q), the Alexandrov locale of Q) has
as subobject classifier at q the cosieves on q, so a propositional sequent T |- phi holds in it
iff phi is valid on the Kripke frame (Q, <=), valuations being the upper sets. Three columns:

  preorders (Q any finite poset), Sh(A_Q) = [Q, Set]:
    Boolean        iff  p <= q implies q <= p                  Prop. 7.8(ii)
    De Morgan      iff  c <= a, b implies a, b <= d for some d  Prop. 7.10(ii)
    two-valued     iff  p <= q and q <= p for all p, q          Prop. 7.11(iii)
    Goedel-Dummett iff  any a, b >= c are comparable            Thm 7.12(iii), via [15]
  meet-semilattices M (the finite posets with all binary meets), S_M with Sh(S_M) = [M^op, Set]:
    Boolean iff M is a singleton (7.8(i)); always De Morgan (7.10(i)); two-valued iff singleton
    (7.11(ii))
  finite distributive lattices D, Stone locale L_D (D is the lattice of lower sets of its poset
  J of join-irreducibles, and Sh(L_D) = [J^op, Set]):
    Boolean iff D is a finite Boolean algebra (7.7(v)); De Morgan iff condition (iii) of
    Prop. 7.9, checked as stated on D; two-valued iff D = {0 < 1} (7.11(i))

Goedel-Dummett for D (Thm 7.12(i)) uses Caramello's notion of a Goedel-Dummett lattice, which is
not checked here.
"""
import itertools
import sys


def posets(n):
    """All partial orders on range(n), as sets of pairs (a, b) meaning a <= b."""
    pairs = [(a, b) for a in range(n) for b in range(n) if a != b]
    out = []
    for bits in itertools.product((0, 1), repeat=len(pairs)):
        le = {(a, a) for a in range(n)} | {p for p, x in zip(pairs, bits) if x}
        if any((b, a) in le for (a, b) in le if a != b):
            continue
        if all((a, c) in le for (a, b) in le for (b2, c) in le if b == b2):
            out.append(le)
    return out


def lower_sets(n, le):
    return [frozenset(s) for r in range(n + 1) for s in itertools.combinations(range(n), r)
            if all(a in s for b in s for a in range(n) if (a, b) in le)]


# formulas: ('var', i), ('bot',), ('or', a, b), ('and', a, b), ('imp', a, b)
def neg(a):
    return ('imp', a, ('bot',))


def ors(xs):
    out = xs[0]
    for x in xs[1:]:
        out = ('or', out, x)
    return out


def bd(n):
    f = ('or', ('var', 0), neg(('var', 0)))
    for k in range(1, n):
        f = ('or', ('var', k), ('imp', ('var', k), f))
    return f


def bw(n):
    return ors([('imp', ('var', i), ors([('var', j) for j in range(n + 1) if j != i]))
                for i in range(n + 1)])


def nvars(f):
    if f[0] == 'var':
        return f[1] + 1
    if f[0] == 'bot':
        return 0
    return max(nvars(f[1]), nvars(f[2]))


def valid(n, le, f):
    below = {p: [q for q in range(n) if (q, p) in le] for p in range(n)}
    vals = lower_sets(n, le)
    k = nvars(f)

    def ev(g, v):
        """The set of points forcing g, a lower set of P."""
        t = g[0]
        if t == 'var':
            return v[g[1]]
        if t == 'bot':
            return frozenset()
        a, b = ev(g[1], v), ev(g[2], v)
        if t == 'or':
            return a | b
        if t == 'and':
            return a & b
        return frozenset(p for p in range(n) if all(q not in a or q in b for q in below[p]))
    return all(len(ev(f, v)) == n for v in itertools.product(vals, repeat=k))


def chain_len(n, le):
    best = {}
    for p in sorted(range(n), key=lambda p: sum((q, p) in le for q in range(n))):
        best[p] = 1 + max([best[q] for q in range(n) if q != p and (q, p) in le and q in best],
                          default=0)
    return max(best.values(), default=0)


def width_in_downsets(n, le):
    w = 0
    for p in range(n):
        d = [q for q in range(n) if (q, p) in le]
        for r in range(len(d), 0, -1):
            if any(all((a, b) not in le and (b, a) not in le for a, b in itertools.combinations(s, 2))
                   for s in itertools.combinations(d, r)):
                w = max(w, r)
                break
    return w



LEM = ('or', ('var', 0), neg(('var', 0)))
WEM = ('or', neg(('var', 0)), neg(neg(('var', 0))))
LC = ('or', ('imp', ('var', 0), ('var', 1)), ('imp', ('var', 1), ('var', 0)))


def opposite(le):
    return {(b, a) for (a, b) in le}


def holds(n, le, f):
    """f holds in [Q, Set] for the poset `le` on range(n): Kripke validity on (Q, <=), which is
    `valid` (written for frames seen downwards) applied to the opposite order."""
    return valid(n, opposite(le), f)


def two_valued(n, le):
    """[Q, Set] has exactly two subterminals (the upper sets of Q)."""
    return len(lower_sets(n, opposite(le))) == 2


def is_meet_semilattice(n, le):
    for a in range(n):
        for b in range(n):
            lbs = [c for c in range(n) if (c, a) in le and (c, b) in le]
            if not any(all((d, c) in le for d in lbs) for c in lbs):
                return False
    return True


def lattice_of_lower_sets(n, le):
    """D = lower sets of J (J the poset `le`), ordered by inclusion."""
    return lower_sets(n, le)


def prop_7_9_iii(D):
    """Caramello, Prop. 7.9(iii), on a finite distributive lattice given as a list of frozensets
    (meet = intersection, join = union, 0 = empty, 1 = the largest)."""
    top = max(D, key=len)
    nz = [x for x in D if x]
    for r in range(len(nz) + 1):
        for A in itertools.combinations(nz, r):
            good = [b for b in nz if all(not (b & a) for a in A)
                    or all(any(x & a for a in A) for x in nz if x <= b)]
            if frozenset().union(*good) != top:
                return False
    return True


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    bad = 0

    def check(name, got, want, detail):
        nonlocal bad
        if got != want:
            bad += 1
            print("exception", name, detail)
    for n in range(1, N + 1):
        ps = posets(n)
        rows = {"preorders": 0, "meet-semilattices": 0, "distributive lattices": 0}
        for le in ps:
            # preorders column
            rows["preorders"] += 1
            check("7.8(ii)", holds(n, le, LEM), all(a == b for a, b in le), sorted(le))
            check("7.10(ii)", holds(n, le, WEM),
                  all(any((a, d) in le and (b, d) in le for d in range(n))
                      for a in range(n) for b in range(n) for c in range(n)
                      if (c, a) in le and (c, b) in le), sorted(le))
            check("7.11(iii)", two_valued(n, le), n == 1, sorted(le))
            check("7.12(iii)", holds(n, le, LC),
                  all((a, b) in le or (b, a) in le for a in range(n) for b in range(n)
                      for c in range(n) if (c, a) in le and (c, b) in le), sorted(le))
            # meet-semilattice column: Sh(S_M) = [M^op, Set]
            if is_meet_semilattice(n, le):
                rows["meet-semilattices"] += 1
                op = opposite(le)
                check("7.8(i)", holds(n, op, LEM), n == 1, sorted(le))
                check("7.10(i)", holds(n, op, WEM), True, sorted(le))
                check("7.11(ii)", two_valued(n, op), n == 1, sorted(le))
            # Stone column: D = lower sets of J = le, Sh(L_D) = [J^op, Set]
            if n <= 4:
                rows["distributive lattices"] += 1
                D = lattice_of_lower_sets(n, le)
                op = opposite(le)
                boolean_D = all(any(not (x & y) and (x | y) == max(D, key=len) for y in D)
                                for x in D)
                check("7.7(v)", holds(n, op, LEM), boolean_D, sorted(le))
                check("7.9(iii)", holds(n, op, WEM), prop_7_9_iii(D), sorted(le))
                check("7.11(i)", two_valued(n, op), len(D) == 2, sorted(le))
        print(f"{n} elements: " + ", ".join(f"{v} {k}" for k, v in rows.items()), flush=True)
    print("no exception" if not bad else f"{bad} exceptions")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
