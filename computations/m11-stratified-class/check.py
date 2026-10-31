"""Folder 147, pp. 62-64: the stratified class of M_{1,1} over Z, checked by point counts.

Realisation: L -> q, zeta_p = [Spec F_p] -> 1 if char F_q = p else 0. Under the invariant of
the reading (each locally closed piece with constant geometric automorphism group H counts as
[coarse space] / card H), the F_q-realisation of [M_{1,1}] is
        N(q) = sum over j in F_q of 1 / card Aut_{F_q-bar}(E_j).
This script computes N(q) from scratch: for each j in F_q it finds a Weierstrass curve over
F_q with that j-invariant, counts its automorphisms (u, r, s, t) over K = F_{q^2}
(and, for q = 2, 3, also over F_{q^4}, to see the count is stable), and compares
    (80)  N(q) = (q-1)/2 - 1/12 + [p=2]/8 + [p=3]/6,
    (79)  N(q) = (q-1)/2 - 1/12            (claimed over Z[1/6]),
    compactification: (80) + 1/2, i.e. q/2 - 1/12 + [p=2]/8 + [p=3]/6
          (the cusp, a nodal cubic with automorphism group Z/2, is taken as given, not computed).
It also checks the strata of p. 63: generic Aut = 2, j = 1728 -> 4, j = 0 -> 6, meeting
in characteristic 2 and 3 with Aut of order 24 and 12; [U] = L - 2 + z2 + z3, [S'_i] = 1 - z2 - z3.
"""
import time
from fractions import Fraction as Fr
from itertools import product
from gf import GF

FIELDS = [(2, 1), (3, 1), (2, 2), (5, 1), (7, 1), (2, 3), (3, 2), (11, 1), (13, 1), (17, 1), (5, 2)]


def invariants(F, a):
    A, M, S = F.add, F.mul, F.sub
    c = F.from_int
    a1, a2, a3, a4, a6 = a
    b2 = A[M[a1][a1]][M[c(4)][a2]]
    b4 = A[M[c(2)][a4]][M[a1][a3]]
    b6 = A[M[a3][a3]][M[c(4)][a6]]
    b8 = S(A[A[M[M[a1][a1]][a6]][M[M[c(4)][a2]][a6]]][M[a2][M[a3][a3]]],
           A[M[M[a1][a3]][a4]][M[a4][a4]])
    c4 = S(M[b2][b2], M[c(24)][b4])
    disc = S(M[M[M[c(9)][b2]][b4]][b6],  # 9 b2 b4 b6 - b2^2 b8 - 8 b4^3 - 27 b6^2
             A[A[M[M[b2][b2]][b8]][M[c(8)][M[M[b4][b4]][b4]]]][M[c(27)][M[b6][b6]]])
    return c4, disc


def j_inv(F, a):
    c4, d = invariants(F, a)
    if d == 0:
        return None
    return F.mul[F.mul[F.mul[c4][c4]][c4]][F.inv[d]]


def count_aut(K, a):
    """Number of (u, r, s, t) in K* x K^3 with the transformed curve equal to a (Silverman III.1)."""
    A, M, S, inv = K.add, K.mul, K.sub, K.inv
    c = K.from_int
    a1, a2, a3, a4, a6 = a
    n = 0
    for u in range(1, K.q):
        ui = inv[u]; u2 = M[u][u]; u3 = M[u2][u]; u4 = M[u2][u2]; u6 = M[u3][u3]
        for s in range(K.q):
            # u a1' = a1 + 2s
            if M[u][a1] != A[a1][M[c(2)][s]]:
                continue
            for r in range(K.q):
                # u^2 a2' = a2 - s a1 + 3r - s^2
                if M[u2][a2] != S(A[S(a2, M[s][a1])][M[c(3)][r]], M[s][s]):
                    continue
                for t in range(K.q):
                    # u^3 a3' = a3 + r a1 + 2t
                    if M[u3][a3] != A[A[a3][M[r][a1]]][M[c(2)][t]]:
                        continue
                    # u^4 a4' = a4 - s a3 + 2 r a2 - (t + r s) a1 + 3 r^2 - 2 s t
                    v4 = S(A[S(A[S(a4, M[s][a3])][M[M[c(2)][r]][a2]], M[A[t][M[r][s]]][a1])][M[c(3)][M[r][r]]],
                           M[M[c(2)][s]][t])
                    if M[u4][a4] != v4:
                        continue
                    # u^6 a6' = a6 + r a4 + r^2 a2 + r^3 - t a3 - t^2 - r t a1
                    r2 = M[r][r]
                    v6 = S(S(S(A[A[A[a6][M[r][a4]]][M[r2][a2]]][M[r2][r]], M[t][a3]), M[t][t]), M[M[r][t]][a1])
                    if M[u6][a6] != v6:
                        continue
                    n += 1
    return n


def run(p, k, out, ext=(2,)):
    q = p ** k
    res = {}
    for e in ext:
        K = GF(p, k * e)
        Fq = sorted(K.subfield(k))
        # one Weierstrass curve over F_q per j in F_q
        rep = {}
        for a in product(Fq, repeat=5):
            jv = j_inv(K, a)
            if jv is not None and jv not in rep:
                rep[jv] = a
            if len(rep) == q:
                break
        assert sorted(rep) == Fq, "some j in F_q not attained"
        res[e] = {jv: count_aut(K, a) for jv, a in rep.items()}
    auts = res[ext[0]]
    stable = all(res[e] == auts for e in ext)
    N = sum(Fr(1, n) for n in auts.values())
    z2, z3 = int(p == 2), int(p == 3)
    f80 = Fr(q - 1, 2) - Fr(1, 12) + Fr(z2, 8) + Fr(z3, 6)
    f79 = Fr(q - 1, 2) - Fr(1, 12)
    K = GF(p, k * ext[0])
    j0, j1728 = 0, K.from_int(1728)
    spectrum = sorted(set(auts.values()))
    generic = [n for jv, n in auts.items() if jv not in (j0, j1728)]
    strata_ok = (all(n == 2 for n in generic) and len(generic) == q - 2 + z2 + z3
                 and (auts[j0] == (24 if p == 2 else 12 if p == 3 else 6))
                 and (p in (2, 3) or auts[j1728] == 4))
    line = (f"q={q:3d} p={p:2d}  Aut orders by j: j=0 -> {auts[j0]}, j=1728 -> {auts[j1728]}, "
            f"others {sorted(set(generic))} ({len(generic)} values)  stable over F_q^{list(ext)}: {stable}  "
            f"N(q) = {N}  (80): {f80}  (79): {f79}  compactified N+1/2 = {N + Fr(1, 2)}  "
            f"(80)-bar: {Fr(q, 2) - Fr(1, 12) + Fr(z2, 8) + Fr(z3, 6)}  "
            f"N=(80): {N == f80}  N=(79): {N == f79}  strata as on p.63: {strata_ok}")
    print(line); out.append(line)
    return N == f80 and stable and strata_ok and (N == f79) == (p not in (2, 3))


if __name__ == '__main__':
    t = time.time()
    out, ok = [], True
    for p, k in FIELDS:
        ok &= run(p, k, out, ext=(2, 4) if p ** k in (2, 3) else (2,))
    out.append(f"ALL OK (N(q) = (80) for every q; = (79) exactly when p >= 5): {ok}   ({time.time() - t:.1f} s)")
    print(out[-1])
    open(__import__('os').path.join(__import__('os').path.dirname(__file__) or '.', 'results.txt'), 'w').write('\n'.join(out) + '\n')
