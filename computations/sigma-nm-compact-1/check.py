"""Folder 1, pp. 71-72: sigma_n^m(u+v) <= sum_p sigma_n^p(u) sigma_n^(m-p)(v), and the product form.

sigma_n^m(w) = e_m(s_0(w), ..., s_{n-1}(w)), elementary symmetric function of the n largest
singular values.  The statement for compact operators reduces to finite rank: P_N w P_N -> w in
norm and |s_i(a) - s_i(b)| <= ||a - b|| (Weyl), and both sides are continuous in finitely many
s_i.  So there is nothing finite to check beyond matrices (the Lean-proved case).  This script
(1) re-tests the matrix case on random complex matrices (sanity, no new information), and
(2) shows the truncation argument at work on two explicit compact operators of l^2.
"""
import mpmath as mp
import random, itertools, sys

mp.mp.dps = 30

def svals(M):
    return sorted([abs(x) for x in mp.svd_c(M, compute_uv=False)], reverse=True)

def esym(xs, m):
    return mp.fsum(mp.fprod(c) for c in itertools.combinations(xs, m)) if m else mp.mpf(1)

def sigma(s, n, m):
    s = (list(s) + [mp.mpf(0)] * n)[:n]
    return esym(s, m)

def worst_margin(su, sv, sw, d):
    """max over n<=d, m<=n of LHS - RHS (should be <= 0) and of product-form violation."""
    worst, worstp = -mp.inf, -mp.inf
    for n in range(1, d + 1):
        for m in range(0, n + 1):
            lhs = sigma(sw, n, m)
            rhs = mp.fsum(sigma(su, n, p) * sigma(sv, n, m - p) for p in range(m + 1))
            worst = max(worst, (lhs - rhs) / (1 + rhs))
        for r in (mp.mpf('0.1'), mp.mpf(1), mp.mpf(10)):
            L = mp.fprod(1 + r * x for x in (sw + [0]*n)[:n])
            R = mp.fprod(1 + r * x for x in (su + [0]*n)[:n]) * mp.fprod(1 + r * x for x in (sv + [0]*n)[:n])
            worstp = max(worstp, (L - R) / R)
    return worst, worstp

def rand_c(rng, a, b):
    return mp.matrix([[mp.mpc(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(b)] for _ in range(a)])

def main():
    rng = random.Random(71)
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    print("Part 1: matrices (Lean-proved case), random complex u, v of size a x b, a, b <= 5")
    W, WP = -mp.inf, -mp.inf
    for t in range(trials):
        a, b = rng.randint(1, 5), rng.randint(1, 5)
        u = rand_c(rng, a, b)
        kind = t % 3
        if kind == 0:
            v = rand_c(rng, a, b)
        elif kind == 1:   # near-cancellation
            v = -u + rand_c(rng, a, b) * mp.mpf('0.01')
        else:             # rank one
            v = rand_c(rng, a, 1) * rand_c(rng, 1, b)
        su, sv, sw = svals(u), svals(v), svals(u + v)
        w, wp = worst_margin(su, sv, sw, min(a, b) + 1)
        W, WP = max(W, w), max(WP, wp)
    print(f"  {trials} pairs; max relative (LHS - RHS) over all n, m: {mp.nstr(W, 6)}; "
          f"product form, r in {{0.1, 1, 10}}: {mp.nstr(WP, 6)}  (<= 0 means the inequality holds)")
    print()
    print("Part 2: compact operators on l^2, truncated to the first N coordinates")
    print("  u = diag(1/(k+1)),  v = weighted shift v e_k = e_{k+1} / sqrt(k+1)  (both compact)")
    exact_u = [mp.mpf(1) / (k + 1) for k in range(6)]
    exact_v = [1 / mp.sqrt(k + 1) for k in range(6)]
    for N in (8, 16, 32):
        u = mp.matrix(N, N); v = mp.matrix(N, N)
        for k in range(N):
            u[k, k] = mp.mpf(1) / (k + 1)
            if k + 1 < N:
                v[k + 1, k] = 1 / mp.sqrt(k + 1)
        su, sv, sw = svals(u), svals(v), svals(u + v)
        w, wp = worst_margin(su[:6], sv[:6], sw[:6], 5)
        err = max(abs(su[i] - exact_u[i]) for i in range(5))
        errv = max(abs(sv[i] - exact_v[i]) for i in range(5))
        print(f"  N = {N:2d}: s_0..s_4(u+v) = {[mp.nstr(x, 6) for x in sw[:5]]}; "
              f"|s_i - exact| (u, v) = {mp.nstr(err, 3)}, {mp.nstr(errv, 3)}; "
              f"max rel. violation n<=5: {mp.nstr(w, 4)}, product: {mp.nstr(wp, 4)}")
    print("  The s_i(u+v) of the truncations stabilise (Weyl: they move by at most ||tail|| -> 0),")
    print("  so the limit inequality is the finite one passed to the limit; no extra finite content.")

main()
