"""Folder 5, page 7: the ideal I_{nu,r} = (Theta_0..Theta_r) of
A^(nu) = Z_(p)[L_0..L_nu]/(L_i^p - q_i L_{i+1}, L_nu^p), L_i = lambda_i + Theta_i,
is exactly the diagonal lattice of the page:
  w_a in p^{i-r} if the first nonzero a_i has i > r (no condition if i <= r),
  w_0 in p^{c(nu)-r},  c(nu) = nu + p*v_p(lambda_nu).
Work in Z/p^N, N = c(nu)+1: I + p^N A = L and L >= p^N A >= pL gives I = L (Nakayama).
Check: (1) every generator Theta_j*Theta^a (j<=r) lies in L; (2) length of
A/(I+p^N A) (Smith form over Z/p^N) equals the length of A/L."""
import itertools, sys, time
from math import factorial

def vp(n, p):
    v = 0
    while n % p == 0: n //= p; v += 1
    return v

def run(p, nu):
    lam_v = p**nu - vp(factorial(p**nu), p)
    c = nu + p*lam_v
    N = c + 1; M = p**N
    def frac(num, den):  # element of Z_(p) mod p^N
        g = vp(den, p); assert vp(num, p) >= g
        num //= p**g; den //= p**g
        return num * pow(den, -1, M) % M
    lam = [frac(p**(p**i), factorial(p**i)) for i in range(nu+1)]
    q = [factorial(p**(i+1)) // factorial(p**i)**p for i in range(nu)]
    idx = list(itertools.product(range(p), repeat=nu+1))  # a=(a_0..a_nu)
    pos = {a: k for k, a in enumerate(idx)}
    n = len(idx)
    # multiplication in Lambda basis: add exponents, carry L_i^p = q_i L_{i+1}
    def mono_mul(a, b):
        e = [x+y for x, y in zip(a, b)]; coef = 1
        for i in range(nu+1):
            while e[i] >= p:
                if i == nu: return None, 0
                e[i] -= p; e[i+1] += 1; coef = coef*q[i] % M
        return tuple(e), coef
    def mul(u, v):  # vectors in Lambda basis
        w = [0]*n
        for i, x in enumerate(u):
            if x == 0: continue
            for j, y in enumerate(v):
                if y == 0: continue
                m, cf = mono_mul(idx[i], idx[j])
                if m is not None: w[pos[m]] = (w[pos[m]] + x*y*cf) % M
        return w
    # Theta^a in Lambda basis: prod (L_i - lam_i)^{a_i}, exponents < p so no carry
    from math import comb
    T = []
    for a in idx:
        vec = [0]*n
        for b in itertools.product(*[range(ai+1) for ai in a]):
            cf = 1
            for i in range(nu+1):
                cf = cf*comb(a[i], b[i])*pow(-lam[i], a[i]-b[i], M) % M
            vec[pos[b]] = (vec[pos[b]] + cf) % M
        T.append(vec)
    # convert Lambda-coords -> Theta-coords: T is unitriangular w.r.t. componentwise order;
    # solve by back substitution in order of decreasing total degree
    order = sorted(range(n), key=lambda k: -sum(idx[k]))
    def to_theta(v):
        v = v[:]; out = [0]*n
        for k in order:  # coefficient of Lambda^{idx[k]} only gets contributions from Theta^b, b>=a
            x = v[k] % M
            if x:
                out[k] = x
                for j in range(n):
                    if T[k][j]: v[j] = (v[j] - x*T[k][j]) % M
        return out
    def theta(i):
        v = [0]*n; a = [0]*(nu+1); a[i] = 1; return T[pos[tuple(a)]][:] 
    results = []
    for r in range(0, nu+1):
        def expo(a):
            if all(x == 0 for x in a): return c - r
            i = next(k for k, x in enumerate(a) if x)
            return max(i - r, 0)
        ex = [min(expo(a), N) for a in idx]
        gens = []
        for j in range(r+1):
            tj = theta(j)
            for k in range(n):
                gens.append(to_theta(mul(tj, T[k])))
        inL = all(g[k] % p**ex[k] == 0 for g in gens for k in range(n))
        # Smith form over Z/p^N: elementary divisors by min-valuation pivoting
        rows = [g[:] for g in gens if any(g)]
        length_I = 0  # sum of valuations of elementary divisors, zero rows count N
        cols = list(range(n)); rank_vals = []
        while rows and cols:
            best = None
            for ri, rw in enumerate(rows):
                for cj in cols:
                    if rw[cj]:
                        v = vp(rw[cj], p)
                        if best is None or v < best[0]: best = (v, ri, cj)
                        if v == 0: break
                if best and best[0] == 0: break
            if best is None: break
            v, ri, cj = best; rank_vals.append(v)
            piv = rows.pop(ri); u = pow(piv[cj] // p**v, -1, M)
            new = []
            for rw in rows:
                if rw[cj]:
                    f = (rw[cj] // p**v) * u % M
                    rw = [(x - f*y) % M for x, y in zip(rw, piv)]
                if any(rw): new.append(rw)
            rows = new; cols.remove(cj)
        len_quot = sum(rank_vals) + N*(n - len(rank_vals))
        len_L = sum(ex)
        results.append((r, inL, len_quot, len_L, inL and len_quot == len_L))
    return c, results

if __name__ == "__main__":
    cases = [(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1),(3,2),(3,3),(3,4),(5,1),(5,2),(7,1),(7,2),(11,1),(13,1)]
    allok = True
    for p, nu in cases:
        t = time.time(); c, res = run(p, nu)
        for r, inL, lq, lL, ok in res:
            allok &= ok
            print(f"p={p} nu={nu} c(nu)={c} r={r}: I in L: {inL}, length A/I = {lq}, length A/L = {lL} -> {'OK' if ok else 'FAIL'}")
        print(f"   ({time.time()-t:.1f}s)"); sys.stdout.flush()
    print("ALL OK" if allok else "SOME FAIL")
