"""Type B_n: every Borel through the centraliser of e + e_{-theta} is opposite to B.

so(2n+1) on V = C^{2n+1}, basis v_1..v_{2n+1}, form J with J[i][2n+2-i] = 1,
torus diag(t_1..t_n, 0, -t_n..-t_1).  Borel subgroups of SO(2n+1) <-> isotropic
flags V_1 < ... < V_n; opposite to the standard one iff V_k meets F_{2n+1-k} = <v_1..v_{2n+1-k}>
trivially for k = 1..n.  The Borels through T' = centraliser of E0 = e + e_{-theta}
give the flags V_k = span of eigenvectors u_{mu_1}, ..., u_{mu_k}, mu_j eigenvalues of E0 with
no two opposite (the T'-weights +-eps'_i take distinct values on E0).

Certificate: we compute modulo a prime p = 1 mod 2n in which the eigenvalues of E0 (the roots
of t^{2n} = a, and 0) are distinct.  A minor nonzero mod p is nonzero in characteristic 0
(reduction at a prime above p of the eigenlines, which are 1-dimensional on both sides).
"""
import itertools, sys


def so_matrices(n):
    N = 2 * n + 1
    def E(i, j):
        m = [[0] * N for _ in range(N)]
        m[i - 1][j - 1] = 1
        return m
    def add(*ms):
        out = [[0] * N for _ in range(N)]
        for c, m in ms:
            for i in range(N):
                for j in range(N):
                    out[i][j] += c * m[i][j]
        return out
    simple = []
    for i in range(1, n):          # eps_i - eps_{i+1}
        simple.append(add((1, E(i, i + 1)), (-1, E(N + 1 - (i + 1), N + 1 - i))))
    simple.append(add((1, E(n, n + 1)), (-1, E(n + 1, n + 2))))   # eps_n
    neg_theta = add((1, E(N - 1, 1)), (-1, E(N, 2)))              # -(eps_1 + eps_2)
    return N, simple, neg_theta


def check_so(N, m):
    J = [[1 if i + j == N - 1 else 0 for j in range(N)] for i in range(N)]
    mt = [list(r) for r in zip(*m)]
    a = [[sum(mt[i][k] * J[k][j] for k in range(N)) for j in range(N)] for i in range(N)]
    b = [[sum(J[i][k] * m[k][j] for k in range(N)) for j in range(N)] for i in range(N)]
    return all(a[i][j] + b[i][j] == 0 for i in range(N) for j in range(N))


def nullspace_mod(A, p):
    m = [list(r) for r in A]
    rows, cols = len(m), len(m[0])
    piv, r = [], 0
    for c in range(cols):
        s = next((i for i in range(r, rows) if m[i][c] % p), None)
        if s is None:
            continue
        m[r], m[s] = m[s], m[r]
        inv = pow(m[r][c], p - 2, p)
        m[r] = [x * inv % p for x in m[r]]
        for i in range(rows):
            if i != r and m[i][c] % p:
                f = m[i][c]
                m[i] = [(x - f * y) % p for x, y in zip(m[i], m[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(cols) if c not in piv]
    basis = []
    for f in free:
        v = [0] * cols
        v[f] = 1
        for i, c in enumerate(piv):
            v[c] = -m[i][f] % p
        basis.append(v)
    return basis


def det_mod(M, p):
    m = [list(r) for r in M]
    k, d = len(m), 1
    for c in range(k):
        s = next((i for i in range(c, k) if m[i][c] % p), None)
        if s is None:
            return 0
        if s != c:
            m[c], m[s] = m[s], m[c]
            d = -d
        d = d * m[c][c] % p
        inv = pow(m[c][c], p - 2, p)
        for i in range(c + 1, k):
            f = m[i][c] * inv % p
            m[i] = [(x - f * y) % p for x, y in zip(m[i], m[c])]
    return d % p


def run(n, p):
    N, simple, neg_theta = so_matrices(n)
    E0 = [[sum(m[i][j] for m in simple) + neg_theta[i][j] for j in range(N)] for i in range(N)]
    assert all(check_so(N, m) for m in simple + [neg_theta])
    # eigenvalues: roots of t (t^{2n} - a); find a from E0^{2n+1} = a E0
    P = [row[:] for row in E0]
    for _ in range(2 * n):
        P = [[sum(P[i][k] * E0[k][j] for k in range(N)) for j in range(N)] for i in range(N)]
    nz = [(i, j) for i in range(N) for j in range(N) if E0[i][j]]
    a = P[nz[0][0]][nz[0][1]] // E0[nz[0][0]][nz[0][1]]
    assert all(P[i][j] == a * E0[i][j] for i in range(N) for j in range(N)), "E0^(2n+1) != a E0"
    roots = sorted({x for x in range(1, p) if (pow(x, 2 * n, p) - a) % p == 0})
    if len(roots) != 2 * n:
        return None
    vecs = {}
    for mu in roots:
        A = [[(E0[i][j] - (mu if i == j else 0)) % p for j in range(N)] for i in range(N)]
        ns = nullspace_mod(A, p)
        assert len(ns) == 1
        vecs[mu] = ns[0]
    pairs = [(mu, (-mu) % p) for mu in roots if mu < (-mu) % p]
    assert len(pairs) == n
    bad = checked = 0
    for k in range(1, n + 1):
        for idx in itertools.combinations(range(n), k):
            for signs in itertools.product((0, 1), repeat=k):
                S = [pairs[i][s] for i, s in zip(idx, signs)]
                M = [[vecs[mu][r] for mu in S] for r in range(N - k, N)]
                checked += 1
                if det_mod(M, p) == 0:
                    bad += 1
    return a, checked, bad


if __name__ == "__main__":
    for n in range(2, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 7):
        for p in range(4 * n + 1, 10 ** 6, 2 * n):
            if all(p % d for d in range(2, int(p ** 0.5) + 1)):
                res = run(n, p)
                if res:
                    a, checked, bad = res
                    print(f"B{n}: a={a}, p={p}, minors checked={checked}, vanishing={bad}")
                    break
