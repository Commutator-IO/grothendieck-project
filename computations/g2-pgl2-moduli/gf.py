"""Minimal finite fields GF(p^k): elements are ints 0..q-1 (base-p digits =
coefficients of a polynomial in a root of a primitive polynomial). Standard library only."""
from itertools import product


class GF:
    def __init__(self, p, k=1):
        self.p, self.k, self.q = p, k, p ** k
        q = self.q
        # add table via digit-wise addition
        def digits(x):
            return [(x // p ** i) % p for i in range(k)]
        def undigits(d):
            return sum(c * p ** i for i, c in enumerate(d))
        self._dig = [digits(x) for x in range(q)]
        self.add = [[undigits([(a + b) % p for a, b in zip(self._dig[x], self._dig[y])])
                     for y in range(q)] for x in range(q)]
        self.neg = [undigits([(-a) % p for a in self._dig[x]]) for x in range(q)]
        # find a primitive polynomial x^k - (c_{k-1} x^{k-1} + ... + c_0) by brute force
        for coeffs in product(range(p), repeat=k):
            if k > 1 and coeffs[0] == 0:
                continue
            exp, cur = [], [1] + [0] * (k - 1)  # polynomial 1
            seen = set()
            ok = True
            for _ in range(q - 1):
                v = undigits(cur)
                if v in seen:
                    ok = False
                    break
                seen.add(v)
                exp.append(v)
                # multiply cur by x modulo the polynomial
                top = cur[-1]
                cur = [0] + cur[:-1]
                cur = [(cur[i] + top * coeffs[i]) % p for i in range(k)]
            if ok and len(seen) == q - 1:
                break
        if k == 1:  # find a primitive root mod p
            for g in range(1, p):
                pw, s = 1, set()
                for _ in range(p - 1):
                    s.add(pw); pw = pw * g % p
                if len(s) == p - 1:
                    break
            exp, pw = [], 1
            for _ in range(p - 1):
                exp.append(pw); pw = pw * g % p
        self.exp = exp
        self.log = [None] * q
        for i, v in enumerate(exp):
            self.log[v] = i
        n = q - 1
        L = self.log
        self.mul = [[0 if (x == 0 or y == 0) else exp[(L[x] + L[y]) % n]
                     for y in range(q)] for x in range(q)]
        self.inv = [None] + [exp[(-L[x]) % n] for x in range(1, q)]
        self.zero, self.one = 0, 1

    def sub(self, x, y):
        return self.add[x][self.neg[y]]

    def from_int(self, n):
        n %= self.p
        return n  # prime-field elements are the ints 0..p-1 (digit 0)

    def pw(self, x, e):
        r = 1
        for _ in range(e):
            r = self.mul[r][x]
        return r

    def elements(self):
        return range(self.q)

    def subfield(self, d):
        """Elements of the subfield GF(p^d) (d | k)."""
        Q = self.p ** d
        return [x for x in range(self.q) if self.pw_fast(x, Q) == x]

    def pw_fast(self, x, e):
        if x == 0:
            return 0 if e > 0 else 1
        return self.exp[(self.log[x] * e) % (self.q - 1)]


def pgl2(F):
    """All elements of PGL2(F) as normalised 4-tuples (first non-zero entry = 1)."""
    out = []
    M = F.mul
    for a, b, c, d in product(F.elements(), repeat=4):
        first = next((v for v in (a, b, c, d) if v), None)
        if first != 1:
            continue
        if F.sub(M[a][d], M[b][c]) != 0:
            out.append((a, b, c, d))
    return out


def make_ops(F):
    A, M, inv = F.add, F.mul, F.inv

    def norm(g):
        for v in g:
            if v:
                i = inv[v]
                return tuple(M[i][x] for x in g)
        raise ValueError

    def mul(g, h):
        a, b, c, d = g
        e, f, k, l = h
        return norm((A[M[a][e]][M[b][k]], A[M[a][f]][M[b][l]],
                     A[M[c][e]][M[d][k]], A[M[c][f]][M[d][l]]))

    def tr(g):
        return A[g[0]][g[3]]

    def det(g):
        return F.sub(M[g[0]][g[3]], M[g[1]][g[2]])

    def invariant(g):
        t = tr(g)
        return F.sub(M[M[t][t]][inv[det(g)]], F.from_int(2))

    return norm, mul, tr, det, invariant
