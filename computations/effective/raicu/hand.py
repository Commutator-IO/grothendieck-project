# Checks, over the integers, every identity used in the proof by hand of the note
# (docs/effective/article.tex, subsection « A proof by hand »): the example of length 15
# (16 in characteristic 2)
# A = k[x1,x2]/(f1^2, f2^2, f3^2), with f1 = x1^2, f2 = x1x2 - x2^2, f3 = x2^3.
# All the numbers are integers and the only nonzero one is phi(w) = -1, so the check
# holds in every characteristic. Pure Python, no argument: python3 hand.py

def mul(a, b):
    r = {}
    for (i, j), c in a.items():
        for (k, l), d in b.items():
            r[(i + k, j + l)] = r.get((i + k, j + l), 0) + c * d
    return {m: c for m, c in r.items() if c}

def add(*ps):
    r = {}
    for s, p in ps:
        for m, c in p.items():
            r[m] = r.get(m, 0) + s * c
    return {m: c for m, c in r.items() if c}

def mono(i, j): return {(i, j): 1}
x1, x2, one = mono(1, 0), mono(0, 1), mono(0, 0)
f1 = mul(x1, x1)
f2 = add((1, mul(x1, x2)), (-1, mul(x2, x2)))
f3 = mul(mul(x2, x2), x2)
K4 = [mul(f1, f1), mul(f2, f2)]                      # (f1^2, f2^2) in degree 4

# reduction of a form of degree 4 or 5 to the bases of A_4 and A_5 used in the note
def red4(p):  # x1^4 = 0, x2^4 = 2 x1x2^3 - x1^2x2^2
    p = dict(p); a = p.pop((0, 4), 0); p.pop((4, 0), None)
    return add((1, p), (a, add((2, mono(1, 3)), (-1, mono(2, 2)))))
def red5(p):  # x1^5 = x1^4x2 = 0, x1x2^4 = 2x1^2x2^3 - x1^3x2^2, x2^5 = 3x1^2x2^3 - 2x1^3x2^2
    p = dict(p); a = p.pop((1, 4), 0); b = p.pop((0, 5), 0)
    p.pop((5, 0), None); p.pop((4, 1), None)
    return add((1, p), (a, add((2, mono(2, 3)), (-1, mono(3, 2)))),
               (b, add((3, mono(2, 3)), (-2, mono(3, 2)))))
# the reductions are consequences of the relations
assert not red4(K4[1]) and not red4(K4[0])
for m in (x1, x2):
    assert not red5(mul(K4[1], m)) and not red5(mul(K4[0], m))

# C_5 = A_5: f1f3 and f2f3 reduce to x1^2x2^3 and x1^3x2^2 - x1^2x2^3
assert red5(mul(f1, f3)) == mono(2, 3)
assert red5(mul(f2, f3)) == add((1, mono(3, 2)), (-1, mono(2, 3)))

# relations among e = (1, x1, x2, x2^2) with coefficients in C
e = [one, x1, x2, mul(x2, x2)]
def val(r): return add(*[(1, mul(c, ej)) for c, ej in zip(r, e)])
rho = [f3, f2, add((1, f2), (-1, f1)), {}]
s1 = [{}, add((-1, f3)), f3, f2]
s2 = [{}, add((-2, f3)), f3, f1]
assert not val(rho)                      # identity in k[x1, x2]
assert not val(s1)                       # identity in k[x1, x2]
assert val(s2) == mul(f2, f2)            # = f2^2, zero in A

# the functional
def lam(p):   # on k[x]_4: x1^i x2^(4-i) -> 1 for i <= 3, x1^4 -> 0
    return sum(c for (i, j), c in p.items() if i <= 3)
def nu(p):    # on k[x]_3: x1^3, x1^2x2 -> 2, x1x2^2 -> 1, x2^3 -> 0
    return sum(c * {3: 2, 2: 2, 1: 1, 0: 0}[i] for (i, j), c in p.items())
assert [lam(q) for q in K4] == [0, 0]    # lam is defined on A_4
def phi(v): return lam(v[1]) + nu(v[3])
def scal(a, r): return [mul(a, c) for c in r]

checks = {}
for name, a in (('x1^2', mul(x1, x1)), ('x1x2', mul(x1, x2)), ('x2^2', mul(x2, x2))):
    checks[name + '*rho'] = phi(scal(a, rho))
for name, b in (('x1', x1), ('x2', x2)):
    checks[name + '*sigma1'] = phi(scal(b, s1))
    checks[name + '*sigma2'] = phi(scal(b, s2))
checks['E_5: lam(f1f2)'] = lam(mul(f1, f2))
checks['E_5: nu(f3)'] = nu(f3)
W = [{}, add((-1, mul(x2, f3))), mul(x1, f3), {}]
for k, v in checks.items():
    print(f'{k:16s} {v}')
    assert v == 0
print('phi(w)          ', phi(W))
assert phi(W) == -1
print('all identities hold over Z')
