# Which characteristics does the computation of full.py over Q cover?
#
# full.py run over Q performs Gaussian eliminations whose only divisions are by pivots. Every
# intermediate coefficient is then an integer combination divided by products of pivots, so if a
# prime p divides neither the numerator nor the denominator of any pivot, the same elimination,
# with the same pivot positions, runs over F_p: the ranks, the invariant subspace and the gap are
# the same over every field of characteristic p as over Q. This script reruns full.py over Q,
# records the prime factors of every pivot, and prints them. The remaining primes are to be
# checked directly with full.py.
import sys
from fractions import Fraction

src = open('full.py').read()
body = src.split("exec(open('check.py').read().split('# ring k[x1')[0])", 1)[1]
pre = open('check.py').read().split('# ring k[x1')[0]
pre = pre.replace("def inv(c): return pow(c,P-2,P) if P else 1/c",
                  "def inv(c):\n    _record(c)\n    return 1/c")

primes = set()
def factor(n):
    n = abs(n); f = set(); d = 2
    while d * d <= n:
        while n % d == 0:
            f.add(d); n //= d
        d += 1
    if n > 1: f.add(n)
    return f
def _record(c):
    c = Fraction(c)
    primes.update(factor(c.numerator)); primes.update(factor(c.denominator))

sys.argv = [sys.argv[0], '0']
g = {'_record': _record, '__name__': '__main__'}
exec(pre, g)
exec(body, g)
print('primes dividing a pivot over Q:', sorted(primes))
