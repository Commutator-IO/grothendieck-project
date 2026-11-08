# writes table_n.txt: for each i = 1..n and each cycle type t (as a sorted multiset), the value
# f_i(t) = sum over shapes lam with more than i rows of dim(lam) * chi_lam(t).
import sys
from common import *
n = int(sys.argv[1]); mode = sys.argv[2] if len(sys.argv) > 2 else 'R'; check_table(n); P = list(partitions(n))
# mode R: column i kills blocks with len > i (rank filtration: F_i = blocks with len <= i, the image of gl_i)
# mode LQ: column r kills blocks with len <= r (k[U_n] ∩ blocks with len > r: trace identities of M_r)
with open('table_%d%s.txt' % (n, '' if mode == 'R' else '_LQ'), 'w') as fh:
    fh.write('%d %d\n' % (n, len(P)))
    for t in P:
        vals = [sum(dim(l) * chi(l, t) for l in P if (len(l) > i if mode == "R" else len(l) <= i)) for i in range(1, n + 1)]
        fh.write(' '.join(map(str, list(t) + [0] * (n - len(t)))) + ' ' + ' '.join(map(str, vals)) + '\n')
