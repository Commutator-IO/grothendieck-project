# The other reading (index-reversed annihilator filtration; Loday-Quillen 1984, 6.14 and the Amitsur-Levitzki argument):
# dim k[U_n] ∩ (sum of isotypic blocks with more than r rows)   = cyclic multilinear trace identities of M_r.
import sys
from common import *
from gram import gram, rank_mod
n = int(sys.argv[1])
for r in range(1, n):
    Lam = [l for l in partitions(n) if len(l) <= r]   # kill these blocks
    C, G = gram(n, Lam)
    print('n=%d r=%d  dim k[U_n] ∩ ⊕_{len>r} <= %d' % (n, r, len(C) - rank_mod(G, 1000003)), flush=True)
