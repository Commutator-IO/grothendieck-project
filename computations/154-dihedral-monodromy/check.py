"""Folder 154, pp. 55-63: arithmetic of the dihedral monodromy.

Checks, on realisable line arrangements (random integer lines in RP^2,
with forced multiple points):
  A. sum_{s in D_i} (nu(s)-1) = n-1 for every line D_i;
  B. composing the page's reflections sigma(t) = l - t along the chain
     s_1, a_1, ..., s_m, a_m around D_i (l_s = n - nu_s,
     l_a = (n-1) - (nu_s-1) - (nu_t-1)) gives the rotation t -> t-(n-1)
     of Z/2n, whatever the order of the vertices along D_i;
  C. geometric half-turn: moving a point p half-way round delta_i in the
     dual plane, the direction p->delta_i passes exactly n-1 of the 2n-2
     other directions (doubled cyclic order of the lines p delta_j);
     also records the chain length 2*m_i (m_i = vertices on D_i);
  D. group theory in D_{2n}: <rot(n-1)> has index gcd(n-1,2) in the
     rotations; <rot(2(n-1))> index 2; <rot(n-1), vertex reflection> is
     all of D_{2n} iff n even; adding an edge reflection gives D_{2n}.
"""
import random, math
from fractions import Fraction
from itertools import combinations

random.seed(154)

def cross(u, v):
    return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])

def normalize(p):
    g = 0
    for x in p: g = math.gcd(g, abs(x))
    p = tuple(x//g for x in p)
    for x in p:
        if x != 0:
            return p if x > 0 else tuple(-y for y in p)
    return p

def random_arrangement(n, nmult):
    """n distinct lines (normal vectors); nmult extra lines forced through
    existing vertices to create multiple points."""
    lines = []
    while len(lines) < n:
        if len(lines) >= 2 and nmult > 0 and random.random() < 0.5:
            a, b = random.sample(lines, 2)
            P = cross(a, b)            # their meeting point
            q = (random.randint(-9, 9), random.randint(-9, 9), random.randint(-9, 9))
            L = cross(P, q)
            nmult -= 1
        else:
            L = tuple(random.randint(-9, 9) for _ in range(3))
        if L == (0, 0, 0): continue
        L = normalize(L)
        if L in lines: continue
        lines.append(L)
    return lines

def vertices_on(lines, i):
    """group the other lines by their meeting point with line i"""
    groups = {}
    for j, L in enumerate(lines):
        if j == i: continue
        P = normalize(cross(lines[i], L))
        groups.setdefault(P, []).append(j)
    return groups  # point -> lines other than i through it ; nu = len+1

def composite(seq_l, N):
    perm = list(range(N))
    for l in seq_l:
        perm = [(l - t) % N for t in perm]
    return perm

def check_AB(lines):
    n = len(lines); N = 2*n
    out = []
    for i in range(n):
        g = vertices_on(lines, i)
        nus = [len(v)+1 for v in g.values()]
        A = sum(nu-1 for nu in nus) == n-1
        okB = True
        for _ in range(5):               # several vertex orders
            random.shuffle(nus)
            m = len(nus)
            seq = []
            for k in range(m):
                s, t = nus[k], nus[(k+1) % m]
                seq.append(n - s)
                seq.append((n-1) - (s-1) - (t-1))
            perm = composite(seq, N)
            okB &= all(perm[t] == (t - (n-1)) % N for t in range(N))
        out.append((A, okB, len(nus)))
    return out

def dual_points(lines):
    # dual point delta_j of line j: affine chart; lines with c=0 skipped
    return [(Fraction(L[0], L[2]), Fraction(L[1], L[2])) if L[2] else None for L in lines]

def half_turn_crossings(lines, i, steps=4000):
    """p goes round delta_i on a small circle from angle th0 to th0+pi;
    count how many other direction labels (j,+-) the label (i,+) passes."""
    d = [(float(L[0])/L[2], float(L[1])/L[2]) for L in lines]
    n = len(lines)
    di = d[i]
    # radius smaller than any distance from delta_i to a line delta_j delta_k
    # not through delta_i
    r = 1e9
    for j, k in combinations(range(n), 2):
        if i in (j, k): continue
        (x1, y1), (x2, y2) = d[j], d[k]
        num = abs((x2-x1)*(y1-di[1]) - (x1-di[0])*(y2-y1))
        den = math.hypot(x2-x1, y2-y1)
        if den > 0 and num/den > 1e-12: r = min(r, num/den)
    for j in range(n):
        if j != i: r = min(r, math.hypot(d[j][0]-di[0], d[j][1]-di[1]))
    r *= 0.3
    th0 = random.random()*2*math.pi + 1e-3
    def angles(p):
        out = {}
        for j in range(n):
            a = math.atan2(d[j][1]-p[1], d[j][0]-p[0])
            out[(j, +1)] = a % (2*math.pi)
            out[(j, -1)] = (a + math.pi) % (2*math.pi)
        return out
    passed = 0
    prev = None
    for s in range(steps+1):
        th = th0 + math.pi*s/steps
        p = (di[0] + r*math.cos(th), di[1] + r*math.sin(th))
        A = angles(p)
        rel = {k: (A[k] - A[(i, +1)]) % (2*math.pi) for k in A if k[0] != i}
        if prev is not None:
            for k in rel:
                # a label passes when its relative angle wraps through 0
                if abs(rel[k] - prev[k]) > math.pi: passed += 1
        prev = rel
    return passed

def dihedral_group(N, gens):
    # elements as (sign, shift): t -> sign*t + shift  (mod N)
    def comp(f, g):  # f after g
        return (f[0]*g[0], (f[0]*g[1] + f[1]) % N)
    G = {(1, 0)}
    frontier = [(1, 0)]
    while frontier:
        x = frontier.pop()
        for g in gens:
            y = comp(g, x)
            if y not in G: G.add(y); frontier.append(y)
    return G

def main():
    lines_out = []
    totA = totB = 0; failA = failB = 0
    cross_ok = cross_tot = 0; multi = narr = 0; chain_eq_2n = 0; chain_tot = 0
    for n in range(3, 11):
        for trial in range(40):
            nm = trial % 4
            L = random_arrangement(n, nm)
            if any(l[2] == 0 for l in L): continue
            # skip trivial arrangements (all through one point)
            if all(len(vertices_on(L, 0)) == 1 for _ in [0]) and len(vertices_on(L, 0)) == 1 \
               and all(len(vertices_on(L, i)) == 1 for i in range(n)):
                continue
            if any(len(v) >= 2 for v in vertices_on(L, 0).values()) or \
               any(len(v) >= 2 for i in range(n) for v in vertices_on(L, i).values()):
                multi += 1
            narr += 1
            for i, (A, B, m) in enumerate(check_AB(L)):
                totA += 1; failA += (not A); totB += 1; failB += (not B)
                chain_tot += 1; chain_eq_2n += (2*m == 2*n)
                if trial < 10:
                    c = half_turn_crossings(L, i)
                    cross_tot += 1; cross_ok += (c == n-1)
    lines_out.append(f"{narr} arrangements, n = 3..10, of which {multi} have a point of multiplicity >= 3")
    lines_out.append(f"A. sum (nu-1) = n-1 on every line: {totA-failA}/{totA} lines (n=3..10)")
    lines_out.append(f"B. chain of page reflections = rotation t -> t-(n-1) of Z/2n: {totB-failB}/{totB} (5 vertex orders each)")
    lines_out.append(f"C. realisable half-turn round delta_i: label (i,+) passes exactly n-1 others: {cross_ok}/{cross_tot}")
    lines_out.append(f"   chain length 2*m_i (vertices x2) equal to the page's p = 2n: {chain_eq_2n}/{chain_tot} (m_i <= n-1 always)")
    lines_out.append("D. subgroups of D_{2n} (order 4n), n = 2..20:")
    for n in range(2, 21):
        N = 2*n
        rot = (1, (-(n-1)) % N)
        r1 = len(dihedral_group(N, [rot]))
        r2 = len(dihedral_group(N, [(1, (-2*(n-1)) % N)]))
        v = len(dihedral_group(N, [rot, (-1, 0)]))            # reflection fixing a vertex
        e = len(dihedral_group(N, [rot, (-1, 0), (-1, 1)]))   # plus one through an edge midpoint
        lines_out.append(f"   n={n:2d}: index of <rot(n-1)> in rotations {N//r1}, of <rot(2(n-1))> {N//r2}; "
                         f"<rot, vertex refl> index {4*n//v}; with edge refl index {4*n//e}")
    print("\n".join(lines_out))

if __name__ == "__main__":
    main()
