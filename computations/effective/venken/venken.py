# Venken, CRAS 272 (1971) A1553-A1554: B = K[M,N,X,Y,Z,W]/I, A = K[m, n, mx, nw, my-nz] ⊂ B,
# R = V(J) with J = (a⊗1 - 1⊗a, a in A) + (mxy⊗w) ⊂ B⊗_K B  (his Corollary 3.1).
# Checks that R is an equivalence relation and compares I_R with J_{B^R} degree by degree.
# Usage: python3 venken.py P   (P = 0 for Q, else a prime).  Optional 2nd arg 'simple' uses footnote (1)'s ideal.
import sys, itertools
from fractions import Fraction
P=int(sys.argv[1]); SIMPLE=len(sys.argv)>2
def nm(c): return c%P if P else c
def one(): return 1 if P else Fraction(1)
def inv(c): return pow(c,P-2,P) if P else 1/c
V='MNXYZW'
def mono(s):
    e=[0]*6
    for ch in s: e[V.index(ch)]+=1
    return tuple(e)
gens=['MM','MN','NN','XXX','YYY','ZZZ','WWW'] if SIMPLE else ['MM','MN','NN','XXX','YYY','ZZZ','WWW','YZ','NY','MZ','NXY','MYW']
gens=[mono(g) for g in gens]
for c in itertools.combinations_with_replacement('XYZW',3): gens.append(mono(''.join(c)))
def killed(e): return any(all(e[i]>=g[i] for i in range(6)) for g in gens)
def allmon(d):
    for c in itertools.combinations_with_replacement(range(6),d):
        e=[0]*6
        for i in c: e[i]+=1
        yield tuple(e)
basis=[e for d in range(0,8) for e in allmon(d) if not killed(e)]
print('dim B =',len(basis), ' max degree', max(map(sum,basis)))
k=None
def red(p,ncop):  # p: dict of tuple(6*ncop)->coef; drop monomials killed in some copy
    return {m:c for m,c in p.items() if c and not any(killed(m[6*i:6*i+6]) for i in range(ncop))}
def mul(a,b):
    r={}
    for m1,c1 in a.items():
        for m2,c2 in b.items():
            m=tuple(x+y for x,y in zip(m1,m2)); r[m]=nm(r.get(m,0)+c1*c2)
    return {m:c for m,c in r.items() if c}
def add(a,b,s=1):
    r=dict(a)
    for m,c in b.items(): r[m]=nm(r.get(m,0)+s*c)
    return {m:c for m,c in r.items() if c}
def emb(e,i,ncop):  # monomial e of copy i
    t=[0]*(6*ncop); t[6*i:6*i+6]=e; return tuple(t)
def poly(terms,i,ncop): return {emb(mono(s),i,ncop):nm(c*one()) for s,c in terms}
Agens=[[('M',1)],[('N',1)],[('MX',1)],[('NW',1)],[('MY',1),('NZ',-1)]]
def Rgens(i,j,ncop):
    g=[add(poly(a,i,ncop),poly(a,j,ncop),-1) for a in Agens]
    g.append(mul(poly([('MXY',1)],i,ncop),poly([('W',1)],j,ncop)))
    return g
def span(gs,ncop,d):
    out=[]
    for g in gs:
        dg=sum(next(iter(g)))
        if dg>d: continue
        for c in itertools.combinations_with_replacement(range(6*ncop),d-dg):
            e=[0]*(6*ncop)
            for i in c: e[i]+=1
            v=red(mul(g,{tuple(e):one()}),ncop)
            if v: out.append(v)
    return out
PIVP=set()
def _fac(n):
    n=abs(int(n)); f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f
def note(c):
    if not P: PIVP.update(_fac(c.numerator)|_fac(c.denominator))
class Elim:
    def __init__(s): s.piv={}
    def reduce(s,v):
        v=dict(v)
        while True:
            ms=[m for m in v if m in s.piv]
            if not ms: return v
            m=ms[0]; c=v[m]; v=add(v,{k:nm(c*x) for k,x in s.piv[m].items()},-1)
    def insert(s,v):
        v=s.reduce(v)
        if not v: return False
        m=max(v); note(v[m]); c=inv(v[m]); s.piv[m]={k:nm(c*x) for k,x in v.items()}; return True
def member(gs,ncop,g):
    d=sum(next(iter(g))); E=Elim()
    for v in span(gs,ncop,d): E.insert(v)
    return not E.reduce(red(g,ncop))
# equivalence relation: reflexive (I_R in kernel of multiplication: generators vanish on diagonal), symmetric, transitive
print('symmetric:', all(member(Rgens(0,1,2),2,g) for g in Rgens(1,0,2)))
print('transitive:', all(member(Rgens(0,1,3)+Rgens(1,2,3),3,g) for g in Rgens(0,2,3)))
# invariants B^R and comparison
IR=Rgens(0,1,2); Bdiff=[]; maxd=max(map(sum,basis))
for d in range(1,maxd+1):
    E=Elim()
    for v in span(IR,2,d): E.insert(v)
    ms=[e for e in basis if sum(e)==d]
    # kernel of b -> class of b(x)-b(y) modulo (I_R)_d
    rows=[]; Ek={}
    vecs=[E.reduce(red(add({emb(e,0,2):one()},{emb(e,1,2):one()},-1),2)) for e in ms]
    # solve linear dependencies among vecs
    piv={}
    for j,v in enumerate(vecs):
        v=dict(v); t={j:one()}
        while True:
            mm=[m for m in v if m in piv]
            if not mm: break
            m=mm[0]; c=v[m]; wv,tw=piv[m]
            v=add(v,{k:nm(c*x) for k,x in wv.items()},-1); t=add(t,{k:nm(c*x) for k,x in tw.items()},-1)
        if v:
            m=max(v); note(v[m]); c=inv(v[m]); piv[m]=({k:nm(c*x) for k,x in v.items()},{k:nm(c*x) for k,x in t.items()})
        else:
            b={ms[i]:c for i,c in t.items()}
            Bdiff.append(add({emb(e,0,2):c for e,c in b.items()},{emb(e,1,2):c for e,c in b.items()},-1))
print('dim B^R (incl. constants) =',1+len(Bdiff))
bad=[]
for d in range(1,2*maxd+1):
    E1=Elim(); a=sum(E1.insert(v) for v in span(IR,2,d))
    E2=Elim(); b=sum(E2.insert(v) for v in span(Bdiff,2,d))
    if a!=b: bad.append((d,a,b))
print('degrees where I_R != J_{B^R} (d, dim I_R, dim J):',bad)
w=IR[-1]; E2=Elim()
for v in span(Bdiff,2,4): E2.insert(v)
print('mxy⊗w in J_{B^R}:', not E2.reduce(red(w,2)))
if not P: print('primes dividing a pivot over Q:', sorted(PIVP))
