# Certificates for lean/Grothendieck/EffectiveVenken.lean (Venken, CRAS 272 (1971), A1553-A1554, Cor. 3.1).
# Usage: python3 lean_cert.py OUTDIR  (writes OUTDIR/cert.json and OUTDIR/lean-data.txt, the Lean data blocks).
# Everything is over Z; every pivot is checked to be +-1, so the certificates hold over every commutative ring.
import itertools, sys, json
OUT=sys.argv[1]
from fractions import Fraction
V='MNXYZW'
def mono(s):
    e=[0]*6
    for ch in s: e[V.index(ch)]+=1
    return tuple(e)
rels=[mono(g) for g in ['MM','MN','NN','XXX','YYY','ZZZ','WWW','YZ','NY','MZ','NXY','MYW']]
for c in itertools.combinations_with_replacement('XYZW',3): rels.append(mono(''.join(c)))
def killed(e): return any(all(e[i]>=r[i] for i in range(6)) for r in rels)
def allmon(d):
    for c in itertools.combinations_with_replacement(range(6),d):
        e=[0]*6
        for i in c: e[i]+=1
        yield tuple(e)
basis=[]
for d in range(0,5):
    ms=sorted((e for e in allmon(d) if not killed(e)), reverse=True)
    basis+=ms
assert len(basis)==33
idx={e:i for i,e in enumerate(basis)}
deg=[sum(e) for e in basis]
NB=33; ZERO=NB
def addm(a,b): return tuple(x+y for x,y in zip(a,b))
mt=[[idx.get(addm(basis[i],basis[j]),ZERO) for j in range(NB)] for i in range(NB)]
for i in range(NB):
    for j in range(NB):
        if mt[i][j]==ZERO: assert killed(addm(basis[i],basis[j]))
I=lambda s: idx[mono(s)]
def diff(terms):  # sum c*(a⊗1 - 1⊗a)
    out=[]
    for s,c in terms: out+= [(I(s),0,c),(0,I(s),-c)]
    return out
gens=[diff([('M',1)]),diff([('N',1)]),diff([('MX',1)]),diff([('NW',1)]),diff([('MY',1),('NZ',-1)]),[(I('MXY'),I('W'),1)]]
gdeg=[1,1,2,2,2,4]
def norm(l):
    d={}
    for i,j,c in l:
        if i==ZERO or j==ZERO: continue
        d[(i,j)]=d.get((i,j),0)+c
    return {k:v for k,v in d.items() if v}
def mulpair(u,v,g): return norm([(mt[u][s],mt[v][t],c) for s,t,c in g])
def pairs(t): return [(u,v) for u in range(NB) for v in range(NB) if deg[u]+deg[v]==t]
class RREF:
    def __init__(s): s.rows={}  # pivot key -> row (pivot coef 1), fully reduced at the end
    def reduce(s,v):
        v={k:Fraction(c) for k,c in v.items()}
        for p in sorted(s.rows, reverse=True):
            if p in v and v[p]:
                c=v[p]
                for k,x in s.rows[p].items(): v[k]=v.get(k,0)-c*x
        return {k:c for k,c in v.items() if c}
    def insert(s,v):
        v=s.reduce_full(v)
        if not v: return False
        p=max(v); c=v[p]; assert abs(c)==1, c
        r={k:x/c for k,x in v.items()}
        # reduce existing rows
        for q in list(s.rows):
            if p in s.rows[q]:
                a=s.rows[q][p]; s.rows[q]={k:s.rows[q].get(k,0)-a*r.get(k,0) for k in set(s.rows[q])|set(r)}
                s.rows[q]={k:x for k,x in s.rows[q].items() if x}
        s.rows[p]=r; return True
    def reduce_full(s,v):
        v={k:Fraction(c) for k,c in v.items()}
        for p,r in s.rows.items():
            if p in v and v[p]:
                c=v[p]
                for k,x in r.items(): v[k]=v.get(k,0)-c*x
                v={k:x for k,x in v.items() if x}
        return v
def inverse(A):
    n=len(A); M=[row[:]+[Fraction(int(i==j)) for j in range(n)] for i,row in enumerate(A)]
    for c in range(n):
        r=next(r for r in range(c,n) if M[r][c]); M[c],M[r]=M[r],M[c]
        assert abs(M[c][c])==1
        pv=M[c][c]; M[c]=[x/pv for x in M[c]]
        for r in range(n):
            if r!=c and M[r][c]:
                a=M[r][c]; M[r]=[x-a*y for x,y in zip(M[r],M[c])]
    return [row[n:] for row in M]
def isint(x): return Fraction(x).denominator==1
psis={}; Fset=[]; Pset=[]
for d in range(1,4):
    E=RREF()
    for gi,g in enumerate(gens):
        if gdeg[gi]>d: continue
        for u,v in pairs(d-gdeg[gi]):
            w=mulpair(u,v,g)
            if w: E.insert(w)
    for r in E.rows.values(): assert all(isint(x) for x in r.values())
    nonpiv=[k for k in pairs(d) if k not in E.rows]
    Bd=[e for e in range(NB) if deg[e]==d]
    D={e:E.reduce_full(norm(diff_idx)) for e in Bd for diff_idx in [[(e,0,1),(0,e,-1)]]}
    # choose pivots among Bd: eliminate D rows
    piv={}  # column key -> (row combination over Bd, reduced vector)
    P=[];F=[]
    for e in Bd:
        v=dict(D[e]); t={e:Fraction(1)}
        for k,(rw,rt) in piv.items():
            if k in v and v[k]:
                c=v[k]
                for kk,x in rw.items(): v[kk]=v.get(kk,0)-c*x
                for kk,x in rt.items(): t[kk]=t.get(kk,0)-c*x
                v={a:b for a,b in v.items() if b}
        if v:
            k=max(v); c=v[k]; assert abs(c)==1
            piv[k]=({a:b/c for a,b in v.items()},{a:b/c for a,b in t.items()}); P.append(e)
        else: F.append(e)
    # functionals: psi_p = sum over columns C of Linv; solve D[P,C] L = I. Use columns C = pivot keys.
    C=list(piv)
    Mx=[[Fraction(D[p].get(k,0)) for k in C] for p in P]
    Linv=inverse(Mx)  # Mx * Linv = I => psi_p(v) = sum_k NF(v)_k Linv[k,p]
    for pi,p in enumerate(P):
        coef={k:Linv[ci][pi] for ci,k in enumerate(C) if Linv[ci][pi]!=0}
        psi={}
        for key in pairs(d):
            nf=E.reduce_full({key:1})
            val=sum(nf.get(k,0)*c for k,c in coef.items())
            if val: assert isint(val); psi[key]=int(val)
        psis[p]=(d,psi)
    Pset+=P; Fset+=F
    print('deg',d,'P',P,'F',F,'dim IV_d',len(E.rows),'nonpiv',len(nonpiv),file=sys.stderr)
def evp(psi,i,j): return psi.get((i,j),0)
# check
for p,(d,psi) in psis.items():
    for gi,g in enumerate(gens):
        for u in range(NB):
            for v in range(NB):
                w=mulpair(u,v,g); assert sum(c*evp(psi,a,b) for (a,b),c in w.items())==0
    for e in Pset:
        assert evp(psi,e,0)-evp(psi,0,e)==(1 if e==p else 0)
Mpf={(p,f):evp(psis[p][1],f,0)-evp(psis[p][1],0,f) for p in Pset for f in Fset}
vf={f:[(f,1)]+[(p,-Mpf[(p,f)]) for p in Pset if Mpf[(p,f)]] for f in Fset}
Fset=[0]+Fset if 0 not in Fset else Fset
print('F',Fset,file=sys.stderr)
for f in Fset:
    if f==0: continue
    print('v_f',' + '.join('%d*%s'%(c,''.join(V[i]*basis[e][i] for i in range(6))) for e,c in vf[f]),file=sys.stderr)
# J_4
E4=RREF()
jg=[]
for f in Fset:
    if f==0: continue
    g=[]
    for e,c in vf[f]: g+=[(e,0,c),(0,e,-c)]
    jg.append((f,g))
    for u,v in pairs(4-deg[f]):
        w=mulpair(u,v,g)
        if w: E4.insert(w)
target={(I('MXY'),I('W')):1}
nf=E4.reduce_full(target)
print('NF of mxy⊗w',nf,file=sys.stderr)
k0=[k for k,c in nf.items() if abs(c)==1][0]; s0=nf[k0]
phi={}
for key in pairs(4):
    val=E4.reduce_full({key:1}).get(k0,0)*s0
    if val: assert isint(val); phi[key]=int(val)
for f,g in jg:
    for u in range(NB):
        for v in range(NB):
            assert sum(c*phi.get(k,0) for k,c in mulpair(u,v,g).items())==0
assert phi.get((I('MXY'),I('W')),0)==1
print('sizes psi',[len(psis[p][1]) for p in Pset],'phi',len(phi),file=sys.stderr)
import json
json.dump(dict(basis=basis,mt=mt,P=Pset,F=Fset,psis={p:[(a,b,c) for (a,b),c in sorted(psis[p][1].items())] for p in Pset},
  vf={f:vf[f] for f in Fset if f},phi=[(a,b,c) for (a,b),c in sorted(phi.items())],rels=rels),open(sys.argv[1]+'/cert.json','w'))

# Membership certificates (invariants in B^R, symmetry, transitivity), by elimination tracking combinations.
# membership: express target (dict key->coef over pair indices) as sum c*(u,v)*g_k
def solve(target, cands, prod):
    # cands: list of labels; prod(label)-> dict ; Gaussian elimination tracking combos
    piv={}
    for lab in cands:
        v={k:Fraction(c) for k,c in prod(lab).items()}; t={lab:Fraction(1)}
        for k,(rv,rt) in piv.items():
            if v.get(k):
                c=v[k]
                for a,b in rv.items(): v[a]=v.get(a,0)-c*b
                for a,b in rt.items(): t[a]=t.get(a,0)-c*b
                v={a:b for a,b in v.items() if b}
        if v:
            k=max(v); c=v[k]
            rv={a:b/c for a,b in v.items()}; rt={a:b/c for a,b in t.items()}
            # full reduce others
            for k2 in list(piv):
                rv2,rt2=piv[k2]
                if rv2.get(k):
                    c2=rv2[k]
                    rv2={a:rv2.get(a,0)-c2*rv.get(a,0) for a in set(rv2)|set(rv)}; rt2={a:rt2.get(a,0)-c2*rt.get(a,0) for a in set(rt2)|set(rt)}
                    piv[k2]=({a:b for a,b in rv2.items() if b},{a:b for a,b in rt2.items() if b})
            piv[k]=(rv,rt)
    v={k:Fraction(c) for k,c in target.items()}; t={}
    for k,(rv,rt) in piv.items():
        if v.get(k):
            c=v[k]
            for a,b in rv.items(): v[a]=v.get(a,0)-c*b
            for a,b in rt.items(): t[a]=t.get(a,0)+c*b
            v={a:b for a,b in v.items() if b}
    assert not v, v
    t={a:b for a,b in t.items() if b}
    assert all(b.denominator==1 for b in t.values()), t
    return {a:int(b) for a,b in t.items()}
out={}
def cert2(target,d):
    cands=[(k,u,v) for k in range(6) if gdeg[k]<=d for (u,v) in pairs(d-gdeg[k])]
    return solve(target,cands,lambda l: mulpair(l[1],l[2],gens[l[0]]))
for name,terms in [('MXX',[('MXX',1)]),('MYY',[('MYY',1)]),('NZZ',[('NZZ',1)]),('NWW',[('NWW',1)])]:
    tg=norm(diff([(s,c) for s,c in terms])); c=cert2(tg,3); out[name]=c; print(name,len(c),c)
tg={(I('W'),I('MXY')):1}; c=cert2(tg,4); out['sym']=c; print('sym',len(c),c)
def norm3(l):
    d={}
    for i,j,k,c in l:
        if ZERO in (i,j,k): continue
        d[(i,j,k)]=d.get((i,j,k),0)+c
    return {k:v for k,v in d.items() if v}
g3=[]
for k in range(6):
    g3.append([(s,t,0,c) for s,t,c in gens[k]]); g3.append([(0,s,t,c) for s,t,c in gens[k]])
g3deg=[gdeg[k//2] for k in range(12)]
def triples(t): return [(a,b,c) for a in range(NB) for b in range(NB) for c in range(NB) if deg[a]+deg[b]+deg[c]==t]
def mul3(a,b,c,g): return norm3([(mt[a][s],mt[b][t],mt[c][u],cc) for s,t,u,cc in g])
# restrict: only use triples whose first/third parts are plausible; just try full
cands=[(k,)+tr for k in range(12) if g3deg[k]<=4 for tr in triples(4-g3deg[k])]
print(len(cands))
c=solve({(I('MXY'),0,I('W')):1},cands,lambda l: mul3(l[1],l[2],l[3],g3[l[0]]))
print('trans',len(c),c)
out['trans']=c
# vf certs for nz-my? it's -gen5; m,n,mx,nw gens. only cubics need certs
L=[]
cd=json.load(open(OUT+'/cert.json'))
def lpairs(l): return '[' + ', '.join('((%d, %d), %d)'%(a,b,c) for a,b,c in l) + ']'
def E(e): return '⟨%s⟩'%', '.join(map(str,e))
L.append('def bas : List Exp :=\n  [' + ',\n   '.join(', '.join(E(tuple(e)) for e in cd['basis'][i:i+6]) for i in range(0,33,6)) + ']')
L.append('def psiData : List (ℕ × List ((ℕ × ℕ) × ℤ)) :=\n  [' + ',\n   '.join('(%d, %s)'%(int(p),lpairs(l)) for p,l in cd['psis'].items()) + ']')
L.append('def phi : List ((ℕ × ℕ) × ℤ) :=\n  ' + lpairs(cd['phi']))
vf={0:[(0,1)]}; vf.update({int(f):l for f,l in cd['vf'].items()})
L.append('def vfData : List (ℕ × List (ℕ × ℤ)) :=\n  [' + ',\n   '.join('(%d, [%s])'%(f,', '.join('(%d, %d)'%(e,c) for e,c in l)) for f,l in vf.items()) + ']')
def lc(d,n): return '[' + ', '.join('((' + ', '.join(map(str,k)) + '), %d)'%v for k,v in sorted(d.items())) + ']'
for nm in ['MXX','MYY','NZZ','NWW','sym']:
    L.append('-- %s\n%s'%(nm, lc(out[nm],3)))
L.append('-- trans\n'+lc(out['trans'],4))
open(OUT+'/lean-data.txt','w').write('\n\n'.join(L))
