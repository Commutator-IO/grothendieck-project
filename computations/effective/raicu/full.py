# Full check on the finite k-scheme Z = V(f1^3, f2^3, f3^2) (length 27): compare I_Z and J_{B_Z} in every degree.
import sys
P=int(sys.argv[1])
sys.argv=[sys.argv[0],str(P)]
exec(open('check.py').read().split('# ring k[x1')[0])
n=4
def X(i,b): return var(2*b+i,n)
def pw(a,k):
    r={tuple([0]*n):F(1)}
    for _ in range(k): r=mul(r,a)
    return r
def f1(b): return mul(X(0,b),X(0,b))
def f2(b): return add(mul(X(0,b),X(1,b)),mul(X(1,b),X(1,b)),-1)
def f3(b): return mul(mul(X(1,b),X(1,b)),X(1,b))
def K(b): return [pw(f1(b),3),pw(f2(b),3),pw(f3(b),2)]
w=add(mul(X(0,0),X(1,1)),mul(X(1,0),X(0,1)),-1); f=mul(w,pw(X(1,1),3))
I=[add(f1(0),f1(1),-1),add(f2(0),f2(1),-1),add(f3(0),f3(1),-1),f]
KK=K(0)+K(1)
IZ=I+KK
# invariants of A_Z in degree d (1..7): a in k[x]_d with a(x)-a(y) in (I_Z)_d
Bg=[]
ms_by_d={}
for d in range(1,8):
    ms=[m for m in monos(n,d) if m[2]==m[3]==0]
    D=[add({m:F(1)},{(0,0,m[0],m[1]):F(1)},-1) for m in ms]
    Id=homog_part(IZ,n,d)
    rows=[(v,{}) for v in Id]+[(v,{j:F(1)}) for j,v in enumerate(D)]
    piv={}
    for v,t in rows:
        v=dict(v);t=dict(t)
        while True:
            mm=[m for m in v if m in piv]
            if not mm: break
            m=mm[0];c=v[m];wv,tw=piv[m]
            v=add(v,{k:norm(c*x) for k,x in wv.items()},-1);t=add(t,{k:norm(c*x) for k,x in tw.items()},-1)
        if v:
            m=max(v);c=inv(v[m]);piv[m]=({k:norm(c*x) for k,x in v.items()},{k:norm(c*x) for k,x in t.items()})
        elif t:
            Bg.append(add({ms[j]:c for j,c in t.items()},{(0,0,ms[j][0],ms[j][1]):c for j,c in t.items()},-1))
print('invariant differences found:',len(Bg))
bad=[]
for d in range(1,15):
    a=rank_and_member(homog_part(IZ,n,d)); b=rank_and_member(homog_part(Bg+KK,n,d))
    # J_B + K subset I_Z always; compare dims
    if a!=b: bad.append((d,a,b))
print('degrees where I_Z != J_B + K (d, dim I_Z, dim J_B+K):',bad)
