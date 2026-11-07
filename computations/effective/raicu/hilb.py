import sys
sys.argv=[sys.argv[0],'2']
exec(open('check.py').read().split('# ring k[x1')[0])
n=2
x1=var(0,2);x2=var(1,2)
g1=mul(x1,x1); g2=add(mul(x1,x2),mul(x2,x2),-1); g3=mul(mul(x2,x2),x2)
def pw(a,k):
    r={(0,0):F(1)}
    for _ in range(k): r=mul(r,a)
    return r
for K,name in [([pw(g1,3),pw(g2,3),pw(g3,2)],'f1^3,f2^3,f3^2'),([pw(g1,3),pw(g2,3),pw(g3,3)],'f1^3,f2^3,f3^3')]:
    tot=0;hf=[]
    for d in range(0,40):
        h=(d+1)-rank_and_member(homog_part(K,2,d)) if d>=1 else 1
        hf.append(h); tot+=h
        if d>8 and h==0: break
    print(name,'Hilbert function',hf,'dim',tot)
