import json,random,sys,collections
W=sys.argv[1]
r=json.load(open(W+'/pop.json')); sz=json.load(open(W+'/sizes.json'))
Q=[('illegible',5),('unrelated',5),('administrative',8),("others' typescript",18),('gap only (no header mention)',7),
   ('skipped, reason not classifiable',5),('printed/published',3),('duplicate',2),('verso (unspecified)',2),('cover/wrapper',2),('blank',4)]
rng=random.Random(66)
per=collections.Counter(); out=[]
for name,q in Q:
    s=sorted([x for x in r if x['reason']==name],key=lambda x:(x['cote'],x['page']))
    rng.shuffle(s)
    got=0
    for lim in (80e6,250e6):
        for x in s:
            if got>=q: break
            if x in out: continue
            if sz[x['cote']][0]>=lim or per[x['cote']]>=3: continue
            out.append(x); per[x['cote']]+=1; got+=1
print(len(out),len(per),sum(sz[c][0] for c in per)/1e6)
json.dump(out,open(W+'/sample.json','w'),ensure_ascii=False,indent=0)
for c in sorted(per,key=lambda c:[int(t) for t in c.split('-')]):
    print(c,round(sz[c][0]/1e6),[ (x['page'],x['reason'][:6]) for x in out if x['cote']==c])
