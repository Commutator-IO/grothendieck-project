import os,re,sys,json
root,ip=sys.argv[1],sys.argv[2]; idx=json.load(open(ip)); n=0
pat=re.compile(r'^add_to_stacks\s+([0-9A-Z]{4})((?:\s+"[^"]*")*)\s*([^\s"]*)',re.M)
for d,_,fs in os.walk(root):
  for f in fs:
    if not f.endswith('.lean'): continue
    p=os.path.join(d,f); rel=os.path.relpath(p,root); s=open(p,errors='replace').read()
    for m in pat.finditer(s):
      idx.setdefault(m.group(1),[]).append([rel,s.count('\n',0,m.start())+1,'add_to_stacks '+(m.group(3) or '(Mathlib)')]); n+=1
json.dump(idx,open(ip,'w')); print(n)
