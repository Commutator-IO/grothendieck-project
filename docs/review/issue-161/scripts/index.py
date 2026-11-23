import os,re,sys,json
root=sys.argv[1]; out={}
attr=re.compile(r'@\[((?:[^\[\]"]|"[^"]*"|\[[^\]]*\])*)\]',re.S)
tag=re.compile(r'\bstacks\s+([0-9A-Z]{4})\b')
decl=re.compile(r'\b(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|noncomputable def|irreducible_def)\s+([^\s:({\[]+)')
for d,_,fs in os.walk(root):
  for f in fs:
    if not f.endswith('.lean'): continue
    p=os.path.join(d,f); rel=os.path.relpath(p,root)
    s=open(p,encoding='utf-8',errors='replace').read()
    for m in attr.finditer(s):
      tags=tag.findall(m.group(1))
      if not tags: continue
      dm=decl.search(s,m.end(),m.end()+600)
      name=dm.group(1) if dm else '?'
      line=s.count('\n',0,m.start())+1
      for t in tags: out.setdefault(t,[]).append([rel,line,name])
json.dump(out,open(sys.argv[2],'w'))
print(len(out),sum(len(v) for v in out.values()))
