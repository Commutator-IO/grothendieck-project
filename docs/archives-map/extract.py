import re,os,json,sys
root='gap'
DECL=re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|public|nonrec|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|instance|example|axiom|opaque)\b\s*([^\s:({\[]*)')
IMP=re.compile(r'^(?:public\s+)?import\s+(\S+)',re.M)
files=[]
for d,_,fs in os.walk(root):
    if '.lake' in d or '/.git' in d or d.endswith('.git'): continue
    for f in fs:
        if not f.endswith('.lean'): continue
        p=os.path.join(d,f); rel=os.path.relpath(p,root)
        L=open(p,encoding='utf8').read().split('\n')
        decls=[]; ns=[]
        for i,l in enumerate(L,1):
            m=DECL.match(l)
            if m:
                k=m.group(1); k={'lemma':'theorem'}.get(k,k)
                decls.append({'k':k,'n':m.group(2) or '_','l':i})
        for j,dc in enumerate(decls):
            end=(decls[j+1]['l']-1) if j+1<len(decls) else len(L)
            dc['len']=max(1,end-dc['l']+1)
        code=sum(1 for l in L if l.strip() and not l.strip().startswith('--'))
        src='\n'.join(L)
        st=sorted({m for m in IMP.findall(src) if m.startswith('Stacks')})
        files.append({'path':rel,'lines':len(L),'code':code,'decls':decls,'st':st})
files.sort(key=lambda x:x['path'])
# sizes in bytes of the Stacks modules imported, from `stacks_sizes.json` (path -> bytes, by the GitHub contents API at the pinned revision)
ss=json.load(open('viz/stacks_sizes.json')) if os.path.exists('viz/stacks_sizes.json') else {}
mods={m for f in files for m in f['st']}
stacks={m:ss.get(m.replace('.','/')+'.lean',0) for m in mods}
json.dump({'commit':sys.argv[1],'stacksRev':sys.argv[2] if len(sys.argv)>2 else '','stacks':stacks,'files':files},open('viz/data.json','w'),separators=(',',':'))
tot=sum(len(f['decls']) for f in files)
print(len(files),'files',sum(f['lines'] for f in files),'lines',tot,'decls')
from collections import Counter
print(Counter(d['k'] for f in files for d in f['decls']))
