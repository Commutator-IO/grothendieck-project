import re,os,json,sys
root='gap'
DECL=re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|public|nonrec|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|instance|example|axiom|opaque)\b\s*([^\s:({\[]*)')
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
        files.append({'path':rel,'lines':len(L),'code':code,'decls':decls})
files.sort(key=lambda x:x['path'])
json.dump({'commit':sys.argv[1],'files':files},open('viz/data.json','w'),separators=(',',':'))
tot=sum(len(f['decls']) for f in files)
print(len(files),'files',sum(f['lines'] for f in files),'lines',tot,'decls')
from collections import Counter
print(Counter(d['k'] for f in files for d in f['decls']))
