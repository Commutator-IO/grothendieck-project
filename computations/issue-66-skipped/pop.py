import re,glob,os,json,sys
rows=[]
def natkey(c): return [int(x) for x in re.findall(r'\d+',c)]
cat=open('src/content/catalogue.ts').read()
# folder page counts
pc={}
for m in re.finditer(r'"cote":\s*"([^"]+)"[^}]*?"pages":\s*(\d+)',cat,re.S): pc[m.group(1)]=int(m.group(2))
CL=[('blank',r'\bblank|\bempty\b|vierge|\bblanche?s?\b'),
    ("others' typescript",r"typescript|typed|typewritten|dactylograph|mimeograph|frappe|carbon|stencil|polycopi|ronéo|tapuscrit"),
    ('administrative',r"administrat|circular|circulaire|letterhead|\bform\b|formulaire|invoice|envelope|memo|bureaucr|convocation|\bletter\b|minist|university|universit|\bCNRS\b|procès|bulletin|timetable|notice"),
    ('printed/published',r"galley|offprint|printed|proof sheet|épreuve|published|preprint|tiré à part|listing|computer|print-out|printout"),
    ('duplicate',r"duplicat|photocop|\bcopy\b|copies|xerox|same as|repeat|doublon"),
    ('illegible',r"illegible|unreadable|illisible|faint|show-through|shows through"),
    ('unrelated',r"unrelated|not the mathematics|no mathematics|sans rapport|not his|other hand|another hand|someone else"),
    ('cover/wrapper',r"cover|wrapper|chemise|kraft|folder label|title leaf|title page|divider|intercalaire"),
    ('verso (unspecified)',r"verso|\bback\b|backs\b"),
    ]
def mentions(text,n):
    # numbers and ranges
    for m in re.finditer(r'(?<![\d.])(\d{1,3})\s*(?:-|–|—|to|à)\s*(\d{1,3})(?![\d])',text):
        a,b=int(m.group(1)),int(m.group(2))
        if a<=n<=b and b-a<60: return True
    return re.search(r'(?<![\d.,-])%d(?![\d])'%n,text) is not None
for f in sorted(glob.glob('transcripts/*/batch-*.fr.tex'),key=lambda p:(natkey(p.split('/')[1]),p)):
    cote=f.split('/')[1]
    if cote.startswith('_'): continue
    L=open(f,encoding='utf-8').read().split('\n')
    bn=int(re.search(r'batch-(\d+)',f).group(1))
    head=' '.join(l.lstrip('% ') for l in L[:8])
    m=re.search(r'pages?\s+(\d+)\s*(?:-|–|—|to)\s*(\d+)',head)
    if m: a,b=int(m.group(1)),int(m.group(2))
    else:
        m=re.search(r'\(page (\d+)',head)
        if m: a=b=int(m.group(1))
        else:
            a=(bn-1)*20+1; b=min(bn*20,pc.get(cote,bn*20))
    exp=((bn-1)*20+1, min(bn*20,pc.get(cote,bn*20)))
    if (a,b)!=exp: sys.stderr.write(f'range {f}: header {a}-{b} vs expected {exp}\n')
    pages=set()
    for i,l in enumerate(L):
        if l.lstrip().startswith('%'): continue
        for m in re.finditer(r'\\page\{(\d+)\}',l): pages.add(int(m.group(1)))
    # comment lines with index
    com=[(i+1,l.lstrip()[1:].strip()) for i,l in enumerate(L) if l.lstrip().startswith('%')]
    # build sentences: join consecutive comment lines; split on sentence ends, keep first line no
    sents=[]; cur=[]; curline=None; prev=None
    def flush():
        global cur,curline
    buf='';start=None
    for ln,t in com:
        if t=='' or (prev is not None and ln!=prev+1):
            if buf: sents.append((start,buf)); buf='';start=None
        prev=ln
        if t=='': continue
        parts=re.split(r'(?<=[.;])\s+(?=[A-ZÉ«(])',t)
        for k,p in enumerate(parts):
            if start is None: start=ln
            buf=(buf+' '+p).strip()
            if k<len(parts)-1 or re.search(r'[.;]$',p):
                if k<len(parts)-1 or True:
                    if re.search(r'[.;]$',buf) and not re.search(r'\b(p|pp|cf|n°|no|Prop|Th|Def|§)\.$',buf):
                        sents.append((start,buf)); buf='';start=None
    if buf: sents.append((start,buf))
    for n in range(a,b+1):
        if n in pages: continue
        hit=[(ln,s) for ln,s in sents if mentions(s,n) and re.search(r'skip|absent|blank|not transcribed|omitted|left out|typescript|typed|unrelated|verso|administr|illegible|nothing|no mathematics|summar|duplic|cover|printed|galley|not his|letter',s,re.I)]
        # prefer sentences with skip words
        pref=[h for h in hit if re.search(r'skip|absent|not transcribed|omitted|left out|blank',h[1],re.I)] or hit
        if pref:
            ln,s=pref[0]
            # narrow: clause around the number
            reason=None
            # clause: split on ';' or ', page' 
            cl=[c for c in re.split(r';|(?<=\))\s*,\s*(?=(?:pages? )?\d)|:\s+(?=pages?\b)',s) if mentions(c,n)]
            clause=cl[0] if cl else s
            for name,rx in CL:
                if re.search(rx,clause,re.I): reason=name;break
            if not reason:
                for name,rx in CL:
                    if re.search(rx,s,re.I): reason=name;break
            reason=reason or 'skipped, reason not classifiable'
            txt=clause.strip()
            if len(txt)>230: txt=txt[:230]+'…'
        else:
            ln=1; reason='gap only (no header mention)'; txt=''
        rows.append(dict(cote=cote,page=n,reason=reason,file=f,line=ln,text=txt))
json.dump(rows,open(sys.argv[1],'w'),ensure_ascii=False,indent=0)
from collections import Counter
c=Counter(r['reason'] for r in rows)
print(len(rows),len(set(r['cote'] for r in rows)))
for k,v in c.most_common(): print(v,k)
