# Usage: gh pr diff N --repo leanprover-community/mathlib4 > diffs/N.diff for each PR, then
#   python3 stylecheck.py diffs/
# Flags style-guide slips on the added lines of each diff; "check" items need a human look.
import sys,re,os
for fn in sorted(os.listdir(sys.argv[1])):
    n=fn[:-5]; cur=None; ln=0; out=[]; added=[]
    for l in open(os.path.join(sys.argv[1],fn)):
        if l.startswith('+++ '): cur=l[6:].strip(); continue
        m=re.match(r'@@ -\d+(?:,\d+)? \+(\d+)',l)
        if m: ln=int(m.group(1))-1; continue
        if l.startswith('-') or cur is None or not cur.endswith('.lean'): 
            continue
        ln+=1 if not l.startswith('\\') else 0
        if not l.startswith('+'): continue
        t=l[1:].rstrip('\n'); added.append((cur,ln,t))
    prev=None
    for i,(f,k,t) in enumerate(added):
        c=t.split('--')[0]
        def rep(msg): out.append(f"  {os.path.basename(f)}:{k}: {msg}: {t.strip()[:90]}")
        if len(t)>100: rep('>100 chars')
        if re.search(r'\bfun\b[^↦]*=>',c): rep('fun =>')
        if 'λ' in c: rep('lambda')
        if re.search(r'\s\$\s',c): rep('$')
        if re.search(r'←\S',c): rep('← no space')
        if t.strip()=='by': rep('by alone')
        if re.match(r'\s+:=',t): rep(':= at line start')
        if re.match(r'\s+(\+|\*|∧|∨|→|↔|=|≤|<)\s',t) and not t.strip().startswith(('_','·')): rep('operator at line start')
        if t.rstrip()!=t: rep('trailing ws')
        if re.search(r'\(by [^()]*\)\s*$',c) and False: rep('(by)')
        if re.search(r'\bsimp only \[[^\]]*\]\s*$',c):
            nxt=added[i+1][2] if i+1<len(added) else ''
            if (nxt.strip()=='' or not nxt.startswith(' ') or len(nxt)-len(nxt.lstrip()) < len(t)-len(t.lstrip())) : rep('terminal simp only? (check)')
        if re.match(r'^\s*\(h\w* : [^)]*∧',c): rep('conjunction hypothesis?')
    # empty lines inside declarations: blank added line followed by indented line
    for i in range(1,len(added)-1):
        f,k,t=added[i]
        if t.strip()=='' and added[i+1][2].startswith('  ') and added[i-1][2].startswith('  ') and added[i+1][1]==k+1: out.append(f"  {os.path.basename(f)}:{k}: blank line inside declaration?")
    if out: print(n); print('\n'.join(out))
