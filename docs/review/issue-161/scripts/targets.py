import re,sys
s=open(sys.argv[1]).read()
# split into declarations with preceding docstring
pat=re.compile(r'(/--(.*?)-/\s*)?(?:@\[[^\]]*\]\s*)?((?:noncomputable |private |protected )*(theorem|lemma|def|abbrev|structure|class|instance|opaque|axiom)\s+([^\s:({\[]+))',re.S)
ms=list(pat.finditer(s))
for i,m in enumerate(ms):
  end=ms[i+1].start() if i+1<len(ms) else len(s)
  body=s[m.end():end]
  if 'sorry' not in body: continue
  doc=re.sub(r'\s+',' ',(m.group(2) or '')).strip()
  print(f"{m.group(4)} {m.group(5)} :: {doc[:260]}")
