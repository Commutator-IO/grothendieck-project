#!/usr/bin/env python3
"""
The PDF edition of Gaeta's notes for grothendieck-transcripts (#167): the nine batch files of
transcripts-gaeta/ag/ joined into one file, with the front matter set by LaTeX itself, in the
typescript's page order: a title page and a half-title (pages 1-2), a generated table of contents
(pages 3-4, with the typist's printed page numbers), and the bibliography as a `thebibliography`
(pages 6-7). The words are those of the batches; only the structure changes.

    python3 scripts/gaeta-edition.py <transcripts-repo>     writes <repo>/gaeta/ag/ag.en.tex
"""
import glob, os, re, sys

SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'transcripts-gaeta')
OUT = sys.argv[1]

TITLEPAGES = r"""\begin{titlepage}
\centering
\page{1}
\vspace*{2.2cm}
{\Large\scshape Alexander Grothendieck\par}
\vspace{1.6cm}
{\Huge\bfseries Introduction to\\[4pt] Functorial Algebraic Geometry\par}
\vspace{1cm}
{\Large Part 1\par}
{\Large\itshape Affine algebraic geometry\par}
\vspace{1.6cm}
{\large Lecture notes written by\par}
{\LARGE Federico Gaeta\par}
\vfill
{\large State University of New York at Buffalo\par}
{\large Department of Mathematics\par}
\end{titlepage}

\begin{titlepage}
\centering
\page{2}
\vspace*{3cm}
{\large\itshape INTRODUCTION\\[3pt] TO\\[3pt] FUNCTORIAL ALGEBRAIC GEOMETRY\par}
\vspace{1cm}
After a Summer course by\par
\vspace{4pt}
{\large\itshape A. G R O T H E N D I E C K\par}
\vspace{1.4cm}
VOL. I\par
\vspace{4pt}
{\large\itshape AFFINE ALGEBRAIC GEOMETRY\par}
\vspace{1.4cm}
Notes written by\par
\vspace{4pt}
{\large F. GAETA\par}
\vfill
SUNY at Buffalo\par
Department of Mathematics\par
\end{titlepage}

\pagerange{3}{4}
\tableofcontents
\clearpage
"""

def strip_marks(t):
    for _ in range(3):
        t = re.sub(r'\\(?:uncertain|supplied|add|struck|ill)\{((?:[^{}]|\{[^{}]*\})*)\}', r'\1', t)
    t = re.sub(r'\\(?:note|drawing)\{(?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*\}', '', t)
    return re.sub(r'\s+', ' ', t).strip()

def bibliography(block):
    """Entries of the printed bibliography (blank-line separated), as \\bibitem's."""
    block = re.sub(r'\\note\{[^}]*\}\n*', '', block)
    block = re.sub(r'^Quoted as\s*\n', '', block, flags=re.M)
    marks = re.findall(r'\\page\{\d+\}\s*\\pagehead\{[^}]*\}', block)
    chunks = re.split(r'\n\s*\n', block.strip())
    items = []
    for c in chunks:
        m = re.fullmatch(r'(\\page\{\d+\}\s*\\pagehead\{[^}]*\})', c.strip())
        if m:
            items.append(('mark', m.group(1)))
            continue
        # a page mark may stand in front of an entry
        lead = ''
        pm = re.match(r'(\\page\{\d+\}\s*\\pagehead\{[^}]*\})\s*(.*)', c, flags=re.S)
        if pm:
            items.append(('mark', pm.group(1)))
            c = pm.group(2)
        labels = re.findall(r' --- ([^\n]+)', c)
        text = re.sub(r' --- [^\n]+', '', c).strip()
        lab = labels[0].split(';')[0].strip() if labels else None
        extra = '; '.join(l.strip() for l in labels[1:]) if len(labels) > 1 else ''
        if labels and ';' in labels[0]:
            extra = '; '.join(x.strip() for x in labels[0].split(';')[1:]) + ('; ' + extra if extra else '')
        items.append(('item', lab, text, extra))
    out = [r'\begin{thebibliography}{ATIYAH-MACDONALD-LONGEST}']
    n = 0
    for it in items:
        if it[0] == 'mark':
            out.append(it[1])
            continue
        n += 1
        _, lab, text, extra = it
        if not lab:
            first = re.sub(r'[\\$^{}]|ulcorner|lrcorner', '', text.split(',')[0]).strip().split(':')[0].strip()
            lab = first or f'ref{n}'
        text = re.sub(r'\n(?=\\emph\{|\.\.\.\.\.\.)', r' \\\\\n', text)
        tail = f' \\hfill{{\\small(also quoted as: {extra})}}' if extra else ''
        out.append(f'\\bibitem[{lab}]{{gaeta{n}}}\n{text}{tail}\n')
    out.append(r'\end{thebibliography}')
    return '\n'.join(out)

def build():
    fs = sorted(glob.glob(os.path.join(SRC, 'ag', 'batch-*.en.tex')))
    parts = []
    for f in fs:
        s = open(f).read(); b = s.index('\\begin{document}'); e = s.rindex('\\end{document}'); head = s[:b]; hl = head.split('\n')
        n = int(re.search(r'batch-(\d+)', f).group(1))
        m = re.search(r'\\pages\{(\d+)\}\{(\d+)\}', head)
        mp = os.path.join(SRC, 'ag', 'drawings', f'batch-{n:02d}.en.map.tex')
        mapping = ''.join(re.findall(r'\\grothDrawingFile\{\d+\}\{[^}]*\}', open(mp).read())) if os.path.exists(mp) else ''
        parts.append(dict(prov=[l for l in hl if re.match(r'% (Pass|Revised):', l)],
                          meta=hl[[i for i, l in enumerate(hl) if not l.startswith('%')][0]:],
                          body=s[b + 16:e].strip(), a=int(m.group(1)), b=int(m.group(2)), map=mapping))
    first, last = parts[0]['a'], parts[-1]['b']
    meta = [l for l in parts[0]['meta'] if not l.strip().startswith(('\\batch{', '\\watermark{'))]
    meta = [re.sub(r'\\pages\{\d+\}\{\d+\}', f'\\\\pages{{{first}}}{{{last}}}', l) for l in meta]
    while meta and not meta[-1].strip(): meta.pop()
    # no running title block: the title page stands in its place
    meta.append('\\renewcommand{\\grothTitleBlock}{}')
    hdr = [f"% Transcription — Gaeta, Introduction to Functorial Algebraic Geometry (notes of Grothendieck's 1973 Buffalo course), PDF pages {first}-{last}:",
           f"% the {len(parts)} batches in one file, in the typescript's page order; the title pages, the table of contents and the bibliography are set with LaTeX structures.",
           "% Facsimile: scan U26.pdf (https://csg.igrothendieck.org/wp-content/uploads/2025/02/U26.pdf) (page n here = page n of that PDF; printed page n = PDF page n+4).",
           '% Transcription only: no modernisation, no commentary. Provenance of each batch:', '%']
    for i, p in enumerate(parts, 1):
        hdr.append(f'% Batch {i} (pages {p["a"]}-{p["b"]}):'); hdr += p['prov']
    bodies = []
    for i, p in enumerate(parts, 1):
        t = p['body']
        if i > 1: t = re.sub(r'^\\selectlanguage\{english\}\s*', '', t)
        bodies.append(f'% ===== Batch {i}, pages {p["a"]}-{p["b"]} =====\n\\setcounter{{grothDrawing}}{{0}}{p["map"]}\n\n{t}')
    text = '\n\n'.join(bodies)
    # 1. pages 1-4: title pages and table of contents
    i1 = text.index('\\page{1}'); i5 = text.index('\\page{5}')
    text = text[:i1] + TITLEPAGES + '\n' + text[i5:]
    # 2. pages 6-7: the bibliography
    i6 = text.index('\\page{6}'); ic = text.index('\\section*{CHAPTER 0}')
    block = text[i6:ic]
    pre = re.match(r'(\\page\{6\}\s*\\pagehead\{[^}]*\}\s*)\\section\*\{BIBLIOGRAPHY\}\s*(.*)', block, flags=re.S)
    text = text[:i6] + pre.group(1) + '\\section*{BIBLIOGRAPHY}\n\\gtoc{section}{BIBLIOGRAPHY}\n\n' + bibliography(pre.group(2)) + '\n\n' + text[ic:]
    # 3. every heading enters the table of contents with the printed page
    def head(m):
        kind = 'section' if m.group(1) == 'section' else 'subsection'
        title = strip_marks(m.group(2))
        if m.group(2).strip().upper().startswith(('BIBLIOGRAPHY', 'ALGEBRAIC GEOMETRY ONE CENTURY', 'PART II.')): return m.group(0)
        return m.group(0) + f'\n\\gtoc{{{kind}}}{{{title}}}'
    text = re.sub(r'\\(section|subsection)\*\{((?:[^{}]|\{[^{}]*\}|\{(?:[^{}]|\{[^{}]*\})*\})*)\}', head, text)
    out = '\n'.join(hdr) + '\n' + '\n'.join(meta) + '\n\n\\begin{document}\n\n' + text + '\n\n\\end{document}\n'
    os.makedirs(os.path.join(OUT, 'gaeta', 'ag'), exist_ok=True)
    open(os.path.join(OUT, 'gaeta', 'ag', 'ag.en.tex'), 'w').write(out)

build()
