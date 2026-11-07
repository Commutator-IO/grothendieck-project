"""List the \\drawing{...} marks of one or more folders.

  python3.12 extract.py [--work DIR] [--repo DIR] [--offset 1] <cote> [<cote> ...]

Reads transcripts/<cote>/batch-*.fr.tex (read only), gives each mark the id
<batch>-<n> (n counts the marks of the batch, from 1), the archive page of the
last \\page{N} before it, pdf_page = archive page + offset, its source line and
its description, and merges them into <work>/marks.json (other cotes kept).
Mentions of \\drawing inside % comments (batch headers) are skipped.
"""
import re, json, glob, os, argparse
from common import add_path_args


def marks_of(repo, cote, offset=1):
    items = []
    for f in sorted(glob.glob(os.path.join(repo, 'transcripts', cote, 'batch-*.fr.tex'))):
        batch = int(re.search(r'batch-(\d+)', os.path.basename(f)).group(1))
        tex = open(f, encoding='utf8').read()
        # blank out % comments (keeping offsets and line numbers): batch headers mention \drawing{} in comments
        tex = re.sub(r'(?<!\\)%.*', lambda m: ' ' * len(m.group(0)), tex)
        tokens = [(m.start(), 'page', int(m.group(1))) for m in re.finditer(r'\\page\{(\d+)\}', tex)]
        tokens += [(m.start(), 'drawing', None) for m in re.finditer(r'\\drawing\{', tex)]
        tokens.sort()
        n, page = 0, None
        for pos, kind, val in tokens:
            if kind == 'page':
                page = val
                continue
            j = tex.index('{', pos) + 1
            depth, k = 1, j
            while depth and k < len(tex):
                c = tex[k]
                if c == '\\':
                    k += 2
                    continue
                if c == '{':
                    depth += 1
                elif c == '}':
                    depth -= 1
                k += 1
            n += 1
            items.append(dict(id=f'{batch:02d}-{n}', cote=cote, batch=batch, archive_page=page,
                              pdf_page=None if page is None else page + offset,
                              line=tex.count('\n', 0, pos) + 1,
                              description=re.sub(r'\s+', ' ', tex[j:k - 1]).strip()))
    return items


def main():
    ap = add_path_args(argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter))
    ap.add_argument('--offset', type=int, default=1, help='pdf page = archive page + offset (Montpellier cover sheet: 1; check it)')
    ap.add_argument('cotes', nargs='+')
    a = ap.parse_args()
    os.makedirs(a.work, exist_ok=True)
    out_f = os.path.join(a.work, 'marks.json')
    out = json.load(open(out_f, encoding='utf8')) if os.path.exists(out_f) else {}
    for cote in a.cotes:
        out[cote] = marks_of(a.repo, cote, a.offset)
        if not out[cote]:
            print(f'{cote}: no \\drawing marks (or no transcripts/{cote}/batch-*.fr.tex)')
    with open(out_f, 'w', encoding='utf8') as fh:
        json.dump(out, fh, ensure_ascii=False, indent=1)
    for cote in a.cotes:
        v = out[cote]
        pages = sorted({d['archive_page'] for d in v if d['archive_page'] is not None})
        print(f'{cote}: {len(v)} marks on {len(pages)} pages -> {out_f}')
        for d in v:
            flag = '  (NO \\page BEFORE THIS MARK)' if d['archive_page'] is None else ''
            print(f"  {d['id']}  p. {d['archive_page']}  | {d['description']}{flag}")


if __name__ == '__main__':
    main()
