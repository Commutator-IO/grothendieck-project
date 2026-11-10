"""Build a folder's drawings from its spec file: the repository files, the previews and the contact sheet.

  python3.12 build.py [--work DIR] [--repo DIR] <cote> [<id> ...]

Reads <work>/marks.json and <work>/specs/<cote>.py (SPECS = {id: spec}, cote with
"-" written "_"), and the page renders in <work>/pages/<cote>/. Writes
  <repo>/transcripts/<cote>/drawings/<id>.tex      every drawing (TikZ, standalone)
  <repo>/transcripts/<cote>/drawings/<id>.json     method 3 only (encodings + derived checks)
  <repo>/transcripts/<cote>/drawings/drawings.json the index, one record per mark
and locally <work>/out/<cote>/<id>.svg, <id>-triptych.png (crop | redraw | overlay)
and <work>/contact-<cote>.pdf (+ .png pages). With ids, only those previews are
rebuilt; the repository files are always all rewritten.

Spec keys: bbox (page fractions), kind, method (2|3), status (ok|partial|failed),
notes, items (dsl.py), and optionally comb (one encoding or a list), rot180 or
rotate (degrees ccw, for turned sheets), orientation (text), figures
([{what, bbox}] when one mark covers several figures), disagreement (text).
A mark without a spec is written as status "failed", notes "not yet done".
"""
import sys, os, json, importlib.util, argparse, datetime
from PIL import Image, ImageDraw
from common import add_path_args, load_marks, page_file, font, HERE
import drawkit, comb

SCHEMA_DOC = ('schemas: .claude/skills/vectorise-drawings/SKILL.md (dessin/1, map/1, cellular/1, polyhedron/1, '
              'stable-graph/1, stable-graph-table/1, segment-config/1)')
CHECK_KEYS = ('black', 'white', 'faces', 'genus', 'vertices', 'edges', 'euler', 'type', 'stable', 'all_ok',
              'expected_ok', 'expected_mismatch')


def main():
    ap = add_path_args(argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter))
    ap.add_argument('cote')
    ap.add_argument('ids', nargs='*', help='only rebuild the previews of these drawings')
    ap.add_argument('--model', default='claude-fable-5-2', help='model named in the headers (default claude-fable-5-2; claude-opus-5-5 is the other model allowed)')
    ap.add_argument('--date', default=datetime.date.today().isoformat())
    ap.add_argument('--compiled', action='store_true', help='say in the headers that the TikZ was compiled (after compile_tikz.py passed)')
    a = ap.parse_args()
    cote, only = a.cote, set(a.ids)

    spec_file = os.path.join(a.work, 'specs', cote.replace('-', '_') + '.py')
    sys.path.insert(0, HERE)  # specs do `from dsl import *`
    spec_mod = importlib.util.spec_from_file_location('specs_' + cote.replace('-', '_'), spec_file)
    mod = importlib.util.module_from_spec(spec_mod); spec_mod.loader.exec_module(mod)
    SPECS = mod.SPECS
    marks = {d['id']: d for d in load_marks(a.work, cote)}
    unknown = set(SPECS) - set(marks)
    if unknown:
        print('warning: specs with no mark (ignored):', ', '.join(sorted(unknown)))

    outdir = os.path.join(a.repo, 'transcripts', cote, 'drawings')
    prev = os.path.join(a.work, 'out', cote)
    os.makedirs(outdir, exist_ok=True); os.makedirs(prev, exist_ok=True)
    FONT = font(16)
    tex_note = 'TikZ compiled' if a.compiled else 'not compiled (no TeX in the session)'
    pages, index, rows = {}, [], []

    for did, m in marks.items():
        sp = SPECS.get(did)
        entry = dict(id=did, cote=cote, batch=m['batch'], pdf_page=m['pdf_page'], archive_page=m['archive_page'],
                     bbox=None, description=m['description'], kind=None, method=None, status='failed', notes='not yet done', files=[])
        if sp is None:
            index.append(entry); continue
        p = m['archive_page']
        if p not in pages:
            pages[p] = Image.open(page_file(a.work, cote, p)).convert('RGB')
        im = pages[p]
        W, Hp = im.size
        x0, y0, x1, y1 = sp['bbox']
        crop = im.crop((int(x0 * W), int(y0 * Hp), int(x1 * W), int(y1 * Hp)))
        rot = 180 if sp.get('rot180') else sp.get('rotate', 0)
        if rot:
            crop = crop.rotate(rot, expand=True)
        spec = dict(W=100, H=round(100 * crop.height / crop.width, 1), items=sp.get('items', []))
        entry.update(bbox=[round(v, 3) for v in sp['bbox']], kind=sp['kind'], method=sp['method'], status=sp['status'], notes=sp.get('notes', ''))
        if sp.get('orientation'):
            entry['orientation'] = sp['orientation']
        elif rot == 180:
            entry['orientation'] = 'upside down on the page (tete-beche half); crop rotated 180 degrees, redraw upright, coordinates in the rotated crop'
        elif rot:
            entry['orientation'] = f'turned sheet; crop rotated {rot} degrees counter-clockwise, coordinates in the rotated crop'
        for k in ('figures', 'disagreement'):
            if sp.get(k):
                entry[k] = sp[k]
        header = (f'Drawing {cote}/{did} -- folder {cote}, batch {m["batch"]:02d}, archive page {p} (PDF page {m["pdf_page"]}).\n'
                  f'Transcription: {m["description"]}\n'
                  f'Kind: {sp["kind"]}. Method {sp["method"]} ({"encoded, rendered from the data" if sp["method"] == 3 else "schematic redraw from the facsimile"}). Status: {sp["status"]}.\n'
                  f'Notes: {sp.get("notes", "")}\n'
                  f'Coordinates: 1 unit = 1 mm = 1/100 of the crop width (bbox in page fractions: {entry["bbox"]}).\n'
                  f'Redrawn by Claude ({a.model}), issue #73, {a.date}; not checked by a human; {tex_note}.\n'
                  f'Rights: reproduces part of the work -- behind RENDER_TRANSCRIPTS, never published by itself.')
        with open(os.path.join(outdir, f'{did}.tex'), 'w', encoding='utf8') as fh:
            fh.write(drawkit.to_tikz(spec, header))
        entry['files'].append(f'{did}.tex')
        if sp.get('comb'):
            encs = sp['comb'] if isinstance(sp['comb'], list) else [sp['comb']]
            for e in encs:
                e['derived'] = comb.check({k: v for k, v in e.items() if k != 'derived'})
            data = dict(id=did, cote=cote, archive_page=p, encodings=encs, schema_doc=SCHEMA_DOC)
            with open(os.path.join(outdir, f'{did}.json'), 'w', encoding='utf8') as fh:
                fh.write(json.dumps(data, ensure_ascii=False, indent=1) + '\n')
            entry['files'].append(f'{did}.json')
            entry['checks'] = [dict(name=e.get('name', ''), schema=e['schema'], **{k: v for k, v in e['derived'].items() if k in CHECK_KEYS}) for e in encs]
            for c in entry['checks']:
                if c.get('expected_ok') is False or c.get('all_ok') is False:
                    print(f'CHECK FAILED {did} {c["name"]}: {c.get("expected_mismatch", "")}')
        index.append(entry)
        trip_f = os.path.join(prev, f'{did}-triptych.png')
        if only and did not in only and os.path.exists(trip_f):
            rows.append(trip_f); continue
        with open(os.path.join(prev, f'{did}.svg'), 'w', encoding='utf8') as fh:
            fh.write(drawkit.to_svg(spec))
        sc_ = min(560 / crop.width, 500 / crop.height)
        cw, h2 = max(1, int(crop.width * sc_)), max(1, int(crop.height * sc_))
        c = crop.resize((cw, h2))
        red = drawkit.to_png(spec, cw, color=(0, 0, 0)).resize((cw, h2)).convert('RGB')
        ov_lines = drawkit.to_png(spec, cw, color=(220, 0, 0), bg=(255, 255, 255, 0)).resize((cw, h2))
        alpha = ov_lines.split()[3].point(lambda v: int(v * 0.65))
        ov = Image.blend(c, Image.new('RGB', c.size, 'white'), 0.35)
        ov.paste(Image.new('RGB', c.size, (220, 0, 0)), (0, 0), alpha)
        trip = Image.new('RGB', (3 * cw + 40, h2 + 26), 'white')
        for i, t in enumerate((c, red, ov)):
            trip.paste(t, (10 + i * (cw + 10), 24))
        ImageDraw.Draw(trip).text((10, 3), f'{cote} {did}  p.{p}  {sp["kind"]}  method {sp["method"]}  [{sp["status"]}]', fill=(0, 0, 0), font=FONT)
        trip.save(trip_f)
        rows.append(trip_f)

    with open(os.path.join(outdir, 'drawings.json'), 'w', encoding='utf8') as fh:
        json.dump(dict(cote=cote, issue=73, generated_by=a.model, date=a.date,
                       conventions=dict(pdf_page='archive_page + 1 (Montpellier cover sheet)',
                                        bbox='[x0, y0, x1, y1], fractions of the PDF page (A4, incl. the white frame around the scan)',
                                        method={'2': 'schematic TikZ redraw', '3': 'combinatorial encoding (.json) + TikZ rendering'}),
                       drawings=index), fh, ensure_ascii=False, indent=1)

    # contact sheet, pages of about 4200 px -- LOCAL ONLY (crops may show typed names)
    ims = [Image.open(r) for r in rows]
    sheets, cur, hh = [], [], 0
    for im in ims:
        if hh + im.height > 4200 and cur:
            sheets.append(cur); cur, hh = [], 0
        cur.append(im); hh += im.height + 8
    if cur: sheets.append(cur)
    out_pages = []
    for sh in sheets:
        P = Image.new('RGB', (max(i.width for i in sh), sum(i.height + 8 for i in sh)), 'white'); y = 0
        for i in sh:
            P.paste(i, (0, y)); y += i.height + 8
        out_pages.append(P)
    if out_pages:
        out_pages[0].save(os.path.join(a.work, f'contact-{cote}.pdf'), save_all=True, append_images=out_pages[1:], resolution=100)
        for k, P in enumerate(out_pages):
            P.save(os.path.join(a.work, f'contact-{cote}-{k + 1}.png'))
    st = {s: sum(1 for e in index if e['status'] == s) for s in ('ok', 'partial', 'failed')}
    print(f'{cote}: {len(index)} marks, {sum(1 for e in index if e["method"])} specified; {st["ok"]} ok, {st["partial"]} partial, {st["failed"]} failed')
    print(f'repo files in {outdir}; contact sheet {os.path.join(a.work, f"contact-{cote}.pdf")} (local only)')


if __name__ == '__main__':
    main()
