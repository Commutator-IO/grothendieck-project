"""Download a folder's PDF and render only the pages that carry drawings.

  python3.12 fetch.py [--work DIR] <cote>                 PDF + 300 dpi renders of the marked pages
  python3.12 fetch.py [--work DIR] <cote> --pages 12 66   only these archive pages
  python3.12 fetch.py [--work DIR] <cote> --clean         delete the PDF and the renders

The PDF comes from https://grothendieck.umontpellier.fr/<cote>.pdf (curl, through
the session's proxy, TLS verification on) into <work>/pdf/. Renders go to
<work>/pages/<cote>/p<archive page>.png, taken from PDF page archive + offset.
Disk is shared: one folder's PDF at a time, and --clean when the folder is done.
"""
import os, sys, json, shutil, subprocess, argparse
from common import add_path_args, load_marks

URL = 'https://grothendieck.umontpellier.fr/{cote}.pdf'


def main():
    ap = add_path_args(argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter), repo=False)
    ap.add_argument('cote')
    ap.add_argument('--pages', type=int, nargs='*', help='archive pages to render (default: every page with a mark in marks.json)')
    ap.add_argument('--offset', type=int, default=1, help='pdf page = archive page + offset (default 1)')
    ap.add_argument('--dpi', type=int, default=300)
    ap.add_argument('--color', action='store_true', help='render in colour (coloured pencils); default grey')
    ap.add_argument('--min-free-gb', type=float, default=1.0, help='refuse to download below this much free disk')
    ap.add_argument('--clean', action='store_true', help='delete the PDF and the renders of this folder, then exit')
    a = ap.parse_args()
    pdf = os.path.join(a.work, 'pdf', f'{a.cote}.pdf')
    pages_dir = os.path.join(a.work, 'pages', a.cote)

    if a.clean:
        for p in (pdf,):
            if os.path.exists(p):
                os.remove(p); print('deleted', p)
        if os.path.isdir(pages_dir):
            shutil.rmtree(pages_dir); print('deleted', pages_dir)
        return

    pages = a.pages
    if not pages:
        pages = sorted({d['archive_page'] for d in load_marks(a.work, a.cote) if d['archive_page'] is not None})
    os.makedirs(os.path.dirname(pdf), exist_ok=True)
    os.makedirs(pages_dir, exist_ok=True)

    if not os.path.exists(pdf):
        free = shutil.disk_usage(a.work).free / 1e9
        print(f'free disk: {free:.1f} GB')
        if free < a.min_free_gb:
            sys.exit(f'less than {a.min_free_gb} GB free: clean another folder first (fetch.py <cote> --clean)')
        url = URL.format(cote=a.cote)
        print('downloading', url)
        r = subprocess.run(['curl', '-fSL', '--retry', '3', '-o', pdf + '.part', url])
        if r.returncode:
            sys.exit(f'download failed ({r.returncode}); see the proxy notes of the session if TLS or 403')
        os.replace(pdf + '.part', pdf)
    print(f'{pdf}: {os.path.getsize(pdf) / 1e6:.0f} MB')

    for p in pages:
        out = os.path.join(pages_dir, f'p{p}')
        if os.path.exists(out + '.png'):
            continue
        n = p + a.offset
        cmd = ['pdftoppm', '-r', str(a.dpi), '-f', str(n), '-l', str(n), '-singlefile', '-png']
        if not a.color:
            cmd.append('-gray')
        subprocess.run(cmd + [pdf, out], check=True)
    print(f'{len(pages)} pages rendered in {pages_dir} (archive pages {pages[0]}..{pages[-1]})' if pages else 'no pages')
    print('check the offset: the archivists\' pencilled number of p. %s must be on its render (views.py page %s %s)' % (pages[0], a.cote, pages[0]) if pages else '')


if __name__ == '__main__':
    main()
