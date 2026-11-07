"""Compile the standalone TikZ drawings, when a TeX engine is available.

  python3.12 compile_tikz.py [--work DIR] [--engine E] [--svg] <dir-or-.tex> [...]

Each <id>.tex is compiled alone in a temporary directory (nothing is written next
to the sources). With --svg, the PDF is turned into <work>/out/<cote>/<id>.tikz.svg
by pdftocairo, to replace the preview in a second overlay pass. Exit status: 0 all
compiled, 1 some failed (their log tails are printed), 2 no TeX engine found --
then keep the SVG previews and say "not compiled" (build.py's default header).
"""
import os, sys, glob, shutil, subprocess, tempfile, argparse
from common import add_path_args

ENGINES = ('pdflatex', 'lualatex', 'xelatex', 'tectonic')


def main():
    ap = add_path_args(argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter), repo=False)
    ap.add_argument('paths', nargs='+', help='drawings directories (transcripts/<cote>/drawings) or .tex files')
    ap.add_argument('--engine', choices=ENGINES)
    ap.add_argument('--svg', action='store_true')
    a = ap.parse_args()
    engine = a.engine or next((e for e in ENGINES if shutil.which(e)), None)
    if not engine or not shutil.which(engine):
        print('no TeX engine (pdflatex, lualatex, xelatex, tectonic) on PATH: nothing compiled; keep the SVG previews')
        return 2
    files = []
    for p in a.paths:
        files += sorted(glob.glob(os.path.join(p, '*-*.tex'))) if os.path.isdir(p) else [p]
    bad = 0
    for f in files:
        f = os.path.abspath(f)
        with tempfile.TemporaryDirectory() as tmp:
            cmd = [engine, f] if engine == 'tectonic' else [engine, '-interaction=nonstopmode', '-halt-on-error', f]
            if engine == 'tectonic':
                cmd = [engine, '--outdir', tmp, f]
            r = subprocess.run(cmd, cwd=tmp, capture_output=True, text=True)
            pdf = os.path.join(tmp, os.path.splitext(os.path.basename(f))[0] + '.pdf')
            if r.returncode or not os.path.exists(pdf):
                bad += 1
                print('FAILED', f); print('\n'.join((r.stdout + r.stderr).splitlines()[-15:]))
                continue
            print('ok    ', f)
            if a.svg:
                cote = os.path.basename(os.path.dirname(os.path.dirname(f)))
                out = os.path.join(a.work, 'out', cote)
                os.makedirs(out, exist_ok=True)
                subprocess.run(['pdftocairo', '-svg', pdf, os.path.join(out, os.path.basename(f)[:-4] + '.tikz.svg')], check=True)
    print(f'{len(files) - bad} of {len(files)} compiled with {engine}')
    return 1 if bad else 0


if __name__ == '__main__':
    raise SystemExit(main())
