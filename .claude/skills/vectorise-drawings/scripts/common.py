"""Shared paths and helpers for the vectorise-drawings scripts.

Paths are never hard-coded. Each script takes
  --work DIR   the local work dir (pages, marks.json, specs, previews, contact
               sheets); default $VECTORISE_WORK, else <tmp>/vectorise-drawings.
               Point it into the session's scratchpad: nothing in it is committed.
  --repo DIR   the grothendieck-project checkout; default $GROTHENDIECK_REPO,
               else the repository these scripts live in.

Work dir layout:
  marks.json                 the \\drawing marks, by cote (extract.py)
  pdf/<cote>.pdf             the folder's PDF, one at a time (fetch.py)
  pages/<cote>/p<N>.png      page renders, N = archive page (fetch.py)
  specs/<cote>.py            the redraws as data, SPECS = {id: {...}} (written by hand)
  out/<cote>/                SVG previews and crop | redraw | overlay triptychs (build.py)
  view/                      gridded views for reading coordinates (views.py)
  contact-<cote>.pdf         the contact sheet (build.py) -- LOCAL ONLY
"""
import os, sys, json, tempfile, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
FONT_PATH = '/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf'


def font(size):
    from PIL import ImageFont
    try:
        return ImageFont.truetype(FONT_PATH, size)
    except OSError:
        try:
            return ImageFont.load_default(size)
        except TypeError:
            return ImageFont.load_default()


def default_work():
    return os.environ.get('VECTORISE_WORK') or os.path.join(tempfile.gettempdir(), 'vectorise-drawings')


def default_repo():
    if os.environ.get('GROTHENDIECK_REPO'):
        return os.environ['GROTHENDIECK_REPO']
    up = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))  # .claude/skills/<skill>/scripts -> repo
    if os.path.isdir(os.path.join(up, 'transcripts')):
        return up
    try:
        return subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return os.getcwd()


def add_path_args(ap, repo=True):
    ap.add_argument('--work', default=default_work(), help='local work dir (default: $VECTORISE_WORK or <tmp>/vectorise-drawings)')
    if repo:
        ap.add_argument('--repo', default=default_repo(), help='repository checkout (default: $GROTHENDIECK_REPO or this skill\'s repository)')
    return ap


def page_file(work, cote, p):
    """The render of archive page p (PNG, or JPG if that is what was rendered)."""
    for ext in ('png', 'jpg'):
        f = os.path.join(work, 'pages', cote, f'p{p}.{ext}')
        if os.path.exists(f):
            return f
    raise FileNotFoundError(f'no render of {cote} p. {p} in {work}/pages/{cote}/ -- run fetch.py {cote} first')


def load_marks(work, cote=None):
    f = os.path.join(work, 'marks.json')
    if not os.path.exists(f):
        raise FileNotFoundError(f'{f} missing -- run extract.py <cote> first')
    m = json.load(open(f, encoding='utf8'))
    if cote is None:
        return m
    if cote not in m:
        raise KeyError(f'{cote} not in {f} -- run extract.py {cote}')
    return m[cote]


def view_dir(work):
    d = os.path.join(work, 'view')
    os.makedirs(d, exist_ok=True)
    return d


sys.path.insert(0, HERE)
