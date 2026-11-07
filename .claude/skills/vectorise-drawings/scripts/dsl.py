"""Short constructors for the drawing items of a spec (see drawkit.py), and encoding helpers.

A spec file <work>/specs/<cote>.py does `from dsl import *` and fills
SPECS = {id: dict(bbox=..., kind=..., method=2|3, status=..., notes=..., items=flat(...), comb=...)}.

  L(p, q, ..., s=[...], closed=False)   polyline        Cv(...)  smooth curve through the points
  Ci(c, r)                              circle          E(c, rx, ry[, a0, a1])  ellipse or arc
  D(c, f='full'|'open'|'ring')          point           Dots(c1, c2, ...)  several points
  H(p, q, ...)                          hatched region  T(c, '$tex$', u='plain', size='s'|'n'|'l')  label
  flat(...)                             flattens nested lists of items
  shift(items, dx, dy), affine(items, sx, sy, dx, dy)   move a group (e.g. one figure of a page)
  from_view(view, bbox, *items)        items typed in a wider gridded view's units -> the bbox crop's units
  sphere_cells(equator, chords, ...)    cellular/1 for a sphere cut by an equator and circles
  stable_graph_items(sg, x0, y0)        canonical drawing of a stable-graph/1 (for tables, method 3)
Styles s: dashed, dotted, thick, ->, <-, <->, pencil (his faint strokes), struck (crossed out, grey),
west (label anchored on its left), and the colours Or Ye Lg Dg Br Rd Bl Gy (coloured pencils).
"""
import math
from collections import Counter

def L(*p, s=(), closed=False):
    return dict(k='line', p=[list(q) for q in p], s=list(s), closed=closed)

def Cv(*p, s=(), closed=False):
    return dict(k='curve', p=[list(q) for q in p], s=list(s), closed=closed)

def Ci(c, r, s=()):
    return dict(k='circle', c=list(c), r=r, s=list(s))

def E(c, rx, ry, a0=None, a1=None, s=()):
    d = dict(k='ellipse', c=list(c), rx=rx, ry=ry, s=list(s))
    if a0 is not None:
        d.update(a0=a0, a1=a1)
    return d

def D(c, f='full', s=()):
    return dict(k='dot', c=list(c), f=f, s=list(s))

def Dots(*cs, f='full', s=()):
    return [D(c, f, s) for c in cs]

def H(*p, s=()):
    return dict(k='hatch', p=[list(q) for q in p], s=list(s))

def T(c, t, u=None, size='n', s=()):
    d = dict(k='text', c=list(c), t=t, size=size, s=list(s))
    if u:
        d['u'] = u
    return d

def flat(*xs):
    out = []
    for x in xs:
        if isinstance(x, list):
            out += flat(*x)
        else:
            out.append(x)
    return out


def sphere_cells(equator, chords, name='', expected=None, extra=None):
    """cellular/1 encoding of a sphere cut by an equator (cyclic vertex list) and by
    circles meeting the equator twice, given as chords [u, v]: each circle gives a
    northern arc and a southern arc. Chords on one side must not cross."""
    edges = {}
    def ename(u, v, tag=''):
        n = f'{u}-{v}{tag}'
        edges[n] = [u, v]
        return n
    ring = [(equator[i], equator[(i + 1) % len(equator)], ename(equator[i], equator[(i + 1) % len(equator)])) for i in range(len(equator))]
    faces = []
    for side in ('N', 'S'):
        regions = [list(ring)]
        for (u, v) in chords:
            e = ename(u, v, side)
            for r in regions:
                vs = [a for a, b, n in r]
                if u in vs and v in vs:
                    i, j = vs.index(u), vs.index(v)
                    if i > j: i, j = j, i
                    r1 = r[i:j] + [(vs[j], vs[i], e)]
                    r2 = r[j:] + r[:i] + [(vs[i], vs[j], e)]
                    regions.remove(r); regions += [r1, r2]
                    break
            else:
                raise ValueError('chord %s-%s fits no region' % (u, v))
        faces += [[n for a, b, n in r] for r in regions]
    d = dict(schema='cellular/1', name=name, edges=edges, faces=faces)
    if expected: d['expected'] = expected
    if extra: d.update(extra)
    return d


def shift(items, dx=0, dy=0):
    out = []
    for it in items:
        it = dict(it)
        if 'p' in it: it['p'] = [[x + dx, y + dy] for x, y in it['p']]
        if 'c' in it: it['c'] = [it['c'][0] + dx, it['c'][1] + dy]
        out.append(it)
    return out


def affine(items, sx=1, sy=None, dx=0, dy=0):
    sy = sx if sy is None else sy
    out = []
    for it in items:
        it = dict(it)
        if 'p' in it: it['p'] = [[x * sx + dx, y * sy + dy] for x, y in it['p']]
        if 'c' in it: it['c'] = [it['c'][0] * sx + dx, it['c'][1] * sy + dy]
        for key in ('r', 'rx'):
            if key in it: it[key] = it[key] * sx
        if 'ry' in it: it['ry'] = it['ry'] * sy
        out.append(it)
    return out



def stable_graph_items(sg, x0, y0, step=5.5):
    """Canonical rendering of a stable graph (stable-graph/1 dict): vertices on a line from
    (x0, y0), multiple edges as lenses, loops as small ellipses above, legs as short arrows,
    genus written by the vertex when non-zero. It does not overlay the page by design."""
    vs = list(sg['vertices'])
    pos = {v: (x0 + i * step, y0) for i, v in enumerate(vs)}
    out = []
    mult = Counter(tuple(e) for e in sg['edges'])
    for (a, b), m in mult.items():
        (xa, ya), (xb, yb) = pos[a], pos[b]
        if a == b:
            for k in range(m):
                out.append(E((xa, ya - 2 - 1.2 * k), 1.3 + 0.5 * k, 2 + 1.2 * k))
            continue
        offs = [0] if m == 1 else ([-1.6, 1.6] if m == 2 else [-2.2, 0, 2.2])
        if abs(xa - xb) > step * 1.5 and m == 1:
            offs = [-2.5]
        for o in offs:
            out.append(L((xa, ya), (xb, yb)) if o == 0 else Cv((xa, ya), ((xa + xb) / 2, ya + o), (xb, yb)))
    for v in vs:
        x, y = pos[v]
        k = sg.get('legs', {}).get(v, 0)
        for j in range(k):
            ang = math.pi * (0.25 + 0.5 * (j + 0.5) / k)
            out.append(L((x, y), (x + 3.5 * math.cos(ang), y + 3.5 * math.sin(ang)), s=['->']))
        out.append(D((x, y)))
        if sg['vertices'][v]:
            out.append(T((x + 1.6, y - 1.6), '$%s$' % sg['vertices'][v], size='s'))
    return out


def from_view(view, bbox, *items, aspect=3508 / 2481):
    """Items whose coordinates were typed in the units of a gridded view crop `view`
    (page fractions x0, y0, x1, y1, 100 units wide) -> units of the drawing's own `bbox` crop.
    aspect = page height / width in pixels (A4 render: 3508 / 2481). Coordinates read off a
    wide view drift by 5-10 units: re-read a tight crop after the overlay check."""
    vx0, vy0, vx1, vy1 = view
    bx0, by0, bx1, by1 = bbox
    sc = (vx1 - vx0) / (bx1 - bx0)
    return affine(flat(*items), sx=sc, dx=(vx0 - bx0) / (bx1 - bx0) * 100, dy=(vy0 - by0) * aspect / (bx1 - bx0) * 100)
