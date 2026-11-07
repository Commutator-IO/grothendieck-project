"""One drawing model, three outputs: TikZ (the deliverable), SVG (preview), PNG (overlay).

A spec is a dict: {"W": 100, "H": h, "items": [...]} in *crop units*: the crop
of the facsimile is W=100 units wide, y grows downwards, so a coordinate read
off the gridded crop is typed as is.  The TikZ output flips y and sets 1 unit =
1 mm (a 10 cm wide figure).

items (each a dict, key "k"):
  line   p=[[x,y],...]  closed?            s=[dashed|dotted|thick|->|<-|<->|pencil]
  curve  p=[[x,y],...]  closed?            smooth curve through the points
  circle c=[x,y] r
  ellipse c=[x,y] rx ry [a0 a1]            arc from a0 to a1 (degrees, ccw on the page)
  dot    c=[x,y] f=full|open|ring          ring = a point circled (his marked vertex)
  hatch  p=[[x,y],...]                     hatched region (pattern north east lines)
  text   c=[x,y] t="$\\tilde R_r$" [u="R~r"] [size=s|n|l]
styles s: dashed dotted thick -> <- <-> pencil struck west, and the colours of COLOURS.
A label rotated on a turned sheet takes s=["rotate=90"] (TikZ only; previews stay upright).
"""
import math, re
from PIL import Image, ImageDraw
from common import font as _font

# ---------------------------------------------------------------- geometry
def catmull(pts, closed=False, n=12):
    P = [tuple(p) for p in pts]
    if len(P) < 3:
        return P
    if closed:
        P = P + P[:3]
        rng = range(1, len(P) - 2)
        ext = P
    else:
        ext = [P[0]] + P + [P[-1]]
        rng = range(1, len(ext) - 2)
    out = []
    for i in rng:
        p0, p1, p2, p3 = ext[i - 1], ext[i], ext[i + 1], ext[i + 2]
        for k in range(n):
            t = k / n
            t2, t3 = t * t, t * t * t
            out.append(tuple(0.5 * ((2 * p1[j]) + (-p0[j] + p2[j]) * t + (2 * p0[j] - 5 * p1[j] + 4 * p2[j] - p3[j]) * t2 + (-p0[j] + 3 * p1[j] - 3 * p2[j] + p3[j]) * t3) for j in (0, 1)))
    out.append(ext[rng[-1] + 1])
    return out

def ellipse_pts(c, rx, ry, a0=0, a1=360, n=None):
    n = n or max(16, int(abs(a1 - a0) / 4))
    return [(c[0] + rx * math.cos(math.radians(a0 + (a1 - a0) * k / n)),
             c[1] - ry * math.sin(math.radians(a0 + (a1 - a0) * k / n))) for k in range(n + 1)]

def polyline(it):
    k = it['k']
    if k == 'line':
        p = [tuple(q) for q in it['p']]
        return p + [p[0]] if it.get('closed') else p
    if k == 'curve':
        return catmull(it['p'], it.get('closed'))
    if k == 'circle':
        return ellipse_pts(it['c'], it['r'], it['r'])
    if k == 'ellipse':
        return ellipse_pts(it['c'], it['rx'], it['ry'], it.get('a0', 0), it.get('a1', 360))
    return []

# ---------------------------------------------------------------- tex → plain (preview only)
# Macro -> preview character. An empty value drops the macro and keeps its argument.
GREEK = {
    'alpha': 'α', 'beta': 'β', 'gamma': 'γ', 'delta': 'δ', 'epsilon': 'ε', 'varepsilon': 'ε', 'zeta': 'ζ', 'eta': 'η',
    'theta': 'θ', 'iota': 'ι', 'kappa': 'κ', 'lambda': 'λ', 'mu': 'μ', 'nu': 'ν', 'xi': 'ξ', 'pi': 'π', 'rho': 'ρ',
    'sigma': 'σ', 'tau': 'τ', 'varphi': 'φ', 'chi': 'χ', 'omega': 'ω',
    'Gamma': 'Γ', 'Delta': 'Δ', 'Theta': 'Θ', 'Lambda': 'Λ', 'Pi': 'Π', 'Sigma': 'Σ', 'Phi': 'Φ', 'Psi': 'Ψ', 'Omega': 'Ω',
    'infty': '∞', 'emptyset': '∅', 'cap': '∩', 'neq': '≠', 'leqslant': '≤', 'bullet': '•', 'circ': '∘', 'times': '×',
    'vee': '∨', 'wedge': '∧', 'perp': '⊥', 'simeq': '≃', 'wr': '≀', 'pm': '±', 'partial': '∂', 'star': '*', 'ast': '*',
    'ldots': '…', 'cdots': '⋯', 'dots': '…', 'to': '→', 'rightarrow': '→', 'leftarrow': '←', 'mapsto': '↦',
    'Rightarrow': '⇒', 'hookrightarrow': '↪', 'rightrightarrows': '⇉', 'circlearrowleft': '↺', 'jmath': 'ȷ', 'S': 'S',
    'mathrm': '', 'mathbb': '', 'mathfrak': '', 'mathcal': '', 'operatorname': '', 'boldsymbol': '', 'textbf': '',
    'underline': '', 'acute': '', 'vec': '', 'frac': '', 'tfrac': '', 'overset': '',
}

# Coloured-pencil styles: name -> (TikZ colour, preview hex).
COLOURS = {'Or': ('orange!90!black', '#e07b00'), 'Ye': ('yellow!80!orange', '#d8c000'), 'Lg': ('green!60!black!70', '#6cbf3a'),
           'Dg': ('green!45!black', '#1f6e1f'), 'Br': ('brown!80!black', '#7a4a1c'), 'Rd': ('red!85!black', '#d01010'),
           'Bl': ('blue!70!black', '#2040c0'), 'Gy': ('black!40', '#888888')}

def tex2plain(t):
    s = t.replace('$', '')
    s = re.sub(r'\\([A-Za-z]+)', lambda m: GREEK[m.group(1)] if m.group(1) in GREEK and GREEK[m.group(1)] else m.group(0), s)
    for acc, comb in (('widetilde', '̃'), ('tilde', '̃'), ('bar', '̄'), ('overline', '̄'), ('hat', '̂')):
        s = re.sub(r'\\' + acc + r'\s*\{([^{}]*)\}', lambda m: m.group(1)[:1] + comb + m.group(1)[1:], s)
        s = re.sub(r'\\' + acc + r'\s*([^\s{}\\])', lambda m: m.group(1) + comb, s)
    s = re.sub(r'\\([A-Za-z]+)', lambda m: GREEK.get(m.group(1), m.group(1)), s)
    s = s.replace('{', '').replace('}', '').replace('\\,', ' ').replace('~', ' ')
    return s

# ---------------------------------------------------------------- TikZ
def f(v):
    return ('%.1f' % v).rstrip('0').rstrip('.')

def P(x, y):
    return '(%s,%s)' % (f(x), f(-y))

def tikz_style(s):
    out = []
    for st in s:
        out.append({'dashed': 'dashed', 'dotted': 'densely dotted', 'thick': 'very thick', '->': '-{Stealth[length=2mm]}',
                    '<-': '{Stealth[length=2mm]}-', '<->': '{Stealth[length=2mm]}-{Stealth[length=2mm]}', 'pencil': 'pencil',
                    'struck': 'struck', 'west': 'anchor=west'}.get(st, st))
    return ','.join(out)

def to_tikz(spec, header):
    L = ['% ' + l for l in header.splitlines()]
    L += [r'\documentclass[tikz,border=3pt]{standalone}', r'\usepackage{amsmath,amssymb}',
          r'\usetikzlibrary{patterns,arrows.meta}',
          r'\tikzset{' + ''.join('%s/.style={%s}, ' % (k, v[0]) for k, v in COLOURS.items() if any(k in it.get('s', []) for it in spec['items'])) + r'pencil/.style={black!45}, struck/.style={black!35}, mark/.style={circle,draw,inner sep=1.3pt}, pt/.style={circle,fill,inner sep=0.9pt}, opt/.style={circle,draw,fill=white,inner sep=1.1pt}}',
          r'\begin{document}', r'\begin{tikzpicture}[x=1mm,y=1mm,line cap=round,line join=round,font=\scriptsize]']
    for it in spec['items']:
        k, s = it['k'], tikz_style(it.get('s', []))
        opt = '[' + s + ']' if s else ''
        if k == 'line':
            path = ' -- '.join(P(*q) for q in it['p']) + (' -- cycle' if it.get('closed') else '')
            L.append(r'\draw%s %s;' % (opt, path))
        elif k == 'curve':
            kind = 'smooth cycle' if it.get('closed') else 'smooth'
            L.append(r'\draw%s plot[%s, tension=0.55] coordinates {%s};' % (opt, kind, ' '.join(P(*q) for q in it['p'])))
        elif k == 'circle':
            L.append(r'\draw%s %s circle[radius=%s];' % (opt, P(*it['c']), f(it['r'])))
        elif k == 'ellipse':
            c, rx, ry = it['c'], it['rx'], it['ry']
            if 'a0' in it:
                a0, a1 = it['a0'], it['a1']
                x0, y0 = c[0] + rx * math.cos(math.radians(a0)), c[1] - ry * math.sin(math.radians(a0))
                L.append(r'\draw%s %s arc[start angle=%s, end angle=%s, x radius=%s, y radius=%s];' % (opt, P(x0, y0), f(a0), f(a1), f(rx), f(ry)))
            else:
                L.append(r'\draw%s %s ellipse[x radius=%s, y radius=%s];' % (opt, P(*c), f(rx), f(ry)))
        elif k == 'dot':
            sty = {'full': 'pt', 'open': 'opt', 'ring': 'mark'}[it.get('f', 'full')]
            L.append(r'\node[%s%s] at %s {};' % (sty, (',' + s) if s else '', P(*it['c'])))
        elif k == 'hatch':
            L.append(r'\fill[pattern=north east lines%s] %s -- cycle;' % ((',' + s) if s else '', ' -- '.join(P(*q) for q in it['p'])))
        elif k == 'text':
            size = {'s': r'\tiny', 'n': r'\scriptsize', 'l': r'\small'}.get(it.get('size', 'n'))
            L.append(r'\node[inner sep=1pt%s] at %s {%s %s};' % ((',' + s) if s else '', P(*it['c']), size, it['t']))
    L += [r'\end{tikzpicture}', r'\end{document}', '']
    return '\n'.join(L)

# ---------------------------------------------------------------- SVG
def to_svg(spec, scale=4):
    W, H = spec['W'], spec['H']
    out = ['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 %s %s" width="%d" height="%d"><rect width="100%%" height="100%%" fill="white"/>' % (f(W), f(H), W * scale, H * scale)]
    for it in spec['items']:
        s = it.get('s', [])
        col = '#777' if ('pencil' in s or 'struck' in s) else '#000'
        for _k, (_t, _hex) in COLOURS.items():
            if _k in s: col = _hex
        sw = 0.9 if 'thick' in s else 0.35
        dash = ' stroke-dasharray="1.5,1"' if 'dashed' in s else (' stroke-dasharray="0.4,0.8"' if 'dotted' in s else '')
        k = it['k']
        if k in ('line', 'curve', 'circle', 'ellipse'):
            pts = polyline(it)
            out.append('<polyline fill="none" stroke="%s" stroke-width="%s"%s points="%s"/>' % (col, sw, dash, ' '.join('%s,%s' % (f(x), f(y)) for x, y in pts)))
        elif k == 'dot':
            c = it['c']; ff = it.get('f', 'full')
            r = 0.8 if ff == 'full' else 1.3
            out.append('<circle cx="%s" cy="%s" r="%s" fill="%s" stroke="%s" stroke-width="0.3"/>' % (f(c[0]), f(c[1]), r, '#000' if ff == 'full' else 'white', col))
        elif k == 'hatch':
            out.append('<polygon fill="#000" fill-opacity="0.18" stroke="none" points="%s"/>' % ' '.join('%s,%s' % (f(x), f(y)) for x, y in it['p']))
        elif k == 'text':
            c = it['c']
            out.append(('<text x="%s" y="%s" font-size="%s" text-anchor="' + ('start' if 'west' in s else 'middle') + '" dominant-baseline="middle" fill="%s" font-family="serif">%s</text>') % (f(c[0]), f(c[1]), 3.2 if it.get('size') != 's' else 2.4, col, (it.get('u') or tex2plain(it['t'])).replace('&', '&amp;').replace('<', '&lt;')))
    out.append('</svg>')
    return '\n'.join(out)

# ---------------------------------------------------------------- PNG (for overlay)
def to_png(spec, width_px, color=(0, 0, 0), bg=(255, 255, 255, 255)):
    W, H = spec['W'], spec['H']
    sc = width_px / W
    h_px = int(round(H * sc))
    im = Image.new('RGBA', (width_px, h_px), bg)
    d = ImageDraw.Draw(im)
    font = _font(max(12, int(4.2 * sc)))
    sfont = _font(max(10, int(3.2 * sc)))
    for it in spec['items']:
        s = it.get('s', [])
        col = tuple(int(c + (255 - c) * 0.5) for c in color) + (255,) if ('pencil' in s or 'struck' in s) else color + (255,)
        if color == (0, 0, 0):
            for _k, (_t, _hex) in COLOURS.items():
                if _k in s: col = tuple(int(_hex[i:i + 2], 16) for i in (1, 3, 5)) + (255,)
        lw = max(1, int((0.9 if 'thick' in s else 0.4) * sc))
        k = it['k']
        if k in ('line', 'curve', 'circle', 'ellipse'):
            pts = [(x * sc, y * sc) for x, y in polyline(it)]
            if 'dashed' in s or 'dotted' in s:
                on, off = ((1.6, 1.0) if 'dashed' in s else (0.4, 0.8))
                draw_dashed(d, pts, on * sc, off * sc, col, lw)
            else:
                d.line(pts, fill=col, width=lw, joint='curve')
            for a in ('->', '<->'):
                if a in s: arrowhead(d, pts[-2], pts[-1], sc, col)
            for a in ('<-', '<->'):
                if a in s: arrowhead(d, pts[1], pts[0], sc, col)
        elif k == 'dot':
            x, y = it['c'][0] * sc, it['c'][1] * sc
            ff = it.get('f', 'full')
            r = (0.9 if ff == 'full' else 1.4) * sc
            if ff == 'full': d.ellipse([x - r, y - r, x + r, y + r], fill=col)
            else: d.ellipse([x - r, y - r, x + r, y + r], outline=col, width=max(1, int(0.35 * sc)))
        elif k == 'hatch':
            mask = Image.new('L', im.size, 0)
            ImageDraw.Draw(mask).polygon([(x * sc, y * sc) for x, y in it['p']], fill=255)
            hat = Image.new('RGBA', im.size, (0, 0, 0, 0))
            hd = ImageDraw.Draw(hat)
            step = max(4, int(1.5 * sc))
            for o in range(-h_px, width_px + h_px, step):
                hd.line([(o, h_px), (o + h_px, 0)], fill=col, width=max(1, int(0.2 * sc)))
            im.paste(hat, (0, 0), Image.composite(hat, Image.new('RGBA', im.size, (0, 0, 0, 0)), mask))
        elif k == 'text':
            x, y = it['c'][0] * sc, it['c'][1] * sc
            d.text((x, y), it.get('u') or tex2plain(it['t']), fill=col, font=sfont if it.get('size') == 's' else font, anchor='lm' if 'west' in s else 'mm')
    return im

def draw_dashed(d, pts, on, off, col, lw):
    acc, draw = 0.0, True
    seg = on
    for (x0, y0), (x1, y1) in zip(pts, pts[1:]):
        L = math.hypot(x1 - x0, y1 - y0)
        t = 0.0
        while t < L:
            step = min(seg - acc, L - t)
            if draw:
                a, b = t / L, (t + step) / L
                d.line([(x0 + (x1 - x0) * a, y0 + (y1 - y0) * a), (x0 + (x1 - x0) * b, y0 + (y1 - y0) * b)], fill=col, width=lw)
            t += step; acc += step
            if acc >= seg - 1e-9:
                acc = 0; draw = not draw; seg = on if draw else off

def arrowhead(d, p0, p1, sc, col):
    ang = math.atan2(p1[1] - p0[1], p1[0] - p0[0])
    L = 2.0 * sc
    a = [(p1[0] - L * math.cos(ang + e), p1[1] - L * math.sin(ang + e)) for e in (0.4, -0.4)]
    d.polygon([p1, a[0], a[1]], fill=col)
