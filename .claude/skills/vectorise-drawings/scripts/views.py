"""Gridded views for locating figures and reading coordinates by eye. All go to <work>/view/.

  views.py page  <cote> <p>                        whole page, grid in page twentieths -> view/<cote>-p<p>.jpg
  views.py pages <cote> <p> [<p> ...] [--width W]  pages side by side (one image read for several pages)
  views.py crop  <cote> <p> x0 y0 x1 y1 <tag> [--rot 180] [--width W]
                                                   one crop, grid in crop units (W = 100, step 5) -> view/<cote>-<tag>.jpg
  views.py crops <cote> <out.jpg> tag:p:x0,y0,x1,y1[:r|:r90|:r270] ...
                                                   several gridded crops flowed in rows (batch them: halves the image tokens)
  views.py overlays <cote> <out.jpg> <id> ...      the overlay panels of built triptychs, three per row, to re-check drift

Page fractions are of the rendered PDF page (bbox convention of drawings.json);
crop units are what the specs use: the crop is 100 units wide, y grows downwards.
"""
import os, sys, argparse
from PIL import Image, ImageDraw
from common import add_path_args, page_file, view_dir, font


def _grid_page(im, w, label=None):
    im = im.resize((w, int(im.height * w / im.width)))
    d = ImageDraw.Draw(im); F = font(13)
    for i in range(1, 20):
        x = im.width * i / 20; y = im.height * i / 20
        c = (255, 0, 0) if i % 2 == 0 else (255, 180, 180)
        d.line([(x, 0), (x, im.height)], fill=c); d.line([(0, y), (im.width, y)], fill=c)
        if i % 2 == 0:
            d.text((x + 2, 2), '%.1f' % (i / 20), fill=(200, 0, 0), font=F)
            d.text((2, y + 2), '%.1f' % (i / 20), fill=(200, 0, 0), font=F)
    if label:
        d.text((w - 70, im.height - 22), label, fill=(0, 0, 255), font=font(18))
    return im


def _rotate(c, rot):
    return c.rotate(rot, expand=True) if rot else c


def _grid_crop(c, width):
    c = c.resize((width, max(1, int(c.height * width / c.width))))
    d = ImageDraw.Draw(c); F = font(13); u = width / 100
    k = 0
    while k * 5 * u < max(c.height, width + 1):
        v = k * 5 * u; col = (255, 0, 0) if k % 2 == 0 else (255, 195, 195)
        if v <= width: d.line([(v, 0), (v, c.height)], fill=col)
        if v < c.height: d.line([(0, v), (width, v)], fill=col)
        if k % 2 == 0:
            if v <= width: d.text((v + 2, 1), str(k * 5), fill=(200, 0, 0), font=F)
            if v < c.height: d.text((2, v + 1), str(k * 5), fill=(200, 0, 0), font=F)
        k += 1
    return c


def crop_img(work, cote, p, bb, rot=0):
    im = Image.open(page_file(work, cote, p)).convert('RGB')
    W, H = im.size
    return _rotate(im.crop((int(bb[0] * W), int(bb[1] * H), int(bb[2] * W), int(bb[3] * H))), rot)


def flow(cols, maxw=1500, gap=8):
    rows, cur, wsum = [], [], 0
    for col in cols:
        if cur and wsum + col.width > maxw:
            rows.append(cur); cur, wsum = [], 0
        cur.append(col); wsum += col.width + gap
    if cur: rows.append(cur)
    RW = max(sum(c.width + gap for c in r) for r in rows); RH = sum(max(c.height for c in r) + gap for r in rows)
    out = Image.new('RGB', (RW, RH), 'white'); y = 0
    for r in rows:
        x = 0
        for c in r:
            out.paste(c, (x, y)); x += c.width + gap
        y += max(c.height for c in r) + gap
    return out


def main():
    ap = add_path_args(argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter), repo=False)
    ap.add_argument('cmd', choices=['page', 'pages', 'crop', 'crops', 'overlays'])
    ap.add_argument('cote')
    ap.add_argument('args', nargs='+')
    ap.add_argument('--width', type=int, default=None)
    ap.add_argument('--rot', type=int, default=0, help='crop: rotate counter-clockwise by this many degrees (180 for a tete-beche half)')
    ap.add_argument('--max-height', type=int, default=700, help='crops: cap on each crop\'s height in pixels')
    a = ap.parse_args()
    V = view_dir(a.work)
    if a.cmd == 'page':
        p = a.args[0]
        out = os.path.join(V, f'{a.cote}-p{p}.jpg')
        _grid_page(Image.open(page_file(a.work, a.cote, p)).convert('RGB'), a.width or 900, f'p{p}').save(out, quality=70)
    elif a.cmd == 'pages':
        ims = [_grid_page(Image.open(page_file(a.work, a.cote, p)).convert('RGB'), a.width or 600, f'p{p}') for p in a.args]
        o = Image.new('RGB', (sum(i.width + 6 for i in ims), max(i.height for i in ims)), 'white'); x = 0
        for i in ims:
            o.paste(i, (x, 0)); x += i.width + 6
        out = os.path.join(V, f'{a.cote}-pv-{"-".join(a.args)}.jpg')
        o.save(out, quality=70)
    elif a.cmd == 'crop':
        p, (x0, y0, x1, y1), tag = a.args[0], map(float, a.args[1:5]), a.args[5]
        c = _grid_crop(crop_img(a.work, a.cote, p, (x0, y0, x1, y1), a.rot), a.width or 1000)
        out = os.path.join(V, f'{a.cote}-{tag}.jpg')
        c.save(out, quality=75)
        print('H units = %.1f' % (100 * c.height / c.width))
    elif a.cmd == 'crops':
        name, cols = a.args[0], []
        cw = a.width or 700
        for spec in a.args[1:]:
            parts = spec.split(':')
            tag, p, bb = parts[0], parts[1], [float(v) for v in parts[2].split(',')]
            rot = 0
            if len(parts) > 3:
                rot = {'r': 180, 'r180': 180, 'r90': 90, 'r270': 270}.get(parts[3], 0)
            c = crop_img(a.work, a.cote, p, bb, rot)
            w = min(cw, int(a.max_height * c.width / c.height))
            c = _grid_crop(c, w)
            col = Image.new('RGB', (max(c.width, 300), c.height + 22), 'white')
            ImageDraw.Draw(col).text((4, 2), f'{tag} p{p} {bb}  H={100 * c.height / c.width:.1f}', fill=(0, 0, 255), font=font(15))
            col.paste(c, (0, 22)); cols.append(col)
            print(f'{tag}: H units = {100 * c.height / c.width:.1f}')
        out = os.path.join(V, name)
        flow(cols).save(out, quality=72)
    elif a.cmd == 'overlays':
        name, cols = a.args[0], []
        for i in a.args[1:]:
            t = Image.open(os.path.join(a.work, 'out', a.cote, f'{i}-triptych.png'))
            cw = (t.width - 40) // 3
            ov = t.crop((10 + 2 * (cw + 10), 24, t.width, t.height))
            w = min(420, ov.width)
            ov = ov.resize((w, int(ov.height * w / ov.width)))
            col = Image.new('RGB', (ov.width, ov.height + 20), 'white')
            ImageDraw.Draw(col).text((3, 2), i, fill=(0, 0, 255), font=font(14)); col.paste(ov, (0, 20))
            cols.append(col)
        out = os.path.join(V, name)
        flow(cols, maxw=1300, gap=6).save(out, quality=70)
    print(out)


if __name__ == '__main__':
    main()
