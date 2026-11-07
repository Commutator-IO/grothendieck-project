"""Headline estimate of the carbon article, subagents whose log was deleted included (#121).

usage: python3 computations/carbon/headline.py > computations/carbon/headline.txt

Reads computations/carbon/activity.txt (the output of activity.py, run on the evening of
7 November 2026) and recomputes every inference figure of docs/carbon/article.tex from it,
with the method of the article's section « Méthode »:

* tokens weighted by list price relative to an output token (catalogue weighting), and a
  high weighting (one-hour writes at 0.40, reads at 0.02);
* energy 0.5 / 2 / 5 mWh per output-equivalent token, grid 0.2 / 0.3 / 0.4 kgCO2e/kWh;
* extrapolation to the whole project (7 August -- 7 November) x1.2 / x1.5 / x2.5;
* the low bound combines the low extremes (catalogue weighting, low subagent estimate),
  the high bound the high extremes (high weighting, high subagent estimate).

The subagents launched in the window whose log was deleted are now added to the measured
tokens: central +62.5 M, low +34.2 M, high +172.9 M (activity.txt). Work run from the same
folder for other projects (0.4 M) is left out, as in the table by activity.

Continuous integration and the laptop are not inference and keep the article's figures.

If the Claude Code logs are present, the script also prints the per-model token counts of
the table tab:jetons, from the messages up to 2026-11-07T17:43Z: that cut-off gives back the
19 235 messages and the per-model totals of activity.txt.
"""
import collections, glob, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ACT = os.path.join(HERE, 'activity.txt')
LOGDIR = os.path.expanduser('~/.claude/projects/-Users-michel-Commutator-grothendieck-project')
CUTOFF = '2026-11-07T17:43'

E = (0.5e-6, 2e-6, 5e-6)        # kWh per output-equivalent token (low, central, high)
G = (0.2, 0.3, 0.4)             # kgCO2e per kWh
X = (1.2, 1.5, 2.5)             # extrapolation to the whole project
DAYS = 44                       # days of the measured window
PAGES, THEOREMS = 9414, 6685
MISTRAL = 1.14e-3 / 400         # kgCO2e per output-equivalent token (400-token answer)
CI_KWH, CI_KG = (5, 6.6, 10), (1.0, 2.0, 4.2)       # article, unchanged
LAPTOP_KWH = (15, 22.5, 30)                          # article, unchanged
LAPTOP_KG = tuple(k * 0.06 for k in LAPTOP_KWH)     # French grid, 60 g/kWh


def parse():
    txt = open(ACT, encoding='utf-8').read()
    proj = re.search(r'^project \(measured\)\t+([\d.]+)\t[\d.]+\t([\d.]+)\t([\d.]+)\t([\d.]+)$', txt, re.M)
    sub = re.search(r'^all\t\d+\t\d+\t([\d.]+)\t([\d.]+)\t([\d.]+)$', txt, re.M)
    cal = re.search(r'= ([\d.]+) \(min\), ([\d.]+) \(median\), ([\d.]+) \(max\)', txt)
    m = float(proj.group(1)) * 1e6
    m_high = float(proj.group(4)) / (E[2] * G[2])          # high-weighted measured tokens
    s = tuple(float(sub.group(i)) * 1e6 for i in (1, 2, 3))
    r = tuple(float(cal.group(i)) for i in (1, 2, 3))
    return m, m_high, s, r


def per_model():
    files = glob.glob(os.path.join(LOGDIR, '**', '*.jsonl'), recursive=True)
    if not files:
        return None
    seen, agg = set(), collections.defaultdict(collections.Counter)
    for f in sorted(files, key=os.path.getsize, reverse=True):
        for line in open(f, encoding='utf-8', errors='replace'):
            try:
                d = json.loads(line)
            except ValueError:
                continue
            if d.get('type') != 'assistant':
                continue
            msg = d.get('message') or {}
            mid = msg.get('id')
            if not mid or mid in seen or msg.get('model') in (None, '<synthetic>'):
                continue
            seen.add(mid)
            if d.get('timestamp', '') > CUTOFF:
                continue
            u = msg.get('usage') or {}
            a = agg[msg['model']]
            a['calls'] += 1
            a['out'] += u.get('output_tokens', 0) or 0
            a['cw'] += u.get('cache_creation_input_tokens', 0) or 0
            a['cr'] += u.get('cache_read_input_tokens', 0) or 0
    return agg


def main():
    m, m_high, s, r = parse()
    # The subagent estimate at the high weighting but the median calibration, for the
    # Mistral cross-check (which, as in the article, spans the weighting only).
    s_high_med = s[2] * r[1] / r[2]
    tok = (m + s[0], m + s[1], m_high + s[2])               # low, central, high
    print('# inputs from activity.txt')
    print(f'measured tokens (project, catalogue weighting)\t{m / 1e6:.1f} M')
    print(f'measured tokens (project, high weighting)\t{m_high / 1e6:.1f} M')
    print(f'deleted subagents, low / central / high\t{s[0] / 1e6:.1f} / {s[1] / 1e6:.1f} / {s[2] / 1e6:.1f} M')
    print(f'calibration min / median / max\t{r[0]} / {r[1]} / {r[2]}')
    print(f'tokens used, low / central / high\t{tok[0] / 1e6:.1f} / {tok[1] / 1e6:.1f} / {tok[2] / 1e6:.1f} M')
    print(f'subagents at high weighting, median calibration\t{s_high_med / 1e6:.1f} M')
    print()

    w_kwh = tuple(t * e for t, e in zip(tok, E))
    w_kg = tuple(k * g for k, g in zip(w_kwh, G))
    p_kwh = tuple(k * x for k, x in zip(w_kwh, X))
    p_kg = tuple(k * x for k, x in zip(w_kg, X))
    print('# table tab:resultats (low / central / high)')
    print(f'inference, measured window\t{w_kwh[0]:.1f} / {w_kwh[1]:.1f} / {w_kwh[2]:.1f} kWh'
          f'\t{w_kg[0]:.1f} / {w_kg[1]:.1f} / {w_kg[2]:.1f} kg')
    print(f'inference, whole project\t{p_kwh[0]:.1f} / {p_kwh[1]:.1f} / {p_kwh[2]:.1f} kWh'
          f'\t{p_kg[0]:.1f} / {p_kg[1]:.1f} / {p_kg[2]:.1f} kg')
    print(f'continuous integration (unchanged)\t{CI_KWH[0]} -- {CI_KWH[2]} kWh\t{CI_KG[0]} -- {CI_KG[2]} kg')
    print(f'laptop, website (unchanged)\t{LAPTOP_KWH[0]} -- {LAPTOP_KWH[2]} kWh'
          f'\t{LAPTOP_KG[0]:.1f} -- {LAPTOP_KG[2]:.1f} kg')
    t_kwh = p_kwh[1] + CI_KWH[1] + LAPTOP_KWH[1]
    t_kg = p_kg[1] + CI_KG[1] + LAPTOP_KG[1]
    print(f'total, central\t{t_kwh:.0f} kWh\t{t_kg:.1f} kg')
    print()

    mis_w = (tok[1] * MISTRAL, (m_high + s_high_med) * MISTRAL)
    mis_p = tuple(k * X[1] for k in mis_w)
    print('# cross-check with Mistral Large 2 (1.14 g per 400-token answer)')
    print(f'measured window\t{mis_w[0]:.0f} -- {mis_w[1]:.0f} kg')
    print(f'whole project (x1.5)\t{mis_p[0]:.0f} -- {mis_p[1]:.0f} kg')
    print(f'ratio to the central inference estimate\t{mis_p[0] / p_kg[1]:.1f} -- {mis_p[1] / p_kg[1]:.1f}')
    print()

    yr = tuple(k / DAYS * 365 / 1e3 for k in w_kg)
    yr_m = tuple(k / DAYS * 365 / 1e3 for k in mis_w)
    print('# figure fig:echelle and its paragraph (t per year at the pace of the measured weeks)')
    print(f'project, one year\t{yr[0]:.2f} / {yr[1]:.2f} / {yr[2]:.2f} t')
    print(f'with hardware (Mistral)\t{yr_m[0]:.2f} -- {yr_m[1]:.2f} t')
    print(f'three months, central, share of a researcher-year (3.6 t)\t{p_kg[1] / 3600:.3f}')
    print(f'three months, extremes: low / 5 t, high / 2 t\t{p_kg[0] / 5000:.4f} / {p_kg[2] / 2000:.2f}')
    print(f'one year, share of the group (7 t central; low / 25 t, high / 2 t)\t'
          f'{yr[1] / 7:.3f}; {yr[0] / 25:.4f} / {yr[2] / 2:.2f}')
    print()

    print('# per page and per theorem')
    print(f'whole-project inference per page ({PAGES} pages)\t'
          f'{p_kg[0] * 1e3 / PAGES:.1f} / {p_kg[1] * 1e3 / PAGES:.1f} / {p_kg[2] * 1e3 / PAGES:.0f} g')
    print('transcription per page and Lean per theorem: already measured + estimated in activity.txt'
          ' (0.30 / 2.76 / 23.39 g per page, 0.40 / 2.88 / 20.69 g per theorem), unchanged')
    print()

    agg = per_model()
    if agg is None:
        return
    print(f'# table tab:jetons: messages up to {CUTOFF}Z, de-duplicated by message id')
    print('model\tcalls\tout_M\tcw_M\tcr_G\teq_M\tper call: cr / cw / out')
    tot = collections.Counter()
    for k, a in sorted(agg.items()):
        w = 0.02 if 'haiku' in k else 0.01
        e = a['out'] + 0.25 * a['cw'] + w * a['cr']
        tot.update(a)
        tot['eq'] += e
        tot['eqh'] += a['out'] + 0.40 * a['cw'] + 2 * w * a['cr']
        n = a['calls']
        print(f"{k}\t{n}\t{a['out'] / 1e6:.3f}\t{a['cw'] / 1e6:.2f}\t{a['cr'] / 1e9:.4f}\t{e / 1e6:.2f}"
              f"\t{a['cr'] / n:.0f} / {a['cw'] / n:.0f} / {a['out'] / n:.0f}")
    print(f"all\t{tot['calls']}\t{tot['out'] / 1e6:.3f}\t{tot['cw'] / 1e6:.2f}\t{tot['cr'] / 1e9:.4f}\t"
          f"{tot['eq'] / 1e6:.2f}")
    cw_e, cr_e = 0.25 * tot['cw'], tot['eq'] - tot['out'] - 0.25 * tot['cw']
    print(f"catalogue weighting: output {tot['out'] / 1e6:.1f} M, writes {cw_e / 1e6:.1f} M, reads {cr_e / 1e6:.1f} M;"
          f" shares {tot['out'] / tot['eq']:.3f} / {cw_e / tot['eq']:.3f} / {cr_e / tot['eq']:.3f}")
    cwh, crh = 0.40 * tot['cw'], tot['eqh'] - tot['out'] - 0.40 * tot['cw']
    print(f"high weighting: total {tot['eqh'] / 1e6:.1f} M, writes {cwh / 1e6:.1f} M, reads {crh / 1e6:.1f} M"
          f" (share {crh / tot['eqh']:.3f})")
    raw = tot['out'] + tot['cw'] + tot['cr']
    print(f"cache reads, share of raw tokens\t{tot['cr'] / raw:.3f}")


if __name__ == '__main__':
    main()
