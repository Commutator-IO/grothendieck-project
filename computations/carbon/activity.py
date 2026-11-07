"""Cost of the project by activity, from the Claude Code session logs (#121).

usage: python3 computations/carbon/activity.py [LOGDIR] > computations/carbon/activity.txt

Reads every *.jsonl under LOGDIR (default: this project's Claude Code log
folder), line by line, and prints aggregates only: no message text leaves the
script. Method of docs/carbon/article.tex, section « Méthode »:

* assistant messages de-duplicated by message id (the session files are
  cumulative copies of one another);
* tokens weighted by list price relative to an output token: output 1, cache
  write 0.25, cache read 0.01 (Haiku 0.02); high weighting: writes 0.40,
  reads 0.02. Uncached input is left out, as in the article;
* energy 0.5 / 2 / 5 mWh per output-equivalent token, grid 0.2 / 0.3 / 0.4
  kgCO2e per kWh (low / central / high; the low and high bounds combine the
  extremes, as in the article).

Classification. The main thread is cut into segments, each opened by a
message that is not a tool result (a prompt of the author or a subagent's
completion notice). A segment is given the activity that scores highest from
the skills it calls, the files it writes, edits or reads, the commands it runs
and the briefs of the subagents it launches; a subagent is classified the same
way from its brief and its own tool calls. Segments with no signal go to
« pilotage ». Sessions that belong to other work run from the same folder
(titles listed in OTHER_TITLES) are counted apart.

Subagents whose log was deleted (Claude Code kept 14 days of history until
7 November 2026) are not in the token totals of the article. Their brief and
their model are still in the main thread; when their completion notice gives
a tool count, their weighted tokens are estimated from the subagents whose log
survives (median weighted tokens per tool call, per model). They are printed
as a separate line and not added to the measured totals.
"""
import collections, glob, json, os, re, statistics, subprocess, sys

LOGDIR = sys.argv[1] if len(sys.argv) > 1 else os.path.expanduser(
    '~/.claude/projects/-Users-michel-Commutator-grothendieck-project')
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
WINDOW_START = '2026-09-24'
OTHER_TITLES = {'Weekly communication review', 'Weekly teams agent channels check',
                'Monthly cra prep'}

CATS = [
    ('transcription', r'transcribe-grothendieck|batch-\d+\.fr\.tex|/batch-\d|transcri(re|ption|be)'
                      r'|vectoris|/drawings/|archives/raw|magick|sips -r|\\pagerange|status\.json'),
    ('modernisation', r'\.modern\.tex|moderni[sz]|tag-grothendieck|\\keywords|lecture modernis'),
    ('lean', r'grothendieck-project/lean/|(^|[\s\'"(=])lean/|\.lean\b|lake (build|env|exe)|mathlib'
             r'|mcp__lean|lean4:|tauceti|contribute-to-mathlib'),
    ('autres fonds', r'quillen|bourbaki|illusie|ihes|ihés|buffalo'),
    ('articles', r'docs/|article|tectonic|\.bib\b|humaniseur|humanizer|peer-review'
                 r'|citation-verification|palomar|rhm\b|jtei|cicm'),
    ('trouvailles et relecture', r'findings|find-novelty|/review/|review-queue|review-bnf'
                                 r'|rediscoveries|major-findings|literature'),
    ('site', r'grothendieck-project/src/|(^|\s)src/|scripts/|npm |vite|\.tsx?\b|mcp__claude_browser'
             r'|preview_|\.github|relay/|wrangler|/tei/|manifest\.mjs'),
]
CATS = [(n, re.compile(p, re.I)) for n, p in CATS]
ORDER = [n for n, _ in CATS] + ['pilotage', 'hors projet']

W_STD = {'out': 1, 'cw': 0.25, 'cr': 0.01}
W_HIGH = {'out': 1, 'cw': 0.40, 'cr': 0.02}


def weights(model, high):
    w = dict(W_HIGH if high else W_STD)
    if 'haiku' in (model or ''):
        w['cr'] = 0.02 if not high else 0.04
    return w


def eq(u, model, high=False):
    w = weights(model, high)
    return u['out'] * w['out'] + u['cw'] * w['cw'] + u['cr'] * w['cr']


def score_text(sc, text, weight):
    if not text:
        return
    for n, rx in CATS:
        if rx.search(text):
            sc[n] += weight


def tool_signals(sc, x):
    name, inp = x.get('name', ''), x.get('input') or {}
    if name == 'Skill':
        score_text(sc, str(inp.get('skill', '')), 5)
    elif name in ('Write', 'Edit', 'NotebookEdit'):
        score_text(sc, str(inp.get('file_path', '')), 3)
    elif name == 'Read':
        score_text(sc, str(inp.get('file_path', '')), 1)
    elif name == 'Bash':
        score_text(sc, str(inp.get('command', ''))[:400], 1)
    elif name == 'Agent':
        score_text(sc, str(inp.get('description', '')) + ' ' + str(inp.get('prompt', ''))[:3000], 2)
    else:
        score_text(sc, name, 1)


def classify(sc):
    if not sc:
        return 'pilotage'
    return max(sc.items(), key=lambda kv: (kv[1], -ORDER.index(kv[0])))[0]


def usage(m):
    u = m.get('usage') or {}
    return {'out': u.get('output_tokens', 0) or 0,
            'cw': u.get('cache_creation_input_tokens', 0) or 0,
            'cr': u.get('cache_read_input_tokens', 0) or 0}


def is_prompt(d):
    if d.get('type') != 'user':
        return False
    c = d.get('message', {}).get('content')
    if isinstance(c, str):
        return True
    return isinstance(c, list) and not any(isinstance(x, dict) and x.get('type') == 'tool_result' for x in c)


def prompt_text(d):
    c = d['message']['content']
    if isinstance(c, str):
        return c[:3000]
    return ' '.join(x.get('text', '') for x in c if isinstance(x, dict))[:3000]


def read_file(path):
    for line in open(path, encoding='utf-8', errors='replace'):
        try:
            yield json.loads(line)
        except ValueError:
            continue


def main():
    files = sorted(glob.glob(os.path.join(LOGDIR, '**', '*.jsonl'), recursive=True),
                   key=os.path.getsize, reverse=True)
    seen = set()
    msgs = []          # (model, usage, segment key, date)
    seg_scores = {}    # segment key -> Counter
    agent_launch = {}  # tool_use id -> (model param, Counter, date)
    agent_of_tool = {} # tool_use id -> agentId, resolvedModel
    agent_notice = {}  # agentId -> tool uses
    logged_agents = set()
    titles = {}
    for f in files:
        sub = '/subagents/' in f
        base = os.path.basename(f)[:-6]
        agent_id = base[6:] if sub else None
        if sub:
            logged_agents.add(agent_id)
        title = None
        seg = 0
        key = (base, 0)
        seg_scores.setdefault(key, collections.Counter())
        for d in read_file(f):
            t = d.get('type')
            if t == 'custom-title' and d.get('customTitle'):
                title = d['customTitle']
            if not sub and is_prompt(d) and not d.get('isMeta'):
                seg += 1
                key = (base, seg)
                sc = seg_scores.setdefault(key, collections.Counter())
                txt = prompt_text(d)
                score_text(sc, txt, 2)
                for blk in re.findall(r'<task-notification>(.*?)</task-notification>', txt, re.S):
                    a = re.search(r'<task-id>(.*?)</task-id>', blk)
                    n = re.search(r'<tool_uses>(\d+)</tool_uses>', blk)
                    T = re.search(r'<subagent_tokens>(\d+)</subagent_tokens>', blk)
                    if a and n and T:
                        agent_notice[a.group(1)] = (int(n.group(1)), int(T.group(1)))
            elif sub and is_prompt(d) and not d.get('isMeta'):
                score_text(seg_scores[key], prompt_text(d), 2)
            if t == 'user' and isinstance(d.get('toolUseResult'), dict):
                r = d['toolUseResult']
                if 'agentId' in r:
                    for x in d['message'].get('content') or []:
                        if isinstance(x, dict) and x.get('type') == 'tool_result':
                            agent_of_tool[x.get('tool_use_id')] = (r['agentId'], r.get('resolvedModel'))
                    if 'totalToolUseCount' in r:
                        agent_notice[r['agentId']] = (r['totalToolUseCount'], r.get('totalTokens') or 0)
            if t != 'assistant':
                continue
            m = d.get('message') or {}
            for x in m.get('content') or []:
                if isinstance(x, dict) and x.get('type') == 'tool_use':
                    tool_signals(seg_scores[key], x)
                    if x.get('name') == 'Agent':
                        sc = collections.Counter()
                        tool_signals(sc, x)
                        agent_launch[x.get('id')] = ((x.get('input') or {}).get('model'), sc,
                                                     d.get('timestamp', '')[:10])
            mid = m.get('id')
            if not mid or mid in seen or m.get('model') in (None, '<synthetic>'):
                continue
            seen.add(mid)
            msgs.append((m['model'], usage(m), key, d.get('timestamp', '')[:10]))
        titles[base] = title

    # Activity of each segment.
    cls = {}
    for key, sc in seg_scores.items():
        cls[key] = 'hors projet' if titles.get(key[0]) in OTHER_TITLES else classify(sc)
    # A subagent file is one segment: merge its segment scores.
    for key in list(cls):
        if key[0].startswith('agent-'):
            tot = collections.Counter()
            for k2, sc in seg_scores.items():
                if k2[0] == key[0]:
                    tot.update(sc)
            cls[key] = classify(tot)

    agg = collections.defaultdict(lambda: collections.Counter())
    calib = collections.defaultdict(lambda: collections.Counter())  # agentId -> eq, calls
    by_model = collections.Counter()
    for model, u, key, day in msgs:
        a = cls.get(key, 'pilotage')
        agg[a]['eq'] += eq(u, model)
        agg[a]['eqh'] += eq(u, model, True)
        agg[a]['calls'] += 1
        for k in u:
            agg[a][k] += u[k]
        by_model[model] += eq(u, model)
        if key[0].startswith('agent-'):
            calib[key[0][6:]]['eq'] += eq(u, model)
            calib[key[0][6:]]['eqh'] += eq(u, model, True)
            calib[key[0][6:]]['model'] = model

    # Calibration on logged subagents whose completion notice gives the tool count n and the
    # final context T. A context that grows to T over n + 1 calls is re-read about (n + 1) T / 2
    # times and written once: eq ~ r (w_cr (n + 1) T / 2 + w_cw T); r is fitted on the logs.
    def model_eq(n, T, model, high=False):
        w = weights(model, high)
        return w['cr'] * (n + 1) * T / 2 + w['cw'] * T
    ratios = []
    for aid, c in calib.items():
        if aid in agent_notice and agent_notice[aid][1]:
            n, T = agent_notice[aid]
            ratios.append(c['eq'] / model_eq(n, T, c['model']))
    ratios.sort()
    r_lo, r_med, r_hi = ratios[0], statistics.median(ratios), ratios[-1]

    missing = collections.defaultdict(lambda: collections.Counter())
    est_by_cat = collections.defaultdict(list)
    pending = []
    for tid, (mparam, sc, day) in agent_launch.items():
        aid, rmodel = agent_of_tool.get(tid, (None, None))
        if aid is None or aid in logged_agents or day < WINDOW_START:
            continue
        a = classify(sc)
        model = rmodel or mparam or 'opus'
        missing[a]['agents'] += 1
        n, T = agent_notice.get(aid, (None, None))
        if n is not None and T:
            e = model_eq(n, T, model)
            missing[a]['lo'] += r_lo * e
            missing[a]['est'] += r_med * e
            missing[a]['hi'] += r_hi * model_eq(n, T, model, True)
            missing[a]['with_count'] += 1
            est_by_cat[a].append((r_lo * e, r_med * e, r_hi * model_eq(n, T, model, True)))
        else:
            pending.append(a)
    allest = [x for v in est_by_cat.values() for x in v]
    for a in pending:  # no notice: the median agent of its activity (of all, if none)
        src = est_by_cat.get(a) or allest
        for i, k in enumerate(('lo', 'est', 'hi')):
            missing[a][k] += statistics.median(x[i] for x in src)

    # Pages transcribed in the window, from the batches' first commit.
    log = subprocess.run(['git', '-C', REPO, 'log', '--diff-filter=A', '--format=@%ad', '--date=short',
                          '--name-only', '--', 'transcripts/*/batch-*.fr.tex'],
                         capture_output=True, text=True).stdout
    first, date = {}, None
    for l in log.splitlines():
        if l.startswith('@'):
            date = l[1:]
        elif l.strip():
            first[l.strip()] = date
    pages = collections.Counter()
    for path in glob.glob(os.path.join(REPO, 'transcripts', '*', 'batch-*.fr.tex')):
        rel = os.path.relpath(path, REPO)
        if '/_specimen/' in rel:
            continue
        s = open(path, encoding='utf-8').read()
        p = len(re.findall(r'\\page\{', s)) + sum(int(b) - int(a) + 1 for a, b in
                                                 re.findall(r'\\pagerange\{(\d+)\}\{(\d+)\}', s))
        d0 = first.get(rel, '9999')
        pages['window' if d0 >= WINDOW_START else 'before'] += p

    # Lean theorems.
    thm = re.compile(r'^\s*(@\[[^\]]*\]\s*)?((private|protected|nonrec|noncomputable)\s+)*(theorem|lemma)\s', re.M)
    nthm = 0
    for path in glob.glob(os.path.join(REPO, 'lean', '**', '*.lean'), recursive=True):
        if '/.lake/' in path:
            continue
        nthm += len(thm.findall(open(path, encoding='utf-8').read()))

    def kg(e, eh):  # low, central, high, from output-equivalent tokens
        return e * 0.5e-6 * 0.2, e * 2e-6 * 0.3, eh * 5e-6 * 0.4

    total = sum(v['eq'] for v in agg.values())
    proj = total - agg['hors projet']['eq']
    print(f'# logs: {len(files)} files, {len(msgs)} assistant messages after de-duplication')
    print(f'# messages dated {min(m[3] for m in msgs)} to {max(m[3] for m in msgs)}')
    for k, v in sorted(by_model.items()):
        print(f'# {k}: {v / 1e6:.1f} M output-equivalent tokens')
    print(f'# total {total / 1e6:.1f} M, of which other work run from this folder {agg["hors projet"]["eq"] / 1e6:.2f} M')
    print()
    print('activity\tcalls\tout_M\tcw_M\tcr_G\teq_M\tshare_of_project\tkg_low\tkg_central\tkg_high')
    for a in ORDER:
        v = agg.get(a)
        if not v:
            continue
        lo, ce, hi = kg(v['eq'], v['eqh'])
        share = v['eq'] / proj if a != 'hors projet' else float('nan')
        print(f"{a}\t{v['calls']}\t{v['out'] / 1e6:.2f}\t{v['cw'] / 1e6:.1f}\t{v['cr'] / 1e9:.3f}\t"
              f"{v['eq'] / 1e6:.1f}\t{share:.3f}\t{lo:.1f}\t{ce:.1f}\t{hi:.1f}")
    lo, ce, hi = kg(proj, sum(v['eqh'] for a, v in agg.items() if a != 'hors projet'))
    print(f'project (measured)\t\t\t\t\t{proj / 1e6:.1f}\t1.000\t{lo:.1f}\t{ce:.1f}\t{hi:.1f}')
    print()
    print('# subagents launched in the window whose log was deleted (not in the totals above)')
    print(f'# calibration on {len(ratios)} logged subagents: logged / modelled tokens = '
          f'{r_lo:.2f} (min), {r_med:.2f} (median), {r_hi:.2f} (max)')
    print('activity\tagents\twith_notice\test_eq_M_low\test_eq_M\test_eq_M_high\tkg_low\tkg_central\tkg_high')
    for a in ORDER:
        v = missing.get(a)
        if not v:
            continue
        print(f"{a}\t{v['agents']}\t{v['with_count']}\t{v['lo'] / 1e6:.1f}\t{v['est'] / 1e6:.1f}\t{v['hi'] / 1e6:.1f}\t"
              f"{v['lo'] * 0.5e-6 * 0.2:.1f}\t{v['est'] * 2e-6 * 0.3:.1f}\t{v['hi'] * 5e-6 * 0.4:.1f}")
    m_lo = sum(v['lo'] for v in missing.values()); m_ce = sum(v['est'] for v in missing.values())
    m_hi = sum(v['hi'] for v in missing.values())
    print(f'all\t{sum(v["agents"] for v in missing.values())}\t{sum(v["with_count"] for v in missing.values())}\t'
          f'{m_lo / 1e6:.1f}\t{m_ce / 1e6:.1f}\t{m_hi / 1e6:.1f}')
    print()
    print('# measured + estimated, by activity')
    print('activity\teq_M\tshare\tkg_low\tkg_central\tkg_high')
    comb = {}
    for a in ORDER:
        if a == 'hors projet':
            continue
        v, w = agg.get(a, collections.Counter()), missing.get(a, collections.Counter())
        comb[a] = (v['eq'] + w['lo'], v['eq'] + w['est'], v['eqh'] + w['hi'])
    ctot = sum(x[1] for x in comb.values())
    for a, (lo_e, ce_e, hi_e) in comb.items():
        print(f'{a}\t{ce_e / 1e6:.1f}\t{ce_e / ctot:.3f}\t{lo_e * 0.5e-6 * 0.2:.1f}\t{ce_e * 2e-6 * 0.3:.1f}\t{hi_e * 5e-6 * 0.4:.1f}')
    lo_t = sum(x[0] for x in comb.values()); hi_t = sum(x[2] for x in comb.values())
    print(f'all\t{ctot / 1e6:.1f}\t1.000\t{lo_t * 0.5e-6 * 0.2:.1f}\t{ctot * 2e-6 * 0.3:.1f}\t{hi_t * 5e-6 * 0.4:.1f}')
    print()
    print(f"# pages transcribed (\\page and \\pagerange markers): {pages['before']} before {WINDOW_START}, "
          f"{pages['window']} in the window, {sum(pages.values())} in all")
    print(f'# Lean theorems and lemmas in lean/ (excluding .lake): {nthm}')
    for a, n, label in (('transcription', pages['window'], 'g per page transcribed in the window'),
                        ('lean', nthm, 'g per Lean theorem')):
        lo_e, ce_e, hi_e = comb[a]
        print(f'# {a}: {lo_e * 0.5e-6 * 0.2 * 1e3 / n:.2f} / {ce_e * 2e-6 * 0.3 * 1e3 / n:.2f} / '
              f'{hi_e * 5e-6 * 0.4 * 1e3 / n:.2f} {label} (low / central / high, measured + estimated)')
    # Cross-check from the per-batch measurements of src/MethodPage.tsx (PILOT.transcribe, twelve
    # passes of 25 September 2026): 25 M tokens of context and 75k written per batch of 20 pages,
    # the context split between cache writes and reads as in the measured transcription segments.
    t = agg['transcription']
    fw = t['cw'] / (t['cw'] + t['cr'])
    ctx, out = 25e6, 75e3
    e = (out + 0.25 * fw * ctx + 0.01 * (1 - fw) * ctx) / 20
    eh = (out + 0.40 * fw * ctx + 0.02 * (1 - fw) * ctx) / 20
    print(f'# cross-check, Method page batches: write share {fw:.3f}, {e:.0f} output-equivalent tokens '
          f'per page (high {eh:.0f}): {e * 0.5e-6 * 0.2 * 1e3:.1f} / {e * 2e-6 * 0.3 * 1e3:.1f} / '
          f'{eh * 5e-6 * 0.4 * 1e3:.1f} g per page')


if __name__ == '__main__':
    main()
