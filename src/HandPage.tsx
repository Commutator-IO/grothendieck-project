import { useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import handRaw from './content/hand.json';

/**
 * The hand, measured: what the transcriptions could read, what they could
 * not, what he struck and added, and what he drew.
 *
 * Every number here is counted by `npm run hand` from the transcription
 * apparatus — `\ill{}`, `\uncertain{}`, `\struck{}`, `\add{}`, `\marginal{}`,
 * `tikzcd` — and not from the ink. They say how a first pass fared with each
 * folder, which is a fact about the hand and about the pass at once; the page
 * says so before the first figure and does not let a chart forget it.
 */

interface Folder {
  id: string;
  title: string;
  date: string;
  year: number | null;
  batches: number;
  pages: number;
  words: number;
  ill: number;
  uncertain: number;
  struck: number;
  add: number;
  marginal: number;
  diagrams: number;
  drawings: number;
  math: number;
  languages: string[];
}
const HAND = handRaw as unknown as {
  built: string;
  folders: Folder[];
  abbreviations: { form: string; n: number }[];
};
const FOLDERS = HAND.folders;

const BLUE = '#38539d';
const AMBER = '#c9900c';
const GREEN = '#128557';

/** Share of the words that could not be read: an `\ill{}` stands for one word. */
const unread = (f: Folder) => f.ill / Math.max(1, f.words + f.ill);
const doubtful = (f: Folder) => f.uncertain / Math.max(1, f.words + f.ill);
const perK = (n: number, f: Folder) => (1000 * n) / Math.max(1, f.words + f.ill);
const pct = (x: number, d = 1) => `${(100 * x).toFixed(d)}%`;
const n = (x: number) => x.toLocaleString('en-GB');
const shortTitle = (t: string) => t.replace(/\s*:\s*notes manuscrites.*$/i, '').replace(/\s*:.*$/, '');
const byShelfmark = (a: string, b: string) => {
  const [a0, a1 = '0'] = a.split('-');
  const [b0, b1 = '0'] = b.split('-');
  return Number(a0) - Number(b0) || Number(a1) - Number(b1);
};

function Kpi({ value, label, help }: { value: string; label: string; help?: string }) {
  return (
    <div className="card px-4 py-3">
      <p className="tabular text-[24px] font-semibold leading-tight text-ink-900">{value}</p>
      <p className="mt-0.5 text-[12.5px] text-ink-600">{label}</p>
      {help && <p className="mt-1 text-[11.5px] leading-snug text-ink-400">{help}</p>}
    </div>
  );
}

function H2({ id, children }: { id: string; children: React.ReactNode }) {
  return (
    <h2 id={id} className="scroll-mt-16 text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
      {children}
    </h2>
  );
}

/* ---------- 1. legibility against the inventory's dating ---------- */

function LegibilityOverTime() {
  const [sel, setSel] = useState<Folder | null>(null);
  const W = 900;
  const H = 340;
  const L = 48;
  const R = 110; // room for the undated column
  const T = 16;
  const B = 34;
  const y0 = 1949;
  const y1 = 1991;
  const top = Math.ceil(Math.max(...FOLDERS.map(unread)) * 10) / 10;
  const x = (y: number) => L + ((y - y0) / (y1 - y0)) * (W - L - R);
  const y = (v: number) => T + (1 - v / top) * (H - T - B);
  const r = (f: Folder) => 2.5 + 1.1 * Math.sqrt(f.pages);
  const undated = FOLDERS.filter((f) => f.year === null).sort((a, b) => unread(b) - unread(a));
  const ux = W - R / 2 + 10;
  const ticks = Array.from({ length: Math.round(top * 10) + 1 }, (_, i) => i / 10);

  return (
    <section className="mt-12">
      <H2 id="over-time">What could not be read, folder by folder, against the inventory's dating</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        Each dot is a folder, placed at the middle of the archivists' dating — a guess from a
        verso more often than a date he wrote — and at the share of its words the first pass left{' '}
        <code className="rounded bg-ink-100 px-1 text-[12px]">\ill{'{}'}</code>. A larger dot, more pages
        read. Undated folders stand in the column at the right.
      </p>
      <div className="mt-3 overflow-x-auto" onMouseLeave={() => setSel(null)}>
        <svg
          viewBox={`0 0 ${W} ${H}`}
          className="w-full min-w-[640px] rounded-[var(--radius-card)] border border-ink-200 bg-white"
          role="img"
          aria-label="Share of unread words per folder, by the inventory's dating"
        >
          {ticks.map((t) => (
            <g key={t}>
              <line x1={L} x2={W - 12} y1={y(t)} y2={y(t)} stroke="var(--color-ink-200)" strokeWidth="1" />
              <text x={L - 8} y={y(t) + 4} textAnchor="end" className="tabular" style={{ fontSize: 11, fill: 'var(--color-ink-400)' }}>
                {Math.round(t * 100)}%
              </text>
            </g>
          ))}
          {[1950, 1955, 1960, 1965, 1970, 1975, 1980, 1985, 1990].map((yr) => (
            <text key={yr} x={x(yr)} y={H - 12} textAnchor="middle" className="tabular" style={{ fontSize: 11, fill: 'var(--color-ink-400)' }}>
              {yr}
            </text>
          ))}
          <text x={ux} y={H - 12} textAnchor="middle" style={{ fontSize: 11, fill: 'var(--color-ink-400)' }}>
            s.d.
          </text>
          <line x1={W - R + 8} x2={W - R + 8} y1={T} y2={H - B} stroke="var(--color-ink-200)" strokeDasharray="3 3" />
          {[...FOLDERS]
            .sort((a, b) => b.pages - a.pages)
            .map((f) => {
              const k = undated.indexOf(f);
              const cx = f.year === null ? ux + ((k % 3) - 1) * 18 : x(f.year);
              const on = sel === null || sel === f;
              return (
                <g key={f.id} tabIndex={0} onMouseEnter={() => setSel(f)} onFocus={() => setSel(f)} style={{ cursor: 'pointer', outline: 'none' }}>
                  <circle cx={cx} cy={y(unread(f))} r={r(f) + 5} fill="#fff" fillOpacity={0} />
                  <circle
                    cx={cx}
                    cy={y(unread(f))}
                    r={r(f)}
                    fill={BLUE}
                    fillOpacity={on ? 0.55 : 0.12}
                    stroke="#fff"
                    strokeWidth="1.5"
                  />
                  <title>{`n° ${f.id} — ${pct(unread(f))} unread`}</title>
                </g>
              );
            })}
          {sel && (
            <circle
              cx={sel.year === null ? ux + ((undated.indexOf(sel) % 3) - 1) * 18 : x(sel.year)}
              cy={y(unread(sel))}
              r={r(sel) + 2}
              fill="none"
              stroke="var(--color-ink-900)"
              strokeWidth="1.5"
            />
          )}
        </svg>
      </div>
      <p className="mt-2 min-h-[3em] text-[12.5px] leading-relaxed text-ink-600">
        {sel ? (
          <>
            <a href={`/archive/#${sel.id}/1`} className="tabular font-semibold text-ink-900 hover:text-brand-700">
              n° {sel.id}
            </a>{' '}
            {shortTitle(sel.title)} <span className="text-ink-400">· {sel.date || 's.d.'}</span>
            <br />
            <span className="tabular">
              {n(sel.pages)} pages, {n(sel.words)} words read, {pct(unread(sel))} unread, {(100 * doubtful(sel)).toFixed(1)} doubtful readings per hundred words
            </span>
          </>
        ) : (
          <span className="text-ink-400">
            Hover or focus a dot for the folder. No trend is drawn: the datings are ranges, often
            decades wide, and a line through their midpoints would claim a precision they lack.
          </span>
        )}
      </p>
    </section>
  );
}

/* ---------- 2. every folder, as a table with bars ---------- */

type Col = 'id' | 'pages' | 'unread' | 'doubtful' | 'struck' | 'add' | 'marginal' | 'diagrams' | 'math';
const COLS: { key: Col; label: string; help: string; value: (f: Folder) => number; fmt: (f: Folder) => string; colour?: string }[] = [
  { key: 'pages', label: 'Pages', help: 'pages transcribed', value: (f) => f.pages, fmt: (f) => n(f.pages) },
  { key: 'unread', label: 'Unread', help: 'share of words left \\ill{}', value: unread, fmt: (f) => pct(unread(f)), colour: BLUE },
  { key: 'doubtful', label: 'Doubtful', help: 'readings in \\uncertain{}, per hundred words', value: doubtful, fmt: (f) => (100 * doubtful(f)).toFixed(1), colour: AMBER },
  { key: 'struck', label: 'Struck', help: 'his strike-outs, per thousand words', value: (f) => perK(f.struck, f), fmt: (f) => perK(f.struck, f).toFixed(0) },
  { key: 'add', label: 'Added', help: 'his insertions, per thousand words', value: (f) => perK(f.add, f), fmt: (f) => perK(f.add, f).toFixed(0) },
  { key: 'marginal', label: 'Margin', help: 'margin notes, per hundred pages', value: (f) => (100 * f.marginal) / Math.max(1, f.pages), fmt: (f) => ((100 * f.marginal) / Math.max(1, f.pages)).toFixed(0) },
  { key: 'diagrams', label: 'Diagrams', help: 'commutative diagrams, per hundred pages', value: (f) => (100 * f.diagrams) / Math.max(1, f.pages), fmt: (f) => ((100 * f.diagrams) / Math.max(1, f.pages)).toFixed(0), colour: GREEN },
  { key: 'math', label: 'Formulas', help: 'share of the text set as mathematics', value: (f) => f.math, fmt: (f) => pct(f.math, 0) },
];

function FolderTable() {
  const [sort, setSort] = useState<Col>('id');
  const rows = useMemo(() => {
    const col = COLS.find((c) => c.key === sort);
    return [...FOLDERS].sort((a, b) => (col ? col.value(b) - col.value(a) : 0) || byShelfmark(a.id, b.id));
  }, [sort]);
  const max = Object.fromEntries(COLS.map((c) => [c.key, Math.max(...FOLDERS.map(c.value))]));

  return (
    <section className="mt-12">
      <H2 id="folders">Every folder read so far</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        Rates rather than counts, so that a folder of forty pages sits beside one of four hundred.
        Sort by any column; the bars are scaled to the column's largest value.
      </p>
      <div className="mt-3 max-h-[34rem] overflow-auto rounded-[var(--radius-card)] border border-ink-200 bg-white">
        <table className="w-full min-w-[820px] text-[12.5px]">
          <thead className="sticky top-0 z-10 bg-white text-left text-[11px] uppercase tracking-wide text-ink-400">
            <tr className="border-b border-ink-200">
              <th className="px-3 py-2 font-semibold">
                <button type="button" onClick={() => setSort('id')} className={sort === 'id' ? 'text-ink-900' : 'hover:text-ink-900'}>
                  Folder
                </button>
              </th>
              {COLS.map((c) => (
                <th key={c.key} className="px-2 py-2 font-semibold" title={c.help}>
                  <button type="button" onClick={() => setSort(c.key)} className={sort === c.key ? 'text-ink-900' : 'hover:text-ink-900'}>
                    {c.label}
                    {sort === c.key && ' ↓'}
                  </button>
                </th>
              ))}
            </tr>
          </thead>
          <tbody>
            {rows.map((f) => (
              <tr key={f.id} className="border-b border-ink-100 last:border-0 hover:bg-ink-50">
                <td className="w-[15rem] whitespace-nowrap px-3 py-1.5">
                  <a href={`/archive/#${f.id}/1`} className="tabular font-semibold text-ink-900 hover:text-brand-700">
                    {f.id}
                  </a>{' '}
                  <span className="text-ink-500" title={f.title}>
                    {shortTitle(f.title).slice(0, 26)}
                    {shortTitle(f.title).length > 26 ? '…' : ''}
                  </span>
                </td>
                {COLS.map((c) => (
                  <td key={c.key} className="px-2 py-1.5">
                    <div className="flex items-center gap-1.5">
                      <span className="tabular w-10 shrink-0 text-right text-ink-700">{c.fmt(f)}</span>
                      <span className="h-1.5 w-10 rounded-full bg-ink-100">
                        <span
                          className="block h-1.5 rounded-full"
                          style={{ width: `${(100 * c.value(f)) / (max[c.key] || 1)}%`, background: c.colour ?? 'var(--color-ink-400)' }}
                        />
                      </span>
                    </div>
                  </td>
                ))}
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </section>
  );
}

/* ---------- 3. small multiples: the apparatus by kind ---------- */

function Multiples() {
  // The five measures side by side, each over the folders in shelfmark
  // order: one strip per measure, the same x for every strip.
  const order = [...FOLDERS].sort((a, b) => byShelfmark(a.id, b.id));
  const W = 900;
  const h = 46;
  const L = 96;
  const bw = (W - L - 8) / order.length;
  const measures = COLS.filter((c) => ['unread', 'doubtful', 'struck', 'marginal', 'diagrams'].includes(c.key));
  const [sel, setSel] = useState<Folder | null>(null);
  return (
    <section className="mt-12">
      <H2 id="strips">The same measures across the fonds, in shelfmark order</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        One strip per measure, one bar per folder, the folders in the inventory's order — which is
        roughly by subject: crystals, motives, topoi, then the long runs of the 1980s. Hover a bar
        to read the folder across all five.
      </p>
      <div className="mt-3 overflow-x-auto" onMouseLeave={() => setSel(null)}>
        <svg
          viewBox={`0 0 ${W} ${measures.length * (h + 10) + 20}`}
          className="w-full min-w-[640px] rounded-[var(--radius-card)] border border-ink-200 bg-white"
          role="img"
          aria-label="Five apparatus measures per folder, in shelfmark order"
        >
          {measures.map((m, j) => {
            const top = 10 + j * (h + 10);
            const mx = Math.max(...order.map(m.value)) || 1;
            return (
              <g key={m.key}>
                <text x={10} y={top + h / 2 + 4} style={{ fontSize: 11.5, fill: 'var(--color-ink-600)' }}>
                  {m.label}
                </text>
                <line x1={L} x2={W - 8} y1={top + h} y2={top + h} stroke="var(--color-ink-200)" />
                {order.map((f, i) => {
                  const v = (m.value(f) / mx) * h;
                  return (
                    <rect
                      key={f.id}
                      x={L + i * bw + 0.5}
                      y={top + h - v}
                      width={Math.max(1, bw - 1)}
                      height={Math.max(0.5, v)}
                      fill={m.colour ?? 'var(--color-ink-400)'}
                      opacity={sel === null || sel === f ? 0.85 : 0.25}
                    />
                  );
                })}
              </g>
            );
          })}
          {order.map((f, i) => (
            <rect
              key={f.id}
              x={L + i * bw}
              y={0}
              width={bw}
              height={measures.length * (h + 10) + 20}
              fill="#fff"
              fillOpacity={0}
              onMouseEnter={() => setSel(f)}
            >
              <title>{`n° ${f.id}`}</title>
            </rect>
          ))}
        </svg>
      </div>
      <p className="tabular mt-2 min-h-[1.5em] text-[12.5px] text-ink-600">
        {sel ? (
          <>
            <span className="font-semibold text-ink-900">n° {sel.id}</span> {shortTitle(sel.title)} —{' '}
            {measures.map((m) => `${m.label.toLowerCase()} ${m.fmt(sel)}`).join(' · ')}
          </>
        ) : (
          <span className="text-ink-400">Struck is per thousand words; margin and diagrams per hundred pages.</span>
        )}
      </p>
    </section>
  );
}

/* ---------- 4. languages and abbreviations ---------- */

const LANG: Record<string, string> = { fr: 'French', en: 'English', de: 'German' };

function Languages() {
  const mixed = FOLDERS.filter((f) => f.languages.length > 1 || f.languages[0] !== 'fr').sort((a, b) => byShelfmark(a.id, b.id));
  const french = FOLDERS.length - mixed.length;
  return (
    <section className="mt-12">
      <H2 id="languages">The languages he wrote in</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        {french} of the {FOLDERS.length} folders are in French throughout. The others, where a second
        language carries at least a fifth as many of its common words as the first — letters to
        and from colleagues abroad, notes written for them:
      </p>
      <ul className="mt-2 grid gap-x-6 gap-y-1 text-[12.5px] text-ink-600 sm:grid-cols-2">
        {mixed.map((f) => (
          <li key={f.id}>
            <a href={`/archive/#${f.id}/1`} className="tabular font-semibold text-ink-900 hover:text-brand-700">
              n° {f.id}
            </a>{' '}
            {shortTitle(f.title).slice(0, 44)} <span className="text-ink-400">— {f.languages.map((l) => LANG[l] ?? l).join(', ')}</span>
          </li>
        ))}
      </ul>
    </section>
  );
}

function Abbreviations() {
  const list = HAND.abbreviations.slice(0, 24);
  const max = list[0]?.n ?? 1;
  return (
    <section className="mt-12">
      <H2 id="abbreviations">His abbreviations</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        The shortened words that recur most in the transcriptions, counted by the lexicon the
        transcription pass reads before a hard leaf. They are what a reader learns first: « ens. »
        is <em>ensemble</em>, « isom. » <em>isomorphisme</em>, « t.f. » <em>de type fini</em>.
      </p>
      <ul className="mt-3 grid gap-x-8 gap-y-1 text-[12.5px] sm:grid-cols-2">
        {list.map((a) => (
          <li key={a.form} className="flex items-center gap-2">
            <span className="w-16 shrink-0 font-medium text-ink-900">{a.form}</span>
            <span className="h-2 flex-1 rounded-full bg-ink-100">
              <span className="block h-2 rounded-full" style={{ width: `${(100 * a.n) / max}%`, background: BLUE }} />
            </span>
            <span className="tabular w-12 shrink-0 text-right text-ink-500">{n(a.n)}</span>
          </li>
        ))}
      </ul>
    </section>
  );
}

export function HandPage() {
  const t = useMemo(() => {
    const s = (k: keyof Folder) => FOLDERS.reduce((a, f) => a + (f[k] as number), 0);
    return {
      pages: s('pages'),
      words: s('words'),
      ill: s('ill'),
      uncertain: s('uncertain'),
      struck: s('struck'),
      add: s('add'),
      marginal: s('marginal'),
      diagrams: s('diagrams'),
      drawings: s('drawings'),
    };
  }, []);

  return (
    <>
      <Header path="/hand/" />

      <main className="mx-auto max-w-5xl px-5 py-12">
        <header className="max-w-[44em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.14em] text-ink-400">The hand</p>
          <h1 className="titre mt-2 text-[30px] leading-tight text-ink-900">
            What the pages could and could not give up
          </h1>
          <p className="mt-4 text-[15.5px] leading-relaxed text-ink-600">
            He wrote fast, in ink and pencil, over and between his own lines, and struck as freely as
            he wrote. This page counts what the transcriptions record of that: words left
            unread, readings marked doubtful, strike-outs and insertions, margins, diagrams and
            drawings — folder by folder, across the {FOLDERS.length} folders begun so far.
          </p>
        </header>

        <div className="mt-6 rounded-[var(--radius-card)] border border-encours-200 bg-encours-50 px-4 py-3 text-[13px] leading-relaxed text-ink-700">
          <strong className="font-semibold">These count the transcription, not the ink.</strong> An{' '}
          <code className="text-[12px]">\ill{'{}'}</code> is a word a first machine pass could not read: it
          measures the hand and the pass together, and a folder read again would count differently.
          The folders are comparable with one another only because the same rules produced every
          file.
        </div>

        <div className="mt-6 grid grid-cols-2 gap-3 sm:grid-cols-4">
          <Kpi value={n(t.pages)} label="pages transcribed" />
          <Kpi value={n(t.words)} label="words read" help="prose outside the formulas, his margins included" />
          <Kpi value={pct(t.ill / (t.words + t.ill))} label="of words unread" help={`${n(t.ill)} \\ill{}`} />
          <Kpi value={n(t.uncertain)} label="doubtful readings" help={`\\uncertain{}, ${(100 * t.uncertain / (t.words + t.ill)).toFixed(1)} per hundred words`} />
          <Kpi value={n(t.struck)} label="strike-outs" help={`and ${n(t.add)} insertions`} />
          <Kpi value={n(t.marginal)} label="margin notes" />
          <Kpi value={n(t.diagrams)} label="commutative diagrams" help="set in tikz-cd, read from his drawing" />
          <Kpi value={n(t.drawings)} label="drawings" help="figures described in a note, not redrawn" />
        </div>

        <LegibilityOverTime />
        <Multiples />
        <FolderTable />
        <Languages />
        <Abbreviations />

        <p className="mt-12 max-w-[44em] text-[12px] leading-relaxed text-ink-400">
          Built on {HAND.built} by <code>npm run hand</code> from transcripts/*/batch-*.fr.tex. The
          transcriber's notes are left out of every count but the drawings; his margins are
          counted both as words and as margins. Language is judged by common function words, so a
          quoted title does not make a folder bilingual.
        </p>
      </main>

      <Footer />
    </>
  );
}
