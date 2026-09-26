import { useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import { COTES } from './content/catalogue.ts';
import datedRaw from './content/dated-leaves.json';
import handRaw from './content/hand.json';
import { openEnd, parseDating, type Dating } from './lib/dating.ts';

/**
 * When the folders were written — and how anyone knows.
 *
 * Two kinds of date meet here and are never merged. The inventory's datings
 * are the archivists', mostly deduced (their square brackets), often decades
 * wide. The dates written on the leaves are his, or a typist's, or a machine's,
 * and exact — but rare, and only as many as the folders read so far. The page
 * draws the first as ranges and the second as dots over them, so that a reader
 * sees at once where the two agree, where they do not, and how little of the
 * fonds either covers.
 */

interface Leaf {
  folder: string;
  batch: number;
  page: string;
  written: string;
  iso: string | null;
  kind: string;
  hand: string;
  context: string;
  where: string;
}
const LEAVES = ((datedRaw as unknown as { records: Leaf[] }).records ?? []).filter((l) => l.iso);
/**
 * A machine stamp — the banner of a computer listing he wrote on the back of,
 * a postmark — dates the paper, not the writing: the leaf can be no older, and
 * may be years younger. Drawn hollow, and kept off the calendar of his days.
 */
const isStamp = (l: Leaf) => l.kind === 'stamp' || l.hand === 'machine';
const BEGUN = new Set((handRaw as unknown as { folders: { id: string }[] }).folders.map((f) => f.id));

const Y0 = 1949;
const Y1 = 1992;
const DARK = '#38539d';
const LIGHT = '#97afe1';
const DOT = '#c9900c';

/** A date as a fractional year: « 1983-12-31 » → 1983.997. */
function frac(iso: string): number {
  const [y, m, d] = iso.split('-').map(Number);
  if (!m) return y + 0.5;
  if (!d) return y + (m - 0.5) / 12;
  return y + (m - 1) / 12 + (d - 0.5) / 365;
}
const shortTitle = (t: string) => t.replace(/\s*:\s*notes manuscrites.*$/i, '').replace(/\s*:.*$/, '');
const byShelfmark = (a: string, b: string) => {
  const [a0, a1 = '0'] = a.split('-');
  const [b0, b1 = '0'] = b.split('-');
  return Number(a0) - Number(b0) || Number(a1) - Number(b1);
};

interface Row {
  id: string;
  title: string;
  dating: Dating;
  from: number;
  to: number;
  open: boolean;
  openStart: boolean;
  read: boolean;
  leaves: Leaf[];
}

const ROWS: Row[] = COTES.flatMap((c) => {
  const d = parseDating(c.date);
  if (!d) return [];
  const from = d.start?.year ?? (d.end ? d.end.year - 4 : Y0);
  const to = d.end ? d.end.year + 1 : from + 1;
  return [
    {
      id: c.id,
      title: c.title,
      dating: d,
      from,
      to,
      open: openEnd(d),
      openStart: d.start === null,
      read: !(d.start?.inferred ?? true) && !(d.end?.inferred ?? true),
      leaves: LEAVES.filter((l) => l.folder === c.id),
    },
  ];
}).sort((a, b) => a.from - b.from || a.to - b.to || byShelfmark(a.id, b.id));
const UNDATED = COTES.filter((c) => !parseDating(c.date));

/**
 * Lanes: a folder goes in the first lane whose last bar, fade included, ends
 * before its own starts. One row per folder made the figure 150 rows tall
 * for a chart whose busiest year has about fifty; packed, it is as tall as
 * the overlap actually is, and still read left to right in order of start.
 */
const GAP = 0.8; // years of white between two bars in a lane
const LANE: number[] = [];
{
  const ends: number[] = [];
  for (const r of ROWS) {
    // A leaf dated outside its folder's range widens the folder's claim on the
    // lane, so its dot never lands on a neighbour's bar.
    const ls = r.leaves.map((l) => frac(l.iso as string));
    const start = Math.min(r.from, ...ls);
    const end = Math.max(r.open ? r.to + 5 : r.to, ...ls.map((v) => v + 0.3));
    let k = ends.findIndex((e) => e + GAP <= start);
    if (k < 0) k = ends.push(-Infinity) - 1;
    ends[k] = end;
    LANE.push(k);
  }
}
const LANES = Math.max(...LANE) + 1;

function H2({ id, children }: { id: string; children: React.ReactNode }) {
  return (
    <h2 id={id} className="scroll-mt-16 text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
      {children}
    </h2>
  );
}

/* ---------- the life, sourced ---------- */

const MACTUTOR = 'https://mathshistory.st-andrews.ac.uk/Biographies/Grothendieck/';
const FONDS = 'https://grothendieck.umontpellier.fr/';
const LIFE: { year: number; what: string; source: string }[] = [
  { year: 1953, what: 'Thesis at Nancy, on topological tensor products and nuclear spaces', source: MACTUTOR },
  { year: 1958, what: 'Joins the new Institut des Hautes Études Scientifiques', source: MACTUTOR },
  { year: 1960, what: 'First volume of the Éléments de géométrie algébrique, with Dieudonné', source: MACTUTOR },
  { year: 1966, what: 'Fields Medal', source: MACTUTOR },
  { year: 1970, what: 'Leaves the IHÉS', source: MACTUTOR },
  { year: 1973, what: 'Professor at the University of Montpellier', source: MACTUTOR },
  { year: 1988, what: 'Retires', source: MACTUTOR },
  { year: 1991, what: 'Leaves Montpellier; his papers stay with Jean Malgoire, and later form this fonds', source: FONDS },
];

/* ---------- figure 1: the ranges and the dots ---------- */

function Ranges() {
  const [sel, setSel] = useState<Row | null>(null);
  const W = 900;
  const L = 16;
  const R = 16;
  const TOP = 26;
  const ROW = 9;
  const H = TOP + LANES * ROW + 24;
  const x = (y: number) => L + ((y - Y0) / (Y1 - Y0)) * (W - L - R);
  const decades = [1950, 1955, 1960, 1965, 1970, 1975, 1980, 1985, 1990];

  return (
    <section className="mt-10">
      <H2 id="ranges">Every dated folder: the inventory's range, and the dates on the leaves</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        One bar per folder, placed by where its dating starts; folders that do not overlap share
        a row. A dark bar is a dating the
        archivists read on the pages; a light one is a dating they deduced, in their square
        brackets; a bar that fades is open-ended — « à partir de 1982 », from 1982 with no end
        given. The dots are dates written on the leaves themselves, found by the transcriptions.
        A hollow dot is a stamp printed on the paper — most often the banner of a computer
        listing whose back he wrote on — which dates the paper, not the writing. Folders not yet
        begun are drawn fainter: they can have no dots.
      </p>
      <ul className="mt-3 flex flex-wrap items-center gap-x-5 gap-y-1 text-[12px] text-ink-500">
        <li className="flex items-center gap-1.5">
          <span className="inline-block h-2 w-5 rounded-sm" style={{ background: DARK }} /> dating read on the pages
        </li>
        <li className="flex items-center gap-1.5">
          <span className="inline-block h-2 w-5 rounded-sm" style={{ background: LIGHT }} /> dating deduced [in brackets]
        </li>
        <li className="flex items-center gap-1.5">
          <span className="inline-block h-2 w-5 rounded-sm" style={{ background: `linear-gradient(90deg, ${LIGHT}, transparent)` }} /> open-ended
        </li>
        <li className="flex items-center gap-1.5">
          <span className="inline-block h-2.5 w-2.5 rounded-full" style={{ background: DOT }} /> a date written on a leaf
        </li>
        <li className="flex items-center gap-1.5">
          <span className="inline-block h-2.5 w-2.5 rounded-full border-[1.5px] bg-white" style={{ borderColor: DOT }} /> a machine stamp on the paper — the leaf is no older
        </li>
      </ul>
      <div className="mt-3 overflow-x-auto" onMouseLeave={() => setSel(null)}>
        <svg
          viewBox={`0 0 ${W} ${H}`}
          className="w-full min-w-[640px] rounded-[var(--radius-card)] border border-ink-200 bg-white"
          role="img"
          aria-label="Each folder's inventory dating as a range, with dates written on its leaves as dots"
        >
          <defs>
            <linearGradient id="fade" x1="0" x2="1">
              <stop offset="0" stopColor={LIGHT} />
              <stop offset="1" stopColor={LIGHT} stopOpacity="0" />
            </linearGradient>
            <linearGradient id="fade-in" x1="0" x2="1">
              <stop offset="0" stopColor={LIGHT} stopOpacity="0" />
              <stop offset="1" stopColor={LIGHT} />
            </linearGradient>
          </defs>
          {decades.map((d) => (
            <g key={d}>
              <line x1={x(d)} x2={x(d)} y1={TOP - 6} y2={H - 20} stroke="var(--color-ink-200)" />
              <text x={x(d)} y={TOP - 12} textAnchor="middle" className="tabular" style={{ fontSize: 11, fill: 'var(--color-ink-400)' }}>
                {d}
              </text>
            </g>
          ))}
          {LIFE.map((e) => (
            <line key={e.year} x1={x(e.year + 0.5)} x2={x(e.year + 0.5)} y1={H - 18} y2={H - 8} stroke="var(--color-ink-500)" strokeWidth="1.5">
              <title>{`${e.year} — ${e.what}`}</title>
            </line>
          ))}
          {ROWS.map((r, i) => {
            const y = TOP + LANE[i] * ROW;
            const on = sel === null || sel === r;
            const fill = r.read ? DARK : LIGHT;
            return (
              <g
                key={r.id}
                opacity={on ? (BEGUN.has(r.id) ? 1 : 0.45) : 0.15}
                onMouseEnter={() => setSel(r)}
                style={{ cursor: 'pointer' }}
              >
                <rect x={x(r.from)} y={y} width={x(r.open ? r.to + 5 : r.to) - x(r.from)} height={ROW} fill="#fff" fillOpacity={0} />
                {r.openStart && <rect x={x(r.from)} y={y + 1} width={x(r.from + 4) - x(r.from)} height={ROW - 2} fill="url(#fade-in)" />}
                <rect
                  x={x(r.openStart ? r.from + 4 : r.from)}
                  y={y + 1}
                  width={Math.max(3, x(r.to) - x(r.openStart ? r.from + 4 : r.from))}
                  height={ROW - 2}
                  rx={1.5}
                  fill={fill}
                />
                {r.open && <rect x={x(r.to)} y={y + 1} width={x(r.to + 5) - x(r.to)} height={ROW - 2} fill="url(#fade)" />}
                {r.leaves.map((l, j) =>
                  isStamp(l) ? (
                    <circle key={j} cx={x(frac(l.iso as string))} cy={y + ROW / 2} r={3} fill="#fff" stroke={DOT} strokeWidth="1.6" />
                  ) : (
                    <circle key={j} cx={x(frac(l.iso as string))} cy={y + ROW / 2} r={3.4} fill={DOT} stroke="#fff" strokeWidth="1" />
                  ),
                )}
              </g>
            );
          })}
        </svg>
      </div>
      <div className="mt-2 min-h-[4.5em] text-[12.5px] leading-relaxed text-ink-600">
        {sel ? (
          <>
            <p>
              <a href={`/archive/#${sel.id}/1`} className="tabular font-semibold text-ink-900 hover:text-brand-700">
                n° {sel.id}
              </a>{' '}
              {shortTitle(sel.title)} <span className="text-ink-500">· inventory: « {sel.dating.raw} »</span>
              {!BEGUN.has(sel.id) && <span className="text-ink-400"> · not yet transcribed</span>}
            </p>
            {sel.leaves.length > 0 ? (
              <p className="text-ink-500">
                On the leaves:{' '}
                {sel.leaves.slice(0, 12).map((l, i) => (
                  <span key={i}>
                    {i > 0 && '; '}« {l.written} » <span className="text-ink-400">(p. {l.page})</span>
                  </span>
                ))}
                {sel.leaves.length > 12 && `; and ${sel.leaves.length - 12} more`}
              </p>
            ) : (
              <p className="text-ink-400">No date found written on its leaves{BEGUN.has(sel.id) ? ' so far' : ''}.</p>
            )}
          </>
        ) : (
          <p className="text-ink-400">
            Hover a bar for the folder, its dating as the inventory writes it, and the dates on its
            leaves. The ticks along the foot are the events listed below. {UNDATED.length} folders are
            « s.d. », undated, and are not drawn.
          </p>
        )}
      </div>
    </section>
  );
}

/* ---------- figure 2: two strips on one year axis ---------- */

function Strips() {
  const W = 900;
  const L = 130;
  const R = 16;
  const h = 56;
  const years = Array.from({ length: Y1 - Y0 }, (_, i) => Y0 + i);
  const x = (y: number) => L + ((y - Y0) / (Y1 - Y0)) * (W - L - R);
  const bw = (W - L - R) / years.length;
  const covering = years.map((y) => ROWS.filter((r) => r.from <= y && y < (r.open ? r.to + 5 : r.to)).length);
  const leaves = years.map((y) => LEAVES.filter((l) => !isStamp(l) && Math.floor(frac(l.iso as string)) === y).length);
  const strips = [
    { label: 'Folders the inventory dates to the year', data: covering, colour: LIGHT },
    { label: 'Dates written on leaves, stamps left out', data: leaves, colour: DOT },
  ];
  return (
    <section className="mt-12">
      <H2 id="by-year">Year by year</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        Two counts on the same years, each on its own scale: how many folders the inventory's
        ranges cover in a year (an open end counted five years on), and how many dates the
        transcriptions have found written on the leaves of that year.
      </p>
      <div className="mt-3 overflow-x-auto">
        <svg
          viewBox={`0 0 ${W} ${strips.length * (h + 22) + 22}`}
          className="w-full min-w-[640px] rounded-[var(--radius-card)] border border-ink-200 bg-white"
          role="img"
          aria-label="Folders dated to each year, and dates written on leaves per year"
        >
          {strips.map((s, j) => {
            const top = 14 + j * (h + 22);
            const mx = Math.max(1, ...s.data);
            return (
              <g key={s.label}>
                <text x={10} y={top + h / 2} style={{ fontSize: 11, fill: 'var(--color-ink-600)' }}>
                  {s.label.split(' ').slice(0, 3).join(' ')}
                </text>
                <text x={10} y={top + h / 2 + 14} style={{ fontSize: 11, fill: 'var(--color-ink-600)' }}>
                  {s.label.split(' ').slice(3).join(' ')}
                </text>
                <text x={W - R} y={top + 8} textAnchor="end" className="tabular" style={{ fontSize: 10.5, fill: 'var(--color-ink-400)' }}>
                  max {mx}
                </text>
                <line x1={L} x2={W - R} y1={top + h} y2={top + h} stroke="var(--color-ink-200)" />
                {s.data.map((v, i) => (
                  <rect key={i} x={x(years[i]) + 1} y={top + h - (v / mx) * h} width={bw - 2} height={(v / mx) * h} rx={1} fill={s.colour}>
                    <title>{`${years[i]}: ${v}`}</title>
                  </rect>
                ))}
              </g>
            );
          })}
          {[1950, 1960, 1970, 1980, 1990].map((d) => (
            <text key={d} x={x(d) + bw / 2} y={strips.length * (h + 22) + 14} textAnchor="middle" className="tabular" style={{ fontSize: 11, fill: 'var(--color-ink-400)' }}>
              {d}
            </text>
          ))}
        </svg>
      </div>
    </section>
  );
}

/* ---------- figure 3: the days ---------- */

function Calendar() {
  const days = useMemo(() => {
    const m = new Map<string, Leaf[]>();
    for (const l of LEAVES) if (!isStamp(l) && /^\d{4}-\d\d-\d\d$/.test(l.iso as string)) m.set(l.iso as string, [...(m.get(l.iso as string) ?? []), l]);
    return m;
  }, []);
  // A year with a leaf or two dated to the day is a row of empty cells; those
  // are named under the calendar instead, and the register lists them.
  const perYear = new Map<number, number>();
  for (const [d, ls] of days) perYear.set(Number(d.slice(0, 4)), (perYear.get(Number(d.slice(0, 4))) ?? 0) + ls.length);
  const years = [...perYear].filter(([, k]) => k >= 5).map(([y]) => y).sort();
  const sparse = [...perYear].filter(([, k]) => k < 5).sort((a, b) => a[0] - b[0]);
  const [sel, setSel] = useState<string | null>(null);
  if (!years.length) return null;
  const C = 10;
  const max = Math.max(...[...days.values()].map((v) => v.length));
  const shade = (n: number) => (n === 0 ? 'var(--color-ink-100)' : ['#dfe6f6', '#97afe1', '#6b8ad0', '#4a6bbd', '#38539d', '#223154'][Math.min(5, Math.ceil((5 * n) / max))]);

  return (
    <section className="mt-12">
      <H2 id="days">The days he dated</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        Every year with five leaves or more dated to the day, a week to a column, stamps left out.
        A darker cell, more dated leaves that day. The late notebooks are why this exists: some runs are dated day by
        day, and the calendar shows the rhythm of the work as the ranges above cannot.
      </p>
      <div className="mt-3 space-y-1.5 overflow-x-auto">
        {years.map((y) => {
          const jan1 = new Date(Date.UTC(y, 0, 1));
          const offset = (jan1.getUTCDay() + 6) % 7; // Monday first
          const n = (Date.UTC(y + 1, 0, 1) - jan1.getTime()) / 864e5;
          const cells = Array.from({ length: n }, (_, i) => {
            const d = new Date(jan1.getTime() + i * 864e5);
            const iso = d.toISOString().slice(0, 10);
            return { iso, col: Math.floor((i + offset) / 7), row: (i + offset) % 7, n: days.get(iso)?.length ?? 0 };
          });
          const total = cells.reduce((a, c) => a + c.n, 0);
          return (
            <div key={y} className="flex items-start gap-3">
              <p className="tabular w-16 shrink-0 pt-1 text-[12px] text-ink-500">
                {y}
                <br />
                <span className="text-ink-400">{total} dated</span>
              </p>
              <svg width={54 * C + 2} height={7 * C + 2} role="img" aria-label={`Leaves dated to the day in ${y}`}>
                {cells.map((c) => (
                  <rect
                    key={c.iso}
                    x={1 + c.col * C}
                    y={1 + c.row * C}
                    width={C - 2}
                    height={C - 2}
                    rx={2}
                    fill={shade(c.n)}
                    stroke={sel === c.iso ? 'var(--color-ink-900)' : 'none'}
                    onMouseEnter={() => c.n && setSel(c.iso)}
                    style={{ cursor: c.n ? 'pointer' : 'default' }}
                  >
                    <title>{`${c.iso}${c.n ? ` — ${c.n}` : ''}`}</title>
                  </rect>
                ))}
              </svg>
            </div>
          );
        })}
      </div>
      <div className="mt-2 min-h-[3em] text-[12.5px] leading-relaxed text-ink-600">
        {sel ? (
          <ul>
            {(days.get(sel) ?? []).map((l, i) => (
              <li key={i}>
                <span className="tabular text-ink-900">{sel}</span> ·{' '}
                <a href={`/archive/#${l.folder}/${l.batch}`} className="tabular font-semibold text-ink-900 hover:text-brand-700">
                  n° {l.folder}
                </a>{' '}
                p. {l.page} — « {l.written} », {l.context}
              </li>
            ))}
          </ul>
        ) : (
          <p className="text-ink-400">
            Hover a coloured day for the leaves dated to it. Fewer than five in{' '}
            {sparse.map(([y, k]) => `${y} (${k})`).join(', ')}: they are in the register below.
          </p>
        )}
      </div>
    </section>
  );
}

/* ---------- the register of dated leaves ---------- */

function Register() {
  const byFolder = useMemo(() => {
    const m = new Map<string, Leaf[]>();
    for (const l of LEAVES) m.set(l.folder, [...(m.get(l.folder) ?? []), l]);
    return [...m].sort((a, b) => byShelfmark(a[0], b[0]));
  }, []);
  return (
    <details className="mt-6 text-[12.5px] text-ink-600">
      <summary className="cursor-pointer text-ink-500">
        All {LEAVES.length} dates written on leaves, by folder, each with the line it rests on
      </summary>
      <ul className="mt-2 space-y-2">
        {byFolder.map(([f, ls]) => (
          <li key={f}>
            <span className="tabular font-semibold text-ink-900">n° {f}</span>
            <ul className="pl-4">
              {ls.map((l, i) => (
                <li key={i}>
                  <a href={`/archive/#${l.folder}/${l.batch}`} className="tabular hover:text-brand-700">
                    p. {l.page}
                  </a>{' '}
                  « {l.written} » <span className="text-ink-400">— {l.kind}, {l.context} · {l.where}</span>
                </li>
              ))}
            </ul>
          </li>
        ))}
      </ul>
    </details>
  );
}

export function TimelinePage() {
  const inferred = ROWS.filter((r) => !r.read).length;
  const foldersWithLeaves = new Set(LEAVES.map((l) => l.folder)).size;
  return (
    <>
      <Header path="/timeline/" />

      <main className="mx-auto max-w-5xl px-5 py-12">
        <header className="max-w-[44em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.14em] text-ink-400">Timeline</p>
          <h1 className="titre mt-2 text-[30px] leading-tight text-ink-900">
            When the folders were written, and how anyone knows
          </h1>
          <p className="mt-4 text-[15.5px] leading-relaxed text-ink-600">
            Almost nothing in the fonds is dated. The inventory proposes a dating for most folders,
            but of the {ROWS.length} it dates, {inferred} rest at least in part on a deduction of the
            archivists' — a verso, a letter, a neighbouring folder — and {UNDATED.length} more carry
            none at all. The transcriptions have so far found {LEAVES.length} dates on the leaves
            themselves, in {foldersWithLeaves} folders — {LEAVES.filter(isStamp).length} of them
            machine stamps on reused paper, which date the paper rather than the writing. This page
            keeps them all apart.
          </p>
        </header>

        <Ranges />
        <Strips />
        <Calendar />
        <Register />

        <section className="mt-12">
          <H2 id="life">The life, where it is sourced</H2>
          <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
            Only what a reference work states, for orientation against the ranges above — not a
            biography.
          </p>
          <ul className="mt-3 space-y-1.5 text-[13px] text-ink-700">
            {LIFE.map((e) => (
              <li key={e.year} className="flex gap-3">
                <span className="tabular w-10 shrink-0 font-semibold text-ink-900">{e.year}</span>
                <span>
                  {e.what}{' '}
                  <a href={e.source} target="_blank" rel="noopener noreferrer" className="text-[12px] text-brand-600 hover:text-brand-700">
                    {e.source === MACTUTOR ? 'MacTutor' : 'the fonds'} ↗
                  </a>
                </span>
              </li>
            ))}
          </ul>
        </section>

        <p className="mt-12 max-w-[44em] text-[12px] leading-relaxed text-ink-400">
          The ranges are read from the inventory's datings as src/content/catalogue.ts carries them,
          brackets included. The dates on the leaves are src/content/dated-leaves.json, each with
          the file and line of the transcription that records it.
        </p>
      </main>

      <Footer />
    </>
  );
}
