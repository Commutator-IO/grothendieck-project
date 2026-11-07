import { useEffect, useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import { BY_ID } from './content/catalogue.ts';
import lettersRaw from './content/letters.json';
import { CommentButton, commentData, useComments } from './components/Comments.tsx';
import type { CommentContext } from './lib/report.ts';

/**
 * The correspondence the folders hold, as a register.
 *
 * Not the letters: a line per letter — who, when, where it is in the fonds,
 * how the transcription gives it — so a reader can find one without the site
 * circulating what it should not. Third-party letters may not be circulated
 * without permission, and those already in print stay condensed; the register
 * says which is which rather than deciding it again here.
 */

interface Letter {
  folder: string;
  batch: number;
  pages: string;
  date: string | null;
  iso: string | null;
  dating: 'written' | 'inferred' | 'none';
  direction: 'from' | 'to' | 'other';
  correspondent: string | null;
  correspondentNote: string | null;
  place: string | null;
  form: string;
  language: string;
  treatment: 'full' | 'summarised' | 'named';
  summary: string;
  where: string;
  checked?: string;
}
const RAW = (lettersRaw as unknown as { built: string; records: Letter[] });
const RECORDS = RAW.records;

// One letter to three people is three records; the counts of letters use the
// physical letter, keyed by where it sits.
const letterKey = (l: Letter) => `${l.folder}#${l.pages}`;
const LETTERS = [...new Map(RECORDS.map((l) => [letterKey(l), l])).values()];

const DIR: Record<Letter['direction'], { label: string; colour: string }> = {
  from: { label: 'from him', colour: '#38539d' },
  to: { label: 'to him', colour: '#c9900c' },
  other: { label: 'between others, or unclear', colour: 'var(--color-ink-300)' },
};
const TREAT: Record<Letter['treatment'], string> = {
  full: 'transcribed',
  summarised: 'summarised',
  named: 'named only',
};
const LANG: Record<string, string> = { fr: 'French', en: 'English', de: 'German' };
const who = (l: Letter) => l.correspondent ?? l.correspondentNote ?? 'unidentified';
const shortTitle = (id: string) =>
  (BY_ID.get(id)?.title ?? '').replace(/\s*:\s*notes manuscrites.*$/i, '').replace(/\s*:.*$/, '');

function H2({ id, children }: { id: string; children: React.ReactNode }) {
  return (
    <h2 id={id} className="scroll-mt-16 text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
      {children}
    </h2>
  );
}

function Kpi({ value, label, help }: { value: string | number; label: string; help?: string }) {
  return (
    <div className="card px-4 py-3">
      <p className="tabular text-[24px] font-semibold leading-tight text-ink-900">{value}</p>
      <p className="mt-0.5 text-[12.5px] text-ink-600">{label}</p>
      {help && <p className="mt-1 text-[11.5px] leading-snug text-ink-400">{help}</p>}
    </div>
  );
}

function Legend() {
  return (
    <ul className="mt-3 flex flex-wrap items-center gap-x-5 gap-y-1 text-[12px] text-ink-500">
      {(Object.keys(DIR) as Letter['direction'][]).map((d) => (
        <li key={d} className="flex items-center gap-1.5">
          <span className="inline-block h-2.5 w-2.5 rounded-sm" style={{ background: DIR[d].colour }} /> {DIR[d].label}
        </li>
      ))}
    </ul>
  );
}

/** Letters per year, stacked by direction, over the years the register spans. */
function ByYear() {
  const dated = RECORDS.filter((l) => l.iso);
  const ys = dated.map((l) => Number((l.iso as string).slice(0, 4)));
  const y0 = Math.min(...ys) - 1;
  const y1 = Math.max(...ys) + 1;
  const years = Array.from({ length: y1 - y0 + 1 }, (_, i) => y0 + i);
  const stack = years.map((y) => {
    const here = LETTERS.filter((l) => l.iso && Number(l.iso.slice(0, 4)) === y);
    return (Object.keys(DIR) as Letter['direction'][]).map((d) => ({ d, n: here.filter((l) => l.direction === d).length }));
  });
  const max = Math.max(1, ...stack.map((s) => s.reduce((a, b) => a + b.n, 0)));
  const W = 900;
  const H = 200;
  const L = 30;
  const B = 26;
  const bw = (W - L - 10) / years.length;
  const y = (v: number) => ((H - B - 10) * v) / max;
  const [sel, setSel] = useState<number | null>(null);
  const undated = LETTERS.filter((l) => !l.iso).length;

  return (
    <section className="mt-12">
      <H2 id="by-year">Letters by year</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        Each letter counted once, by the year written on it (or, for one, by the transcriber's
        dating). {undated} letters carry no date and are not drawn.
      </p>
      <Legend />
      <div className="mt-2 overflow-x-auto" onMouseLeave={() => setSel(null)}>
        <svg viewBox={`0 0 ${W} ${H}`} className="w-full min-w-[560px] rounded-[var(--radius-card)] border border-ink-200 bg-white" role="img" aria-label="Letters per year by direction">
          {Array.from({ length: max + 1 }, (_, i) => i).filter((i) => i % Math.max(1, Math.ceil(max / 4)) === 0).map((i) => (
            <g key={i}>
              <line x1={L} x2={W - 10} y1={H - B - y(i)} y2={H - B - y(i)} stroke="var(--color-ink-200)" />
              <text x={L - 6} y={H - B - y(i) + 4} textAnchor="end" className="tabular" style={{ fontSize: 11, fill: 'var(--color-ink-400)' }}>
                {i}
              </text>
            </g>
          ))}
          {stack.map((s, i) => {
            let acc = 0;
            return (
              <g key={years[i]} onMouseEnter={() => setSel(years[i])} opacity={sel === null || sel === years[i] ? 1 : 0.35}>
                <rect x={L + i * bw} y={0} width={bw} height={H - B} fill="#fff" fillOpacity={0} />
                {s.map(({ d, n }) => {
                  if (!n) return null;
                  const h = y(n);
                  const r = <rect key={d} x={L + i * bw + 2} y={H - B - acc - h} width={bw - 4} height={Math.max(0, h - 2)} rx={2} fill={DIR[d].colour} />;
                  acc += h;
                  return r;
                })}
                {(years[i] % 5 === 0 || years.length < 16) && (
                  <text x={L + i * bw + bw / 2} y={H - 8} textAnchor="middle" className="tabular" style={{ fontSize: 11, fill: 'var(--color-ink-400)' }}>
                    {years[i]}
                  </text>
                )}
              </g>
            );
          })}
        </svg>
      </div>
      <div className="mt-2 min-h-[3em] text-[12.5px] leading-relaxed text-ink-600">
        {sel !== null ? (
          <ul>
            {LETTERS.filter((l) => l.iso?.startsWith(String(sel))).map((l) => (
              <li key={letterKey(l)}>
                <span className="tabular text-ink-900">{l.date}</span> · {DIR[l.direction].label}
                {l.direction !== 'other' && `, ${l.direction === 'from' ? 'to' : 'from'} ${who(l)}`} ·{' '}
                <a href={`/fonds/#${l.folder}/${l.batch}`} className="tabular font-semibold text-ink-900 hover:text-brand-700">
                  n° {l.folder}
                </a>
              </li>
            ))}
            {!LETTERS.some((l) => l.iso?.startsWith(String(sel))) && <li className="text-ink-400">{sel}: none.</li>}
          </ul>
        ) : (
          <p className="text-ink-400">Hover a year for its letters.</p>
        )}
      </div>
    </section>
  );
}

/** Correspondents, each a bar split by direction. */
function Correspondents({ onPick, picked }: { onPick: (c: string | null) => void; picked: string | null }) {
  const rows = useMemo(() => {
    const m = new Map<string, Record<Letter['direction'], number>>();
    for (const l of RECORDS) {
      const k = l.correspondent ?? 'Not named here';
      const e = m.get(k) ?? { from: 0, to: 0, other: 0 };
      e[l.direction]++;
      m.set(k, e);
    }
    return [...m]
      .map(([name, c]) => ({ name, c, n: c.from + c.to + c.other }))
      .sort((a, b) => (a.name === 'Not named here' ? 1 : 0) - (b.name === 'Not named here' ? 1 : 0) || b.n - a.n || a.name.localeCompare(b.name));
  }, []);
  const max = Math.max(...rows.map((r) => r.n));
  return (
    <section className="mt-12">
      <H2 id="correspondents">Correspondents</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        A letter to three people counts for each. People who are not public figures are not named:
        they are counted together at the foot. Choose a name to filter the register below.
      </p>
      <Legend />
      <ul className="mt-3 grid gap-x-8 gap-y-1 text-[12.5px] sm:grid-cols-2">
        {rows.map((r) => (
          <li key={r.name}>
            <button
              type="button"
              onClick={() => onPick(picked === r.name ? null : r.name)}
              aria-pressed={picked === r.name}
              className={`flex w-full items-center gap-2 rounded px-1 py-0.5 text-left ${picked === r.name ? 'bg-ink-100' : 'hover:bg-ink-50'}`}
            >
              <span className={`w-40 shrink-0 truncate ${r.name === 'Not named here' ? 'italic text-ink-500' : 'text-ink-900'}`}>{r.name}</span>
              <span className="flex h-2.5 flex-1 gap-px">
                {(Object.keys(DIR) as Letter['direction'][]).map((d) =>
                  r.c[d] ? <span key={d} className="h-2.5 rounded-sm" style={{ width: `${(100 * r.c[d]) / max}%`, background: DIR[d].colour }} /> : null,
                )}
              </span>
              <span className="tabular w-6 shrink-0 text-right text-ink-500">{r.n}</span>
            </button>
          </li>
        ))}
      </ul>
    </section>
  );
}

const letterCtx = (l: Letter, names: string): CommentContext => ({
  kind: 'letter',
  label: `n° ${l.folder}, p. ${l.pages}: ${l.direction === 'from' ? 'his letter to' : l.direction === 'to' ? 'letter to him from' : 'letter,'} ${names || 'unidentified'}`,
  cote: l.folder,
  batch: l.batch,
  page: Number.parseInt(l.pages, 10) || undefined,
  ref: letterKey(l),
  details: [
    `**Pages** ${l.pages}`,
    `**Date** ${l.date ?? (l.iso ? `[${l.iso}], inferred` : 's.d.')}`,
    l.place ? `**Place** ${l.place}` : null,
    `**Correspondent** ${names || 'unidentified'} (letter ${DIR[l.direction].label})`,
    `**Source** ${l.where}`,
  ].filter((x): x is string => x !== null),
  link: `https://grothendieck.commutator.io/#${l.folder}/${l.batch}`,
});

// ── The guide: search, filters with counts, a link per letter, shareable state ──

/** The anchor of one letter: folder and pages, stable as long as the shelfmark is. */
const anchorOf = (l: Letter) => `l-${l.folder}-p${l.pages.replace(/[^0-9a-z]+/gi, '-')}`;

type Sort = 'shelf' | 'date';
interface Filters {
  q: string;
  dir: Letter['direction'] | '';
  how: Letter['treatment'] | '';
  lang: string;
  dated: '' | 'yes' | 'no';
  sort: Sort;
}
const NO_FILTERS: Filters = { q: '', dir: '', how: '', lang: '', dated: '', sort: 'shelf' };

function readHash(): { f: Filters; who: string | null } {
  const p = new URLSearchParams(location.hash.replace(/^#/, '').replace(/^l-[^&]*&?/, ''));
  const pick = <T extends string>(k: string, ok: readonly T[], d: T): T => {
    const v = p.get(k) as T | null;
    return v && ok.includes(v) ? v : d;
  };
  return {
    f: {
      q: p.get('q') ?? '',
      dir: pick('dir', ['from', 'to', 'other', ''] as const, ''),
      how: pick('how', ['full', 'summarised', 'named', ''] as const, ''),
      lang: p.get('lang') ?? '',
      dated: pick('dated', ['yes', 'no', ''] as const, ''),
      sort: pick('sort', ['shelf', 'date'] as const, 'shelf'),
    },
    who: p.get('who'),
  };
}

function writeHash(f: Filters, who: string | null) {
  const p = new URLSearchParams();
  if (f.q) p.set('q', f.q);
  if (f.dir) p.set('dir', f.dir);
  if (f.how) p.set('how', f.how);
  if (f.lang) p.set('lang', f.lang);
  if (f.dated) p.set('dated', f.dated);
  if (f.sort !== 'shelf') p.set('sort', f.sort);
  if (who) p.set('who', who);
  const h = p.toString();
  const next = `${location.pathname}${location.search}${h ? `#${h}` : ''}`;
  if ((h ? `#${h}` : '') !== location.hash && !location.hash.startsWith('#l-')) history.replaceState(null, '', next);
}

const fold = (t: string) => t.normalize('NFD').replace(/[̀-ͯ]/g, '').toLowerCase();
const haystack = (l: Letter, names: string) =>
  fold([names, l.summary, l.place ?? '', l.date ?? '', l.iso ?? '', `n° ${l.folder}`, l.folder, shortTitle(l.folder), l.where].join(' '));

function matches(l: Letter, names: string, f: Filters, except?: keyof Filters) {
  if (except !== 'dir' && f.dir && l.direction !== f.dir) return false;
  if (except !== 'how' && f.how && l.treatment !== f.how) return false;
  if (except !== 'lang' && f.lang && l.language !== f.lang) return false;
  if (except !== 'dated' && f.dated === 'yes' && l.dating === 'none') return false;
  if (except !== 'dated' && f.dated === 'no' && l.dating !== 'none') return false;
  if (f.q) {
    const h = haystack(l, names);
    if (!fold(f.q).split(/\s+/).filter(Boolean).every((w) => h.includes(w))) return false;
  }
  return true;
}

/** Letters written on this day of the year, or the next ones to come round. */
function OnThisDay() {
  const today = new Date();
  const md = (d: Date) => `${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`;
  const full = LETTERS.filter((l) => l.iso && l.iso.length >= 10);
  const todays = full.filter((l) => (l.iso as string).slice(5, 10) === md(today));
  let shown = todays;
  let when = 'Written on this day';
  if (!todays.length) {
    for (let k = 1; k <= 366 && !shown.length; k++) {
      const d = new Date(today);
      d.setDate(d.getDate() + k);
      shown = full.filter((l) => (l.iso as string).slice(5, 10) === md(d));
      if (shown.length) when = `Next anniversary, ${d.toLocaleDateString('en-GB', { day: 'numeric', month: 'long' })}`;
    }
  }
  if (!shown.length) return null;
  return (
    <div className="mt-6 rounded-[var(--radius-card)] border border-ink-200 bg-white px-4 py-3 text-[13px] leading-relaxed text-ink-700">
      <p className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">{when}</p>
      <ul className="mt-1">
        {shown.map((l) => (
          <li key={letterKey(l)}>
            <a href={`#${anchorOf(l)}`} className="font-semibold text-ink-900 hover:text-brand-700">
              {l.date}
            </a>{' '}
            · {l.direction === 'from' ? `his letter to ${who(l)}` : l.direction === 'to' ? `${who(l)} to him` : who(l)} · {l.summary.slice(0, 140)}
            {l.summary.length > 140 ? '…' : ''}
          </li>
        ))}
      </ul>
    </div>
  );
}

function Chips<T extends string>({
  label,
  value,
  options,
  onChange,
}: {
  label: string;
  value: T | '';
  options: { v: T; label: string; n: number }[];
  onChange: (v: T | '') => void;
}) {
  return (
    <div className="flex flex-wrap items-center gap-1.5">
      <span className="w-20 shrink-0 text-[11px] font-semibold uppercase tracking-wide text-ink-400">{label}</span>
      {options.map((o) => (
        <button
          key={o.v}
          type="button"
          aria-pressed={value === o.v}
          disabled={!o.n && value !== o.v}
          onClick={() => onChange(value === o.v ? '' : o.v)}
          className={`rounded-full border px-2.5 py-0.5 text-[12px] ${
            value === o.v ? 'border-ink-900 bg-ink-900 text-white' : 'border-ink-200 bg-white text-ink-700 hover:border-ink-400 disabled:opacity-40'
          }`}
        >
          {o.label} <span className={`tabular ${value === o.v ? 'text-ink-200' : 'text-ink-400'}`}>{o.n}</span>
        </button>
      ))}
    </div>
  );
}

function Register({ picked, onPick, f, setF }: { picked: string | null; onPick: (c: string | null) => void; f: Filters; setF: (f: Filters) => void }) {
  const namesOf = (l: Letter) => (picked ? [who(l)] : RECORDS.filter((r) => letterKey(r) === letterKey(l)).map(who)).join(', ');
  const base = picked ? RECORDS.filter((l) => (l.correspondent ?? 'Not named here') === picked) : LETTERS;
  const count = (k: keyof Filters, test: (l: Letter) => boolean) => base.filter((l) => matches(l, namesOf(l), f, k) && test(l)).length;
  const rows = base
    .filter((l) => matches(l, namesOf(l), f))
    .sort((x, y) => (f.sort === 'date' ? (x.iso ?? '9999').localeCompare(y.iso ?? '9999') : 0));
  const langs = [...new Set(LETTERS.map((l) => l.language))].sort((a, b) => (a === 'unknown' ? 1 : b === 'unknown' ? -1 : a.localeCompare(b)));
  const active = picked !== null || JSON.stringify({ ...f, sort: 'shelf' }) !== JSON.stringify(NO_FILTERS);

  const [target, setTarget] = useState<string | null>(() => (location.hash.startsWith('#l-') ? location.hash.slice(1) : null));
  useEffect(() => {
    const on = () => setTarget(location.hash.startsWith('#l-') ? location.hash.slice(1) : null);
    window.addEventListener('hashchange', on);
    return () => window.removeEventListener('hashchange', on);
  }, []);
  useEffect(() => {
    if (target) document.getElementById(target)?.scrollIntoView({ block: 'center' });
  }, [target]);

  return (
    <section className="mt-12">
      <H2 id="register">The register</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        The date is as the letter writes it; « how given » says whether the transcription gives its
        text, a summary, or only notes that it is there. Each line has its own link (¶), and the
        filters are kept in the address, so a search can be shared.
      </p>

      <div className="mt-4 space-y-2 rounded-[var(--radius-card)] border border-ink-200 bg-ink-50/60 px-4 py-3">
        <div className="flex flex-wrap items-center gap-2">
          <input
            type="search"
            value={f.q}
            onChange={(e) => setF({ ...f, q: e.target.value })}
            placeholder="Search: a name, a subject, a place, a year, a folder (n° 31)"
            aria-label="Search the register"
            className="min-w-[16em] flex-1 rounded-md border border-ink-200 bg-white px-3 py-1.5 text-[13.5px] text-ink-900 placeholder:text-ink-400 focus:border-ink-500 focus:outline-none"
          />
          <label className="flex items-center gap-1.5 text-[12.5px] text-ink-600">
            Order
            <select value={f.sort} onChange={(e) => setF({ ...f, sort: e.target.value as Sort })} className="rounded-md border border-ink-200 bg-white px-2 py-1 text-[12.5px]">
              <option value="shelf">by shelfmark</option>
              <option value="date">by date</option>
            </select>
          </label>
        </div>
        <Chips
          label="Direction"
          value={f.dir}
          options={(Object.keys(DIR) as Letter['direction'][]).map((d) => ({ v: d, label: DIR[d].label, n: count('dir', (l) => l.direction === d) }))}
          onChange={(v) => setF({ ...f, dir: v })}
        />
        <Chips
          label="How given"
          value={f.how}
          options={(Object.keys(TREAT) as Letter['treatment'][]).map((t) => ({ v: t, label: TREAT[t], n: count('how', (l) => l.treatment === t) }))}
          onChange={(v) => setF({ ...f, how: v })}
        />
        <Chips
          label="Language"
          value={f.lang}
          options={langs.map((g) => ({ v: g, label: LANG[g] ?? (g === 'unknown' ? 'not stated' : g), n: count('lang', (l) => l.language === g) }))}
          onChange={(v) => setF({ ...f, lang: v })}
        />
        <Chips
          label="Date"
          value={f.dated}
          options={[
            { v: 'yes' as const, label: 'dated', n: count('dated', (l) => l.dating !== 'none') },
            { v: 'no' as const, label: 'undated', n: count('dated', (l) => l.dating === 'none') },
          ]}
          onChange={(v) => setF({ ...f, dated: v })}
        />
        <p className="flex flex-wrap items-center gap-2 pt-1 text-[12.5px] text-ink-600" aria-live="polite">
          <span>
            <span className="tabular font-semibold text-ink-900">{rows.length}</span> of {base.length} {base.length === 1 ? 'letter' : 'letters'}
            {picked && <> with <strong className="font-semibold">{picked}</strong></>}
          </span>
          {active && (
            <button
              type="button"
              onClick={() => {
                setF({ ...NO_FILTERS, sort: f.sort });
                onPick(null);
              }}
              className="rounded border border-ink-200 bg-white px-2 py-0.5 text-[12px] text-ink-700 hover:border-ink-400"
            >
              Clear filters
            </button>
          )}
        </p>
      </div>

      <div className="mt-3 overflow-x-auto rounded-[var(--radius-card)] border border-ink-200 bg-white">
        <table className="w-full min-w-[760px] text-[12.5px]">
          <thead className="text-left text-[11px] uppercase tracking-wide text-ink-400">
            <tr className="border-b border-ink-200">
              <th className="px-3 py-2 font-semibold">Where</th>
              <th className="px-2 py-2 font-semibold">Date</th>
              <th className="px-2 py-2 font-semibold">Who</th>
              <th className="px-2 py-2 font-semibold">How given</th>
              <th className="px-2 py-2 font-semibold">What</th>
            </tr>
          </thead>
          <tbody>
            {rows.map((l, i) => {
              const names = namesOf(l);
              const id = anchorOf(l);
              return (
                <tr
                  key={i}
                  id={id}
                  className={`scroll-mt-20 border-b border-ink-100 align-top last:border-0 ${target === id ? 'bg-encours-50' : ''}`}
                  {...commentData(letterCtx(l, names))}
                >
                  <td className="whitespace-nowrap px-3 py-2">
                    <a href={`/fonds/#${l.folder}/${l.batch}`} className="tabular font-semibold text-ink-900 hover:text-brand-700" title={BY_ID.get(l.folder)?.title}>
                      n° {l.folder}
                    </a>
                    <span className="tabular text-ink-400"> p. {l.pages}</span>{' '}
                    <a href={`#${id}`} className="text-ink-300 hover:text-brand-700" title="Link to this letter" aria-label="Link to this letter">
                      ¶
                    </a>
                    <br />
                    <span className="text-[11.5px] text-ink-400">{shortTitle(l.folder).slice(0, 24)}</span>
                  </td>
                  <td className="px-2 py-2 text-ink-700">
                    {l.date ?? <span className="text-ink-400">{l.dating === 'inferred' ? `[${l.iso}]` : 's.d.'}</span>}
                    {l.place && <span className="block text-[11.5px] text-ink-400">{l.place}</span>}
                  </td>
                  <td className="px-2 py-2 text-ink-700">
                    <span className="inline-block h-2 w-2 rounded-sm align-middle" style={{ background: DIR[l.direction].colour }} />{' '}
                    {l.direction === 'from' ? 'to ' : l.direction === 'to' ? 'from ' : ''}
                    {names}
                  </td>
                  <td className="whitespace-nowrap px-2 py-2 text-ink-500">
                    {TREAT[l.treatment]}
                    <br />
                    <span className="text-[11.5px] text-ink-400">
                      {l.form}, {LANG[l.language] ?? l.language}
                    </span>
                    {l.checked && (
                      <>
                        <br />
                        <span className="text-[11.5px] text-ink-400" title={`Checked: ${l.checked}`}>
                          ✓ checked on the facsimile
                        </span>
                      </>
                    )}
                  </td>
                  <td className="px-2 py-2 text-ink-600">
                    {l.summary} <CommentButton scope="letters" ctx={letterCtx(l, names)} text={l.summary} />
                  </td>
                </tr>
              );
            })}
            {!rows.length && (
              <tr>
                <td colSpan={5} className="px-3 py-6 text-center text-ink-400">
                  No letter matches. Try fewer words, or clear the filters.
                </td>
              </tr>
            )}
          </tbody>
        </table>
      </div>
    </section>
  );
}

export function LettersPage() {
  const commentRoot = useComments<HTMLElement>('letters', 'Letters');
  const init = useMemo(readHash, []);
  const [picked, setPickedRaw] = useState<string | null>(init.who);
  const [f, setF] = useState<Filters>(init.f);
  useEffect(() => writeHash(f, picked), [f, picked]);
  const setPicked = (c: string | null) => {
    setPickedRaw(c);
    if (c) document.getElementById('register')?.scrollIntoView({ behavior: 'smooth', block: 'start' });
  };
  const named = new Set(RECORDS.map((l) => l.correspondent).filter(Boolean)).size;
  const dated = LETTERS.filter((l) => l.dating === 'written').length;
  const from = LETTERS.filter((l) => l.direction === 'from').length;
  const to = LETTERS.filter((l) => l.direction === 'to').length;
  const ys = LETTERS.filter((l) => l.iso).map((l) => Number((l.iso as string).slice(0, 4)));

  return (
    <>
      <Header path="/letters/" />

      <main ref={commentRoot} className="mx-auto max-w-5xl px-5 py-12">
        <header className="max-w-[44em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.14em] text-ink-400">Letters</p>
          <h1 className="titre mt-2 text-[30px] leading-tight text-ink-900">
            The correspondence in the folders
          </h1>
          <p className="mt-4 text-[15.5px] leading-relaxed text-ink-600">
            The fonds is working notes, not a correspondence, but letters turn up in it: carbons of
            his, answers filed with the mathematics they answer, drafts broken off. The register below
            lists those the transcriptions have found so far, with where each one is, when it was
            written, with whom, and how the site gives it.
          </p>
        </header>

        <div className="mt-6 max-w-[44em] rounded-[var(--radius-card)] border border-encours-200 bg-encours-50 px-4 py-3 text-[13px] leading-relaxed text-ink-700">
          <strong className="font-semibold">A register, not the letters.</strong> Letters from others
          may not be circulated without permission, and those already published (the
          Grothendieck–Serre correspondence) stay condensed. People who are not public figures are
          not named. The count grows only as folders are read: {ys.length ? `${Math.min(...ys)}–${Math.max(...ys)}` : ''} is
          the span found so far, not the span of his correspondence.
        </div>

        <div className="mt-6 grid grid-cols-2 gap-3 sm:grid-cols-4">
          <Kpi value={LETTERS.length} label="letters found" help={`in ${new Set(LETTERS.map((l) => l.folder)).size} folders`} />
          <Kpi value={dated} label="dated on the letter" />
          <Kpi value={`${from} · ${to}`} label="from him · to him" help={`${LETTERS.length - from - to} between others or unclear`} />
          <Kpi value={named} label="named correspondents" />
        </div>

        <OnThisDay />
        <ByYear />
        <Correspondents onPick={setPicked} picked={picked} />
        <Register picked={picked} onPick={setPicked} f={f} setF={setF} />

        <p className="mt-12 max-w-[44em] text-[12px] leading-relaxed text-ink-400">
          src/content/letters.json, built on {RAW.built} by reading the transcriptions' headers and
          pages; every record carries the file and line it rests on. Letters only referred to, such
          as « ma lettre à Verdier », are left out unless the folder holds them.
        </p>
      </main>

      <Footer />
    </>
  );
}
