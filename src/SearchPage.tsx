import { type ReactNode, useDeferredValue, useEffect, useMemo, useState } from 'react';
import katex from 'katex';
import 'katex/dist/katex.min.css';
import { Footer, Header } from './components/Frame.tsx';

/**
 * The metadata search (#108): every document the site catalogues, in one list.
 *
 * It searches what a catalogue says about a document — title, dating,
 * shelfmark, holder, keywords, a summary in the registers' own words — and
 * sends the reader to the holder to read it. The index never holds the
 * transcriptions, nor the modernised readings: a client-side index ships every
 * word it carries to the browser, and the texts are not ours to ship
 * (scripts/search-index.mjs says what goes in).
 *
 * The query lives in the URL fragment, `#q=topos&src=bourbaki&from=1960&to=1970`,
 * so a search can be sent as a link.
 */

type Source = 'montpellier' | 'letter' | 'bourbaki' | 'quillen' | 'ihes' | 'buffalo' | 'bnf' | 'finding';

interface Rec {
  id: string;
  source: Source;
  title: string;
  yearFrom: number | null;
  yearTo: number | null;
  date: string | null;
  shelfmark: string | null;
  holder: string;
  tags: string[];
  summary: string | null;
  url: string | null;
  siteUrl: string | null;
}
interface Indexed extends Rec {
  hay: string;
  hayTitle: string;
}

const SOURCES: { id: Source; label: string; colour: string; aliases: string[] }[] = [
  { id: 'montpellier', label: 'Montpellier folders', colour: '#38539d', aliases: ['montpellier', 'fonds', 'folder', 'folders'] },
  { id: 'letter', label: 'Letters', colour: '#c9900c', aliases: ['letter', 'letters'] },
  { id: 'bourbaki', label: 'Bourbaki (AHP)', colour: '#2e6b3f', aliases: ['bourbaki', 'ahp'] },
  { id: 'quillen', label: 'Quillen (Clay)', colour: '#8a3f7a', aliases: ['quillen', 'clay'] },
  { id: 'ihes', label: 'Illusie fonds (IHÉS)', colour: '#a8322f', aliases: ['ihes', 'illusie'] },
  { id: 'bnf', label: 'BnF boxes', colour: '#5e5e5e', aliases: ['bnf'] },
  { id: 'buffalo', label: 'Buffalo lectures', colour: '#8a5a00', aliases: ['buffalo', 'lecture', 'lectures'] },
  { id: 'finding', label: 'Findings', colour: '#2f4da8', aliases: ['finding', 'findings'] },
];
const SOURCE = new Map(SOURCES.map((s) => [s.id, s]));
const ALIAS = new Map(SOURCES.flatMap((s) => s.aliases.map((a) => [a, s.id] as const)));


/** Lower case, no accents, no LaTeX control words: « Étale » and « etale », « $\mathrm{Hom}$ » and « Hom ». */
const fold = (s: string) =>
  s
    .normalize('NFD')
    .replace(/[̀-ͯ]/g, '')
    .replace(/\\(mathrm|mathbf|mathcal|mathbb|mathfrak|operatorname|text|textit|emph)\b/g, ' ')
    .replace(/\\([a-zA-Z]+)/g, ' $1 ')
    .replace(/[{}$^_\\]/g, ' ')
    .replace(/[’']/g, "'")
    .toLowerCase();

interface Query {
  terms: string[];
  sources: Source[];
  from: number | null;
  to: number | null;
}

/** Free terms, « "quoted phrases" », and the tokens `source:bourbaki` and `year:1960-1970` (or `year:1965`, `year:1960-`). */
function parseQuery(q: string): Query {
  const out: Query = { terms: [], sources: [], from: null, to: null };
  for (const m of q.matchAll(/"([^"]*)"|(\S+)/g)) {
    const tok = m[1] ?? m[2];
    if (m[1] === undefined) {
      const src = /^(?:source|src):(\S+)$/i.exec(tok);
      if (src) {
        for (const a of src[1].toLowerCase().split(',')) {
          const id = ALIAS.get(fold(a));
          if (id) out.sources.push(id);
        }
        continue;
      }
      const yr = /^(?:year|years|date):(\d{4})?(?:(-)(\d{4})?)?$/i.exec(tok);
      if (yr && (yr[1] || yr[3])) {
        out.from = yr[1] ? Number(yr[1]) : null;
        out.to = yr[3] ? Number(yr[3]) : yr[2] ? null : out.from;
        continue;
      }
    }
    const t = fold(tok).trim();
    if (t) out.terms.push(t);
  }
  return out;
}

interface State {
  q: string;
  src: Source[];
  from: string;
  to: string;
  undated: boolean;
  tags: string[];
  page: number;
}
const EMPTY: State = { q: '', src: [], from: '', to: '', undated: true, tags: [], page: 1 };

function readHash(): State {
  const p = new URLSearchParams(location.hash.replace(/^#/, ''));
  return {
    q: p.get('q') ?? '',
    src: (p.get('src') ?? '').split(',').filter((s): s is Source => SOURCE.has(s as Source)),
    from: /^\d{4}$/.test(p.get('from') ?? '') ? (p.get('from') as string) : '',
    to: /^\d{4}$/.test(p.get('to') ?? '') ? (p.get('to') as string) : '',
    undated: p.get('undated') !== '0',
    tags: p.getAll('tag'),
    page: Math.max(1, Number(p.get('p')) || 1),
  };
}
function writeHash(s: State) {
  const p = new URLSearchParams();
  if (s.q) p.set('q', s.q);
  if (s.src.length) p.set('src', s.src.join(','));
  if (s.from) p.set('from', s.from);
  if (s.to) p.set('to', s.to);
  if (!s.undated) p.set('undated', '0');
  for (const t of s.tags) p.append('tag', t);
  if (s.page > 1) p.set('p', String(s.page));
  const h = p.toString().replace(/\+/g, '%20');
  const next = h ? `#${h}` : location.pathname + location.search;
  if ((h ? `#${h}` : '') !== location.hash) history.replaceState(null, '', next);
}

const span = (r: Rec): [number, number] | null => {
  const a = r.yearFrom ?? r.yearTo;
  const b = r.yearTo ?? r.yearFrom;
  return a === null || b === null ? null : [a, b];
};

const texCache = new Map<string, string>();
const escape = (s: string) => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
const PER = 20;

/** One character folded as `fold` does, so that offsets in the folded text are offsets in the original. */
const foldChar = (c: string) => c.normalize('NFD').replace(/[̀-ͯ]/g, '').toLowerCase()[0] ?? c;
const foldChars = (s: string) => s.split('').map(foldChar).join('');

/** `text` escaped, with every occurrence of a query term in a <mark>. */
function marked(text: string, terms: string[]): string {
  if (!terms.length) return escape(text);
  const f = foldChars(text);
  const hits: [number, number][] = [];
  for (const t of terms) for (let i = f.indexOf(t); i >= 0; i = f.indexOf(t, i + t.length)) hits.push([i, i + t.length]);
  if (!hits.length) return escape(text);
  hits.sort((a, b) => a[0] - b[0]);
  let out = '';
  let at = 0;
  for (const [a, b] of hits) {
    if (b <= at) continue;
    const s = Math.max(a, at);
    out += escape(text.slice(at, s)) + '<mark class="rounded-sm bg-encours-100 text-ink-900">' + escape(text.slice(s, b)) + '</mark>';
    at = b;
  }
  return out + escape(text.slice(at));
}

/** Plain text with its $…$ typeset (only the Buffalo index carries any) and the query's terms marked outside the formulas. */
function withMath(s: string, terms: string[] = []): string {
  const key = `${terms.join('\u0001')}\u0002${s}`;
  const hit = texCache.get(key);
  if (hit !== undefined) return hit;
  const html = s
    .split(/(\$[^$]+\$)/)
    .map((p) => (p.length > 2 && p.startsWith('$') && p.endsWith('$') ? katex.renderToString(p.slice(1, -1), { throwOnError: false }) : marked(p, terms)))
    .join('');
  texCache.set(key, html);
  return html;
}

/** Where a long summary should start so that its first match shows: a space outside any formula, some words before the match. */
function excerptStart(s: string, terms: string[]): number {
  if (s.length < 360 || !terms.length) return 0;
  const f = foldChars(s);
  const first = Math.min(...terms.map((t) => f.indexOf(t)).filter((i) => i >= 0));
  if (!Number.isFinite(first) || first < 220) return 0;
  for (let i = first - 120; i < first; i++) {
    if (s[i] === ' ' && (s.slice(0, i).match(/\$/g)?.length ?? 0) % 2 === 0) return i + 1;
  }
  return 0;
}

const NOISE = /^\d+ (pages|leaves)$/;

function Chevron({ open }: { open: boolean }) {
  return (
    <svg viewBox="0 0 12 12" className={`h-3 w-3 shrink-0 transition-transform ${open ? '' : '-rotate-90'}`} aria-hidden="true">
      <path d="M2.5 4.5 6 8l3.5-3.5" fill="none" stroke="currentColor" strokeWidth="1.6" strokeLinecap="round" strokeLinejoin="round" />
    </svg>
  );
}

function Facet({ title, n, children }: { title: string; n?: number; children: ReactNode }) {
  const [open, setOpen] = useState(() => typeof matchMedia === 'undefined' || matchMedia('(min-width: 1024px)').matches);
  return (
    <section className="overflow-hidden rounded-[var(--radius-card)] border border-ink-200 bg-white">
      <button
        type="button"
        aria-expanded={open}
        onClick={() => setOpen(!open)}
        className="flex w-full items-center justify-between gap-2 border-b border-brand-100 bg-brand-50 px-3 py-2 text-left text-[13px] font-semibold text-brand-800 hover:bg-brand-100"
      >
        <span>
          {title}
          {n !== undefined && <span className="tabular ml-1 font-normal text-brand-600">({n})</span>}
        </span>
        <Chevron open={open} />
      </button>
      {open && <div className="px-3 py-2">{children}</div>}
    </section>
  );
}

function Row({ label, n, on, onClick, swatch }: { label: string; n: number; on?: boolean; onClick: () => void; swatch?: string }) {
  return (
    <button
      type="button"
      aria-pressed={on}
      onClick={onClick}
      className={`flex w-full items-baseline justify-between gap-2 rounded px-1 py-[3px] text-left text-[13px] hover:bg-ink-50 ${
        on ? 'font-semibold text-ink-900' : 'text-brand-700'
      } ${n === 0 && !on ? 'opacity-50' : ''}`}
    >
      <span className="flex min-w-0 items-baseline gap-1.5">
        {swatch && <span className="inline-block h-2 w-2 shrink-0 rounded-sm" style={{ background: swatch }} aria-hidden="true" />}
        <span className={on ? '' : 'hover:underline'}>{on ? `✓ ${label}` : label}</span>
      </span>
      <span className="tabular shrink-0 text-[12px] font-normal text-ink-500">({n.toLocaleString('en')})</span>
    </button>
  );
}

function Pager({ page, pages, go }: { page: number; pages: number; go: (p: number) => void }) {
  if (pages <= 1) return null;
  const shown = [...new Set([1, page - 2, page - 1, page, page + 1, page + 2, pages])].filter((p) => p >= 1 && p <= pages).sort((a, b) => a - b);
  const cell = 'tabular inline-flex h-8 min-w-8 items-center justify-center border-r border-ink-200 px-2 text-[13px] last:border-r-0';
  const items: ReactNode[] = [];
  shown.forEach((p, i) => {
    if (i && p - shown[i - 1] > 1) items.push(<span key={`gap${p}`} className={`${cell} text-ink-400`}>…</span>);
    items.push(
      <button
        key={p}
        type="button"
        aria-current={p === page ? 'page' : undefined}
        onClick={() => go(p)}
        className={`${cell} ${p === page ? 'bg-brand-600 font-semibold text-white' : 'text-brand-700 hover:bg-brand-50'}`}
      >
        {p}
      </button>,
    );
  });
  return (
    <nav aria-label="Pages" className="inline-flex overflow-hidden rounded-lg border border-ink-200 bg-white">
      <button type="button" disabled={page === 1} onClick={() => go(page - 1)} className={`${cell} text-brand-700 hover:bg-brand-50 disabled:text-ink-300`} aria-label="Previous page">
        ‹
      </button>
      {items}
      <button type="button" disabled={page === pages} onClick={() => go(page + 1)} className={`${cell} text-brand-700 hover:bg-brand-50 disabled:text-ink-300`} aria-label="Next page">
        ›
      </button>
    </nav>
  );
}

const badge = 'inline-flex items-center gap-1 whitespace-nowrap rounded-md border border-ink-200 bg-white px-2 py-0.5 text-[11.5px] font-medium text-brand-700 hover:border-brand-300 hover:bg-brand-50';

function Result({ r, terms, onTag, chosen }: { r: Indexed; terms: string[]; onTag: (t: string) => void; chosen: string[] }) {
  const [open, setOpen] = useState(false);
  const [allTags, setAllTags] = useState(false);
  const s = SOURCE.get(r.source)!;
  const start = r.summary ? excerptStart(r.summary, terms) : 0;
  const summary = r.summary ? (start ? '… ' + r.summary.slice(start) : r.summary) : null;
  const long = (summary?.length ?? 0) > 320;
  const own = r.tags.filter((t) => !NOISE.test(t));
  const tags = allTags ? own : own.slice(0, 8);
  const sp = span(r);
  const years = sp ? (sp[0] === sp[1] ? String(sp[0]) : `${sp[0]}–${sp[1]}`) : null;
  const href = r.siteUrl ?? r.url;
  return (
    <li className="flex flex-col gap-2 border-b border-ink-100 py-4 last:border-b-0 sm:flex-row sm:gap-4">
      <div className="min-w-0 flex-1">
        <h3 className="text-[15px] font-semibold leading-snug">
          {href ? (
            <a href={href} className="text-brand-700 hover:underline" dangerouslySetInnerHTML={{ __html: withMath(r.title, terms) }} />
          ) : (
            <span className="text-ink-900" dangerouslySetInnerHTML={{ __html: withMath(r.title, terms) }} />
          )}
        </h3>
        <p className="mt-1 text-[13px] font-semibold text-ink-800">{r.holder}</p>
        <p className="mt-0.5 flex flex-wrap items-baseline gap-x-1.5 text-[13px] text-ink-600">
          <span className="inline-flex items-center gap-1.5">
            <span className="inline-block h-2 w-2 rounded-sm" style={{ background: s.colour }} aria-hidden="true" />
            {s.label}
          </span>
          {r.shelfmark && <span>· {r.shelfmark}</span>}
          {(r.date || years) && <span className="tabular">· {r.date ?? years}</span>}
        </p>
        {summary && (
          <div className="mt-2 max-w-[52em] border-l-2 border-ink-200 pl-3 text-[12.5px] leading-relaxed text-ink-500">
            <p className={open || !long ? '' : 'line-clamp-3'} dangerouslySetInnerHTML={{ __html: withMath(summary, terms) }} />
            {long && (
              <button type="button" onClick={() => setOpen(!open)} className="mt-0.5 text-[12px] font-medium text-brand-600 hover:text-brand-700">
                {open ? 'less' : 'more'}
              </button>
            )}
          </div>
        )}
        {own.length > 0 && (
          <ul className="mt-2 flex flex-wrap gap-1" aria-label="Keywords">
            {tags.map((t) => {
              const on = chosen.includes(t);
              return (
                <li key={t}>
                  <button
                    type="button"
                    onClick={() => onTag(t)}
                    aria-pressed={on}
                    title={on ? 'Remove this keyword from the filters' : 'Show only documents with this keyword'}
                    className={`rounded-full border px-2 py-0.5 text-[11.5px] ${
                      on ? 'border-brand-600 bg-brand-600 text-white' : 'border-ink-200 bg-ink-50 text-ink-600 hover:border-brand-300 hover:text-brand-700'
                    }`}
                  >
                    {t}
                  </button>
                </li>
              );
            })}
            {own.length > 8 && (
              <li>
                <button type="button" onClick={() => setAllTags(!allTags)} className="px-1 py-0.5 text-[11.5px] font-medium text-brand-600 hover:text-brand-700">
                  {allTags ? 'fewer' : `+${own.length - 8}`}
                </button>
              </li>
            )}
          </ul>
        )}
      </div>
      <div className="flex shrink-0 flex-wrap gap-1.5 sm:flex-col sm:items-end sm:pt-0.5">
        {r.url && (
          <a href={r.url} target="_blank" rel="noopener noreferrer" className={badge} title={`At ${r.holder}`}>
            Archive ↗
          </a>
        )}
        {r.siteUrl && (
          <a href={r.siteUrl} className={badge}>
            On this site
          </a>
        )}
      </div>
    </li>
  );
}

export function SearchPage() {
  const [data, setData] = useState<{ built: string; records: Indexed[] } | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [st, setSt] = useState<State>(() => (typeof location === 'undefined' ? EMPTY : readHash()));
  const [openDecade, setOpenDecade] = useState<number | null>(null);
  const [moreTags, setMoreTags] = useState(false);
  const q = useDeferredValue(st.q);

  useEffect(() => {
    fetch(`${import.meta.env.BASE_URL}search-index.json`)
      .then((r) => (r.ok ? r.json() : Promise.reject(new Error(`HTTP ${r.status}`))))
      .then((d: { built: string; records: Rec[] }) =>
        setData({
          built: d.built,
          records: d.records.map((r) => ({
            ...r,
            hayTitle: fold(r.title),
            hay: fold([r.title, r.summary, r.shelfmark, r.date, r.holder, ...r.tags].filter(Boolean).join(' \u0001 ')),
          })),
        }),
      )
      .catch((e: Error) => setError(e.message));
  }, []);

  useEffect(() => {
    const on = () => setSt(readHash());
    addEventListener('hashchange', on);
    return () => removeEventListener('hashchange', on);
  }, []);
  useEffect(() => writeHash(st), [st]);

  /** Any change but a page turn goes back to the first page. */
  const set = (patch: Partial<State>) => setSt((s) => ({ ...s, page: 1, ...patch }));

  const parsed = useMemo(() => parseQuery(q), [q]);
  const yearTokens = parsed.from !== null || parsed.to !== null;
  const from = yearTokens ? parsed.from : st.from ? Number(st.from) : null;
  const to = yearTokens ? parsed.to : st.to ? Number(st.to) : null;
  const sources = parsed.sources.length ? parsed.sources : st.src;

  // Words and keywords: the year facet counts over this.
  const worded = useMemo(() => {
    if (!data) return [];
    return data.records.filter((r) => st.tags.every((t) => r.tags.includes(t)) && parsed.terms.every((t) => r.hay.includes(t)));
  }, [data, parsed.terms, st.tags]);

  // Everything but the source filter: the source facet counts over this.
  const matched = useMemo(() => {
    if (from === null && to === null) return worded;
    return worded.filter((r) => {
      const sp = span(r);
      if (!sp) return st.undated;
      return !((to !== null && sp[0] > to) || (from !== null && sp[1] < from));
    });
  }, [worded, from, to, st.undated]);

  const counts = useMemo(() => {
    const m = new Map<Source, number>();
    for (const r of matched) m.set(r.source, (m.get(r.source) ?? 0) + 1);
    return m;
  }, [matched]);

  const results = useMemo(() => {
    const rs = sources.length ? matched.filter((r) => sources.includes(r.source)) : matched.slice();
    const order = new Map(SOURCES.map((s, i) => [s.id, i]));
    const score = (r: Indexed) => parsed.terms.reduce((n, t) => n + (r.hayTitle.includes(t) ? 1 : 0), 0);
    const year = (r: Indexed) => span(r)?.[0] ?? 9999;
    return rs
      .map((r) => ({ r, s: score(r) }))
      .sort((a, b) => b.s - a.s || order.get(a.r.source)! - order.get(b.r.source)! || year(a.r) - year(b.r))
      .map((x) => x.r);
  }, [matched, sources, parsed.terms]);

  // Decades and years over the worded set restricted to the chosen sources, so that choosing a decade leaves the others visible.
  const { decades, undatedCount } = useMemo(() => {
    const years = new Map<number, number>();
    let undated = 0;
    for (const r of worded) {
      if (sources.length && !sources.includes(r.source)) continue;
      const sp = span(r);
      if (!sp) {
        undated++;
        continue;
      }
      for (let y = sp[0]; y <= Math.min(sp[1], sp[0] + 60); y++) years.set(y, (years.get(y) ?? 0) + 1);
    }
    const dec = new Map<number, { n: Set<number>; years: [number, number][] }>();
    for (const [y, n] of [...years].sort((a, b) => b[0] - a[0])) {
      const d = Math.floor(y / 10) * 10;
      if (!dec.has(d)) dec.set(d, { n: new Set(), years: [] });
      dec.get(d)!.years.push([y, n]);
    }
    // A decade counts each document once, however many of its years fall in it.
    for (const r of worded) {
      if (sources.length && !sources.includes(r.source)) continue;
      const sp = span(r);
      if (!sp) continue;
      for (const [d, e] of dec) if (sp[0] <= d + 9 && sp[1] >= d) e.n.add(worded.indexOf(r));
    }
    return { decades: [...dec].map(([d, e]) => ({ d, n: e.n.size, years: e.years })), undatedCount: undated };
  }, [worded, sources]);

  const topTags = useMemo(() => {
    const m = new Map<string, number>();
    for (const r of results) for (const t of r.tags) if (!NOISE.test(t)) m.set(t, (m.get(t) ?? 0) + 1);
    for (const t of st.tags) if (!m.has(t)) m.set(t, 0);
    return [...m]
      .filter(([t, n]) => n > 1 || st.tags.includes(t))
      .sort((a, b) => Number(st.tags.includes(b[0])) - Number(st.tags.includes(a[0])) || b[1] - a[1] || a[0].localeCompare(b[0]));
  }, [results, st.tags]);

  const toggle = (id: Source) => {
    const cur = new Set(st.src);
    if (cur.has(id)) cur.delete(id);
    else cur.add(id);
    set({ src: SOURCES.map((s) => s.id).filter((s) => cur.has(s)) });
  };
  const toggleTag = (t: string) => set({ tags: st.tags.includes(t) ? st.tags.filter((x) => x !== t) : [...st.tags, t] });
  const range = (a: number, b: number) =>
    !yearTokens && st.from === String(a) && st.to === String(b) ? set({ from: '', to: '' }) : set({ from: String(a), to: String(b) });
  const yearInput = 'tabular w-[4.8em] rounded-md border border-ink-200 bg-white px-1.5 py-1 text-[13px] text-ink-900 focus:border-brand-400 focus:outline-none';

  const pages = Math.max(1, Math.ceil(results.length / PER));
  const page = Math.min(st.page, pages);
  const go = (p: number) => {
    setSt((s) => ({ ...s, page: p }));
    document.getElementById('search-results')?.scrollIntoView({ block: 'start' });
  };
  const active = st.q || st.src.length > 0 || st.tags.length > 0 || st.from || st.to || !st.undated;

  return (
    <>
      <Header path="/search/" />

      <main className="mx-auto max-w-6xl px-5 py-10">
        <header className="max-w-[48em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.14em] text-ink-400">Search</p>
          <h1 className="titre mt-2 text-[28px] leading-tight text-ink-900">Every document, by its catalogue entry</h1>
          <p className="mt-3 text-[14.5px] leading-relaxed text-ink-600">
            Search the catalogue entries of the Montpellier folders, the letters found in them, the Bourbaki archive,
            Quillen's notebooks, the Fonds Grothendieck–Illusie, the BnF boxes, the Buffalo lectures and the edition's
            findings. The index holds titles, dates, shelfmarks, keywords and summaries. It never holds the text of a
            document or of its transcription, so you read each document where it is kept.
          </p>
        </header>

        <form
          role="search"
          onSubmit={(e) => {
            e.preventDefault();
            (document.activeElement as HTMLElement | null)?.blur();
          }}
          className="mt-6 flex flex-wrap items-stretch gap-2 rounded-[var(--radius-card)] border border-ink-200 bg-ink-50 p-3"
        >
          <label htmlFor="search-q" className="sr-only">
            Search
          </label>
          <div className="relative min-w-0 flex-1 basis-64">
            <input
              id="search-q"
              type="search"
              value={st.q}
              onChange={(e) => set({ q: e.target.value })}
              placeholder="topos, Deligne, rédaction 433, source:quillen year:1968-1972 …"
              className="h-10 w-full rounded-lg border border-ink-200 bg-white px-3 text-[15px] text-ink-900 placeholder:text-ink-400 focus:border-brand-400 focus:outline-none"
            />
          </div>
          <label className="sr-only" htmlFor="search-scope">
            Source
          </label>
          <select
            id="search-scope"
            value={sources.length === 1 ? sources[0] : sources.length ? 'many' : ''}
            disabled={parsed.sources.length > 0}
            onChange={(e) => set({ src: e.target.value ? [e.target.value as Source] : [] })}
            className="h-10 rounded-lg border border-ink-200 bg-white px-2 text-[13.5px] text-ink-800 focus:border-brand-400 focus:outline-none"
          >
            <option value="">All sources</option>
            {sources.length > 1 && <option value="many">{sources.length} sources</option>}
            {SOURCES.map((s) => (
              <option key={s.id} value={s.id}>
                {s.label}
              </option>
            ))}
          </select>
          <button type="submit" className="h-10 rounded-lg bg-brand-600 px-4 text-[14px] font-semibold text-white hover:bg-brand-700">
            Search
          </button>
          <details className="w-full text-[12px] leading-relaxed text-ink-500">
            <summary className="cursor-pointer select-none font-medium text-brand-600 hover:text-brand-700">How to search</summary>
            <p className="mt-1">
              A result has to contain every word you type. Case and accents don't matter, and words in "quotes" are
              matched as a phrase. Typing <code className="font-mono text-[11.5px]">source:bourbaki</code> or{' '}
              <code className="font-mono text-[11.5px]">year:1960-1970</code> in the box overrides the filters on the
              left. A document counts for a range of years if its dating overlaps it, so « [vers 1963-1973] » turns up
              for any year from 1963 to 1973. Clicking a keyword, under a result or in the left column, keeps only the
              documents tagged with it.
            </p>
          </details>
        </form>

        <div className="mt-6 grid gap-6 lg:grid-cols-[15.5rem_minmax(0,1fr)]">
          <aside className="flex flex-col gap-3" aria-label="Filters">
            <Facet title="Sources" n={SOURCES.filter((s) => (counts.get(s.id) ?? 0) > 0).length}>
              {SOURCES.map((s) => (
                <Row
                  key={s.id}
                  label={s.label}
                  swatch={s.colour}
                  n={counts.get(s.id) ?? 0}
                  on={sources.includes(s.id)}
                  onClick={() => (parsed.sources.length ? undefined : toggle(s.id))}
                />
              ))}
            </Facet>

            <Facet title="Years" n={decades.length}>
              {decades.map(({ d, n, years }) => (
                <div key={d}>
                  <div className="flex items-center gap-1">
                    <div className="min-w-0 flex-1">
                      <Row label={`${d}–${d + 9}`} n={n} on={!yearTokens && st.from === String(d) && st.to === String(d + 9)} onClick={() => range(d, d + 9)} />
                    </div>
                    <button
                      type="button"
                      onClick={() => setOpenDecade(openDecade === d ? null : d)}
                      aria-expanded={openDecade === d}
                      aria-label={`Years of the ${d}s`}
                      className="rounded p-1 text-ink-500 hover:bg-ink-100"
                    >
                      <Chevron open={openDecade === d} />
                    </button>
                  </div>
                  {openDecade === d && (
                    <div className="mb-1 ml-3 border-l border-ink-200 pl-2">
                      {[...years].reverse().map(([y, m]) => (
                        <Row key={y} label={String(y)} n={m} on={!yearTokens && st.from === String(y) && st.to === String(y)} onClick={() => range(y, y)} />
                      ))}
                    </div>
                  )}
                </div>
              ))}
              <div className="mt-2 flex items-center gap-1.5 border-t border-ink-100 pt-2 text-[13px] text-ink-600">
                <input
                  type="number"
                  inputMode="numeric"
                  min={1900}
                  max={2030}
                  placeholder="from"
                  aria-label="From year"
                  value={yearTokens ? (parsed.from ?? '') : st.from}
                  disabled={yearTokens}
                  onChange={(e) => set({ from: e.target.value.slice(0, 4) })}
                  className={yearInput}
                />
                <span aria-hidden="true">–</span>
                <input
                  type="number"
                  inputMode="numeric"
                  min={1900}
                  max={2030}
                  placeholder="to"
                  aria-label="To year"
                  value={yearTokens ? (parsed.to ?? '') : st.to}
                  disabled={yearTokens}
                  onChange={(e) => set({ to: e.target.value.slice(0, 4) })}
                  className={yearInput}
                />
              </div>
              <label className="mt-1.5 flex items-center gap-1.5 text-[12.5px] text-ink-600">
                <input type="checkbox" checked={st.undated} onChange={(e) => set({ undated: e.target.checked })} className="accent-brand-600" />
                include undated <span className="tabular text-ink-400">({undatedCount.toLocaleString('en')})</span>
              </label>
            </Facet>

            {topTags.length > 0 && (
              <Facet title="Keywords" n={topTags.length}>
                {(moreTags ? topTags.slice(0, 60) : topTags.slice(0, 12)).map(([t, n]) => (
                  <Row key={t} label={t} n={n} on={st.tags.includes(t)} onClick={() => toggleTag(t)} />
                ))}
                {topTags.length > 12 && (
                  <button type="button" onClick={() => setMoreTags(!moreTags)} className="mt-1 px-1 text-[12px] font-medium text-brand-600 hover:text-brand-700">
                    {moreTags ? 'fewer' : `more (${Math.min(topTags.length, 60) - 12})`}
                  </button>
                )}
              </Facet>
            )}
          </aside>

          <section id="search-results" className="min-w-0 scroll-mt-24" aria-live="polite">
            {error ? (
              <p className="text-[14px] text-ink-600">The index could not be loaded ({error}).</p>
            ) : !data ? (
              <p className="text-[14px] text-ink-500">Loading the index…</p>
            ) : (
              <>
                <div className="flex flex-wrap items-baseline justify-between gap-x-4 gap-y-2">
                  <h2 className="text-[22px] font-semibold text-ink-900">
                    <span className="tabular">{results.length.toLocaleString('en')}</span> {results.length === 1 ? 'result' : 'results'}
                    <span className="ml-2 text-[13px] font-normal text-ink-500">of {data.records.length.toLocaleString('en')} documents</span>
                  </h2>
                  {active && (
                    <button type="button" onClick={() => setSt(EMPTY)} className="text-[13px] font-medium text-brand-600 hover:text-brand-700">
                      clear the search
                    </button>
                  )}
                </div>
                {(st.tags.length > 0 || (st.src.length > 0 && !parsed.sources.length) || (!yearTokens && (st.from || st.to))) && (
                  <ul className="mt-2 flex flex-wrap gap-1.5" aria-label="Filters in force">
                    {!parsed.sources.length &&
                      st.src.map((id) => (
                        <li key={id}>
                          <button type="button" onClick={() => toggle(id)} className="rounded-full border border-brand-200 bg-brand-50 px-2.5 py-0.5 text-[12px] text-brand-800 hover:bg-brand-100">
                            {SOURCE.get(id)!.label} ×
                          </button>
                        </li>
                      ))}
                    {!yearTokens && (st.from || st.to) && (
                      <li>
                        <button type="button" onClick={() => set({ from: '', to: '' })} className="tabular rounded-full border border-brand-200 bg-brand-50 px-2.5 py-0.5 text-[12px] text-brand-800 hover:bg-brand-100">
                          {st.from === st.to ? st.from : `${st.from || '…'}–${st.to || '…'}`} ×
                        </button>
                      </li>
                    )}
                    {st.tags.map((t) => (
                      <li key={t}>
                        <button type="button" onClick={() => toggleTag(t)} className="rounded-full border border-brand-200 bg-brand-50 px-2.5 py-0.5 text-[12px] text-brand-800 hover:bg-brand-100">
                          {t} ×
                        </button>
                      </li>
                    ))}
                  </ul>
                )}
                <div className="mt-3">
                  <Pager page={page} pages={pages} go={go} />
                </div>
                {results.length > 0 ? (
                  <ol className="card mt-3 px-4 sm:px-5">
                    {results.slice((page - 1) * PER, page * PER).map((r) => (
                      <Result key={r.id} r={r} terms={parsed.terms} onTag={toggleTag} chosen={st.tags} />
                    ))}
                  </ol>
                ) : (
                  <p className="mt-3 text-[14px] text-ink-500">No document matches all of this. Drop a word or a keyword, or widen the years.</p>
                )}
                <div className="mt-4">
                  <Pager page={page} pages={pages} go={go} />
                </div>
              </>
            )}
          </section>
        </div>

        <p className="mt-12 max-w-[48em] text-[12px] leading-relaxed text-ink-400">
          public/search-index.json{data ? `, built on ${data.built}` : ''} by scripts/search-index.mjs from the
          site's catalogues: the Montpellier inventory and its notices (title, group, typology, keywords, no Résumé),
          the letters' register, the AHP's Bourbaki catalogue, the Clay's file list with Glenys Luke's index, the
          IHÉS inventory, the BnF boxes, our index of the Buffalo lectures (one entry per tape side) and the findings.
          The keywords on the transcribed Bourbaki, Quillen and IHÉS documents are ours, written from the
          transcriptions.
        </p>
      </main>

      <Footer />
    </>
  );
}
