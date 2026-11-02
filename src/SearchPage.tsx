import { useDeferredValue, useEffect, useMemo, useState } from 'react';
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

const CAP = 200;

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
}
const EMPTY: State = { q: '', src: [], from: '', to: '', undated: true };

function readHash(): State {
  const p = new URLSearchParams(location.hash.replace(/^#/, ''));
  return {
    q: p.get('q') ?? '',
    src: (p.get('src') ?? '').split(',').filter((s): s is Source => SOURCE.has(s as Source)),
    from: /^\d{4}$/.test(p.get('from') ?? '') ? (p.get('from') as string) : '',
    to: /^\d{4}$/.test(p.get('to') ?? '') ? (p.get('to') as string) : '',
    undated: p.get('undated') !== '0',
  };
}
function writeHash(s: State) {
  const p = new URLSearchParams();
  if (s.q) p.set('q', s.q);
  if (s.src.length) p.set('src', s.src.join(','));
  if (s.from) p.set('from', s.from);
  if (s.to) p.set('to', s.to);
  if (!s.undated) p.set('undated', '0');
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
/** Plain text with its $…$ typeset; only the Buffalo index carries any. */
function withMath(s: string): string {
  const hit = texCache.get(s);
  if (hit !== undefined) return hit;
  const html = s
    .split(/(\$[^$]+\$)/)
    .map((p) => (p.length > 2 && p.startsWith('$') && p.endsWith('$') ? katex.renderToString(p.slice(1, -1), { throwOnError: false }) : escape(p)))
    .join('');
  texCache.set(s, html);
  return html;
}

const link = 'font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700';

function Result({ r }: { r: Indexed }) {
  const [open, setOpen] = useState(false);
  const [allTags, setAllTags] = useState(false);
  const s = SOURCE.get(r.source)!;
  const long = (r.summary?.length ?? 0) > 320;
  const tags = allTags ? r.tags : r.tags.slice(0, 8);
  const sp = span(r);
  const years = sp ? (sp[0] === sp[1] ? String(sp[0]) : `${sp[0]}–${sp[1]}`) : null;
  return (
    <li className="border-b border-ink-100 py-4 last:border-b-0">
      <div className="flex flex-wrap items-baseline gap-x-2 gap-y-1 text-[11.5px]">
        <span className="inline-flex items-center gap-1.5 font-semibold uppercase tracking-wider text-ink-500">
          <span className="inline-block h-2 w-2 rounded-sm" style={{ background: s.colour }} aria-hidden="true" />
          {s.label}
        </span>
        {(r.date || years) && <span className="tabular text-ink-500">· {r.date ?? years}</span>}
      </div>
      <h3 className="mt-1 text-[15px] font-semibold leading-snug text-ink-900">
        {r.siteUrl ?? r.url ? (
          <a href={(r.siteUrl ?? r.url) as string} className="hover:text-brand-700">
            {r.title}
          </a>
        ) : (
          r.title
        )}
      </h3>
      <p className="mt-0.5 text-[12.5px] text-ink-500">
        {[r.shelfmark, r.holder].filter(Boolean).join(' · ')}
      </p>
      {r.summary && (
        <div className="mt-1.5 max-w-[48em] text-[13.5px] leading-relaxed text-ink-700">
          <p className={open || !long ? '' : 'line-clamp-3'} dangerouslySetInnerHTML={{ __html: withMath(r.summary) }} />
          {long && (
            <button type="button" onClick={() => setOpen(!open)} className="mt-0.5 text-[12px] font-medium text-brand-600 hover:text-brand-700">
              {open ? 'less' : 'more'}
            </button>
          )}
        </div>
      )}
      {r.tags.length > 0 && (
        <ul className="mt-2 flex flex-wrap gap-1">
          {tags.map((t) => (
            <li key={t} className="rounded-full border border-ink-200 bg-ink-50 px-2 py-0.5 text-[11.5px] text-ink-600">
              {t}
            </li>
          ))}
          {r.tags.length > 8 && (
            <li>
              <button type="button" onClick={() => setAllTags(!allTags)} className="px-1 py-0.5 text-[11.5px] font-medium text-brand-600 hover:text-brand-700">
                {allTags ? 'fewer' : `+${r.tags.length - 8}`}
              </button>
            </li>
          )}
        </ul>
      )}
      <p className="mt-2 flex flex-wrap gap-x-4 gap-y-1 text-[12.5px]">
        {r.url && (
          <a href={r.url} target="_blank" rel="noopener noreferrer" className={link}>
            at the archive ↗
          </a>
        )}
        {r.siteUrl && (
          <a href={r.siteUrl} className={link}>
            on this site
          </a>
        )}
      </p>
    </li>
  );
}

export function SearchPage() {
  const [data, setData] = useState<{ built: string; records: Indexed[] } | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [st, setSt] = useState<State>(() => (typeof location === 'undefined' ? EMPTY : readHash()));
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

  const set = (patch: Partial<State>) => setSt((s) => ({ ...s, ...patch }));

  const parsed = useMemo(() => parseQuery(q), [q]);
  const from = parsed.from ?? (st.from ? Number(st.from) : null);
  const to = parsed.from !== null || parsed.to !== null ? parsed.to : st.to ? Number(st.to) : null;
  const sources = parsed.sources.length ? parsed.sources : st.src;

  // Everything but the source filter: the facets count over this.
  const matched = useMemo(() => {
    if (!data) return [];
    const ranged = from !== null || to !== null;
    return data.records.filter((r) => {
      if (ranged) {
        const sp = span(r);
        if (!sp) {
          if (!st.undated) return false;
        } else if ((to !== null && sp[0] > to) || (from !== null && sp[1] < from)) return false;
      }
      return parsed.terms.every((t) => r.hay.includes(t));
    });
  }, [data, parsed.terms, from, to, st.undated]);

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

  const toggle = (id: Source) => {
    const cur = new Set(st.src);
    if (cur.has(id)) cur.delete(id);
    else cur.add(id);
    set({ src: SOURCES.map((s) => s.id).filter((s) => cur.has(s)) });
  };
  const tokensRule = parsed.sources.length > 0 || parsed.from !== null || parsed.to !== null;
  const yearInput = 'tabular w-[5.5em] rounded-lg border border-ink-200 bg-white px-2 py-1 text-[13px] text-ink-900 focus:border-brand-400 focus:outline-none';

  return (
    <>
      <Header path="/search/" />

      <main className="mx-auto max-w-5xl px-5 py-12">
        <header className="max-w-[44em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.14em] text-ink-400">Search</p>
          <h1 className="titre mt-2 text-[30px] leading-tight text-ink-900">Every document, by its catalogue entry</h1>
          <p className="mt-4 text-[15.5px] leading-relaxed text-ink-600">
            One search across the Montpellier folders, the letters found in them, the Bourbaki archive, Quillen's
            notebooks, the Fonds Grothendieck–Illusie, the BnF boxes, the Buffalo lectures and the edition's findings.
            It finds a document by its title, date, shelfmark, keywords and summary, and links to its holder.
          </p>
        </header>

        <div className="mt-6 max-w-[44em] rounded-[var(--radius-card)] border border-encours-200 bg-encours-50 px-4 py-3 text-[13px] leading-relaxed text-ink-700">
          <strong className="font-semibold">Metadata and summaries only.</strong> The index holds what the catalogues
          say about each document, with summaries in the registers' own words, and no text of the documents or of
          their transcriptions. The documents are read at their holders: Montpellier, the AHP, the Clay, the IHÉS,
          the BnF, YouTube.
        </div>

        <section className="card mt-8 p-4 sm:p-5">
          <label htmlFor="search-q" className="sr-only">
            Search
          </label>
          <input
            id="search-q"
            type="search"
            value={st.q}
            onChange={(e) => set({ q: e.target.value })}
            placeholder="topos, Deligne, rédaction 433, source:quillen year:1968-1972 …"
            className="w-full rounded-lg border border-ink-200 bg-white px-3 py-2 text-[15px] text-ink-900 placeholder:text-ink-400 focus:border-brand-400 focus:outline-none"
          />
          <p className="mt-1.5 text-[12px] leading-relaxed text-ink-500">
            Every word must match, in any case and with or without accents; "quoted words" match as a phrase.{' '}
            <code className="font-mono text-[11.5px]">source:bourbaki</code> and{' '}
            <code className="font-mono text-[11.5px]">year:1960-1970</code> in the query override the controls below.
          </p>

          <div className="mt-4 flex flex-wrap gap-1.5" role="group" aria-label="Sources">
            {SOURCES.map((s) => {
              const on = sources.includes(s.id);
              const n = counts.get(s.id) ?? 0;
              return (
                <button
                  key={s.id}
                  type="button"
                  aria-pressed={on}
                  onClick={() => toggle(s.id)}
                  disabled={parsed.sources.length > 0}
                  className={`inline-flex items-center gap-1.5 rounded-full border px-2.5 py-1 text-[12.5px] transition disabled:cursor-not-allowed ${
                    on ? 'border-ink-900 bg-ink-900 text-white' : 'border-ink-200 bg-white text-ink-700 hover:border-ink-400'
                  } ${n === 0 && !on ? 'opacity-50' : ''}`}
                >
                  <span className="inline-block h-2 w-2 rounded-sm" style={{ background: s.colour }} aria-hidden="true" />
                  {s.label}
                  <span className={`tabular ${on ? 'text-ink-200' : 'text-ink-400'}`}>{n}</span>
                </button>
              );
            })}
            {st.src.length > 0 && !parsed.sources.length && (
              <button type="button" onClick={() => set({ src: [] })} className="px-2 py-1 text-[12.5px] font-medium text-brand-600 hover:text-brand-700">
                all sources
              </button>
            )}
          </div>

          <div className="mt-4 flex flex-wrap items-center gap-x-3 gap-y-2 text-[13px] text-ink-700">
            <span className="font-medium">Years</span>
            <label className="flex items-center gap-1.5">
              <span className="sr-only">From</span>
              <input
                type="number"
                inputMode="numeric"
                min={1900}
                max={2030}
                placeholder="from"
                value={parsed.from !== null || parsed.to !== null ? (parsed.from ?? '') : st.from}
                disabled={parsed.from !== null || parsed.to !== null}
                onChange={(e) => set({ from: e.target.value.slice(0, 4) })}
                className={yearInput}
              />
            </label>
            <span aria-hidden="true">–</span>
            <label className="flex items-center gap-1.5">
              <span className="sr-only">To</span>
              <input
                type="number"
                inputMode="numeric"
                min={1900}
                max={2030}
                placeholder="to"
                value={parsed.from !== null || parsed.to !== null ? (parsed.to ?? '') : st.to}
                disabled={parsed.from !== null || parsed.to !== null}
                onChange={(e) => set({ to: e.target.value.slice(0, 4) })}
                className={yearInput}
              />
            </label>
            <label className="flex items-center gap-1.5">
              <input type="checkbox" checked={st.undated} onChange={(e) => set({ undated: e.target.checked })} className="accent-brand-600" />
              include undated
            </label>
            {(st.from || st.to || st.q || st.src.length > 0 || !st.undated) && (
              <button type="button" onClick={() => setSt(EMPTY)} className="ml-auto text-[12.5px] font-medium text-brand-600 hover:text-brand-700">
                clear
              </button>
            )}
          </div>
          <p className="mt-1 text-[12px] text-ink-500">
            A document is kept when its dating overlaps the range; « [vers 1963-1973] » counts as 1963–1973.
            {tokensRule ? ' The query’s tokens are in force.' : ''}
          </p>
        </section>

        <section className="mt-6" aria-live="polite">
          {error ? (
            <p className="text-[14px] text-ink-600">The index could not be loaded ({error}).</p>
          ) : !data ? (
            <p className="text-[14px] text-ink-500">Loading the index…</p>
          ) : (
            <>
              <p className="text-[13px] text-ink-600">
                <strong className="tabular font-semibold text-ink-900">{results.length.toLocaleString('en')}</strong>{' '}
                {results.length === 1 ? 'document' : 'documents'}
                {results.length > CAP ? `, the first ${CAP} shown — narrow the search to see the rest` : ''}
                {' '}of {data.records.length.toLocaleString('en')}.
              </p>
              {results.length > 0 ? (
                <ol className="card mt-3 px-4 sm:px-5">
                  {results.slice(0, CAP).map((r) => (
                    <Result key={r.id} r={r} />
                  ))}
                </ol>
              ) : (
                <p className="mt-3 text-[14px] text-ink-500">Nothing matches every word. Try fewer words, or widen the years.</p>
              )}
            </>
          )}
        </section>

        <p className="mt-12 max-w-[44em] text-[12px] leading-relaxed text-ink-400">
          public/search-index.json{data ? `, built on ${data.built}` : ''} by scripts/search-index.mjs from the
          site's catalogues: the Montpellier inventory and its notices (title, group, typology, keywords, no Résumé),
          the letters' register, the AHP's Bourbaki catalogue, the Clay's file list with Glenys Luke's index, the
          IHÉS inventory, the BnF boxes, our index of the Buffalo lectures (one entry per tape side) and the findings.
        </p>
      </main>

      <Footer />
    </>
  );
}
