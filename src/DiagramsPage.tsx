import { useEffect, useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import diagramsRaw from './content/diagrams.json';
import handRaw from './content/hand.json';

/**
 * Every commutative diagram in the transcriptions, folder by folder.
 *
 * The diagrams are drawn by the same renderer as the reading views — a grid
 * of KaTeX nodes with the arrows measured and drawn in SVG — and each folder's
 * gallery is its own document (public/transcripts/diagrams/<folder>.html,
 * written by `node scripts/diagrams.mjs`), framed here as the reading views are framed
 * beside the facsimile. Each diagram is captioned with its batch and page and
 * links back to the reading, where it stands between the lines it belongs to.
 */

interface Diagram {
  batch: number;
  page: string | null;
  nodes: number;
  arrows: number;
  rows: number;
}
interface FolderDiagrams {
  id: string;
  title: string;
  date: string;
  n: number;
  byBatch: Record<string, number>;
  diagrams: Diagram[];
}
const DG = diagramsRaw as unknown as { built: string; total: number; folders: FolderDiagrams[] };
const PAGES = new Map(
  (handRaw as unknown as { folders: { id: string; pages: number }[] }).folders.map((f) => [f.id, f.pages]),
);

const GREEN = '#128557';
const shortTitle = (t: string) => t.replace(/\s*:\s*notes manuscrites.*$/i, '').replace(/\s*:.*$/, '');
const per100 = (f: FolderDiagrams) => (100 * f.n) / Math.max(1, PAGES.get(f.id) ?? 1);

export function DiagramsPage() {
  const [sel, setSel] = useState<{ id: string; at?: number }>(() => {
    const [id, at] = location.hash.slice(1).split('/');
    const f = DG.folders.find((x) => x.id === id);
    return f ? { id, at: at ? Number(at) : undefined } : { id: [...DG.folders].sort((a, b) => b.n - a.n)[0].id };
  });
  const [order, setOrder] = useState<'shelfmark' | 'count' | 'density'>('count');

  useEffect(() => {
    history.replaceState(null, '', `#${sel.id}${sel.at ? `/${sel.at}` : ''}`);
  }, [sel]);
  // A link from elsewhere on the site to /diagrams/#<folder> arrives as a
  // hash change when the page is already open.
  useEffect(() => {
    const go = () => {
      const [id, at] = location.hash.slice(1).split('/');
      if (DG.folders.some((x) => x.id === id)) setSel({ id, at: at ? Number(at) : undefined });
    };
    addEventListener('hashchange', go);
    return () => removeEventListener('hashchange', go);
  }, []);

  const folder = DG.folders.find((f) => f.id === sel.id) ?? DG.folders[0];
  const list = useMemo(() => {
    const l = [...DG.folders];
    if (order === 'count') l.sort((a, b) => b.n - a.n);
    if (order === 'density') l.sort((a, b) => per100(b) - per100(a));
    return l;
  }, [order]);
  const max = Math.max(...DG.folders.map((f) => (order === 'density' ? per100(f) : f.n)));

  const all = DG.folders.flatMap((f) => f.diagrams.map((d, i) => ({ f, d, i })));
  const largest = [...all].sort((a, b) => b.d.nodes + b.d.arrows - (a.d.nodes + a.d.arrows)).slice(0, 8);
  const pagesRead = [...PAGES.values()].reduce((a, b) => a + b, 0);
  const median = [...all].map((x) => x.d.nodes).sort((a, b) => a - b)[Math.floor(all.length / 2)];
  const squares = all.filter((x) => x.d.nodes === 4 && x.d.rows === 2).length;

  return (
    <>
      <Header path="/diagrams/" />

      <main className="mx-auto max-w-6xl px-5 py-12">
        <header className="max-w-[46em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.14em] text-ink-400">Diagrams</p>
          <h1 className="titre mt-2 text-[30px] leading-tight text-ink-900">
            The commutative diagrams, side by side
          </h1>
          <p className="mt-4 text-[15.5px] leading-relaxed text-ink-600">
            Commutative diagrams are the language of this fonds. He drew them in the margins, across
            a page, crammed between two formulas; the transcriptions set each one in{' '}
            <code className="rounded bg-ink-100 px-1 text-[13px]">tikz-cd</code>. Here are all{' '}
            {DG.total.toLocaleString('en-GB')} of them from the {DG.folders.length} folders that have
            any, a folder at a time, each linked back to the page it stands on.
          </p>
        </header>

        <div className="mt-6 grid grid-cols-2 gap-3 sm:grid-cols-4">
          <div className="card px-4 py-3">
            <p className="tabular text-[24px] font-semibold text-ink-900">{DG.total.toLocaleString('en-GB')}</p>
            <p className="text-[12.5px] text-ink-600">diagrams</p>
          </div>
          <div className="card px-4 py-3">
            <p className="tabular text-[24px] font-semibold text-ink-900">
              {((100 * DG.total) / pagesRead).toFixed(0)}
            </p>
            <p className="text-[12.5px] text-ink-600">per hundred pages read</p>
          </div>
          <div className="card px-4 py-3">
            <p className="tabular text-[24px] font-semibold text-ink-900">{median}</p>
            <p className="text-[12.5px] text-ink-600">nodes in the median diagram</p>
          </div>
          <div className="card px-4 py-3">
            <p className="tabular text-[24px] font-semibold text-ink-900">{squares}</p>
            <p className="text-[12.5px] text-ink-600">squares, two by two</p>
          </div>
        </div>

        <div className="mt-8 grid gap-6 lg:grid-cols-[18rem_1fr]">
          <aside>
            <div className="flex flex-wrap items-center gap-1.5 text-[12px]">
              <span className="text-ink-400">Order</span>
              {(
                [
                  ['count', 'most'],
                  ['density', 'densest'],
                  ['shelfmark', 'shelfmark'],
                ] as const
              ).map(([k, label]) => (
                <button
                  key={k}
                  type="button"
                  onClick={() => setOrder(k)}
                  aria-pressed={order === k}
                  className={`rounded-full border px-2.5 py-0.5 ${
                    order === k ? 'border-ink-900 bg-ink-900 text-white' : 'border-ink-200 text-ink-600 hover:bg-ink-100'
                  }`}
                >
                  {label}
                </button>
              ))}
            </div>
            <ul className="mt-3 max-h-[36rem] space-y-0.5 overflow-y-auto pr-1 text-[12.5px]">
              {list.map((f) => {
                const v = order === 'density' ? per100(f) : f.n;
                return (
                  <li key={f.id}>
                    <button
                      type="button"
                      onClick={() => setSel({ id: f.id })}
                      aria-pressed={f.id === folder.id}
                      title={f.title}
                      className={`flex w-full items-center gap-2 rounded px-1.5 py-1 text-left ${
                        f.id === folder.id ? 'bg-ink-100' : 'hover:bg-ink-50'
                      }`}
                    >
                      <span className="tabular w-11 shrink-0 font-semibold text-ink-900">{f.id}</span>
                      <span className="h-1.5 flex-1 rounded-full bg-ink-100">
                        <span className="block h-1.5 rounded-full" style={{ width: `${(100 * v) / max}%`, background: GREEN }} />
                      </span>
                      <span className="tabular w-10 shrink-0 text-right text-ink-500">
                        {order === 'density' ? v.toFixed(0) : v}
                      </span>
                    </button>
                  </li>
                );
              })}
            </ul>
            <p className="mt-2 text-[11.5px] leading-snug text-ink-400">
              {order === 'density' ? 'Diagrams per hundred pages transcribed.' : 'Diagrams in the folder.'}
            </p>
          </aside>

          <section className="min-w-0">
            <div className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
              <h2 className="text-[15px] font-semibold text-ink-900">
                n° {folder.id} <span className="font-normal text-ink-600">{shortTitle(folder.title)}</span>
              </h2>
              <span className="tabular text-[12.5px] text-ink-400">
                {folder.n} diagram{folder.n > 1 ? 's' : ''} · {folder.date || 's.d.'}
              </span>
              <a
                href={`/transcripts/diagrams/${folder.id}.html`}
                target="_blank"
                rel="noreferrer"
                className="ml-auto text-[12.5px] text-brand-600 hover:text-brand-700"
              >
                open on its own ↗
              </a>
            </div>
            <iframe
              key={`${folder.id}-${sel.at ?? ''}`}
              src={`/transcripts/diagrams/${folder.id}.html${sel.at ? `#d${sel.at}` : ''}`}
              title={`Commutative diagrams of folder ${folder.id}`}
              className="mt-3 h-[40rem] w-full rounded-[var(--radius-card)] border border-ink-200 bg-white"
            />
          </section>
        </div>

        <section className="mt-12">
          <h2 className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">The largest</h2>
          <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
            By nodes and arrows together, as the transcription sets them. Choose one to open it in
            the gallery above.
          </p>
          <ul className="mt-3 grid gap-x-8 gap-y-1 text-[12.5px] sm:grid-cols-2">
            {largest.map(({ f, d, i }) => (
              <li key={`${f.id}-${i}`}>
                <button
                  type="button"
                  onClick={() => {
                    setSel({ id: f.id, at: i + 1 });
                    scrollTo({ top: 0, behavior: 'smooth' });
                  }}
                  className="text-left hover:text-brand-700"
                >
                  <span className="tabular font-semibold text-ink-900">n° {f.id}</span>{' '}
                  <span className="text-ink-500">
                    batch {d.batch}
                    {d.page ? `, p. ${d.page}` : ''} — {d.nodes} nodes, {d.arrows} arrows
                  </span>
                </button>
              </li>
            ))}
          </ul>
        </section>

        <p className="mt-12 max-w-[44em] text-[12px] leading-relaxed text-ink-400">
          Built on {DG.built} by <code>node scripts/diagrams.mjs</code> from the{' '}
          <code>tikzcd</code> environments of the transcriptions. A diagram the transcriber
          described in a note rather than drew is not counted, and none has been checked against
          the facsimile by a person: an arrow can be misread as easily as a word.
        </p>
      </main>

      <Footer />
    </>
  );
}
