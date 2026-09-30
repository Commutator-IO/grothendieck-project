import { useEffect, useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import catalogueRaw from './content/quillen.json';

/**
 * Daniel Quillen's research notebooks, beside the Grothendieck fonds.
 *
 * The Clay Mathematics Institute scanned them from 2013 and serves one PDF per
 * notebook, filed by year. This page is their reading room: the Clay's own
 * file, framed from claymath.org — the server allows it, so unlike Montpellier
 * no relay is needed — and, beside it, the transcription pane the fonds has.
 *
 * No notebook is transcribed. When one is, it is shown only if the build was
 * made with RENDER_QUILLEN set: Quillen died in 2011, the notebooks are in
 * copyright, and nothing transcribed from them goes online before the Clay and
 * the family agree (#36). The facsimile needs no such switch — it is the
 * Clay's publication, not a copy.
 */

interface Notebook {
  id: string;
  group: string;
  filed?: string;
  label: string;
  url: string;
  bytes: number;
  pages: number | null;
}
const CATALOGUE = catalogueRaw as unknown as { built: string; source: string; notebooks: Notebook[] };
const NOTEBOOKS = CATALOGUE.notebooks;

const RENDER_TRANSCRIPTS = import.meta.env.VITE_RENDER_QUILLEN === 'true';

const YEARS = Array.from({ length: 2003 - 1968 + 1 }, (_, i) => String(1968 + i));
const GROUPS: { id: string; label: string }[] = [
  ...YEARS.map((y) => ({ id: y, label: y })),
  { id: 'lectures', label: 'Lecture notes' },
  { id: 'misc', label: 'Miscellaneous' },
];
const inGroup = (g: string) => NOTEBOOKS.filter((n) => n.group === g);
const COUNT = new Map(GROUPS.map((g) => [g.id, inGroup(g.id).length]));
const MAX = Math.max(...YEARS.map((y) => COUNT.get(y) ?? 0));
const totalGB = (NOTEBOOKS.reduce((s, n) => s + n.bytes, 0) / 1e9).toFixed(1);

const mb = (b: number) => `${Math.round(b / 1e6)} MB`;

/** The notebook the fragment names — `#1968/1968-1` — or the first of 1968. */
function fromHash(): Notebook {
  const id = decodeURIComponent(location.hash.slice(1));
  return NOTEBOOKS.find((n) => n.id === id) ?? inGroup('1968')[0] ?? NOTEBOOKS[0];
}

export function QuillenPage() {
  const [nb, setNb] = useState<Notebook>(fromHash);
  const [group, setGroup] = useState(nb.group);

  useEffect(() => {
    const onHash = () => {
      const n = fromHash();
      setNb(n);
      setGroup(n.group);
    };
    addEventListener('hashchange', onHash);
    return () => removeEventListener('hashchange', onHash);
  }, []);

  const open = (n: Notebook) => {
    history.replaceState(null, '', `#${n.id}`);
    setNb(n);
  };
  const list = useMemo(() => inGroup(group), [group]);

  return (
    <>
      <Header path="/quillen/" />

      <main className="mx-auto max-w-6xl px-5 py-12">
        <header className="max-w-[46em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.11em] text-brand-600">Quillen</p>
          <h1 className="titre mt-2 text-[34px] leading-[1.1] text-ink-900">
            Daniel Quillen's research notebooks, 1968–2003
          </h1>
          <p className="mt-4 text-[15px] leading-relaxed text-ink-600">
            The working notes of the other side of the exchanges the fonds records — Grothendieck's
            notes on Quillen's lectures of September 1968 (folders 162-5 and 111), and{' '}
            <em>À la poursuite des champs</em>, which began in 1983 as a letter to him. Quillen kept
            them as a diary, year by year. The Clay Mathematics Institute has scanned them since
            2013 and publishes them as {NOTEBOOKS.length} PDFs ({totalGB} GB); Glenys Luke and
            Graeme Segal are cataloguing them. Each notebook here is the Clay's own file, shown from
            claymath.org and not copied.
          </p>
        </header>

        <section className="mt-9" aria-labelledby="years">
          <h2 id="years" className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
            Notebooks by year
          </h2>
          <div className="mt-3 overflow-x-auto">
            <div className="flex min-w-[640px] items-end gap-[3px]" role="tablist" aria-label="Year">
              {YEARS.map((y) => {
                const k = COUNT.get(y) ?? 0;
                const on = y === group;
                return (
                  <button
                    key={y}
                    type="button"
                    role="tab"
                    aria-selected={on}
                    title={`${y}: ${k} notebook${k === 1 ? '' : 's'}`}
                    onClick={() => setGroup(y)}
                    className="group flex flex-1 flex-col items-center gap-1"
                  >
                    <span
                      className={`w-full rounded-t-[3px] transition ${on ? 'bg-brand-600' : 'bg-brand-200 group-hover:bg-brand-400'}`}
                      style={{ height: `${Math.max(3, (64 * k) / MAX)}px` }}
                    />
                    <span className={`tabular text-[10px] ${on ? 'font-semibold text-ink-900' : 'text-ink-400'}`}>
                      {y.slice(2)}
                    </span>
                  </button>
                );
              })}
            </div>
          </div>
          <div className="mt-3 flex flex-wrap gap-2 text-[12.5px]">
            {GROUPS.slice(YEARS.length).map((g) => (
              <button
                key={g.id}
                type="button"
                onClick={() => setGroup(g.id)}
                aria-pressed={g.id === group}
                className={`rounded-full border px-3 py-1 transition ${
                  g.id === group ? 'border-ink-900 bg-ink-900 text-white' : 'border-ink-200 text-ink-600 hover:bg-ink-50'
                }`}
              >
                {g.label} <span className="tabular opacity-70">{COUNT.get(g.id)}</span>
              </button>
            ))}
          </div>

          <p className="mt-5 text-[13px] text-ink-500">
            <span className="font-semibold text-ink-800">{GROUPS.find((g) => g.id === group)?.label}</span> ·{' '}
            {list.length} notebook{list.length === 1 ? '' : 's'}
          </p>
          <ul className="mt-2 flex flex-wrap gap-1.5">
            {list.map((n) => (
              <li key={n.id}>
                <button
                  type="button"
                  onClick={() => open(n)}
                  aria-current={n.id === nb.id ? 'true' : undefined}
                  title={`${n.label}${n.pages ? ` · ${n.pages} pages` : ''} · ${mb(n.bytes)}${n.filed ? ` · filed under ${n.filed}` : ''}`}
                  className={`tabular rounded-md border px-2.5 py-1 text-[12.5px] transition ${
                    n.id === nb.id
                      ? 'border-brand-600 bg-brand-50 font-semibold text-brand-800'
                      : 'border-ink-200 text-ink-700 hover:border-brand-300 hover:bg-brand-50/50'
                  }`}
                >
                  {n.label.replace(new RegExp(`^${n.group}-`), '')}
                </button>
              </li>
            ))}
          </ul>
        </section>

        <section className="mt-8 grid gap-4 lg:grid-cols-[minmax(0,5fr)_minmax(0,7fr)]" aria-label="Reading">
          <div className="card flex flex-col p-5">
            <p className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">Transcription</p>
            <p className="titre mt-2 text-[20px] text-ink-900">{nb.label}</p>
            <p className="mt-1 text-[12.5px] text-ink-500">
              {nb.pages ? `${nb.pages} pages · ` : ''}
              {mb(nb.bytes)}
              {nb.filed ? ` · filed by the Clay under ${nb.filed}` : ''}
            </p>
            <p className="mt-4 text-[14px] leading-relaxed text-ink-600">
              No notebook is transcribed yet. When one is, its reading will stand here, page by page
              beside the facsimile, as it does for the Grothendieck fonds
              {RENDER_TRANSCRIPTS ? '.' : ' — once the Clay Mathematics Institute and Quillen\'s family have agreed to it.'}
            </p>
            <p className="mt-3 text-[13px] leading-relaxed text-ink-500">
              Quillen died in 2011: the notebooks are in copyright, and the scans are the Clay's.
              This page stores none of them; the facsimile opposite is served by claymath.org.
            </p>
            <p className="mt-auto pt-5 text-[12.5px]">
              <a
                href={nb.url}
                target="_blank"
                rel="noopener noreferrer"
                className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
              >
                Open this notebook at the Clay ↗
              </a>
              <span className="mx-2 text-ink-300" aria-hidden="true">
                ·
              </span>
              <a
                href={CATALOGUE.source}
                target="_blank"
                rel="noopener noreferrer"
                className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
              >
                The collection ↗
              </a>
            </p>
          </div>

          <div className="card overflow-hidden">
            <iframe key={nb.url} src={nb.url} title={`Daniel Quillen, notebook ${nb.label} — Clay Mathematics Institute`} className="h-[78vh] w-full border-0 bg-white" />
            <p className="border-t border-ink-200 bg-ink-50 px-4 py-2.5 text-[12px] leading-relaxed text-ink-500">
              Facsimile: <strong className="font-semibold text-ink-700">Clay Mathematics Institute</strong>, served
              from claymath.org, not copied here.
            </p>
          </div>
        </section>

        <p className="mt-10 max-w-[46em] text-[12px] leading-relaxed text-ink-400">
          The list of notebooks is read from the Clay's file listing (src/content/quillen.json, {CATALOGUE.built});
          copies the Clay files under a second year are left out. Page counts are given for the years
          counted so far.
        </p>
      </main>

      <Footer collection="quillen" />
    </>
  );
}
