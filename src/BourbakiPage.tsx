import { useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import catalogueRaw from './content/bourbaki.json';
import skimRaw from './content/bourbaki-skim.json';

/**
 * The Bourbaki archive, listed beside the fonds.
 *
 * The Archives Henri Poincaré publish the Association des Collaborateurs de
 * Nicolas Bourbaki's papers — rédactions, congress reports, circulars, mostly
 * typescripts — at archives-bourbaki.ahp-numerique.fr. This page is their
 * catalogue only (scripts/bourbaki-catalogue.mjs reads the public API); each
 * document opens on the archive's own page.
 *
 * A red ring marks a document that meets the Grothendieck fonds, and says how:
 * he wrote it, he was present, the archive names him, or a leaf of the fonds
 * carries its rédaction number — he wrote his notes on its back, or a
 * transcription names it. Only that: a shared subject is not a link.
 */

interface Why {
  kind: 'author' | 'present' | 'named' | 'fonds';
  text: string;
  folder?: string;
}
interface Doc {
  id: number;
  type: string;
  title: string;
  number: number | null;
  date: string | null;
  creators: string[];
  identifier: string | null;
  form: string | null;
  book: string | null;
  pages: string | null;
  collection: string | null;
  summary: string;
  url: string;
  grothendieck: Why[];
}
const CATALOGUE = catalogueRaw as unknown as { built: string; source: string; records: Doc[] };
const DOCS = CATALOGUE.records;

/** The skim of #50, priority 3: where he appears in a document, in our words. */
interface Skim {
  present: boolean | null;
  passages: { pages: string; kind: string; context: string }[];
}
const SKIM = (skimRaw as unknown as { built: string; skimmed: Record<string, Skim> }).skimmed;

const TYPES: { id: string; label: string }[] = [
  { id: 'Rédactions', label: 'Rédactions' },
  { id: 'Circulaires, convocations et comptes rendus', label: 'Congresses and circulars' },
  { id: 'Documents anecdotiques', label: 'Anecdotal documents' },
  { id: "Nomenclature et mode d'emploi (rédactions)", label: 'Nomenclature' },
];
const KIND_LABEL: Record<Why['kind'], string> = {
  author: 'by Grothendieck',
  present: 'Grothendieck present',
  named: 'names Grothendieck',
  fonds: 'in the fonds',
};

const fold = (s: string) => s.normalize('NFD').replace(/[̀-ͯ]/g, '').toLowerCase();

export function BourbakiPage() {
  const [type, setType] = useState<string>('all');
  const [onlyHits, setOnlyHits] = useState(false);
  const [q, setQ] = useState('');

  const hits = DOCS.filter((d) => d.grothendieck.length).length;
  const shown = useMemo(() => {
    const needle = fold(q.trim());
    return DOCS.filter(
      (d) =>
        (type === 'all' || d.type === type) &&
        (!onlyHits || d.grothendieck.length > 0) &&
        (!needle || fold(`${d.title} ${d.creators.join(' ')} ${d.summary} ${d.date ?? ''} ${d.identifier ?? ''}`).includes(needle)),
    );
  }, [type, onlyHits, q]);

  return (
    <>
      <Header path="/bourbaki/" />
      <main className="mx-auto max-w-6xl px-5 py-12">
        <header className="max-w-[46em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.11em] text-brand-600">Bourbaki</p>
          <h1 className="titre mt-2 text-[34px] leading-[1.1] text-ink-900">The Bourbaki archive</h1>
          <p className="mt-4 text-[15px] leading-relaxed text-ink-600">
            The papers of the Association des Collaborateurs de Nicolas Bourbaki, as the Archives Henri
            Poincaré publish them: {DOCS.length} documents, most of them typescripts — the numbered
            rédactions of the treatise, the reports of the congresses, the circulars. Grothendieck's name
            is in the congress reports from 1950 to 1965; he wrote rédactions of his own, and he wrote
            notes on the backs of others', which is how some of them reached the fonds.
          </p>
          <p className="mt-3 text-[14px] leading-relaxed text-ink-600">
            <span className="mr-1 inline-block h-3 w-3 rounded-sm align-[-1px] ring-2 ring-alerte-500" aria-hidden="true" />
            A red ring marks the {hits} documents that meet the fonds, and says how. Each title opens the
            document on the archive's site. For {Object.keys(SKIM).length} of them, a skim of the facsimile
            gives the pages where he appears, in a few words of ours (#50; machine-read, unchecked).
          </p>
        </header>

        <div className="mt-8 flex flex-wrap items-center gap-2">
          <button
            type="button"
            onClick={() => setType('all')}
            aria-pressed={type === 'all'}
            className="rounded-lg border border-ink-200 px-3 py-1 text-[12.5px] text-ink-700 aria-pressed:border-brand-500 aria-pressed:bg-brand-50 aria-pressed:font-semibold"
          >
            All · {DOCS.length}
          </button>
          {TYPES.map((t) => (
            <button
              key={t.id}
              type="button"
              onClick={() => setType(t.id)}
              aria-pressed={type === t.id}
              className="rounded-lg border border-ink-200 px-3 py-1 text-[12.5px] text-ink-700 aria-pressed:border-brand-500 aria-pressed:bg-brand-50 aria-pressed:font-semibold"
            >
              {t.label} · {DOCS.filter((d) => d.type === t.id).length}
            </button>
          ))}
          <label className="ml-2 flex items-center gap-1.5 text-[12.5px] text-ink-700">
            <input type="checkbox" checked={onlyHits} onChange={(e) => setOnlyHits(e.target.checked)} />
            Only those meeting the fonds
          </label>
          <input
            type="search"
            value={q}
            onChange={(e) => setQ(e.target.value)}
            placeholder="Search titles, authors, dates…"
            className="ml-auto w-full rounded-lg border border-ink-200 px-3 py-1.5 text-[13px] sm:w-72"
          />
        </div>

        <p className="tabular mt-3 text-[12px] text-ink-500">{shown.length} shown</p>

        <ul className="mt-3 grid gap-2">
          {shown.map((d) => {
            const hit = d.grothendieck.length > 0;
            return (
              <li
                key={d.id}
                className={`rounded-xl border bg-white px-4 py-3 ${hit ? 'border-alerte-200 ring-2 ring-alerte-500' : 'border-ink-200'}`}
              >
                <div className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
                  <a
                    href={d.url}
                    target="_blank"
                    rel="noreferrer"
                    className="min-w-0 flex-1 text-[14px] font-medium text-ink-900 hover:text-brand-700"
                  >
                    {d.title} <span className="text-ink-400">↗</span>
                  </a>
                  <span className="tabular shrink-0 text-[12px] text-ink-500">{d.date ?? 's.d.'}</span>
                </div>
                <p className="mt-1 text-[12px] text-ink-500">
                  {[d.creators.join(', '), d.form, d.pages ? `${d.pages} p.` : null, d.identifier].filter(Boolean).join(' · ')}
                </p>
                {hit && (
                  <ul className="mt-2 flex flex-wrap gap-1.5">
                    {d.grothendieck.map((w, i) => (
                      <li key={i} className="rounded-md bg-alerte-50 px-2 py-0.5 text-[11.5px] text-alerte-700">
                        <strong className="font-semibold">{KIND_LABEL[w.kind]}</strong> — {w.text}
                        {w.folder && (
                          <>
                            {' '}
                            <a href={`/#${w.folder}/1`} className="underline hover:text-alerte-900">
                              open folder {w.folder}
                            </a>
                          </>
                        )}
                      </li>
                    ))}
                  </ul>
                )}
                {SKIM[String(d.id)] && (
                  <details className="mt-2 text-[12.5px] text-ink-700">
                    <summary className="cursor-pointer text-ink-500 hover:text-brand-700">
                      Where he appears ({SKIM[String(d.id)].passages.length})
                      {SKIM[String(d.id)].present === true ? ' · present' : SKIM[String(d.id)].present === false ? ' · not present' : ''}
                    </summary>
                    <ul className="mt-1.5 grid gap-1 pl-1">
                      {SKIM[String(d.id)].passages.map((p, i) => (
                        <li key={i}>
                          <span className="tabular font-semibold text-ink-800">p. {p.pages}</span>{' '}
                          <span className="text-ink-400">({p.kind})</span> {p.context}
                        </li>
                      ))}
                    </ul>
                  </details>
                )}
              </li>
            );
          })}
        </ul>

        <p className="mt-8 text-[12px] text-ink-400">
          Catalogue read from {CATALOGUE.source} on {CATALOGUE.built}.
        </p>
      </main>
      <Footer collection="bourbaki" />
    </>
  );
}
