import { useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import { BY_ID } from './content/catalogue.ts';
import indexRaw from './content/fonds-index.json';

/**
 * The index of the whole fonds: a name, a work of his, or a subject, and the
 * folders and batches where it occurs.
 *
 * Built by `npm run fonds-index` from what the site already checks — the
 * people's evidence, the citations the citation map counts, and the keywords
 * of the modernised readings — so the index makes no reading of its own and
 * cannot say more than those do. What it is not is said on the page, above
 * the entries, because an index read as complete is worse than none.
 */

interface Entry {
  term: string;
  sort: string;
  folders: { id: string; batches: number[]; extra: string[] }[];
}
interface Subject {
  term: string;
  keywords: { keyword: string; folders: string[] }[];
}
const IDX = indexRaw as unknown as {
  built: string;
  coverage: { folders: number; withKeywords: number };
  people: Entry[];
  works: Entry[];
  subjects: Subject[];
};

type Facet = 'people' | 'works' | 'subjects';
const FACETS: { id: Facet; label: string; count: number }[] = [
  { id: 'people', label: 'People', count: IDX.people.length },
  { id: 'works', label: 'His works cited', count: IDX.works.length },
  { id: 'subjects', label: 'Subjects', count: IDX.subjects.length },
];

const shortTitle = (id: string) =>
  (BY_ID.get(id)?.title ?? '').replace(/\s*:\s*notes manuscrites.*$/i, '').replace(/\s*:.*$/, '');
const fold = (s: string) => s.normalize('NFD').replace(/\p{M}/gu, '').toLowerCase();

function FolderRef({ id, batches, extra }: { id: string; batches: number[]; extra?: string[] }) {
  return (
    <li className="text-[12.5px] leading-relaxed text-ink-600">
      <a
        href={`/#${id}/${batches[0] ?? 1}`}
        className="tabular font-semibold text-ink-900 hover:text-brand-700"
        title={BY_ID.get(id)?.title}
      >
        n° {id}
      </a>{' '}
      <span className="text-ink-500">{shortTitle(id).slice(0, 48)}</span>
      {batches.length > 0 && (
        <span className="tabular text-ink-400">
          {' '}
          · batch{batches.length > 1 ? 'es' : ''}{' '}
          {batches.map((b, i) => (
            <span key={b}>
              {i > 0 && ', '}
              <a href={`/#${id}/${b}`} className="hover:text-brand-700">
                {b}
              </a>
            </span>
          ))}
        </span>
      )}
      {extra && extra.length > 0 && <span className="text-ink-400"> — {extra.slice(0, 8).join(', ')}{extra.length > 8 ? ', …' : ''}</span>}
    </li>
  );
}

function Entries({ list, letters }: { list: Entry[]; letters: boolean }) {
  const groups = useMemo(() => {
    if (!letters) return [['', list] as const];
    const m = new Map<string, Entry[]>();
    for (const e of list) {
      const L = fold(e.sort)[0]?.toUpperCase() ?? '#';
      m.set(L, [...(m.get(L) ?? []), e]);
    }
    return [...m];
  }, [list, letters]);

  return (
    <>
      {letters && (
        <p className="mt-4 flex flex-wrap gap-1 text-[12.5px]">
          {groups.map(([L]) => (
            <a key={L} href={`#letter-${L}`} className="tabular rounded px-1.5 py-0.5 text-ink-500 hover:bg-ink-100 hover:text-ink-900">
              {L}
            </a>
          ))}
        </p>
      )}
      {groups.map(([L, es]) => (
        <div key={L} id={L ? `letter-${L}` : undefined} className="scroll-mt-16">
          {L && <h3 className="mt-6 border-b border-ink-200 pb-1 text-[13px] font-bold text-ink-400">{L}</h3>}
          <ul className="mt-2 space-y-3">
            {es.map((e) => (
              <li key={e.term}>
                <p className="text-[14px] font-semibold text-ink-900">
                  {e.term}{' '}
                  <span className="tabular text-[12px] font-normal text-ink-400">
                    {e.folders.length} {e.folders.length === 1 ? 'folder' : 'folders'}
                  </span>
                </p>
                <ul className="mt-0.5 pl-4">
                  {e.folders.map((f) => (
                    <FolderRef key={f.id} {...f} />
                  ))}
                </ul>
              </li>
            ))}
          </ul>
        </div>
      ))}
    </>
  );
}

function Subjects({ list }: { list: Subject[] }) {
  return (
    <>
      <p className="mt-4 flex flex-wrap gap-x-3 gap-y-1 text-[12.5px]">
        {list.map((s, i) => (
          <a key={s.term} href={`#subject-${i}`} className="text-ink-500 hover:text-brand-700">
            {s.term}
          </a>
        ))}
      </p>
      {list.map((s, i) => {
        const other = s.term === 'Other subjects';
        const body = (
          <ul className="mt-2 space-y-1.5">
            {s.keywords.map((k) => (
              <li key={k.keyword} className="text-[13px] leading-relaxed text-ink-700">
                {k.keyword}{' '}
                <span className="tabular text-[12px] text-ink-400">
                  —{' '}
                  {k.folders.map((f, j) => (
                    <span key={f}>
                      {j > 0 && ', '}
                      <a href={`/#${f}/1`} className="hover:text-brand-700" title={BY_ID.get(f)?.title}>
                        {f}
                      </a>
                    </span>
                  ))}
                </span>
              </li>
            ))}
          </ul>
        );
        return (
          <section key={s.term} id={`subject-${i}`} className="mt-6 scroll-mt-16">
            <h3 className="border-b border-ink-200 pb-1 text-[14px] font-semibold text-ink-900">
              {s.term}{' '}
              <span className="tabular text-[12px] font-normal text-ink-400">{s.keywords.length} keywords</span>
            </h3>
            {other ? (
              <details className="mt-2">
                <summary className="cursor-pointer text-[12.5px] text-ink-500">
                  Keywords the thirty subjects do not place — shown on request
                </summary>
                {body}
              </details>
            ) : (
              body
            )}
          </section>
        );
      })}
    </>
  );
}

export function IndexPage() {
  const [facet, setFacet] = useState<Facet>(() => {
    const h = location.hash.slice(1);
    return h === 'works' || h === 'subjects' ? h : 'people';
  });
  const [query, setQuery] = useState('');
  const q = fold(query.trim());

  const choose = (f: Facet) => {
    setFacet(f);
    history.replaceState(null, '', `#${f}`);
  };

  const people = q ? IDX.people.filter((e) => fold(e.term).includes(q)) : IDX.people;
  const works = q ? IDX.works.filter((e) => fold(e.term).includes(q) || e.folders.some((f) => f.extra.some((x) => fold(x).includes(q)))) : IDX.works;
  const subjects = q
    ? IDX.subjects
        .map((s) => ({ ...s, keywords: fold(s.term).includes(q) ? s.keywords : s.keywords.filter((k) => fold(k.keyword).includes(q)) }))
        .filter((s) => s.keywords.length)
    : IDX.subjects;

  return (
    <>
      <Header path="/index/" />

      <main className="mx-auto max-w-4xl px-5 py-12">
        <header className="max-w-[44em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.14em] text-ink-400">Index</p>
          <h1 className="titre mt-2 text-[30px] leading-tight text-ink-900">
            Names, works and subjects, to the folder and the batch
          </h1>
          <p className="mt-4 text-[15.5px] leading-relaxed text-ink-600">
            A way into the {IDX.coverage.folders} folders begun so far for a reader who arrives with
            a name or a subject in mind. Every entry leads to the batch where it occurs, and the
            batch opens beside its facsimile.
          </p>
        </header>

        <details className="mt-6 max-w-[44em] rounded-[var(--radius-card)] border border-ink-200 bg-white px-4 py-3 text-[13px] leading-relaxed text-ink-600">
          <summary className="cursor-pointer font-semibold text-ink-800">What this index is, and is not</summary>
          <ul className="mt-2 list-disc space-y-1.5 pl-5">
            <li>
              <strong>People</strong> are those the folders hold a letter to or from, a text by, or an
              attribution to — « th. de Hodge », « d'après Deligne » — and not an object that merely
              bears a name, « groupe de Galois ». People who are not public figures are not named.
            </li>
            <li>
              <strong>His works cited</strong> are EGA, SGA and FGA where a leaf names a volume, the
              same citations the citation map counts. A reference by year alone, or by a numeral that
              could be an exposé, is not resolved and not listed.
            </li>
            <li>
              <strong>Subjects</strong> come from the keywords of the modernised readings, so only the{' '}
              {IDX.coverage.withKeywords} folders that have one carry subjects, and they are per
              folder, not per batch.
            </li>
            <li>
              It is not complete and cannot be: a folder not yet transcribed has no entries, and an
              unread word may hide a name.
            </li>
          </ul>
        </details>

        <div className="mt-6 flex flex-wrap items-center gap-2">
          {FACETS.map((f) => (
            <button
              key={f.id}
              type="button"
              onClick={() => choose(f.id)}
              aria-pressed={facet === f.id}
              className={`rounded-full border px-3 py-1 text-[13px] transition ${
                facet === f.id
                  ? 'border-ink-900 bg-ink-900 text-white'
                  : 'border-ink-200 text-ink-600 hover:bg-ink-100 hover:text-ink-900'
              }`}
            >
              {f.label} <span className="tabular opacity-70">{f.count}</span>
            </button>
          ))}
          <input
            type="search"
            value={query}
            onChange={(e) => setQuery(e.target.value)}
            placeholder="Filter…"
            className="ml-auto w-full max-w-[14rem] rounded-lg border border-ink-200 bg-white px-3 py-1.5 text-[13px] text-ink-900 placeholder:text-ink-400 focus:border-brand-500 focus:outline-none"
          />
        </div>

        {facet === 'people' && <Entries list={people} letters={!q} />}
        {facet === 'works' && (
          <>
            <p className="mt-4 max-w-[44em] text-[12.5px] text-ink-500">
              After each batch, the precise references where the leaf gives them — the exposé, the
              section, the number.
            </p>
            <Entries list={works} letters={false} />
          </>
        )}
        {facet === 'subjects' && <Subjects list={subjects} />}

        {((facet === 'people' && !people.length) ||
          (facet === 'works' && !works.length) ||
          (facet === 'subjects' && !subjects.length)) && (
          <p className="mt-6 text-[13px] text-ink-400">Nothing under « {query} » here.</p>
        )}

        <p className="mt-12 max-w-[44em] text-[12px] leading-relaxed text-ink-400">
          Built on {IDX.built} by <code>npm run fonds-index</code> from src/content/people-evidence.json,
          the citations in the batches and the keywords of the modernised readings.
        </p>
      </main>

      <Footer />
    </>
  );
}
