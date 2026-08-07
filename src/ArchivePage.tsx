import { useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import { BOOKS } from './content/books.ts';
import { COTES, GROUPS } from './content/catalogue.ts';
import { BATCH_SIZE, batchCount, sourceUrl } from './lib/batches.ts';

/**
 * The whole fonds, in Grothendieck's own filing order.
 *
 * The four notebooks are ways in; this page is the thing itself. It exists so
 * that nobody has to take our groupings on trust: every folder the inventory
 * lists is here, in its group, with its dating and its leaf count, whether or
 * not this site has anything to say about it.
 *
 * The search box filters on title, shelfmark and date at once, because those
 * are the three handles one actually has — one remembers "the Tate letter",
 * or "folder 63", or "the one from 1965", and rarely which of the three it was.
 */
export function ArchivePage() {
  const [query, setQuery] = useState('');

  const inBook = useMemo(() => {
    const m = new Map<string, string>();
    for (const b of BOOKS) for (const s of b.sections) for (const id of s.cotes) m.set(id, b.title);
    return m;
  }, []);

  const needle = query.trim().toLowerCase();
  const matches = (id: string) => {
    if (!needle) return true;
    const c = COTES.find((x) => x.id === id);
    if (!c) return false;
    return `${c.id} ${c.title} ${c.date}`.toLowerCase().includes(needle);
  };

  const visible = GROUPS.map((g) => ({ ...g, cotes: g.cotes.filter(matches) })).filter(
    (g) => g.cotes.length > 0,
  );
  const shown = visible.reduce((s, g) => s + g.cotes.length, 0);

  return (
    <>
      <Header path="/archive/" />

      <main className="mx-auto max-w-6xl px-5 py-10">
        <header className="max-w-[48em]">
          <h1 className="titre text-[34px] leading-tight text-ink-900">The whole fonds</h1>
          <p className="mt-3 text-[15.5px] leading-relaxed text-ink-700">
            All {COTES.length} folders in open access, in the twenty-two groups the archivists
            recorded, in Grothendieck's filing order. Titles in [brackets] were supplied by the
            archivists; the rest are his, pencilled on the folder. Datings outside correspondence
            are nearly all inferred, most often from a verso.
          </p>
        </header>

        <div className="mt-6 flex flex-wrap items-center gap-3">
          <input
            type="search"
            value={query}
            onChange={(e) => setQuery(e.target.value)}
            placeholder="Search a title, a shelfmark, a year…"
            className="w-full max-w-md rounded-lg border border-ink-200 bg-white px-3 py-2 text-[14px] text-ink-900 placeholder:text-ink-400 focus:border-brand-500 focus:outline-none"
          />
          <p className="tabular text-[12.5px] text-ink-500">
            {shown} of {COTES.length} folders
          </p>
        </div>

        {visible.map((g) => (
          <section key={g.id} className="mt-9">
            <h2 className="titre text-[19px] text-ink-900">{g.title}</h2>
            <p className="tabular mt-0.5 text-[12px] text-ink-500">
              folders {g.id.replace(/-/g, ' to ')} {g.date && `· ${g.date}`}
            </p>
            <ul className="mt-3 divide-y divide-ink-100 overflow-hidden rounded-[var(--radius-card)] border border-ink-200 bg-white">
              {g.cotes.map((id) => {
                const c = COTES.find((x) => x.id === id)!;
                const belongs = inBook.get(id);
                return (
                  <li key={id} className="flex flex-wrap items-baseline gap-x-3 gap-y-1 px-4 py-2.5">
                    <span className="tabular w-24 shrink-0 text-[12px] font-semibold text-ink-700">
                      n° {c.id}
                    </span>
                    <span className="min-w-0 flex-1 text-[13.5px] leading-snug text-ink-800">
                      {c.title}
                      {belongs && (
                        <span className="ml-2 rounded-full bg-brand-50 px-1.5 py-0.5 text-[10px] font-semibold uppercase tracking-wide text-brand-700">
                          {belongs}
                        </span>
                      )}
                    </span>
                    <span className="tabular shrink-0 text-[12px] text-ink-500">
                      {c.date || 's.d.'}
                    </span>
                    <span className="tabular w-28 shrink-0 text-right text-[12px] text-ink-500">
                      {c.pages} ll. · {batchCount(c.pages)} b.
                    </span>
                    <a
                      href={sourceUrl(c.id)}
                      target="_blank"
                      rel="noopener noreferrer"
                      title="The PDF at Montpellier (expired certificate: the browser will warn)"
                      className="shrink-0 text-[12px] font-medium text-brand-600 hover:text-brand-700"
                    >
                      PDF ↗
                    </a>
                  </li>
                );
              })}
            </ul>
          </section>
        ))}

        {!visible.length && (
          <p className="mt-10 text-[14px] text-ink-500">Nothing matches “{query}”.</p>
        )}

        <section className="card mt-12 max-w-[52em] px-5 py-4">
          <h2 className="titre text-[17px] text-ink-900">Mirroring anything here</h2>
          <p className="mt-2 text-[13.5px] leading-relaxed text-ink-600">
            Any folder can be pulled and cut into {BATCH_SIZE}-leaf batches, whether or not it
            belongs to one of the four notebooks:
          </p>
          <code className="mt-3 block rounded-lg border border-ink-200 bg-ink-50 px-3 py-2 font-mono text-[12.5px] text-ink-900">
            npm run archive -- 63 91 161-3
          </code>
        </section>
      </main>

      <Footer />
    </>
  );
}
