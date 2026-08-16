import { useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import { BOOKS } from './content/books.ts';
import editionsRaw from './content/editions.json';
import { COTES, GROUPS } from './content/catalogue.ts';
import {
  BATCH_SIZE,
  batchCount,
  editionUrl,
  evidence,
  folderTags,
  sourceUrl,
  useManifest,
} from './lib/batches.ts';
import type { PublishedEdition } from './lib/types.ts';

const EDITIONS = editionsRaw as PublishedEdition[];

/**
 * Which folders already have an edition, and which edition.
 *
 * Built once rather than searched per row: the archive page renders 178 rows,
 * and a linear scan inside each would be 178 × 9 comparisons for a lookup that
 * never changes.
 */
const EDITION_BY_COTE = new Map<string, PublishedEdition>();
for (const e of EDITIONS) for (const c of e.cotes) EDITION_BY_COTE.set(c, e);

const KIND_STYLE: Record<PublishedEdition['kind'], string> = {
  published: 'bg-relu-100 text-relu-700 border-relu-200',
  transcribed: 'bg-brand-100 text-brand-700 border-brand-200',
  partial: 'bg-encours-100 text-encours-700 border-encours-200',
};

const KIND_LABEL: Record<PublishedEdition['kind'], string> = {
  published: 'published',
  transcribed: 'transcribed',
  partial: 'partly edited',
};

/**
 * The whole fonds, in Grothendieck's own filing order.
 *
 * The four notebooks are ways in; this page is the thing itself. It exists so
 * that nobody has to take our groupings on trust: every folder the inventory
 * lists is here, in its group, with its dating and its page count, whether or
 * not this site has anything to say about it.
 *
 * The search box filters on title, shelfmark and date at once, because those
 * are the three handles one actually has — one remembers "the Tate letter",
 * or "folder 63", or "the one from 1965", and rarely which of the three it was.
 */
export function ArchivePage() {
  const [query, setQuery] = useState('');
  const manifest = useManifest();

  /**
   * How far each folder has been taken, counted from the files.
   *
   * The archive page is where one comes to ask "what is left", so the answer
   * belongs on the row rather than one page away. Same two facts as the
   * notebook lists, same colours, so the two pages can be read against each
   * other without translating.
   */
  const workOn = useMemo(() => {
    const m = new Map<string, { transcribed: number; modernised: number; batches: number }>();
    for (const c of COTES) {
      const batches = batchCount(c.pages);
      const ks = Array.from({ length: batches }, (_, i) => i + 1);
      m.set(c.id, {
        batches,
        transcribed: ks.filter((k) => evidence(manifest, c.id, k).transcribed).length,
        modernised: ks.filter((k) => evidence(manifest, c.id, k).modernised).length,
      });
    }
    return m;
  }, [manifest]);

  const started = [...workOn.values()].filter((w) => w.transcribed > 0).length;

  const inBook = useMemo(() => {
    // Title for the badge, path for the way back in: a folder that has a
    // modernised reading gets a link straight to its notebook page.
    const m = new Map<string, { title: string; path: string }>();
    for (const b of BOOKS)
      for (const s of b.sections) for (const id of s.cotes) m.set(id, { title: b.title, path: b.path });
    return m;
  }, []);

  const needle = query.trim().toLowerCase();
  const matches = (id: string) => {
    if (!needle) return true;
    const c = COTES.find((x) => x.id === id);
    if (!c) return false;
    // Tags too: a reader who remembers "Isbell duality" and not a shelfmark
    // has exactly the handle the modernised readings filed themselves under.
    return `${c.id} ${c.title} ${c.date} ${folderTags(manifest, id).join(' ')}`
      .toLowerCase()
      .includes(needle);
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
            {started > 0 && (
              <span className="text-brand-700"> · {started} begun</span>
            )}
          </p>
        </div>

        {/* Two washes on the rows below, and neither is guessable from the
            colour alone — so they are named once, here, rather than left to
            a tooltip nobody hovers. */}
        <ul className="mt-3 flex flex-wrap items-center gap-x-5 gap-y-1.5 text-[12px] text-ink-500">
          <li className="flex items-center gap-1.5">
            <span
              aria-hidden="true"
              className="inline-block h-3.5 w-6 rounded-sm border-l-[3px] border-l-brand-400 bg-brand-50"
            />
            transcribed here
          </li>
          <li className="flex items-center gap-1.5">
            <span
              aria-hidden="true"
              className="inline-block h-3.5 w-6 rounded-sm border-l-[3px] border-l-relu-500 bg-relu-50"
            />
            edited by the mathematical community
          </li>
        </ul>

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
                const edition = EDITION_BY_COTE.get(id);
                const work = workOn.get(id);
                const begun = Boolean(work && work.transcribed > 0);
                return (
                  <li
                    key={id}
                    /* Two independent facts, two independent marks, because a
                       folder can carry both and someone scanning 178 rows for
                       "what is left" needs the answer in peripheral vision,
                       without reading a word. The green rule is a scholarly
                       edition someone else made; the ink-blue wash is our own
                       transcription. Rule and wash rather than two rules: they
                       compose on a row that has both. */
                    className={`flex flex-wrap items-baseline gap-x-3 gap-y-1 py-2.5 pr-4 ${
                      edition
                        ? 'border-l-[3px] border-l-relu-500 pl-[13px]'
                        : begun
                          ? 'border-l-[3px] border-l-brand-400 pl-[13px]'
                          : 'pl-4'
                    } ${begun ? 'bg-brand-50/70' : edition ? 'bg-relu-50/40' : ''}`}
                  >
                    <span className="tabular w-24 shrink-0 text-[12px] font-semibold text-ink-700">
                      n° {c.id}
                    </span>
                    <span className="min-w-0 flex-1 text-[13.5px] leading-snug text-ink-800">
                      {c.title}
                      {belongs && (
                        <span className="ml-2 rounded-full bg-brand-50 px-1.5 py-0.5 text-[10px] font-semibold uppercase tracking-wide text-brand-700">
                          {belongs.title}
                        </span>
                      )}
                      {/* Both chips are the way back in. A chip that states a
                          folder has been transcribed, and cannot be clicked to
                          read the transcription, makes the reader hunt for
                          something the page already knows the address of.
                          Where the folder sits in one of the books, the link
                          goes to the notebook — facsimile beside text, the
                          reading this site is for — and names the edition in
                          the fragment so the toggle arrives already on the
                          right tab. The 100-odd folders outside every book have
                          no notebook page, and fall back to the standalone
                          reading view the renderer writes for each edition. */}
                      {work && work.transcribed > 0 && (
                        <a
                          href={
                            belongs
                              ? `${belongs.path}#${id}/1/fr`
                              : editionUrl(manifest, id, 1, 'fr', 'html')
                          }
                          title={`${work.transcribed} of ${work.batches} batches transcribed — open the transcription, batch 1`}
                          className="ml-2 whitespace-nowrap rounded-full bg-relu-100 px-1.5 py-0.5 text-[10px] font-semibold uppercase tracking-wide text-relu-700 transition hover:bg-relu-200"
                        >
                          {work.transcribed === work.batches
                            ? 'transcribed ↗'
                            : `${work.transcribed}/${work.batches} transcribed ↗`}
                        </a>
                      )}
                      {work && work.modernised > 0 && (
                        <a
                          href={
                            belongs
                              ? `${belongs.path}#${id}/1/modern`
                              : editionUrl(manifest, id, 1, 'modern', 'html')
                          }
                          title={`${work.modernised} of ${work.batches} batches modernised — open the reading, batch 1. Read again by machine, not by a person`}
                          className="ml-1.5 whitespace-nowrap rounded-full bg-brand-100 px-1.5 py-0.5 text-[10px] font-semibold uppercase tracking-wide text-brand-700 transition hover:bg-brand-200"
                        >
                          {work.modernised === work.batches
                            ? 'modernised ↗'
                            : `${work.modernised}/${work.batches} modernised ↗`}
                        </a>
                      )}
                      {folderTags(manifest, id).map((t) => (
                        <span
                          key={t}
                          title="modern vocabulary, from the modernised reading's own keywords"
                          /* Case is left as the keywords line wrote it. Isbell,
                             Picard, Lawvere, Kan and Cauchy are people, and a
                             uniform lowercase chip renames them. */
                          className="ml-1.5 whitespace-nowrap rounded-full border border-ink-200 bg-white px-1.5 py-0.5 text-[10px] font-medium tracking-wide text-ink-500"
                        >
                          {t}
                        </span>
                      ))}
                      {edition && (
                        <a
                          href={edition.url}
                          target="_blank"
                          rel="noopener noreferrer"
                          title={`${edition.title} — ${edition.editors}, ${edition.year}. ${edition.note}`}
                          className={`ml-2 inline-block rounded-full border px-1.5 py-0.5 text-[10px] font-semibold uppercase tracking-wide transition hover:brightness-95 ${KIND_STYLE[edition.kind]}`}
                        >
                          {KIND_LABEL[edition.kind]} ↗
                          {edition.mapping === 'likely' && (
                            <span title="shelfmark correspondence is ours, not the editors'"> ?</span>
                          )}
                        </a>
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

        <ExistingEditions />

        <section className="card mt-12 max-w-[52em] px-5 py-4">
          <h2 className="titre text-[17px] text-ink-900">Mirroring anything here</h2>
          <p className="mt-2 text-[13.5px] leading-relaxed text-ink-600">
            Any folder can be pulled and cut into {BATCH_SIZE}-page batches, whether or not it
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

/**
 * What the mathematical community has already edited.
 *
 * Worth its own section for a practical reason: the most useful thing to know
 * before transcribing a folder is whether someone has already done it, and
 * done it better. Two thousand pages of Dérivateurs were transcribed into
 * LaTeX by Matthias Künzer; redoing that by machine would be a waste of
 * everyone's time, and the transcription here should defer to it.
 *
 * The awkward part is stated rather than smoothed over. Montpellier numbers
 * folders, the editions name works, and nobody has reconciled the two — not
 * one of these editors publishes a shelfmark. So the folder correspondence is
 * ours, and each entry says how far it can be trusted. Where it cannot be
 * established at all, the entry says that too instead of guessing, because a
 * guess here is exactly the kind of thing that gets cited later as fact.
 */
function ExistingEditions() {
  const mapped = EDITIONS.filter((e) => e.cotes.length > 0);
  const unmapped = EDITIONS.filter((e) => e.cotes.length === 0);

  return (
    <section className="mt-14">
      <h2 className="titre text-[24px] text-ink-900">Already edited</h2>
      <p className="mt-2 max-w-[48em] text-[14px] leading-relaxed text-ink-600">
        Parts of the fonds have been transcribed or published by mathematicians, in some cases at
        enormous length. Those folders are marked in the list above with a green rule. Before
        transcribing anything, look here first — where a scholarly edition exists it is better
        than anything produced here, and should be used instead.
      </p>

      <ul className="mt-6 space-y-3">
        {mapped.map((e) => (
          <li key={e.id} className="card border-l-4 border-l-relu-500 px-5 py-4">
            <div className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
              <h3 className="titre text-[17px] text-ink-900">
                <a
                  href={e.url}
                  target="_blank"
                  rel="noopener noreferrer"
                  className="underline decoration-ink-300 underline-offset-2 hover:text-brand-700 hover:decoration-brand-400"
                >
                  {e.title} ↗
                </a>
              </h3>
              <span
                className={`rounded-full border px-2 py-0.5 text-[10px] font-semibold uppercase tracking-wide ${KIND_STYLE[e.kind]}`}
              >
                {KIND_LABEL[e.kind]}
              </span>
              <span className="tabular ml-auto text-[12px] text-ink-500">
                folders {e.cotes.join(', ')}
                {e.mapping === 'likely' && (
                  <span className="ml-1 text-encours-700" title="Correspondence established by us, not by the editors">
                    (our reading)
                  </span>
                )}
              </span>
            </div>
            <p className="mt-1 text-[13px] text-ink-600">
              {e.editors} · {e.year} · <span className="italic">{e.venue}</span>
            </p>
            <p className="mt-2 max-w-[46em] text-[13px] leading-relaxed text-ink-500">{e.note}</p>
          </li>
        ))}
      </ul>

      <h3 className="titre mt-8 text-[17px] text-ink-900">Editions we cannot place</h3>
      <p className="mt-1.5 max-w-[48em] text-[13.5px] leading-relaxed text-ink-600">
        These exist, and relate to material in the fonds, but no source gives a shelfmark and the
        titles are not close enough to guess from. Listed so that nobody transcribes a folder
        these already cover without knowing they might.
      </p>
      <ul className="mt-3 space-y-2">
        {unmapped.map((e) => (
          <li key={e.id} className="card border-l-4 border-l-ink-300 px-5 py-3">
            <a
              href={e.url}
              target="_blank"
              rel="noopener noreferrer"
              className="text-[14px] font-medium text-ink-900 underline decoration-ink-300 underline-offset-2 hover:text-brand-700"
            >
              {e.title} ↗
            </a>
            <p className="mt-0.5 text-[12.5px] text-ink-500">
              {e.editors}
              {e.year !== '—' && ` · ${e.year}`} · <span className="italic">{e.venue}</span>
            </p>
            <p className="mt-1.5 max-w-[46em] text-[12.5px] leading-relaxed text-ink-500">{e.note}</p>
          </li>
        ))}
      </ul>

      <p className="mt-6 max-w-[48em] text-[12.5px] leading-relaxed text-ink-400">
        Compiled from the{' '}
        <a href="https://csg.igrothendieck.org/transcriptions/" target="_blank" rel="noopener noreferrer" className="underline underline-offset-2 hover:text-brand-600">
          Centre for Grothendieckian Studies transcription list
        </a>
        , the{' '}
        <a href="https://webusers.imj-prg.fr/~leila.schneps/grothendieckcircle/unpubtexts.php" target="_blank" rel="noopener noreferrer" className="underline underline-offset-2 hover:text-brand-600">
          Grothendieck Circle
        </a>{' '}
        and{' '}
        <a href="https://webusers.imj-prg.fr/~georges.maltsiniotis/ps.html" target="_blank" rel="noopener noreferrer" className="underline underline-offset-2 hover:text-brand-600">
          Georges Maltsiniotis' pages
        </a>
        . Almost certainly incomplete, and not a substitute for asking the editors.
      </p>
    </section>
  );
}
