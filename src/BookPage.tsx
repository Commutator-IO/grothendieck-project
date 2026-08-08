import { useCallback, useEffect, useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import { Downloads } from './components/Downloads.tsx';
import { FacsimilePane, type OpenBatch } from './components/FacsimilePane.tsx';
import { TranscriptPane } from './components/TranscriptPane.tsx';
import { book, cotesOf } from './content/books.ts';
import { GROUPS } from './content/catalogue.ts';
import {
  BATCH_SIZE,
  batchCount,
  batchRange,
  transcript,
  useFacsimileProxy,
  useManifest,
} from './lib/batches.ts';
import {
  STATES,
  nextState,
  readProgress,
  shownState,
  stateOf,
  tally,
  writeProgress,
  type Progress,
  type State,
} from './lib/progress.ts';
import type { BookKey, Cote, Edition } from './lib/types.ts';

/**
 * A book: its inventory, and — once a batch is open — a two-pane workspace.
 *
 * The page rests on one idea: what you click in the list is exactly what gets
 * transcribed. Each folder unfolds into twenty-page batches, and each batch is
 * at once a PDF file, a row of progress, and the argument to a command. There
 * is no "overview" separate from the working view, because a transcription of
 * sixteen thousand leaves does not survive a site where one must mentally
 * translate between three different divisions of the same thing.
 */
export function BookPage({ bookKey }: { bookKey: BookKey }) {
  const b = book(bookKey);
  const cotes = useMemo(() => cotesOf(b), [b]);
  const manifest = useManifest();
  // Null while the probe is in flight: assume the relay is there rather than
  // flashing the fallback panel for a moment on every open.
  const proxy = useFacsimileProxy();

  const [progress, setProgress] = useState<Progress>({});
  useEffect(() => setProgress(readProgress()), []);
  const update = (p: Progress) => {
    setProgress(p);
    writeProgress(p);
  };

  /**
   * The open batch lives in the URL fragment.
   *
   * `#19/3` names the third batch of folder 19. That is what one writes in a
   * notebook or pastes into a message when noting where to resume, and it is
   * what the transcription skill cites in the header of the file it produces.
   * State living only in React would not be shareable.
   */
  const [open, setOpen] = useState<{ cote: string; batch: number } | null>(null);
  useEffect(() => {
    const readHash = () => {
      const m = /^#([\w-]+)\/(\d+)$/.exec(location.hash);
      setOpen(m ? { cote: m[1], batch: Number(m[2]) } : null);
    };
    readHash();
    addEventListener('hashchange', readHash);
    return () => removeEventListener('hashchange', readHash);
  }, []);

  const goTo = (cote: string, batch: number) => {
    history.replaceState(null, '', `#${cote}/${batch}`);
    setOpen({ cote, batch });
    setLeaf(undefined);
  };
  const close = () => {
    history.replaceState(null, '', location.pathname);
    setOpen(null);
  };

  const [edition, setEdition] = useState<Edition>('fr');

  /**
   * The leaf being read, reported by the transcript and consumed by the
   * facsimile. It is held here rather than in either pane because it is the
   * one thing the two share — and holding it above them is what keeps the
   * dependency one-directional: the transcript never learns what the facsimile
   * is showing.
   */
  const [leaf, setLeaf] = useState<number | undefined>(undefined);
  const onLeaf = useCallback((n: number) => setLeaf(n), []);

  const openCote = open ? cotes.find((c) => c.id === open.cote) : undefined;
  const openBatch: OpenBatch | null =
    open && openCote
      ? {
          cote: openCote.id,
          title: openCote.title,
          date: openCote.date,
          batch: Math.min(open.batch, batchCount(openCote.pages)),
          pages: openCote.pages,
          page: leaf,
          available: proxy !== false,
        }
      : null;

  const allBatches = cotes.flatMap((c) =>
    Array.from({ length: batchCount(c.pages) }, (_, i) => {
      const { first, last } = batchRange(i + 1, c.pages);
      return { cote: c.id, batch: i + 1, pages: last - first + 1 };
    }),
  );
  const t = tally(progress, allBatches);
  // Observed, not declared — the count that answers "how much of this notebook
  // actually exists in LaTeX".
  const transcribedBatches = allBatches.filter(
    (x) => transcript(manifest, x.cote, x.batch).html.length > 0,
  ).length;
  const group = b.inventoryGroup ? GROUPS.find((g) => g.id === b.inventoryGroup) : undefined;

  return (
    <>
      {/* The content shifts rather than sliding under the pane: reading a
          transcript half-hidden by the facsimile would defeat the purpose. The
          header is inside the shift too — left full-width, its navigation ran
          under the pane and broke mid-word.
          The shift is gated on `lg:` exactly as the pane itself is. Below that
          breakpoint the facsimile is not rendered at all — mobile PDF viewers
          cannot display a frame — and a page indented for a pane that is not
          there was left reading in a column two hundred pixels wide. */}
      <div
        className={`transition-[padding] duration-150 ${
          openBatch ? 'lg:pr-[var(--pane,0px)]' : ''
        }`}
      >
        <Header path={b.path} />

        <main className="mx-auto max-w-6xl px-5 py-10">
          {openBatch && openCote ? (
            <Workspace
              cote={openCote}
              batch={openBatch.batch}
              edition={edition}
              onEdition={setEdition}
              onLeaf={onLeaf}
              onClose={close}
              available={transcript(manifest, openCote.id, openBatch.batch)}
              state={shownState(
                progress,
                openCote.id,
                openBatch.batch,
                transcript(manifest, openCote.id, openBatch.batch).html.length > 0,
              )}
              onState={() =>
                update({
                  ...progress,
                  [`${openCote.id}#${openBatch.batch}`]: nextState(
                    stateOf(progress, openCote.id, openBatch.batch),
                  ),
                })
              }
            />
          ) : (
            <>
              <header className="max-w-[48em]">
                <p className="text-[11px] font-bold uppercase tracking-[0.11em] text-brand-600">
                  {b.period}
                </p>
                <h1 className="titre mt-2 text-[34px] leading-tight text-ink-900">{b.title}</h1>
                <p className="mt-3 text-[16px] leading-relaxed text-ink-700">{b.subtitle}</p>

                <p className="tabular mt-5 flex flex-wrap gap-x-5 gap-y-1 text-[13px] text-ink-500">
                  <span>
                    <strong className="font-semibold text-ink-800">{cotes.length}</strong> folders
                  </span>
                  <span>
                    <strong className="font-semibold text-ink-800">
                      {t.pagesTotal.toLocaleString('en-GB')}
                    </strong>{' '}
                    leaves
                  </span>
                  <span>
                    <strong className="font-semibold text-ink-800">{allBatches.length}</strong>{' '}
                    batches of {BATCH_SIZE}
                  </span>
                  <span title="Batches with a transcript, counted from the manifest">
                    <strong className="font-semibold text-relu-600">{transcribedBatches}</strong>{' '}
                    transcribed
                  </span>
                  <span title="Batches you have compared against the leaves — a declaration, not an observation">
                    <strong className="font-semibold text-ink-800">{t.byState.checked}</strong>{' '}
                    checked
                  </span>
                </p>
              </header>

              <Provenance book={b} group={group?.title} />

              {b.sections.map((s) => (
                <section key={s.title} className="mt-9">
                  <h2 className="titre text-[21px] text-ink-900">{s.title}</h2>
                  <p className="mt-1.5 max-w-[46em] text-[13.5px] leading-relaxed text-ink-600">
                    {s.intro}
                  </p>
                  <ul className="mt-4 space-y-2.5">
                    {s.cotes.map((id) => {
                      const cote = cotes.find((c) => c.id === id)!;
                      return (
                        <CoteCard
                          key={id}
                          cote={cote}
                          manifest={manifest}
                          progress={progress}
                          onOpen={goTo}
                          onState={(batch) =>
                            update({
                              ...progress,
                              [`${cote.id}#${batch}`]: nextState(
                                stateOf(progress, cote.id, batch),
                              ),
                            })
                          }
                        />
                      );
                    })}
                  </ul>
                </section>
              ))}

              <MirrorCommand book={b.key} />
            </>
          )}
        </main>

        <Footer />
      </div>

      {openBatch && (
        <FacsimilePane
          open={openBatch}
          onClose={close}
          onBatch={(n) => goTo(openBatch.cote, n)}
        />
      )}
    </>
  );
}

/** The two-pane workspace: transcript left, facsimile right. */
function Workspace({
  cote,
  batch,
  edition,
  onEdition,
  onLeaf,
  onClose,
  available,
  state,
  onState,
}: {
  cote: Cote;
  batch: number;
  edition: Edition;
  onEdition: (e: Edition) => void;
  onLeaf: (n: number) => void;
  onClose: () => void;
  available: ReturnType<typeof transcript>;
  state: State;
  onState: () => void;
}) {
  const label = STATES.find((s) => s.key === state)!;
  return (
    <>
      <div className="flex flex-wrap items-baseline gap-3">
        <button
          type="button"
          onClick={onClose}
          className="rounded-lg border border-ink-200 px-2.5 py-1 text-[12.5px] font-medium text-ink-600 transition hover:border-brand-500 hover:text-brand-700"
        >
          ← Inventory
        </button>
        <h1 className="titre min-w-0 flex-1 truncate text-[21px] text-ink-900" title={cote.title}>
          {cote.title}
        </h1>
        <button
          type="button"
          onClick={onState}
          title={`${label.label} — ${label.help} (click to change)`}
          className={`shrink-0 rounded-md px-2 py-1 text-[11px] font-semibold uppercase tracking-wide transition ${STATE_COLOURS[state]}`}
        >
          {label.label}
        </button>
      </div>

      <p className="tabular mt-1 text-[12.5px] text-ink-500">
        Cote n° {cote.id} · {cote.date || 's.d.'} · {cote.pages} leaves
      </p>

      <TranscriptPane
        cote={cote.id}
        batch={batch}
        pages={cote.pages}
        available={available}
        edition={edition}
        onEdition={onEdition}
        onLeaf={onLeaf}
      />

      <Downloads cote={cote.id} batch={batch} available={available} />

      <p className="mt-6 max-w-[46em] text-[12.5px] leading-relaxed text-ink-500">
        Scrolling the transcript turns the facsimile: whichever source leaf is marked highest in
        the reading area is the one shown on the right. Use ← and → to step between batches, and
        Escape to close the facsimile.
      </p>
    </>
  );
}

/**
 * Where this grouping comes from.
 *
 * Two of the four books reproduce an inventory group; the other two are ours.
 * Conflating the cases would make the site useless for serious work: someone
 * citing "the Cahier de Topos" must know they are citing a reading, not a
 * shelfmark.
 */
function Provenance({
  book: b,
  group,
}: {
  book: { inventoryGroup: string | null; rationale: string };
  group?: string;
}) {
  return (
    <div
      className={`card mt-7 max-w-[52em] px-5 py-4 border-l-4 ${
        b.inventoryGroup ? 'border-l-brand-400' : 'border-l-encours-500'
      }`}
    >
      <p className="text-[11px] font-bold uppercase tracking-[0.1em] text-ink-400">
        {b.inventoryGroup ? 'Grouping from the inventory' : 'Editorial grouping'}
      </p>
      {group && (
        <p className="mt-1 text-[13px] font-medium text-ink-800">
          Reproduces the group “{group}” (folders {b.inventoryGroup?.replace(/-/g, ' to ')}).
        </p>
      )}
      <p className="mt-2 text-[13.5px] leading-relaxed text-ink-600">{b.rationale}</p>
    </div>
  );
}

/** A folder, unfolded into twenty-page batches. */
function CoteCard({
  cote,
  manifest,
  progress,
  onOpen,
  onState,
}: {
  cote: Cote;
  manifest: ReturnType<typeof useManifest>;
  progress: Progress;
  onOpen: (cote: string, batch: number) => void;
  onState: (batch: number) => void;
}) {
  const count = batchCount(cote.pages);
  const [unfolded, setUnfolded] = useState(false);
  // Counted from the manifest rather than from what anyone has ticked: the
  // question "has this folder been transcribed?" has a factual answer, and it
  // should be legible without unfolding the batch list.
  const transcribed = Array.from({ length: count }, (_, i) => i + 1).filter(
    (k) => transcript(manifest, cote.id, k).html.length > 0,
  ).length;

  return (
    <li
      className={`card overflow-hidden ${
        transcribed ? 'border-l-4 border-l-relu-500' : ''
      }`}
    >
      <div className="flex items-start gap-3 px-4 py-3">
        <button
          type="button"
          onClick={() => setUnfolded(!unfolded)}
          aria-expanded={unfolded}
          className="mt-0.5 shrink-0 rounded-md border border-ink-200 px-1.5 py-0.5 text-[11px] text-ink-500 transition hover:border-brand-400 hover:text-brand-700"
        >
          {unfolded ? '▾' : '▸'}
        </button>
        <div className="min-w-0 flex-1">
          <p className="text-[15px] font-medium leading-snug text-ink-900">
            {cote.title}
            {transcribed > 0 && (
              <span
                title={
                  transcribed === count
                    ? 'Every batch of this folder has a transcript'
                    : `${transcribed} of ${count} batches transcribed`
                }
                className="ml-2 whitespace-nowrap rounded-full bg-relu-100 px-2 py-0.5 text-[10px] font-semibold uppercase tracking-wide text-relu-700"
              >
                {transcribed === count ? 'transcribed' : `${transcribed}/${count} transcribed`}
              </span>
            )}
          </p>
          <p className="tabular mt-1 flex flex-wrap gap-x-3 text-[12px] text-ink-500">
            <span className="font-semibold text-ink-700">Cote n° {cote.id}</span>
            <span>{cote.date || 's.d.'}</span>
            <span>{cote.pages} leaves</span>
            <span>
              {count} batch{count > 1 ? 'es' : ''}
            </span>
          </p>
        </div>
        <button
          type="button"
          onClick={() => onOpen(cote.id, 1)}
          className="mt-0.5 shrink-0 rounded-lg border border-ink-200 px-2.5 py-1 text-[12px] font-medium text-ink-600 transition hover:border-brand-500 hover:text-brand-700"
        >
          Open
        </button>
      </div>

      {unfolded && (
        <ol className="grid grid-cols-2 gap-px border-t border-ink-100 bg-ink-100 sm:grid-cols-3 lg:grid-cols-4">
          {Array.from({ length: count }, (_, i) => i + 1).map((k) => (
            <BatchRow
              key={k}
              cote={cote}
              batch={k}
              state={shownState(
                progress,
                cote.id,
                k,
                transcript(manifest, cote.id, k).html.length > 0,
              )}
              onOpen={() => onOpen(cote.id, k)}
              onState={() => onState(k)}
            />
          ))}
        </ol>
      )}
    </li>
  );
}

const STATE_COLOURS: Record<State, string> = {
  todo: 'bg-ink-200 text-ink-500',
  running: 'bg-encours-200 text-encours-700',
  drafted: 'bg-brand-200 text-brand-700',
  checked: 'bg-relu-200 text-relu-700',
  skipped: 'bg-alerte-100 text-alerte-700',
};

function BatchRow({
  cote,
  batch,
  state,
  onOpen,
  onState,
}: {
  cote: Cote;
  batch: number;
  state: State;
  onOpen: () => void;
  onState: () => void;
}) {
  const { first, last } = batchRange(batch, cote.pages);
  const label = STATES.find((s) => s.key === state)!;
  return (
    <li className="flex items-center gap-2 bg-white px-3 py-1.5">
      <button
        type="button"
        onClick={onOpen}
        className="tabular min-w-0 flex-1 text-left text-[12.5px] text-ink-700 transition hover:text-brand-700"
      >
        <span className="font-medium">Batch {batch}</span>{' '}
        <span className="text-ink-400">
          ll. {first}–{last}
        </span>
      </button>
      <button
        type="button"
        onClick={onState}
        title={`${label.label} — ${label.help} (click to change)`}
        className={`shrink-0 rounded px-1.5 py-0.5 text-[10px] font-semibold uppercase tracking-wide transition ${STATE_COLOURS[state]}`}
      >
        {label.label}
      </button>
    </li>
  );
}

/**
 * Mirroring, which reading no longer requires.
 *
 * The panes stream Montpellier's own files, so nothing needs downloading to
 * read. A local copy is still worth having for transcription: handing a
 * twenty-leaf file to a transcriber beats handing it a 204 MB volume and a
 * page range, and it is reproducible months later even if the source moves.
 */
function MirrorCommand({ book: key }: { book: string }) {
  return (
    <section className="card mt-12 max-w-[52em] px-5 py-4">
      <h2 className="titre text-[17px] text-ink-900">Mirroring, for transcription</h2>
      <p className="mt-2 text-[13.5px] leading-relaxed text-ink-600">
        Not needed to read — the panes stream the originals from Montpellier. But transcription
        works from a local {BATCH_SIZE}-leaf file rather than a whole volume:
      </p>
      <code className="mt-3 block rounded-lg border border-ink-200 bg-ink-50 px-3 py-2 font-mono text-[12.5px] text-ink-900">
        npm run archive -- {key}
      </code>
      <p className="mt-2 text-[12.5px] leading-relaxed text-ink-500">
        Files land in <code className="font-mono">archives/</code>, which is git-ignored, and
        nothing from the fonds is ever versioned. To pull only a beginning:{' '}
        <code className="font-mono">npm run archive -- {key} --batches 1-3</code>.
      </p>
    </section>
  );
}
