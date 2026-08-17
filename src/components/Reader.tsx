import { useCallback, useEffect, useState } from 'react';
import { Downloads } from './Downloads.tsx';
import type { OpenBatch } from './FacsimilePane.tsx';
import { TranscriptPane } from './TranscriptPane.tsx';
import {
  availableFor,
  batchCount,
  servedByFolder,
  useFacsimileProxy,
  useManifest,
} from '../lib/batches.ts';
import { documentsFor } from '../content/books.ts';
import { STATES, type State } from '../lib/progress.ts';
import type { Cote, PaneView } from '../lib/types.ts';

/**
 * The two-pane reader, shared by the notebooks and the archive.
 *
 * It lived inside `BookPage` while only the four notebooks had one, and the
 * archive listed 178 folders it could not open — so the hundred-odd folders
 * outside every notebook had no way to be read beside their pages at all, and
 * the ones inside could only be reached by knowing which notebook they were
 * filed under. Extracting it is what lets the archive be a reading surface
 * rather than an index, and the important part is that it is the *same*
 * component: two readers would drift, and the one thing this view promises is
 * that the transcript and the facsimile stay in step.
 *
 * The state is here too, in `useReader`, because it is all one mechanism: which
 * batch is open, which edition, and which page the transcript last reported are
 * three facts the two panes share, and splitting them across two call sites is
 * how they get out of step.
 */

export const STATE_COLOURS: Record<State, string> = {
  todo: 'bg-ink-200 text-ink-500',
  running: 'bg-encours-200 text-encours-700',
  drafted: 'bg-brand-100 text-brand-700',
  reviewed: 'bg-brand-200 text-brand-800',
  checked: 'bg-relu-200 text-relu-700',
  skipped: 'bg-alerte-100 text-alerte-700',
};

/**
 * Everything the reader needs, driven by the URL fragment.
 *
 * `#19/3` names the third batch of folder 19 — what one writes in a notebook or
 * pastes into a message when noting where to resume, and what the transcription
 * skill cites in the header of the file it produces. State living only in React
 * would not be shareable.
 *
 * A third segment may name the edition — `#66/1/modern`. It is optional and no
 * link written here uses it, so the short form stays the one people copy; what
 * needs it is a link arriving from elsewhere, where saying "this folder has a
 * modernised reading" and landing the reader on the transcription would be a
 * broken promise.
 */
export function useReader(cotes: Cote[]) {
  const manifest = useManifest();
  // Probed once, on the page, rather than when a batch opens: by the time a
  // reader has picked one the answer is usually in, and a relay that had to be
  // woken has been waking all the while.
  const proxy = useFacsimileProxy();

  const [open, setOpen] = useState<{ cote: string; batch: number } | null>(null);
  const [edition, setEdition] = useState<PaneView>('fr');
  const [page, setPage] = useState<number | undefined>(undefined);
  const onPage = useCallback((n: number) => setPage(n), []);

  useEffect(() => {
    const readHash = () => {
      const h = /^#([\w-]+)\/(\d+)(?:\/(fr|modern|community))?$/.exec(location.hash);
      setOpen(h ? { cote: h[1], batch: Number(h[2]) } : null);
      // Only when the fragment says so: leaving it alone otherwise is what
      // keeps the toggle where the reader put it as they move between batches.
      if (h?.[3]) setEdition(h[3] as PaneView);
    };
    readHash();
    addEventListener('hashchange', readHash);
    return () => removeEventListener('hashchange', readHash);
  }, []);

  const goTo = useCallback((cote: string, batch: number, ed?: PaneView) => {
    history.replaceState(null, '', `#${cote}/${batch}${ed ? `/${ed}` : ''}`);
    setOpen({ cote, batch });
    if (ed) setEdition(ed);
    setPage(undefined);
  }, []);

  const close = useCallback(() => {
    history.replaceState(null, '', location.pathname);
    setOpen(null);
  }, []);

  /**
   * Open on whatever this folder actually has.
   *
   * `fr` is the right default for a folder this project has transcribed, and
   * the wrong one for the folders it has not: 157-1 opened on an empty
   * Transcription tab reading "no transcription yet", while the Dérivateurs
   * chapters covering those very pages sat behind a tab the reader had no
   * reason to press. The pane was telling the truth and giving the wrong
   * impression, which is the worst combination available.
   *
   * So when neither of our editions exists for the batch in view and somebody
   * else's does, the community one is what opens. Only ever as a default —
   * an explicit `/fr` in the fragment, or a press on the tab, is left alone,
   * which is why this watches the batch rather than the edition.
   */
  useEffect(() => {
    if (!open) return;
    if (/^#[\w-]+\/\d+\/(fr|modern|community)$/.test(location.hash)) return;
    const mine = availableFor(manifest, open.cote, open.batch);
    if (mine.html.length === 0 && documentsFor(open.cote).length > 0) setEdition('community');
    else setEdition('fr');
  }, [open, manifest]);

  const openCote = open ? cotes.find((c) => c.id === open.cote) : undefined;
  const openBatch: OpenBatch | null =
    open && openCote
      ? {
          cote: openCote.id,
          title: openCote.title,
          date: openCote.date,
          batch: Math.min(open.batch, batchCount(openCote.pages)),
          pages: openCote.pages,
          page,
          // The modernised reading is one document for the folder, so its page
          // markers may name any page of it, not only this batch's twenty.
          // A community edition is somebody else's PDF on somebody else's
          // server: it carries no page markers this page can read, so it never
          // widens the facsimile's range.
          wholeFolder:
            edition === 'community'
              ? false
              : servedByFolder(manifest, openCote.id, edition, 'html'),
          relay: proxy,
        }
      : null;

  return { manifest, openCote, openBatch, edition, setEdition, page, onPage, goTo, close };
}

/** The left-hand half: heading, downloads, transcript. */
export function Reader({
  cote,
  batch,
  edition,
  onEdition,
  onPage,
  page,
  onClose,
  backLabel,
  state,
}: {
  cote: Cote;
  batch: number;
  edition: PaneView;
  onEdition: (e: PaneView) => void;
  onPage: (n: number) => void;
  /** The page currently in view, so a report arrives already located. */
  page?: number;
  onClose: () => void;
  /** What the reader came back to — an inventory here, the whole fonds there. */
  backLabel: string;
  state: State;
}) {
  const manifest = useManifest();
  const available = availableFor(manifest, cote.id, batch);
  const label = STATES.find((s) => s.key === state)!;
  return (
    <>
      <div className="flex flex-wrap items-baseline gap-3">
        <button
          type="button"
          onClick={onClose}
          className="rounded-lg border border-ink-200 px-2.5 py-1 text-[12.5px] font-medium text-ink-600 transition hover:border-brand-500 hover:text-brand-700"
        >
          ← {backLabel}
        </button>
        <h1 className="titre min-w-0 flex-1 truncate text-[21px] text-ink-900" title={cote.title}>
          {cote.title}
        </h1>
        <span
          title={label.help}
          className={`shrink-0 rounded-md px-2 py-1 text-[11px] font-semibold uppercase tracking-wide ${STATE_COLOURS[state]}`}
        >
          {label.label}
        </span>
      </div>

      <p className="tabular mt-1 text-[12.5px] text-ink-500">
        Cote n° {cote.id} · {cote.date || 's.d.'} · {cote.pages} pages
      </p>

      {/* Above the reading pane, not below it. The pane is as tall as the
          transcript, so anything after it sits a screen or more down the page —
          a row of links nobody scrolls past the whole document to find. */}
      <Downloads cote={cote.id} batch={batch} page={page} available={available} />

      <TranscriptPane
        cote={cote.id}
        batch={batch}
        pages={cote.pages}
        available={available}
        edition={edition}
        onEdition={onEdition}
        onPage={onPage}
      />

      <p className="mt-4 max-w-[46em] text-[12.5px] leading-relaxed text-ink-500">
        Scrolling the transcript turns the facsimile: whichever source page is marked highest in
        the reading area is the one shown on the right. Use ← and → to step between batches, and
        Escape to close the facsimile.
      </p>
    </>
  );
}
