import { useEffect, useRef, useState } from 'react';
import {
  BATCH_SIZE,
  batchRange,
  folderTranscription,
  transcriptUrl,
  useManifest,
} from '../lib/batches.ts';
import type { Edition, TranscriptEntry } from '../lib/types.ts';

/**
 * The transcript, rendered from LaTeX, in the left pane.
 *
 * It is served as its own document in a frame rather than composed into this
 * page, and that is deliberate. The transcript wears the ar5iv stylesheet —
 * the one LaTeXML produces for arXiv articles, the same file the TIPE report
 * uses — which claims `:root`, `body` and a hundred generic element selectors.
 * Dropped into a Tailwind page it would fight everything; scoped by hand it
 * would no longer be the same stylesheet. A frame keeps it verbatim, which is
 * the point: what one reads on screen is typeset exactly as the compiled
 * article will be.
 *
 * The frame is same-origin, so the parent can still read its layout — which is
 * what drives the facsimile beside it.
 *
 * **It never scrolls itself.** A frame of fixed height inside a scrolling page
 * makes two scroll regions, one nested in the other, and no reader should have
 * to work out which one their wheel is about to move. So the frame is grown to
 * the exact height of its content and the page does all the scrolling: one
 * document, one scrollbar, the facsimile fixed beside it.
 */

export const EDITIONS: { key: Edition; label: string; help: string }[] = [
  { key: 'fr', label: 'Transcription', help: 'The pages as written.' },
  {
    key: 'modern',
    label: 'Modernised',
    help: 'An interpretation in current notation, opening with a summary of the batch.',
  },
];

export function TranscriptPane({
  cote,
  batch,
  pages,
  available,
  edition,
  onEdition,
  onPage,
}: {
  cote: string;
  batch: number;
  pages: number;
  available: TranscriptEntry;
  edition: Edition;
  onEdition: (e: Edition) => void;
  /** Called with the archive page currently at the top of the reading area. */
  onPage: (page: number) => void;
}) {
  const frame = useRef<HTMLIFrameElement>(null);
  const [height, setHeight] = useState(600);
  const { first, last } = batchRange(batch, pages);
  const present = available.html.includes(edition);
  const url = transcriptUrl(cote, batch, edition, 'html');
  // Folder-wide, not batch-wide: the modernised edition's precondition is that
  // every batch of the folder is transcribed, so an empty Modernised tab has to
  // report on the folder even though the reader is looking at one batch of it.
  const folder = folderTranscription(useManifest(), cote, pages);

  /**
   * The frame is grown to its content, so it never scrolls.
   *
   * Measured rather than guessed, and re-measured on every change: KaTeX
   * typesets after load and the commutative diagrams are laid out after that,
   * so the height at `load` is not the final one. A `ResizeObserver` on the
   * document element catches all of it, and the pane's own resize handle too.
   */
  useEffect(() => {
    if (!present) return;
    const el = frame.current;
    if (!el) return;

    let observer: ResizeObserver | undefined;
    const attachHeight = () => {
      const doc = el.contentDocument;
      if (!doc) return;
      const measure = () => setHeight(doc.documentElement.scrollHeight);
      measure();
      observer = new ResizeObserver(measure);
      observer.observe(doc.documentElement);
    };

    el.addEventListener('load', attachHeight);
    if (el.contentDocument?.readyState === 'complete') attachHeight();
    return () => {
      el.removeEventListener('load', attachHeight);
      observer?.disconnect();
    };
  }, [present, url]);

  /**
   * Scrolling the transcript turns the facsimile's pages.
   *
   * The transcript marks each source page with `data-page="47"`. Whichever
   * marker is highest in the reading area names the page being read, and the
   * facsimile follows. This is the whole reason the two panes are worth having
   * side by side: reading the transcription of page 47 while looking at page 41
   * is worse than useless, because the eye trusts what it is shown.
   *
   * Reading position, not intersection ratio: an `IntersectionObserver` fires
   * on entering and leaving, which on a long uninterrupted page of prose can
   * leave no marker "intersecting" at all. The topmost marker above the fold
   * is always defined, and is what a reader would themselves point at.
   *
   * The scroll being watched is the *page's*, since the frame no longer has
   * one of its own. A marker's rectangle is measured inside the frame and
   * shifted by the frame's own offset to land in page coordinates.
   */
  useEffect(() => {
    if (!present) return;
    const el = frame.current;
    if (!el) return;

    let detach = () => {};
    const attach = () => {
      const doc = el.contentDocument;
      if (!doc) return;

      const marks = Array.from(doc.querySelectorAll<HTMLElement>('[data-page]'));
      if (!marks.length) return;

      let last = -1;
      const report = () => {
        // A quarter down the viewport, not the very top: what one is reading
        // sits below the fold line, not on it.
        const line = window.innerHeight * 0.25;
        const offset = el.getBoundingClientRect().top;
        let current = marks[0];
        for (const m of marks) {
          if (m.getBoundingClientRect().top + offset <= line) current = m;
          else break;
        }
        const page = Number(current.dataset.page);
        if (Number.isFinite(page) && page !== last) {
          last = page;
          onPage(page);
        }
      };

      report();
      window.addEventListener('scroll', report, { passive: true });
      detach = () => window.removeEventListener('scroll', report);
    };

    el.addEventListener('load', attach);
    // The document may already be loaded when this effect runs — a remount
    // with the frame in cache, or a fast local file.
    if (el.contentDocument?.readyState === 'complete') attach();
    return () => {
      el.removeEventListener('load', attach);
      detach();
    };
  }, [present, url, onPage]);

  return (
    <section className="card mt-6 overflow-hidden">
      <header className="flex flex-wrap items-center gap-2 border-b border-ink-200 bg-ink-50 px-4 py-2">
        <div className="min-w-0">
          <p className="text-[10.5px] font-bold uppercase tracking-[0.1em] text-ink-400">
            Transcript
          </p>
          <p className="tabular text-[13px] font-medium text-ink-800">
            Cote n° {cote} · batch {batch} · pages {first}–{last}
          </p>
        </div>

        <div className="ml-auto flex rounded-lg bg-ink-100 p-0.5" role="tablist">
          {EDITIONS.map((e) => (
            <button
              key={e.key}
              type="button"
              role="tab"
              aria-selected={edition === e.key}
              title={e.help}
              onClick={() => onEdition(e.key)}
              className={`rounded-md px-2.5 py-1 text-[12px] font-medium transition ${
                edition === e.key
                  ? 'bg-white text-ink-900 shadow-[0_1px_3px_rgb(19_18_16/.12)]'
                  : 'text-ink-500 hover:text-ink-800'
              }`}
            >
              {e.label}
              {/* A hollow dot marks an edition that does not exist yet, so the
                  tab bar says what has been done without a second legend. */}
              {!available.html.includes(e.key) && (
                <span className="ml-1 text-[9px] text-ink-300">○</span>
              )}
            </button>
          ))}
        </div>
      </header>

      {present ? (
        // The legal notice is the document's own, tiled down its whole height
        // by the renderer — not drawn here. A copy in this pane had to be
        // `position: sticky`, and sticky resolves against the nearest scroll
        // container, which is this card's `overflow-hidden`: it never scrolls,
        // so the mark sat at the top of the transcript and slid away with it.
        <iframe
          key={url}
          ref={frame}
          src={url}
          title={`Transcript of folder ${cote}, pages ${first}–${last}`}
          scrolling="no"
          style={{ height }}
          className="w-full border-0 bg-white"
        />
      ) : (
        <MissingTranscript
          cote={cote}
          batch={batch}
          edition={edition}
          first={first}
          last={last}
          folder={folder}
        />
      )}
    </section>
  );
}

const Skill = ({ children }: { children: string }) => (
  <code className="rounded border border-ink-200 bg-ink-50 px-1 py-0.5 font-mono text-[12px]">
    {children}
  </code>
);

/**
 * No transcript yet: say what produces one, and with which command.
 *
 * The two editions are not made the same way, and the message says so rather
 * than describing one pipeline for both. The transcription is cut to batches
 * because reading twenty handwritten pages is as far as one pass carries;
 * the modernised reading takes the folder whole, since its job is to make an
 * argument run continuously and a batch boundary is not where an argument
 * ends. So the command offered here carries a batch number in one case and
 * only the shelfmark in the other.
 */
function MissingTranscript({
  cote,
  batch,
  edition,
  first,
  last,
  folder,
}: {
  cote: string;
  batch: number;
  edition: Edition;
  first: number;
  last: number;
  folder: ReturnType<typeof folderTranscription>;
}) {
  const label = EDITIONS.find((e) => e.key === edition)!.label.toLowerCase();

  return (
    <div className="flex flex-col items-start gap-3 px-6 py-10">
      <p className="text-[14px] font-semibold text-ink-800">
        No {label} yet for pages {first}–{last}.
      </p>

      {edition === 'modern' ? (
        <>
          <p className="max-w-[40em] text-[13.5px] leading-relaxed text-ink-600">
            <Skill>modernize-grothendieck</Skill> derives this edition — a « Résumé » that
            orients a reader new to the subject, then the mathematics in current notation and
            current names, in French. It reads the transcription, never the facsimile, and it
            takes the folder whole rather than one batch: the argument it restates runs across
            the batch boundaries.
          </p>

          {/* Which command to put in the box is the whole question here. Offering
              the modernisation command to a folder that is not fully transcribed
              offers a command that will refuse — so when the folder is not ready,
              the box holds the step that actually comes next. */}
          {folder.complete ? (
            <>
              <code className="w-full max-w-[40em] rounded-lg border border-ink-200 bg-ink-50 px-3 py-2 font-mono text-[12.5px] text-ink-900">
                /modernize-grothendieck {cote}
              </code>
              <p className="max-w-[40em] text-[12.5px] leading-relaxed text-ink-500">
                All {folder.total} {folder.total === 1 ? 'batch' : 'batches'} of this folder are
                transcribed, so one pass writes the modernised reading for every one of them.
              </p>
            </>
          ) : (
            <>
              <p className="max-w-[40em] text-[13.5px] leading-relaxed text-ink-600">
                <strong className="font-semibold text-ink-800">
                  It cannot run on this folder yet.
                </strong>{' '}
                Because it takes the folder whole, it needs every batch transcribed first —{' '}
                {folder.done} of {folder.total} {folder.total === 1 ? 'is' : 'are'} done, and{' '}
                {folder.missing.length === 1
                  ? `batch ${folder.missing[0]} is missing`
                  : `batches ${folder.missing.slice(0, -1).join(', ')} and ${folder.missing.at(-1)} are missing`}
                . A reading made without them would guess where the argument was going.
              </p>
              <code className="w-full max-w-[40em] rounded-lg border border-ink-200 bg-ink-50 px-3 py-2 font-mono text-[12.5px] text-ink-900">
                /transcribe-grothendieck {cote}, batch {folder.missing[0]}
              </code>
              <p className="max-w-[40em] text-[12.5px] leading-relaxed text-ink-500">
                One batch per conversation, until the folder is done. Then{' '}
                <code className="font-mono">/modernize-grothendieck {cote}</code> in a single
                pass.
              </p>
            </>
          )}
        </>
      ) : (
        <>
          <p className="max-w-[40em] text-[13.5px] leading-relaxed text-ink-600">
            <Skill>transcribe-grothendieck</Skill> reads the very facsimile shown on the right
            and writes the LaTeX transcription. It works one batch at a time, {BATCH_SIZE} pages
            per pass — past that the quality of reading falls away with nothing to signal it.
          </p>
          <code className="w-full max-w-[40em] rounded-lg border border-ink-200 bg-ink-50 px-3 py-2 font-mono text-[12.5px] text-ink-900">
            /transcribe-grothendieck {cote} {batch}
          </code>
          <p className="max-w-[40em] text-[12.5px] leading-relaxed text-ink-500">
            The facsimile must be mirrored first — the skill refuses to work from anything but
            the local batch file.
          </p>
        </>
      )}

      <a
        href="/contribute/"
        className="text-[12.5px] font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 transition hover:text-brand-700"
      >
        Want to help? See how to install the skills and open a pull request.
      </a>
    </div>
  );
}
