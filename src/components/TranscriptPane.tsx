import { useEffect, useRef, useState } from 'react';
import { BATCH_SIZE, batchRange, transcriptUrl } from '../lib/batches.ts';
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
  { key: 'fr', label: 'Transcription', help: 'The leaves as written.' },
  {
    key: 'modern',
    label: 'Modernised',
    help: 'An interpretation in current notation, opening with an introduction to the subject.',
  },
];

export function TranscriptPane({
  cote,
  batch,
  pages,
  available,
  edition,
  onEdition,
  onLeaf,
}: {
  cote: string;
  batch: number;
  pages: number;
  available: TranscriptEntry;
  edition: Edition;
  onEdition: (e: Edition) => void;
  /** Called with the archive leaf currently at the top of the reading area. */
  onLeaf: (leaf: number) => void;
}) {
  const frame = useRef<HTMLIFrameElement>(null);
  const [height, setHeight] = useState(600);
  const { first, last } = batchRange(batch, pages);
  const present = available.html.includes(edition);
  const url = transcriptUrl(cote, batch, edition, 'html');

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
   * The transcript marks each source leaf with `data-leaf="47"`. Whichever
   * marker is highest in the reading area names the leaf being read, and the
   * facsimile follows. This is the whole reason the two panes are worth having
   * side by side: reading the transcription of leaf 47 while looking at leaf 41
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

      const marks = Array.from(doc.querySelectorAll<HTMLElement>('[data-leaf]'));
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
        const leaf = Number(current.dataset.leaf);
        if (Number.isFinite(leaf) && leaf !== last) {
          last = leaf;
          onLeaf(leaf);
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
  }, [present, url, onLeaf]);

  return (
    <section className="card mt-6 overflow-hidden">
      <header className="flex flex-wrap items-center gap-2 border-b border-ink-200 bg-ink-50 px-4 py-2">
        <div className="min-w-0">
          <p className="text-[10.5px] font-bold uppercase tracking-[0.1em] text-ink-400">
            Transcript
          </p>
          <p className="tabular text-[13px] font-medium text-ink-800">
            Cote n° {cote} · batch {batch} · leaves {first}–{last}
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
        <iframe
          key={url}
          ref={frame}
          src={url}
          title={`Transcript of folder ${cote}, leaves ${first}–${last}`}
          scrolling="no"
          style={{ height }}
          className="w-full border-0 bg-white"
        />
      ) : (
        <MissingTranscript cote={cote} batch={batch} edition={edition} first={first} last={last} />
      )}
    </section>
  );
}

/** No transcript yet: say what produces one, and with which command. */
function MissingTranscript({
  cote,
  batch,
  edition,
  first,
  last,
}: {
  cote: string;
  batch: number;
  edition: Edition;
  first: number;
  last: number;
}) {
  const label = EDITIONS.find((e) => e.key === edition)!.label.toLowerCase();
  return (
    <div className="flex flex-col items-start gap-3 px-6 py-10">
      <p className="text-[14px] font-semibold text-ink-800">
        No {label} yet for leaves {first}–{last}.
      </p>
      <p className="max-w-[40em] text-[13.5px] leading-relaxed text-ink-600">
        Work runs one batch at a time, {BATCH_SIZE} leaves per pass, through three skills in
        order:{' '}
        <code className="rounded border border-ink-200 bg-ink-50 px-1 py-0.5 font-mono text-[12px]">
          transcribe-grothendieck
        </code>{' '}
        reads the very facsimile shown on the right and writes the LaTeX transcription;{' '}
        <code className="rounded border border-ink-200 bg-ink-50 px-1 py-0.5 font-mono text-[12px]">
          modernize-grothendieck
        </code>{' '}
        and{' '}
        <code className="rounded border border-ink-200 bg-ink-50 px-1 py-0.5 font-mono text-[12px]">
          summarize-grothendieck
        </code>{' '}
        derive the modernised reading and the licence-level summary from it, in French.
      </p>
      <code className="w-full max-w-[40em] rounded-lg border border-ink-200 bg-ink-50 px-3 py-2 font-mono text-[12.5px] text-ink-900">
        /transcribe-grothendieck {cote} {batch}
      </code>
      <p className="max-w-[40em] text-[12.5px] leading-relaxed text-ink-500">
        The facsimile must be mirrored first — the skill refuses to work from anything but the
        local batch file.
      </p>
    </div>
  );
}
