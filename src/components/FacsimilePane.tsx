import { useCallback, useEffect, useRef, useState } from 'react';
import {
  batchCount,
  batchRange,
  facsimileUrl,
  pdfIndexOf,
  sourceUrl,
  type RelayState,
} from '../lib/batches.ts';
import { REPO } from '../lib/report.ts';

/**
 * The facsimile, opened in a pane to the right of the transcript.
 *
 * This is the gesture of anyone transcribing: the page on one side, what one
 * makes of it on the other. Doing it inside the page avoids the round trip
 * between tabs, which costs the reading position every time.
 *
 * Three constraints dictated the shape, and two of them are not choices:
 *
 * — **The PDF cannot come from Montpellier.** Two independent blockers, both
 *   measured rather than assumed. The server sends
 *   `X-Frame-Options: SAMEORIGIN`, so it refuses to be framed by any other
 *   origin at all — a probe iframe never gets a document, and that would hold
 *   even if everything else were in order. On top of that its certificate
 *   expired on 10 December 2025, so the load fails TLS verification, and the
 *   interstitial that would let one proceed does not render inside a frame.
 *   The pane therefore reads the local mirror, and offers the original link
 *   beside it — in a new tab, where the reader can decide for themselves.
 * — **The originals run to 270 MB.** One never opens a whole folder: one opens
 *   a twenty-page batch, a few megabytes, which is also the unit of
 *   transcription. What the pane shows is exactly the file handed to the
 *   transcriber.
 * — **Mobile PDF viewers cannot render a frame.** The pane is therefore for
 *   wide screens, and the direct link stays offered everywhere, here included.
 */

const WIDTH_KEY = 'grothendieck.facsimile.width';
const MIN_WIDTH = 380;
const DEFAULT_WIDTH = 640;
const MAX_SHARE = 0.72;

export interface OpenBatch {
  cote: string;
  title: string;
  date: string;
  /** Batch number within the folder, from 1. */
  batch: number;
  /** Pages in the folder, as the inventory counts them. */
  pages: number;
  /** The archive page to show, when the transcript says which one is being read. */
  page?: number;
  /** Whether the relay is up yet — the frame waits rather than racing it. */
  relay: RelayState;
}

function clamp(w: number): number {
  return Math.min(Math.max(w, MIN_WIDTH), window.innerWidth * MAX_SHARE);
}

/**
 * The page anchor.
 *
 * `#page=N` is understood by the built-in PDF viewers of Chrome, Edge and
 * Firefox. Safari ignores it and opens at the first page: an acceptable
 * degradation, not a reason to do without.
 *
 * N counts in the file, which is the whole folder — so it is the archive page
 * plus one, for the cover sheet Montpellier prefixes. With no page named yet,
 * the anchor is the first page of the batch, which is where a reader starting
 * a batch wants to be.
 */
function address(b: OpenBatch): string {
  const url = facsimileUrl(b.cote);
  const { first, last } = batchRange(b.batch, b.pages);
  const page = b.page ? Math.min(Math.max(b.page, first), last) : first;
  return `${url}#page=${pdfIndexOf(page)}`;
}

/**
 * The iframe's target, held back until the reader stops moving.
 *
 * `onPage` fires on every `\page{}`/`\pagerange{}` marker the transcript
 * scrolls past, and the frame below remounts on every distinct target —
 * necessary, since changing only `#page=` does not make an already-loaded
 * frame navigate. But a fast scroll crosses several markers a second, and
 * each remount is a fresh request to the relay; the ones the scroll outruns
 * are aborted mid-flight rather than never sent; measured on a batch of
 * fourteen sections, one screen's worth of scrolling fired nine of them. This
 * turns "one request per marker passed" into "one request once scrolling
 * stops" — the marker text and page count above still update immediately,
 * only the frame itself waits.
 */
function useSettledAddress(open: OpenBatch, delay = 350): string {
  const target = address(open);
  const [settled, setSettled] = useState(target);
  useEffect(() => {
    const t = setTimeout(() => setSettled(target), delay);
    return () => clearTimeout(t);
  }, [target, delay]);
  return settled;
}

export function FacsimilePane({
  open,
  onClose,
  onBatch,
}: {
  open: OpenBatch;
  onClose: () => void;
  onBatch: (batch: number) => void;
}) {
  const src = useSettledAddress(open);
  const [width, setWidth] = useState(DEFAULT_WIDTH);
  // Two representations of one value, on purpose: state drives the render, the
  // ref lets the event handlers read the current width without being
  // re-created — and without computing inside a state updater, which React
  // runs twice under StrictMode.
  const widthRef = useRef(DEFAULT_WIDTH);
  const dragging = useRef(false);
  const [isDragging, setIsDragging] = useState(false);

  const set = useCallback((w: number) => {
    widthRef.current = w;
    setWidth(w);
  }, []);

  const persist = useCallback(() => {
    try {
      localStorage.setItem(WIDTH_KEY, String(Math.round(widthRef.current)));
    } catch {
      // Private browsing: nothing to remember, the pane still works.
    }
  }, []);

  useEffect(() => {
    try {
      const stored = Number(localStorage.getItem(WIDTH_KEY));
      if (stored >= MIN_WIDTH) set(stored);
    } catch {
      // Default width: enough to read a scanned A4 page.
    }
  }, [set]);

  /**
   * The width ceiling lives in CSS, not in JavaScript.
   *
   * `min(Npx, 72vw)` lets the browser re-evaluate on every viewport change —
   * zoom, a toolbar folding away, a window resized by the system — with no
   * listener and no React render, and without overwriting the width the reader
   * chose just because they shrank the window once.
   */
  const widthCss = `min(${Math.round(width)}px, ${Math.round(MAX_SHARE * 100)}vw)`;

  useEffect(() => {
    document.documentElement.style.setProperty('--pane', widthCss);
    return () => {
      document.documentElement.style.removeProperty('--pane');
    };
  }, [widthCss]);

  const count = batchCount(open.pages);
  const { first, last } = batchRange(open.batch, open.pages);

  // Escape closes; the arrows step through batches. Those are the two gestures
  // one makes without thinking when working through a 695-page folder.
  useEffect(() => {
    const onKey = (e: KeyboardEvent) => {
      if (e.key === 'Escape') onClose();
      // Arrows are not hijacked while focus is inside the PDF frame or a
      // field: the viewer uses them to scroll.
      const tag = document.activeElement?.tagName;
      if (tag === 'IFRAME' || tag === 'INPUT' || tag === 'TEXTAREA') return;
      if (e.key === 'ArrowLeft' && open.batch > 1) onBatch(open.batch - 1);
      if (e.key === 'ArrowRight' && open.batch < count) onBatch(open.batch + 1);
    };
    window.addEventListener('keydown', onKey);
    return () => window.removeEventListener('keydown', onKey);
  }, [onClose, onBatch, open.batch, count]);

  /**
   * Dragging the handle, in pointer events.
   *
   * This gesture has an adversary: the PDF frame. A document in an iframe
   * receives the mouse events passing over it and does not hand them back.
   * With plain `mousemove` / `mouseup` on the window, the handle comes loose
   * as soon as the cursor enters the PDF — and, worse, the release is never
   * seen, so the pane keeps following the mouse after the button is up.
   *
   * Three protections, because none suffices alone: pointer capture, which
   * redirects everything to the handle; `pointer-events: none` on the frame
   * during the gesture, making it transparent even without capture; and
   * listeners on `window`, the only place that sees every event, captured or
   * not.
   */
  const startDrag = (e: React.PointerEvent<HTMLDivElement>) => {
    e.preventDefault();
    dragging.current = true;
    setIsDragging(true);
    document.body.style.userSelect = 'none';
    document.body.style.cursor = 'col-resize';
    try {
      e.currentTarget.setPointerCapture(e.pointerId);
    } catch {
      // Pointer already released: the veil and the window listeners suffice.
    }
  };

  const endDrag = useCallback(() => {
    if (!dragging.current) return;
    dragging.current = false;
    setIsDragging(false);
    document.body.style.userSelect = '';
    document.body.style.cursor = '';
    persist();
  }, [persist]);

  useEffect(() => {
    if (!isDragging) return;
    const follow = (e: PointerEvent) => {
      if (!dragging.current) return;
      // A button released outside the window does not always produce a
      // `pointerup`: the first move with no button down stands in for it.
      if (e.buttons === 0) {
        endDrag();
        return;
      }
      set(clamp(window.innerWidth - e.clientX));
    };
    window.addEventListener('pointermove', follow);
    window.addEventListener('pointerup', endDrag);
    window.addEventListener('pointercancel', endDrag);
    return () => {
      window.removeEventListener('pointermove', follow);
      window.removeEventListener('pointerup', endDrag);
      window.removeEventListener('pointercancel', endDrag);
    };
  }, [isDragging, set, endDrag]);

  // If the pane closes mid-drag, the page would stay unselectable and the
  // cursor stuck as a double arrow.
  useEffect(
    () => () => {
      document.body.style.userSelect = '';
      document.body.style.cursor = '';
    },
    [],
  );

  const onHandleKey = (e: React.KeyboardEvent) => {
    const step = e.shiftKey ? 64 : 16;
    if (e.key === 'ArrowLeft') set(clamp(widthRef.current + step));
    else if (e.key === 'ArrowRight') set(clamp(widthRef.current - step));
    else if (e.key === 'Home') set(clamp(DEFAULT_WIDTH));
    else return;
    e.preventDefault();
    persist();
  };

  return (
    <aside
      className="fixed right-0 top-0 z-50 hidden h-dvh flex-col border-l border-ink-200 bg-white shadow-[-8px_0_24px_-16px_rgb(19_18_16/.35)] lg:flex"
      style={{ width: widthCss }}
      aria-label={`Facsimile — folder ${open.cote}, pages ${first} to ${last}`}
    >
      <div
        role="separator"
        tabIndex={0}
        aria-orientation="vertical"
        aria-label="Facsimile pane width"
        // The announced value is the one actually rendered, not the one
        // stored: on a narrow window the CSS ceiling wins.
        aria-valuenow={Math.round(Math.min(width, window.innerWidth * MAX_SHARE))}
        aria-valuemin={MIN_WIDTH}
        aria-valuemax={Math.round(window.innerWidth * MAX_SHARE)}
        onPointerDown={startDrag}
        onLostPointerCapture={endDrag}
        onKeyDown={onHandleKey}
        className={`absolute left-0 top-0 h-full w-2 cursor-col-resize touch-none transition focus-visible:bg-brand-400 focus-visible:outline-none ${
          isDragging ? 'bg-brand-400' : 'bg-transparent hover:bg-brand-200'
        }`}
      />

      <header className="flex shrink-0 items-start gap-3 border-b border-ink-200 px-4 py-2.5 pl-5">
        <div className="min-w-0 flex-1">
          <p className="text-[10.5px] font-bold uppercase tracking-[0.1em] text-ink-400">
            Cote n° {open.cote} · {open.date || 's.d.'}
          </p>
          <p className="truncate text-[13px] font-medium text-ink-800" title={open.title}>
            {open.title}
          </p>
        </div>
        <a
          href={sourceUrl(open.cote)}
          target="_blank"
          rel="noopener noreferrer"
          title="The whole folder, served by Montpellier (expired certificate: the browser will warn)"
          className="mt-0.5 shrink-0 rounded-lg border border-ink-200 px-2.5 py-1 text-[12px] font-medium text-ink-600 transition hover:border-brand-500 hover:text-brand-700"
        >
          Source ↗<span className="sr-only"> (new tab, at the University of Montpellier)</span>
        </a>
        <button
          type="button"
          onClick={onClose}
          className="mt-0.5 shrink-0 rounded-lg border border-ink-200 px-2.5 py-1 text-[12px] font-medium text-ink-600 transition hover:border-alerte-500 hover:text-alerte-700"
        >
          Close
        </button>
      </header>

      <BatchBar
        batch={open.batch}
        count={count}
        first={first}
        last={last}
        pages={open.pages}
        page={open.page}
        onBatch={onBatch}
      />

      {/* The frame is mounted only once the relay has answered with a PDF.
          Pointed at a relay still starting up, it would frame the host's own
          start-up page — a stranger's loading screen inside the reading
          workspace, which is worse than saying plainly that we are waiting. */}
      {open.relay === 'ready' ? (
        <iframe
          // The key forces a remount when the address changes — changing only
          // the `#page=` fragment does not make an already-loaded frame
          // navigate, so the pane would stay on the previous page. `src` is
          // the settled address, not the live one: see useSettledAddress for
          // why remounting on every marker a scroll passes is not cheap.
          key={src}
          src={src}
          title={`Folder ${open.cote}, pages ${first} to ${last}`}
          className={`min-h-0 flex-1 border-0 bg-ink-100 ${isDragging ? 'pointer-events-none' : ''}`}
        />
      ) : open.relay === 'waking' ? (
        <Waking cote={open.cote} />
      ) : (
        <NoProxy cote={open.cote} />
      )}

      <p className="shrink-0 border-t border-ink-100 bg-ink-50 px-5 py-2 text-[11.5px] leading-relaxed text-ink-500">
        Facsimile from the Grothendieck fonds, University of Montpellier. Scanned versos are often
        unrelated to the notes and may appear upside down.
      </p>
    </aside>
  );
}

/**
 * The twenty-page step, made manoeuvrable.
 *
 * A number field rather than a bare pair of arrows: on a 695-page folder — the
 * second part of the Long March runs to thirty-five batches — resuming at
 * batch 23 must not cost twenty-two clicks.
 */
function BatchBar({
  batch,
  count,
  first,
  last,
  pages,
  page,
  onBatch,
}: {
  batch: number;
  count: number;
  first: number;
  last: number;
  pages: number;
  page?: number;
  onBatch: (b: number) => void;
}) {
  return (
    <div className="flex shrink-0 items-center gap-2 border-b border-ink-100 bg-ink-50 px-4 py-1.5 pl-5">
      <button
        type="button"
        disabled={batch <= 1}
        onClick={() => onBatch(batch - 1)}
        className="rounded-md border border-ink-200 bg-white px-2 py-0.5 text-[12px] text-ink-600 transition enabled:hover:border-brand-500 enabled:hover:text-brand-700 disabled:opacity-35"
        aria-label="Previous batch"
      >
        ←
      </button>
      <label className="flex items-baseline gap-1.5 text-[12px] text-ink-600">
        <span className="font-medium">Batch</span>
        <input
          type="number"
          min={1}
          max={count}
          value={batch}
          onChange={(e) => {
            const v = Number(e.target.value);
            if (v >= 1 && v <= count) onBatch(v);
          }}
          className="tabular w-14 rounded-md border border-ink-200 bg-white px-1.5 py-0.5 text-center text-[12px] text-ink-900"
        />
        <span className="text-ink-400">/ {count}</span>
      </label>
      <button
        type="button"
        disabled={batch >= count}
        onClick={() => onBatch(batch + 1)}
        className="rounded-md border border-ink-200 bg-white px-2 py-0.5 text-[12px] text-ink-600 transition enabled:hover:border-brand-500 enabled:hover:text-brand-700 disabled:opacity-35"
        aria-label="Next batch"
      >
        →
      </button>
      <p className="tabular ml-auto text-[12px] text-ink-500">
        {page ? (
          <>
            page <strong className="font-semibold text-brand-700">{page}</strong>
            <span className="text-ink-400">
              {' '}
              of {first}–{last}
            </span>
          </>
        ) : (
          <>
            pages <strong className="font-semibold text-ink-800">{first}</strong>–
            <strong className="font-semibold text-ink-800">{last}</strong>
            <span className="text-ink-400"> of {pages}</span>
          </>
        )}
      </p>
    </div>
  );
}

/**
 * The relay is not answering.
 *
 * The facsimile is fetched through a relay because the browser will not frame
 * Montpellier directly. When that relay does not answer — never deployed,
 * asleep, or Montpellier itself down — there is nothing useful to put in this
 * pane.
 *
 * Deliberately no "open in a new tab" button here. Reading side by side is the
 * point of the view; a tab that steals the window is not a lesser version of
 * that, it is the thing the view exists to avoid. The provenance link stays in
 * the header, where it belongs, and this panel says what is broken instead of
 * offering a worse way to work.
 */
/**
 * The relay is starting up, and the pane says so in its own words.
 *
 * The wait is real — a free instance spins down when idle and takes the best
 * part of a minute to come back — so the honest thing is to name it and say
 * why, rather than to show a spinner or, worse, whatever page the host serves
 * meanwhile. The reader is given the folder at Montpellier in the meantime:
 * the wait is ours, and it should not be theirs if they are in a hurry.
 */
function Waking({ cote }: { cote: string }) {
  return (
    <div className="flex min-h-0 flex-1 flex-col items-start gap-3 overflow-auto bg-ink-100 px-6 py-8">
      <p className="text-[13px] font-semibold text-ink-800">Waking the facsimile relay…</p>
      <p className="max-w-[34em] text-[13px] leading-relaxed text-ink-600">
        The scans are streamed from Montpellier through a small relay, which sleeps when nobody
        is reading and takes up to a minute to start. The scan appears here by itself once it
        answers — nothing to click.
      </p>
      <a
        href={sourceUrl(cote)}
        target="_blank"
        rel="noopener noreferrer"
        className="text-[12.5px] font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 transition hover:text-brand-700"
      >
        Folder {cote} at Montpellier, in a new tab ↗
      </a>
    </div>
  );
}

function NoProxy({ cote }: { cote: string }) {
  return (
    <div className="flex min-h-0 flex-1 flex-col items-start gap-3 overflow-auto bg-ink-100 px-6 py-8">
      <p className="text-[13px] font-semibold text-ink-800">
        The facsimile relay is not answering.
      </p>
      <p className="max-w-[34em] text-[13px] leading-relaxed text-ink-600">
        Folder {cote} is served by Montpellier, which sends{' '}
        <code className="font-mono">X-Frame-Options: SAMEORIGIN</code> and whose certificate
        expired on 10 December 2025. Your browser enforces both against their origin, so the scan
        can only appear here by passing through this one — and that relay is currently
        unreachable.
      </p>
      <button
        type="button"
        onClick={() => location.reload()}
        className="rounded-lg bg-brand-600 px-3 py-1.5 text-[13px] font-medium text-white transition hover:bg-brand-700"
      >
        Try again
      </button>
      <p className="max-w-[34em] text-[12.5px] leading-relaxed text-ink-500">
        Locally, <code className="font-mono">npm run dev</code> relays it. In production it is a
        small Node service — <code className="font-mono">relay/server.mjs</code> — and it has to
        be Node, for a reason worth reading before trying to fix this.
      </p>
      {/* The panel says what is broken; this says where the fixing is being
          done. Someone who hits this is exactly the person who might solve
          it, and the issue already records both dead ends so they are not
          re-explored. */}
      <a
        href={`${REPO}/issues/1`}
        target="_blank"
        rel="noopener noreferrer"
        className="inline-flex items-center gap-1.5 text-[12.5px] font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 transition hover:text-brand-700"
      >
        Follow or help with this — issue #1 ↗
      </a>
    </div>
  );
}
