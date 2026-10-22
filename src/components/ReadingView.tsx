import { useCallback, useRef, useState } from 'react';
import { FacsimilePane, type OpenBatch } from './FacsimilePane.tsx';
import { useReadingFrame } from './TranscriptPane.tsx';
import { batchCount, batchRange } from '../lib/batches.ts';

/**
 * The reading view of a collection beside the fonds — the Fonds
 * Grothendieck–Illusie, Quillen's notebooks, the Bourbaki archive: one batch's
 * transcription on the left, rendered by scripts/render.mjs and framed by the
 * fonds' own hook (useReadingFrame), so that it lands on the page the fragment
 * names and scrolling it turns the facsimile's pages; the facsimile in the
 * shared pane on the right. One component for the three, as TranscriptPane is
 * one for the fonds, so that they cannot drift apart.
 *
 * Imported only by the readers, which each page imports lazily and only when
 * its switch is on (or in the dev server): off, none of this is in the build.
 */
export function ReadingView({
  label,
  title,
  batch,
  page,
  pages,
  url,
  present,
  transcribed,
  texPath,
  noun,
  link,
  facsimile,
  onBatch,
  onPage,
  onClose,
}: {
  /** The shelfmark, notebook or document, as the header names it. */
  label: string;
  title?: string | null;
  batch: number;
  /** The page being read, which the facsimile shows. */
  page?: number;
  /** Pages in the document; 0 when uncounted. */
  pages: number;
  /** The rendered batch, under public/. */
  url: string;
  /** Whether that batch is rendered on this machine (the manifest says). */
  present: boolean;
  /** The batches of this document that are. */
  transcribed: number[];
  /** Where a transcription of this batch would be written. */
  texPath: string;
  /** « item », « notebook », « document ». */
  noun: string;
  /** The holder's own page for it. */
  link: { href: string; text: string };
  /** The facsimile, without the page being read: this view supplies it. */
  facsimile: Omit<OpenBatch, 'page' | 'transcribed'>;
  onBatch: (batch: number) => void;
  /** Called with the page at the top of the reading area. */
  onPage: (page: number) => void;
  onClose: () => void;
}) {
  // The facsimile can be put away and brought back; closing the reading view
  // itself is the header's button.
  const [pane, setPane] = useState(true);
  // Uncounted pages (0): the batch's nominal twenty.
  const range = batchRange(batch, Math.max(pages, batch * 20));
  const first = range.first;
  const last = pages > 0 ? Math.min(range.last, pages) : range.last;

  const frame = useRef<HTMLIFrameElement>(null);
  const report = useCallback((p: number) => onPage(p), [onPage]);
  const height = useReadingFrame(frame, url, present, report);

  return (
    <>
      <section className="card mt-6 overflow-hidden" aria-label="Reading">
        <header className="flex flex-wrap items-center gap-2 border-b border-ink-200 bg-ink-50 px-4 py-2">
          <div className="min-w-0 flex-1">
            <p className="text-[10.5px] font-bold uppercase tracking-[0.1em] text-ink-400">Transcript</p>
            <p className="tabular text-[13px] font-medium text-ink-800">
              {label} · batch {batch}
              {pages > 0 ? ` of ${batchCount(pages)}` : ''} · pages {first}–{last}
            </p>
            {title && <p className="mt-0.5 text-[12.5px] text-ink-600">{title}</p>}
          </div>
          <a
            href={link.href}
            target="_blank"
            rel="noreferrer"
            className="rounded-lg border border-ink-200 px-2.5 py-1 text-[12px] font-medium text-ink-600 transition hover:border-brand-500 hover:text-brand-700"
          >
            {link.text}
          </a>
          {!pane && (
            <button
              type="button"
              onClick={() => setPane(true)}
              className="hidden rounded-lg border border-brand-500 px-2.5 py-1 text-[12px] font-medium text-brand-700 transition hover:bg-brand-50 lg:inline-block"
            >
              Show the facsimile
            </button>
          )}
          <button
            type="button"
            onClick={onClose}
            className="rounded-lg border border-ink-200 px-2.5 py-1 text-[12px] font-medium text-ink-600 transition hover:border-alerte-500 hover:text-alerte-700"
          >
            Close
          </button>
        </header>
        {present ? (
          <iframe
            key={url}
            ref={frame}
            src={url}
            title={`Transcript of ${label}, pages ${first}–${last}`}
            scrolling="no"
            style={{ height }}
            className="w-full border-0 bg-white"
          />
        ) : (
          <div className="flex flex-col items-start gap-2 px-6 py-8">
            <p className="text-[14px] font-semibold text-ink-800">
              No transcription yet for pages {first}–{last}.
            </p>
            <p className="max-w-[40em] text-[13px] leading-relaxed text-ink-600">
              {transcribed.length
                ? `Batch${transcribed.length > 1 ? 'es' : ''} ${transcribed.join(', ')} of this ${noun} ${transcribed.length > 1 ? 'are' : 'is'} transcribed.`
                : `Nothing of this ${noun} is transcribed here.`}{' '}
              A transcription would be written to{' '}
              <code className="font-mono text-[12px]">{texPath}</code> and rendered here by the same
              renderer as the Montpellier folders.
            </p>
          </div>
        )}
      </section>

      {pane && (
        <FacsimilePane
          open={{ ...facsimile, batch, page, transcribed }}
          onClose={() => setPane(false)}
          onBatch={onBatch}
        />
      )}
    </>
  );
}

/** The batches of `folder` a manifest section lists with `edition`, in order. */
export function batchesOf(views: Record<string, string[]> | undefined, folder: string, edition: string): number[] {
  const prefix = `${folder}#`;
  return Object.entries(views ?? {})
    .filter(([k, v]) => k.startsWith(prefix) && v.includes(edition))
    .map(([k]) => Number(k.slice(prefix.length)))
    .filter(Number.isInteger)
    .sort((a, b) => a - b);
}
