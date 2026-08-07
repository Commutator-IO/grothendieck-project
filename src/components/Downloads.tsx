import { transcriptUrl } from '../lib/batches.ts';
import type { Edition, TranscriptEntry } from '../lib/types.ts';
import { EDITIONS } from './TranscriptPane.tsx';

/**
 * The three editions of a batch, in source and in print.
 *
 * A transcript that can only be read on this site is a transcript one cannot
 * use. The `.tex` is the artifact that matters — it is what gets cited,
 * corrected, and folded into a larger document — and the `.pdf` is what one
 * sends to someone who will not compile anything. Both are offered per edition
 * rather than as one bundle: the person who wants the French transcription and
 * the person who wants the undergraduate summary are almost never the same
 * person.
 *
 * Buttons appear only for files that exist. A download that 404s teaches the
 * reader to distrust every other button on the page.
 */
export function Downloads({
  cote,
  batch,
  available,
}: {
  cote: string;
  batch: number;
  available: TranscriptEntry;
}) {
  const rows = EDITIONS.map((e) => ({
    ...e,
    tex: available.tex.includes(e.key),
    pdf: available.pdf.includes(e.key),
  })).filter((r) => r.tex || r.pdf);

  if (!rows.length) {
    return (
      <p className="mt-4 text-[12.5px] leading-relaxed text-ink-500">
        Nothing to download for this batch yet — the skill writes the LaTeX, and{' '}
        <code className="rounded border border-ink-200 bg-ink-50 px-1 py-0.5 font-mono text-[11.5px]">
          npm run pdf
        </code>{' '}
        compiles it.
      </p>
    );
  }

  return (
    <div className="mt-5">
      <p className="text-[11px] font-bold uppercase tracking-[0.1em] text-ink-400">Downloads</p>
      <ul className="mt-2 flex flex-wrap gap-2">
        {rows.map((r) => (
          <li key={r.key} className="flex items-center gap-1.5 rounded-lg border border-ink-200 bg-white px-2.5 py-1.5">
            <span className="text-[12.5px] font-medium text-ink-700" title={r.help}>
              {r.label}
            </span>
            {(['tex', 'pdf'] as const).map((ext) =>
              r[ext] ? (
                <a
                  key={ext}
                  href={transcriptUrl(cote, batch, r.key as Edition, ext)}
                  download
                  className="rounded-md bg-ink-100 px-1.5 py-0.5 font-mono text-[11px] font-semibold uppercase text-ink-600 transition hover:bg-brand-100 hover:text-brand-700"
                >
                  {ext}
                </a>
              ) : null,
            )}
          </li>
        ))}
      </ul>
    </div>
  );
}
