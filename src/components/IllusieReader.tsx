import { useCallback, useRef, useState } from 'react';
import { FacsimilePane, type OpenBatch } from './FacsimilePane.tsx';
import { useReadingFrame } from './TranscriptPane.tsx';
import { batchCount, batchName, batchRange, useManifest } from '../lib/batches.ts';
import pagesRaw from '../content/illusie-pages.json';

/**
 * The reading view of one item of the Fonds Grothendieck–Illusie: the
 * transcription on the left, the facsimile in the shared pane on the right —
 * the layout of the Montpellier folders and of the Quillen notebooks, made of
 * the same parts. The transcription is rendered from
 * `transcripts-illusie/<item>/batch-NN.fr.tex` by scripts/render.mjs (run with
 * `--illusie`), and framed by the same hook as the fonds' reading views, so
 * that scrolling it turns the facsimile's pages. The facsimile is the IHÉS's
 * own jpg views, loaded from its server; nothing is relayed or copied.
 *
 * This module is imported only by a build made with RENDER_ILLUSIE (and by
 * the dev server): the IHÉS has not published the fonds, and until it agrees,
 * the deployed site carries neither this view nor the page addresses it reads
 * from src/content/illusie-pages.json.
 */

export interface IllusieItem {
  id: string;
  title: string | null;
  date: string | null;
  sort: string | null;
  pages: number;
  /** The item's directory on the IHÉS server. */
  url: string;
}

const VIEWS = (pagesRaw as unknown as { views: Record<string, { jpg: string[]; pdf: string | null }> }).views;

export function IllusieReader({
  item,
  batch,
  page,
  onBatch,
  onPage,
  onClose,
}: {
  item: IllusieItem;
  batch: number;
  page?: number;
  onBatch: (batch: number) => void;
  onPage: (page: number) => void;
  onClose: () => void;
}) {
  const manifest = useManifest();
  // The facsimile can be put away and brought back; closing the reading view
  // itself is the header's button.
  const [pane, setPane] = useState(true);
  const view = VIEWS[item.id];
  const jpg = view?.jpg ?? [];
  const pages = item.pages || jpg.length;
  const { first, last } = batchRange(batch, Math.max(pages, 1));
  const prefix = `${item.id}#`;
  const transcribed = Object.entries(manifest?.illusie ?? {})
    .filter(([k, v]) => k.startsWith(prefix) && v.includes('fr'))
    .map(([k]) => Number(k.slice(prefix.length)))
    .filter(Number.isInteger)
    .sort((a, b) => a - b);
  const present = transcribed.includes(batch);
  const url = `/transcripts-illusie/${item.id}/${batchName(batch)}.fr.html`;

  const frame = useRef<HTMLIFrameElement>(null);
  const report = useCallback((p: number) => onPage(p), [onPage]);
  const height = useReadingFrame(frame, url, present, report);

  const facsimile: OpenBatch = {
    cote: item.id,
    title: item.title ?? item.id,
    date: item.date ?? item.sort ?? 's.d.',
    batch,
    pages,
    page,
    relay: 'ready',
    transcribed,
    source: jpg.length
      ? {
          file: '',
          images: jpg.map((f) => item.url + encodeURIComponent(f)),
          original: item.url,
          heading: `Fonds Grothendieck–Illusie · ${item.id}`,
          credit:
            'Facsimile: Fonds Grothendieck–Illusie, IHÉS — the page views are loaded from its server, repo-archives.ihes.fr, and not copied here. Under its authors’ rights; for any use, archives@ihes.fr.',
          pageOffset: 0,
        }
      : {
          file: '',
          original: view?.pdf ? item.url + encodeURIComponent(view.pdf) : item.url,
          heading: `Fonds Grothendieck–Illusie · ${item.id}`,
          why: 'The IHÉS keeps this item as TIFF masters and a PDF, with no page views a pane can show. The PDF opens on its server, in a tab of its own.',
          credit:
            'Fonds Grothendieck–Illusie, IHÉS. Under its authors’ rights; for any use, archives@ihes.fr.',
          pageOffset: 0,
        },
  };

  return (
    <>
      <section className="card mt-6 overflow-hidden" aria-label="Reading">
        <header className="flex flex-wrap items-center gap-2 border-b border-ink-200 bg-ink-50 px-4 py-2">
          <div className="min-w-0 flex-1">
            <p className="text-[10.5px] font-bold uppercase tracking-[0.1em] text-ink-400">Transcript</p>
            <p className="tabular text-[13px] font-medium text-ink-800">
              {item.id} · batch {batch} of {batchCount(pages)} · pages {first}–{last}
            </p>
            {item.title && <p className="mt-0.5 text-[12.5px] text-ink-600">{item.title}</p>}
          </div>
          <a
            href={item.url}
            target="_blank"
            rel="noreferrer"
            className="rounded-lg border border-ink-200 px-2.5 py-1 text-[12px] font-medium text-ink-600 transition hover:border-brand-500 hover:text-brand-700"
          >
            IHÉS ↗
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
            title={`Transcript of ${item.id}, pages ${first}–${last}`}
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
                ? `Batch${transcribed.length > 1 ? 'es' : ''} ${transcribed.join(', ')} of this item ${transcribed.length > 1 ? 'are' : 'is'} transcribed.`
                : 'Nothing of this item is transcribed.'}{' '}
              A transcription would be written to{' '}
              <code className="font-mono text-[12px]">
                transcripts-illusie/{item.id}/{batchName(batch)}.fr.tex
              </code>{' '}
              and rendered here by the same renderer as the Montpellier folders.
            </p>
          </div>
        )}
      </section>

      {pane && <FacsimilePane open={facsimile} onClose={() => setPane(false)} onBatch={onBatch} />}
    </>
  );
}
