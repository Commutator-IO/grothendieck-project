import { batchesOf, ReadingView } from './ReadingView.tsx';
import { batchName, useManifest } from '../lib/batches.ts';

/**
 * The reading view of one item of the Fonds Grothendieck–Illusie: the
 * transcription on the left, the facsimile in the shared pane on the right —
 * the layout of the Montpellier folders and of the Quillen notebooks, made of
 * the same parts. The transcription is rendered from
 * `transcripts-illusie/<item>/batch-NN.fr.tex` by scripts/render.mjs (run with
 * `--illusie`), and shown by the shared ReadingView, so that scrolling it
 * turns the facsimile's pages. The facsimile is the IHÉS's
 * own jpg views, loaded from its server; nothing is relayed or copied.
 *
 * The page addresses come as a prop: from src/content/illusie-pages.json in a
 * build made with RENDER_ILLUSIE (and in the dev server), otherwise only for
 * the exceptions of src/content/illusie-public.ts — the IHÉS has not published
 * the fonds, and until it agrees the deployed site carries no other item's.
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

export type IllusieView = { jpg: string[]; pdf: string | null };

export function IllusieReader({
  item,
  view,
  batch,
  page,
  onBatch,
  onPage,
  onClose,
}: {
  item: IllusieItem;
  /** The item's page views on the IHÉS server: all items from illusie-pages.json with RENDER_ILLUSIE, else the exceptions of illusie-public.ts. */
  view: IllusieView | undefined;
  batch: number;
  page?: number;
  onBatch: (batch: number) => void;
  onPage: (page: number) => void;
  onClose: () => void;
}) {
  const manifest = useManifest();
  const jpg = view?.jpg ?? [];
  const pages = item.pages || jpg.length;
  const transcribed = batchesOf(manifest?.illusie, item.id, 'fr');

  return (
    <ReadingView
      label={item.id}
      title={item.title}
      batch={batch}
      page={page}
      pages={pages}
      url={`/transcripts-illusie/${item.id}/${batchName(batch)}.fr.html`}
      present={transcribed.includes(batch)}
      transcribed={transcribed}
      texPath={`transcripts-illusie/${item.id}/${batchName(batch)}.fr.tex`}
      noun="item"
      link={{ href: item.url, text: 'IHÉS ↗' }}
      onBatch={onBatch}
      onPage={onPage}
      onClose={onClose}
      facsimile={{
        cote: item.id,
        title: item.title ?? item.id,
        date: item.date ?? item.sort ?? 's.d.',
        batch,
        pages,
        relay: 'ready',
        source: jpg.length
          ? {
              file: '',
              images: jpg.map((f) => item.url + encodeURIComponent(f)),
              original: item.url,
              heading: `Fonds Grothendieck–Illusie · ${item.id}`,
              credit:
                'Facsimile: Fonds Grothendieck–Illusie, IHÉS. The page views are loaded from its server, repo-archives.ihes.fr, and not copied here. Under its authors’ rights; for any use, archives@ihes.fr.',
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
      }}
    />
  );
}
