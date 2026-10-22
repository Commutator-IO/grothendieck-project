import { batchesOf, ReadingView } from './ReadingView.tsx';
import { batchName, useManifest } from '../lib/batches.ts';

/**
 * The reading view of one of Quillen's notebooks: the transcription of a batch
 * on the left, the Clay's PDF in the shared facsimile pane on the right at the
 * page being read — the layout of the Montpellier folders, made of the same
 * parts (ReadingView). The transcription is rendered from
 * `transcripts-quillen/<label>/batch-NN.en.tex` by scripts/render.mjs
 * (`--quillen`) into public/transcripts-quillen/.
 *
 * The notebooks are in copyright (#36): transcripts-quillen/ is git-ignored and
 * exists only on the machine that transcribed them. This module is imported
 * only by the dev server and by a build made with RENDER_QUILLEN; and even
 * such a build, in CI, has no transcription to show and says so.
 */

export interface QuillenNotebook {
  id: string;
  label: string;
  url: string;
  pages: number | null;
}

export function QuillenReader({
  nb,
  heading,
  batch,
  page,
  onBatch,
  onPage,
  onClose,
}: {
  nb: QuillenNotebook;
  /** The year or group, as the page labels it. */
  heading: string;
  batch: number;
  page?: number;
  onBatch: (batch: number) => void;
  onPage: (page: number) => void;
  onClose: () => void;
}) {
  const manifest = useManifest();
  const transcribed = batchesOf(manifest?.quillen, nb.label, 'en');
  const pages = nb.pages ?? 0;

  return (
    <ReadingView
      label={`Notebook ${nb.label}`}
      batch={batch}
      page={page}
      pages={pages}
      url={`/transcripts-quillen/${nb.label}/${batchName(batch)}.en.html`}
      present={transcribed.includes(batch)}
      transcribed={transcribed}
      texPath={`transcripts-quillen/${nb.label}/${batchName(batch)}.en.tex`}
      noun="notebook"
      link={{ href: nb.url, text: 'Clay ↗' }}
      onBatch={onBatch}
      onPage={onPage}
      onClose={onClose}
      facsimile={{
        cote: nb.id,
        title: `Notebook ${nb.label}`,
        date: heading,
        batch,
        pages,
        relay: 'ready',
        source: {
          file: nb.url,
          original: nb.url,
          heading: `Daniel Quillen · ${heading}`,
          credit: 'Facsimile: Clay Mathematics Institute, served from claymath.org, not copied here.',
          pageOffset: 0,
        },
      }}
    />
  );
}
