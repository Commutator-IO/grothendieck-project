import { batchesOf, ReadingView } from './ReadingView.tsx';
import { batchName, useManifest } from '../lib/batches.ts';

/**
 * The reading view of a document of the Bourbaki archive: the transcription
 * of a batch on the left, the AHP's scan in the shared facsimile pane on the
 * right at the page being read — the layout of the Montpellier folders, made
 * of the same parts (ReadingView). The transcription is rendered from
 * `transcripts-bourbaki/<folder>/batch-NN.fr.tex` by scripts/render.mjs
 * (`--bourbaki`); the folder is the rédaction's number (`457`, `383bis`) or
 * `item-<id>`, and the manifest maps the AHP record to it (`bourbakiItems`).
 *
 * The transcriptions stay local until the AHP and the ACNB agree (#50):
 * transcripts-bourbaki/ is git-ignored. This module is imported only by the
 * dev server and by a build made with RENDER_BOURBAKI; and even such a build,
 * in CI, has no transcription to show and says so.
 */

export interface BourbakiDoc {
  id: number;
  title: string;
  number: number | null;
  date: string | null;
  identifier: string | null;
  type: string;
  pages: string | null;
  url: string;
  pdf: string | null;
}

export function BourbakiReader({
  doc,
  batch,
  page,
  onBatch,
  onPage,
  onClose,
}: {
  doc: BourbakiDoc;
  batch: number;
  page?: number;
  onBatch: (batch: number) => void;
  onPage: (page: number) => void;
  onClose: () => void;
}) {
  const manifest = useManifest();
  const folder = manifest?.bourbakiItems?.[String(doc.id)];
  const transcribed = folder ? batchesOf(manifest?.bourbaki, folder, 'fr') : [];
  const pages = Number.parseInt(doc.pages ?? '', 10) || 0;
  // Where a first transcription would go, by the skill's naming.
  const dir = folder ?? (doc.number != null ? String(doc.number) : `item-${doc.id}`);

  return (
    <ReadingView
      label={doc.number != null ? `Rédaction n° ${doc.number}` : `AHP item ${doc.id}`}
      title={doc.title}
      batch={batch}
      page={page}
      pages={pages}
      url={`/transcripts-bourbaki/${dir}/${batchName(batch)}.fr.html`}
      present={transcribed.includes(batch)}
      transcribed={transcribed}
      texPath={`transcripts-bourbaki/${dir}/${batchName(batch)}.fr.tex`}
      noun="document"
      link={{ href: doc.url, text: 'AHP ↗' }}
      onBatch={onBatch}
      onPage={onPage}
      onClose={onClose}
      facsimile={{
        cote: String(doc.id),
        title: doc.title,
        date: doc.date ?? 's.d.',
        batch,
        pages,
        relay: 'ready',
        source: {
          file: doc.pdf ?? '',
          original: doc.pdf ?? doc.url,
          heading: `Bourbaki · ${doc.identifier ?? doc.type} · ${doc.date ?? 's.d.'}`,
          credit:
            'Facsimile: Archives Henri Poincaré (ACNB), served from archives-bourbaki.ahp-numerique.fr, not copied here.',
          pageOffset: 0,
        },
      }}
    />
  );
}
