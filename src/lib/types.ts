/**
 * A *cote* — the archive's own unit of classification, one cardboard folder as
 * Grothendieck left it, digitised into a single PDF.
 */
export interface Cote {
  /** `19`, `140-2`, `156-9` — the shelfmark, which is also the PDF's filename. */
  id: string;
  file: string;
  /** The archivists' proposed dating, brackets included. */
  date: string;
  /** Grothendieck's own title; in [brackets] when the archivists supplied one. */
  title: string;
  /** Leaf count as the inventory gives it — excluding the PDF's generated cover. */
  pages: number;
  depth: number;
  group: string | null;
}

/** A thematic grouping from the Montpellier inventory. */
export interface ArchiveGroup {
  id: string;
  title: string;
  date: string;
  cotes: string[];
}

/**
 * A *book* — this site's unit of reading.
 *
 * The inventory files by folder. One reads otherwise: along a thread — topoi,
 * motives, the Long March — that crosses several folders and sometimes stops
 * halfway through one. A book names that thread and says where it comes from,
 * which is the only honest way to regroup: `inventoryGroup` points at the
 * archive's own group when there is one, and is `null` when the grouping is
 * ours.
 */
export interface Book {
  key: BookKey;
  path: string;
  title: string;
  /** One line: what this book is about, and why these folders. */
  subtitle: string;
  period: string;
  inventoryGroup: string | null;
  /** What was kept and on whose authority — printed at the top of the page. */
  rationale: string;
  sections: BookSection[];
}

export interface BookSection {
  title: string;
  /** What this section holds, and what to know before entering it. */
  intro: string;
  cotes: string[];
}

export type BookKey = 'topos' | 'motives' | 'long-march' | 'late';

/** Which language and register a transcript artifact is written in. */
export type Edition = 'fr' | 'en' | 'summary';

/** Everything present locally, written by `npm run archive` and `npm run manifest`. */
export interface Manifest {
  /** Pages per batch; twenty, because that is one transcription pass. */
  batchSize: number;
  generated: string;
  /** Facsimile batches available under `public/batches/`. */
  facsimiles: Record<string, { pdfPages: number; batches: number[] }>;
  /** Transcript artifacts available under `public/transcripts/`. */
  transcripts: Record<string, TranscriptEntry>;
}

/** Keyed by `<cote>#<batch>`. */
export interface TranscriptEntry {
  /** Editions that have a rendered HTML reading view. */
  html: Edition[];
  /** Editions that have a downloadable LaTeX source. */
  tex: Edition[];
  /** Editions that have a compiled PDF. */
  pdf: Edition[];
}
