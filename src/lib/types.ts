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
  /** Page count as the inventory gives it — excluding the PDF's generated cover. */
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
  /**
   * A shorter label for the header, where the full title will not fit.
   *
   * The menu holds every notebook plus two standing pages, and at the `lg`
   * breakpoint that is already tight: one long title pushes the row into a
   * second line or clips it. Falls back to `title`.
   */
  navTitle?: string;
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

export type BookKey = 'topos' | 'motives' | 'long-march' | 'late' | 'scattered';

/**
 * Which register a transcript artifact is written in.
 *
 * Two, and the order is the order of distance from the page: the
 * transcription is what is on the paper; `modern` is a reading of it in
 * today's mathematics, opening with a summary that orients someone who
 * has not met the subject.
 *
 * Both are in French. Grothendieck wrote in French and the notions were
 * thought in French; a translation was one more artifact to keep in step for
 * no gain, and a standalone summary was a third file saying what the
 * modernised reading's first page now says in place.
 */
export type Edition = 'fr' | 'modern';

/** Everything present locally, written by `npm run archive` and `npm run manifest`. */
export interface Manifest {
  /** Pages per batch; twenty, because that is one transcription pass. */
  batchSize: number;
  generated: string;
  /** Facsimile batches available under `public/batches/`. */
  facsimiles: Record<string, { pdfPages: number; batches: number[] }>;
  /** Transcript artifacts available under `public/transcripts/`. */
  transcripts: Record<string, TranscriptEntry>;
  /**
   * Artifacts whose unit is the folder rather than the batch, keyed by cote.
   *
   * The modernised reading takes the folder whole — that is the unit its
   * argument runs in, and folder 161-3's threads cross the batch boundaries in
   * both directions — so it is written as one `folder.modern.tex` covering
   * every page. It applies to every batch of its folder, and the reading panes
   * offer it against whichever batch is open.
   */
  folders?: Record<string, TranscriptEntry>;
  /**
   * States that had to be declared, from `transcripts/status.json`.
   *
   * Keyed `<folder>#<batch>`. Only the three no file can prove; the rest are
   * read off the files themselves.
   */
  declared: Record<string, 'running' | 'checked' | 'skipped'>;
  /**
   * Modern-vocabulary tags per folder, extracted from the `\keywords{}` line
   * each modernised reading carries at the end of its résumé. English on
   * purpose — they are search keys into today's literature. A folder appears
   * here only once something of it has been modernised: the tags have no
   * other source, so they can never describe unread content.
   */
  tags?: Record<string, string[]>;
  /**
   * Pages actually transcribed per folder, counted from the `\page{N}` marks.
   *
   * Always at most the inventory's page count, and usually below it: a page
   * carrying no mathematics is skipped, and the gap in the numbering is the
   * only record that it was. The ratio of the two is what lets the archive page
   * say how much of an unopened folder is likely to be readable at all.
   */
  read?: Record<string, number>;
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

/**
 * An existing edition of part of the fonds, by the mathematical community.
 *
 * This is the one place in the project where our data makes a claim the
 * archive does not. Montpellier's inventory numbers folders; the editions
 * name works — and the two vocabularies were never reconciled by anyone. None
 * of the editors publishes a shelfmark. So the `cotes` field is *our*
 * correspondence, and `mapping` says how far to trust it. Presenting a guess
 * as a fact here would be worse than saying nothing: someone would cite it.
 */
export interface PublishedEdition {
  id: string;
  title: string;
  editors: string;
  year: string;
  venue: string;
  url: string;
  /** `published` in print · `transcribed` into LaTeX · `partial` coverage. */
  kind: 'published' | 'transcribed' | 'partial';
  /** Folders this edition covers, as far as we can establish. */
  cotes: string[];
  /** How far the shelfmark correspondence can be trusted. */
  mapping: 'certain' | 'likely' | 'unmapped';
  note: string;
}

/**
 * A candidate novelty: something a folder establishes that may not stand in
 * the published literature.
 *
 * The central point of the shape is that a novelty is a claim about the
 * *literature*, never about Grothendieck. The manuscript can be read; the
 * literature can only be searched, and never exhausted. So every entry carries
 * what was searched (`literature`) and how far it got (`status`), and none of
 * them may say who was first — almost nothing in the fonds is dated, and the
 * inventory's « [vers 1963-1973] » is an archivist's guess from a verso.
 *
 * `ours` is the field that keeps the edition honest. The modernised reading
 * supplies hypotheses the page leaves implicit and completes steps it skips;
 * where it did, the novelty is partly ours and not the manuscript's, and
 * hiding that would be claiming a novelty for a sentence nobody wrote.
 */
export interface Finding {
  id: string;
  cote: string;
  /** The pages the claim rests on, as the inventory numbers them. */
  pages: string;
  /**
   * `mathematical` claims are about the literature and carry the real risk;
   * `codicological` ones are about this object — leaves bound out of order,
   * two manuscripts interleaved — and can be settled by looking.
   */
  kind: 'mathematical' | 'codicological';
  /** One sentence: what the folder establishes. */
  claim: string;
  /** What in the folder supports it. */
  basis: string;
  /** What the edition supplied rather than the page — null when the page carries it alone. */
  ours: string | null;
  /** Sources actually searched, by name and section. Empty means nobody looked. */
  literature: string[];
  /**
   * `unsearched` nobody looked it up · `candidate` searched, not found ·
   * `matched` found in the literature, kept as a killed candidate ·
   * `confirmed` a person checked it. Only a person may set the last.
   */
  status: 'unsearched' | 'candidate' | 'matched' | 'confirmed';
  /** The one check that would decide it. */
  settle: string;
}
