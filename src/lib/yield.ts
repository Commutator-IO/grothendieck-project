import { batchCount } from './batches.ts';
import type { Cote, Manifest } from './types.ts';

/**
 * How much of a folder is actually transcribable.
 *
 * The inventory counts sheets. A transcription counts mathematics, and the two
 * are never the same number: Grothendieck wrote on the back of whatever was to
 * hand — USTL letters, offprints, typescripts his secretary had returned — and
 * those pages are skipped rather than transcribed. The archive's own note is
 * blunt about it: "the reverse pages of the documents are often unrelated to
 * the mathematical notes."
 *
 * So "165 folders, 15,816 pages left" overstates the work, and by an amount
 * nobody knows before opening a folder. This module estimates it — badly, but
 * from evidence rather than from nothing, and it says which of the two it is
 * doing on every folder.
 */

/** What a folder's page count is worth, and how much that figure is worth. */
export interface Yield {
  /** Transcribable share of the inventory's pages, 0–1. */
  rate: number;
  /** Pages expected to carry mathematics. */
  pages: number;
  /** `measured` is counted from the transcription; `predicted` is the model. */
  basis: 'measured' | 'predicted';
  /** Why the model said what it said — shown, never hidden in a tooltip. */
  reason: string;
}

/**
 * The model, such as it is, fitted by eye on the thirteen folders transcribed
 * so far — 231 of 263 inventory pages, 88% overall.
 *
 * That average hides the only pattern in the data, which is size. The nine
 * folders of ten pages or fewer all came out at 100%: a five-page folder is one
 * sheaf on one subject, with no room for filler. The five larger ones ran 74%
 * to 92%, mean 83% — long folders accumulate versos, separator sheets and
 * returned typescript. Two coefficients, and both of them are honest about
 * resting on five observations.
 *
 * The second signal is the inventory title, which names what a folder holds.
 * « tapuscrit », « tirés à part », « lettres », « copies » are not handwriting,
 * and a folder announcing them is either denser than a manuscript folder (a
 * typescript has no blank versos) or almost entirely outside what this project
 * transcribes. The adjustment is deliberately small: folder 108, catalogued
 * « Divers », turned out to be seventeen questions on test categories, and the
 * lesson of that was that inventory titles are weak evidence.
 */
const SMALL_RATE = 1.0;
const LARGE_RATE = 0.83;

export function predictYield(c: Cote, manifest: Manifest | null): Yield {
  const measured = manifest?.read?.[c.id];
  if (measured !== undefined && measured > 0) {
    return {
      rate: measured / c.pages,
      pages: measured,
      basis: 'measured',
      reason: `${measured} of ${c.pages} pages carried mathematics`,
    };
  }

  const t = c.title.toLowerCase();
  const typed = /tapuscrit|tirés? à part|copies de tapuscrit/.test(t);
  const letters = /lettres?|correspondance|courrier/.test(t);
  const hand = /notes? manuscrites?|notes et copies de notes/.test(t);

  let rate = c.pages <= 10 ? SMALL_RATE : LARGE_RATE;
  let reason =
    c.pages <= 10
      ? 'short folder — the nine already done at this size all ran to 100%'
      : 'long folder — the five already done at this size averaged 83%';

  // A folder that announces typescript and no hand is read differently: little
  // is skipped, but little of it is manuscript either. Both facts are said.
  if (typed && !hand) {
    rate = 0.95;
    reason = 'typescript rather than a hand — dense, but not handwriting';
  } else if (letters && !hand) {
    rate = 0.9;
    reason = 'correspondence rather than mathematics';
  } else if (typed && hand) {
    rate = Math.min(rate + 0.05, 0.95);
    reason += ', with typescript alongside the notes';
  }

  return { rate, pages: Math.round(c.pages * rate), basis: 'predicted', reason };
}

/** Status of a folder in one word, which is what the mosaic colours. */
export type FolderState = 'here' | 'community' | 'priority' | 'untouched';

/**
 * Which unopened folders are worth opening next, and why.
 *
 * Straight out of the two issues that worked the arithmetic — #12 on the
 * folders that fit one pass, #15 on the ones that need ten or more. Neither
 * concluded that any group can be finished; both concluded that a handful of
 * short folders move a group a long way for very little. Those are what this
 * marks, and the reason travels with the mark so nobody has to take it on
 * trust.
 *
 * Deliberately not a ranking of interest. Size and position in a group are the
 * only axes here; whether a folder holds anything worth reading is exactly what
 * no one knows until it is read.
 */
export const PRIORITY: Record<string, string> = {
  // 150-151 « Espaces stratifiés »: three short passes, 32 pages, take the
  // group from 1/6 to 4/6 and leave it two folders from done. Best ratio in
  // the fonds.
  '153': 'one pass · takes Espaces stratifiés to 4 of 6',
  '155': 'one pass · takes Espaces stratifiés to 4 of 6',
  '152': 'one pass · takes Espaces stratifiés to 4 of 6',
  // 103-118 « Autour de Pursuing stacks »: the group this site is deepest in,
  // and the one whose remainder is smallest. 114 is done; these sit beside it.
  '116': 'one pass · beside 114 and 115, already read',
  '113': 'one pass · Pursuing stacks years',
  '104': 'one pass · Pursuing stacks years',
  '106': 'one pass · Pursuing stacks years',
  // 45-54 « Variétés abéliennes »: six one-batch folders, more than any group
  // but 103-118.
  '54': 'one pass · six short folders open this group',
  '49': 'one pass · six short folders open this group',
  '47': 'one pass · six short folders open this group',
  '50': 'one pass · six short folders open this group',
  '52': 'one pass · six short folders open this group',
  '55': 'one pass · six short folders open this group',
};

export function folderState(
  c: Cote,
  transcribedHere: boolean,
  hasEdition: boolean,
): FolderState {
  if (transcribedHere) return 'here';
  if (hasEdition) return 'community';
  if (PRIORITY[c.id]) return 'priority';
  return 'untouched';
}

/** Batches a folder still needs, given what is transcribed. */
export const batchesLeft = (c: Cote, done: number) => Math.max(0, batchCount(c.pages) - done);
