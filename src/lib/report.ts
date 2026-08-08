import { batchName } from './batches.ts';

/**
 * Reporting a defect in a reading.
 *
 * Everything on this site was produced by a model on a first pass, and the
 * project says so on the home page. That admission is worth nothing without a
 * way to act on it: a reader who spots a misread word is, at that moment, the
 * only person in the world who knows. The cost of telling us has to be one
 * click, or it does not happen.
 *
 * It goes to the repository's issue tracker rather than to a form of our own.
 * There is no server here to receive a form — the site is static — and an
 * issue is public, so a disputed reading stays visible next to the file it
 * disputes, which is what an apparatus is for. The URL carries a prefilled
 * title and body: the shelfmark, the batch and the edition are exactly what
 * one forgets to include, and exactly what makes a report actionable.
 */
export const REPO = 'https://github.com/Commutator-IO/grothendieck-project';

/** Raw file host for the same repository, for downloading a skill directly. */
export const RAW = 'https://raw.githubusercontent.com/Commutator-IO/grothendieck-project/main';

export interface ReportContext {
  cote: string;
  /** Absent when reporting on a whole folder rather than one batch. */
  batch?: number;
  /** The page on screen, when the reader is in the reading view. */
  page?: number;
}

export function issueUrl({ cote, batch, page }: ReportContext): string {
  const where = batch ? `${cote}, ${batchName(batch)}` : `folder ${cote}`;
  const title = `[${where}] `;

  // A template rather than an empty box. Naming the page and quoting what is
  // written are what let anyone else check the claim without reproducing the
  // reader's whole session, and people supply them when asked and rarely
  // otherwise. The pre-filled facts are the ones the page already knows.
  const body = [
    `**Folder** cote n° ${cote}`,
    batch ? `**Batch** ${batchName(batch)}` : null,
    `**Page** ${page ? page : '<which page?>'}`,
    '**Edition** transcription (`.fr`) / modernised reading (`.modern`) — delete one',
    '',
    '### What the reading says',
    '',
    '### What the page shows',
    '',
    '### Anything else',
    '',
    '---',
    `Facsimile: https://grothendieck.umontpellier.fr/${cote}.pdf`,
    'Reported from the reading view. These editions are first-pass machine work;',
    'corrections are the point of publishing them.',
  ]
    .filter((l) => l !== null)
    .join('\n');

  return `${REPO}/issues/new?title=${encodeURIComponent(title)}&body=${encodeURIComponent(body)}&labels=${encodeURIComponent('reading')}`;
}
