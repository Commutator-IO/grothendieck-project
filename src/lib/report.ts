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

/**
 * Where a comment was made: a passage of a reading, a finding, a Lean proof
 * card, a proposed dating. The reading view knows the shelfmark, batch,
 * edition and nearest page marker; the Findings and Timeline pages know the
 * entry's identifier.
 */
export interface CommentContext {
  /** What the passage belongs to, for the title and the notes list. */
  label: string;
  cote?: string;
  batch?: number;
  page?: number;
  edition?: 'fr' | 'modern';
  /** A finding id, a Lean file, a folder whose dating is proposed. */
  ref?: string;
  kind: 'reading' | 'finding' | 'plain' | 'proof' | 'dating' | 'leaf' | 'letter';
  /** Lines the location needs beyond the shelfmark: the evidence of a dating, a letter's date and place. */
  details?: string[];
  /** A link back to the place, on this site. */
  link?: string;
}

/** Words of a selection that may go into a public issue for each kind. */
export const QUOTE_WORDS: Record<CommentContext['kind'], number> = {
  // The transcriptions and modernised readings are under a rights hold (#31):
  // an issue is public, so it cites the passage and points at it rather than
  // copying it. The full selection stays in the reader's own browser.
  reading: 15,
  // The project's own text: a longer quote is what lets a maintainer act.
  finding: 120,
  plain: 120,
  proof: 120,
  dating: 120,
  leaf: 120,
  // Letters to and from him are the correspondents' and his text, not ours.
  letter: 15,
};

/** At most `words` words of `text`, cut with « … ». */
export function shortQuote(text: string, words: number): string {
  const w = text.replace(/\s+/g, ' ').trim().split(' ');
  return w.length > words ? `${w.slice(0, words).join(' ')} …` : w.join(' ');
}

const KIND_NAME: Record<CommentContext['kind'], string> = {
  reading: 'Reading',
  finding: 'Finding',
  plain: 'In plain words',
  proof: 'Lean proof',
  dating: 'Proposed dating',
  leaf: 'Date on a leaf',
  letter: 'Letter',
};

const EDITION_NAME = { fr: 'transcription (`.fr`)', modern: 'modernised reading (`.modern`)' } as const;

/** A prefilled issue for one comment: the location, a short quote, the comment. */
export function commentIssueUrl(ctx: CommentContext, quote: string, comment: string): string {
  const where = ctx.cote
    ? ctx.batch && ctx.edition !== 'modern'
      ? `${ctx.cote}, ${batchName(ctx.batch)}`
      : `folder ${ctx.cote}`
    : ctx.label;
  const first = comment.split('\n')[0].trim();
  const title = `[${ctx.kind === 'reading' ? where : `${ctx.kind} ${ctx.ref ?? where}`}] ${
    first ? first.slice(0, 90) : `Comment on « ${shortQuote(quote, 6)} »`
  }`;
  const q = shortQuote(quote, QUOTE_WORDS[ctx.kind]);
  const body = [
    ctx.cote ? `**Folder** cote n° ${ctx.cote}` : null,
    ctx.batch && ctx.edition !== 'modern' ? `**Batch** ${batchName(ctx.batch)}` : null,
    ctx.edition ? `**Edition** ${EDITION_NAME[ctx.edition]}` : null,
    ctx.cote && (ctx.page || ctx.kind === 'reading') ? `**Page** ${ctx.page ?? '<which page?>'}` : null,
    ctx.kind !== 'reading' ? `**${KIND_NAME[ctx.kind]}** ${ctx.ref ? `\`${ctx.ref}\` — ` : ''}${ctx.label}` : null,
    ...(ctx.details ?? []),
    ctx.link ? `**Where** ${ctx.link}` : null,
    '',
    q ? `> ${q}` : null,
    '',
    '### Comment',
    '',
    comment.trim() || '<what is wrong, or what you read instead>',
    '',
    '---',
    ctx.cote ? `Facsimile: https://grothendieck.umontpellier.fr/${ctx.cote}.pdf` : null,
    ctx.kind === 'reading'
      ? 'Sent from a comment on the reading view. The quote is cut short on purpose: the readings are not reproduced in issues.'
      : 'Sent from a comment on the site.',
  ]
    .filter((l) => l !== null)
    .join('\n');
  const labels = ctx.kind === 'reading' ? `&labels=${encodeURIComponent('reading')}` : '';
  return `${REPO}/issues/new?title=${encodeURIComponent(title.slice(0, 140))}&body=${encodeURIComponent(body)}${labels}`;
}
