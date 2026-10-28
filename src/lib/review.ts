import { batchName } from './batches.ts';
import { REPO, shortQuote } from './report.ts';

/**
 * The review page (/review/): the open checks of issue #35, one spot of a page
 * at a time, answered against the facsimile and sent back as prefilled issues.
 *
 * Nothing leaves the browser until the reader presses « Send my answers »,
 * and then only GitHub's own form opens, for the reader to submit or not.
 */

export type ReviewKind = 'ill' | 'uncertain' | 'add' | 'supplied' | 'date' | 'letter' | 'argument' | 'reference' | 'hypothesis' | 'imprecise' | 'unproved' | 'paper' | 'quoted';

export interface ReviewItem {
  id: string;
  /** The heading of #35 the item comes from. */
  section: string;
  kind: ReviewKind;
  cote: string;
  batch: number;
  page: number | null;
  /** The question put to the reader, in one plain sentence. */
  prompt: string;
  /** Where on the facsimile (or in the reading) to look. */
  hint: string;
  /** The answers offered as buttons; « Can't tell » and « Skip » are always there. */
  choices: Choice[];
  /** A letter's register entry, as the reading to check: [field, value]. */
  entry: [string, string][] | null;
  /** The edition's own argument or references, for the mathematicians. */
  claim: string | null;
  /** #35's own wording of the check. */
  details: string | null;
  context: string | null;
  /** The reading view at that page, on this site. */
  link: string;
}

/** The current reading: at most fifteen words, the doubtful one apart. */
export interface Snippet {
  before: string;
  word: string;
  after: string;
  glueBefore?: boolean;
  glueAfter?: boolean;
}

export type Verdict = 'right' | 'other' | 'illegible' | 'skip';

/** One answer offered as a button: `ask` opens a field for the reader's words. */
export interface Choice {
  value: string;
  verdict: Verdict;
  ask?: string;
}

export interface Answer {
  verdict: Verdict;
  /** The button chosen (a page, « Not a letter » …); absent in answers saved before the choices. */
  choice?: string;
  /** What the reader reads instead, for « other ». */
  reading?: string;
  note?: string;
  date: string;
}

export const VERDICT_NAME: Record<Verdict, string> = {
  right: 'Reading is right',
  other: 'I read something else',
  illegible: "Can't tell / illegible",
  skip: 'Skipped',
};

/** Questions about the mathematics rather than the ink: a section of their own. */
export const isMaths = (k: ReviewKind) => k === 'argument' || k === 'reference' || k === 'hypothesis';

/** What an answer says, in words: the button chosen, else the verdict. */
export function answerName(it: ReviewItem, a: Answer): string {
  if (a.choice) return a.choice;
  if (a.verdict === 'skip') return VERDICT_NAME.skip;
  return it.choices.find((c) => c.verdict === a.verdict)?.value ?? (a.verdict === 'illegible' ? "Can't tell" : VERDICT_NAME[a.verdict]);
}

const KEY = 'gn-review:35';

export function loadAnswers(): Record<string, Answer> {
  try {
    const v = JSON.parse(localStorage.getItem(KEY) || '{}');
    return v && typeof v === 'object' && !Array.isArray(v) ? v : {};
  } catch {
    return {};
  }
}

export function saveAnswers(a: Record<string, Answer>) {
  try {
    if (Object.keys(a).length) localStorage.setItem(KEY, JSON.stringify(a));
    else localStorage.removeItem(KEY);
  } catch {
    /* private mode, storage full: the answers live as long as the tab */
  }
}

const SITE = 'https://grothendieck.commutator.io';

/** French quotation marks as plain ones, for the Markdown of an issue. */
const plain = (s: string) => s.replace(/«\s*/g, '"').replace(/\s*»/g, '"');

/** One answer as a Markdown list item. A proposed reading is cut to fifteen words. */
export function answerLine(it: ReviewItem, a: Answer): string {
  const where = [`folder ${it.cote}`, batchName(it.batch), it.page ? `p. ${it.page}` : null].filter(Boolean).join(', ');
  const parts = [`- \`${it.id}\` — ${where} — **${plain(answerName(it, a))}**`];
  if (a.reading?.trim()) parts.push(`: « ${plain(shortQuote(a.reading, 15))} »`);
  const lines = [parts.join(''), `  - Asked: ${plain(it.prompt)}`];
  if (a.note?.trim()) lines.push(`  - Note: ${a.note.trim().replace(/\s*\n\s*/g, ' ')}`);
  lines.push(`  - ${SITE}/review/#${it.id}`);
  return lines.join('\n');
}

const HEAD = (n: number) =>
  [
    `Answers from the review page (${SITE}/review/) to #35, checked against Montpellier's facsimile.`,
    `${n} answer${n === 1 ? '' : 's'}. Each line: item, folder, batch, page, the answer chosen (a page, a verdict), the reading proposed (fifteen words at most), then the question asked and the reader's note.`,
    '',
  ].join('\n');

const FOOT = '\n\n---\nSent from /review/. Nothing here changes a transcription until someone applies it with a `\\note{}` (see #35).';

/** The whole answer set as Markdown, for « Copy as Markdown ». */
export function answersMarkdown(entries: [ReviewItem, Answer][]): string {
  return `${HEAD(entries.length)}\n${entries.map(([it, a]) => answerLine(it, a)).join('\n')}${FOOT}`;
}

/** GitHub refuses long URLs (about 8 000 characters); stay well under. */
export const URL_BUDGET = 7500;

function url(title: string, body: string) {
  return `${REPO}/issues/new?title=${encodeURIComponent(title)}&body=${encodeURIComponent(body)}&labels=${encodeURIComponent('reading')}`;
}

/**
 * The answers as one or more prefilled issues, each URL under the budget.
 * An answer too long for an issue on its own (a very long note) is cut.
 */
export function answerIssues(entries: [ReviewItem, Answer][]): { title: string; url: string; count: number }[] {
  const groups: string[][] = [];
  let cur: string[] = [];
  const fits = (ls: string[]) => url(`[review #35] ${ls.length} answers (part 10/10)`, `${HEAD(ls.length)}\n${ls.join('\n')}${FOOT}`).length <= URL_BUDGET;
  for (const [it, a] of entries) {
    let line = answerLine(it, a);
    while (!fits([line]) && line.length > 200) line = `${line.slice(0, Math.floor(line.length * 0.8))} …`;
    if (cur.length && !fits([...cur, line])) {
      groups.push(cur);
      cur = [];
    }
    cur.push(line);
  }
  if (cur.length) groups.push(cur);
  return groups.map((ls, i) => {
    const title = `[review #35] ${ls.length} answer${ls.length === 1 ? '' : 's'}${groups.length > 1 ? ` (part ${i + 1}/${groups.length})` : ''}`;
    return { title, count: ls.length, url: url(title, `${HEAD(ls.length)}\n${ls.join('\n')}${FOOT}`) };
  });
}
