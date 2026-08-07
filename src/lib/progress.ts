/**
 * Transcription progress, batch by batch.
 *
 * Nothing leaves the browser. Transcription is long work, often picked up
 * months later, and the only thing one wants back on reopening the site is
 * *where I had got to*. An account would be out of all proportion to that, and
 * a synchronised file would make the site the authority over work whose
 * authority is the Git repository of transcripts.
 *
 * This has a visible consequence, stated on the method page rather than hidden:
 * what is marked here is a *claim*, not an observation. The site does not check
 * that a `.tex` file exists. A progress table one believes to be automatic and
 * which is not misleads more than it informs.
 */

const KEY = 'grothendieck.progress';

export type State = 'todo' | 'running' | 'drafted' | 'checked' | 'skipped';

export const STATES: { key: State; label: string; help: string }[] = [
  { key: 'todo', label: 'To do', help: 'Batch not opened.' },
  { key: 'running', label: 'Running', help: 'Pass launched, output not yet inspected.' },
  { key: 'drafted', label: 'Drafted', help: 'LaTeX produced, not yet held against the leaf.' },
  { key: 'checked', label: 'Checked', help: 'Compared page by page with the facsimile.' },
  {
    key: 'skipped',
    label: 'Skipped',
    help: 'Unrelated versos, separator sheets, illegible leaves — nothing to transcribe.',
  },
];

export type Progress = Record<string, State>;

export const progressKey = (cote: string, batch: number) => `${cote}#${batch}`;

export function readProgress(): Progress {
  try {
    const raw = localStorage.getItem(KEY);
    return raw ? (JSON.parse(raw) as Progress) : {};
  } catch {
    return {};
  }
}

export function writeProgress(p: Progress): void {
  try {
    localStorage.setItem(KEY, JSON.stringify(p));
  } catch {
    // Private browsing or full quota: the site stays usable, without memory.
  }
}

export function stateOf(p: Progress, cote: string, batch: number): State {
  return p[progressKey(cote, batch)] ?? 'todo';
}

/** Advances a batch one notch, and wraps — one gesture, no menu. */
export function nextState(s: State): State {
  const order: State[] = ['todo', 'running', 'drafted', 'checked', 'skipped'];
  return order[(order.indexOf(s) + 1) % order.length];
}

export interface Tally {
  total: number;
  byState: Record<State, number>;
  pagesChecked: number;
  pagesTotal: number;
}

export function tally(p: Progress, batches: { cote: string; batch: number; pages: number }[]): Tally {
  const byState: Record<State, number> = {
    todo: 0,
    running: 0,
    drafted: 0,
    checked: 0,
    skipped: 0,
  };
  let pagesChecked = 0;
  let pagesTotal = 0;
  for (const b of batches) {
    const s = stateOf(p, b.cote, b.batch);
    byState[s] += 1;
    pagesTotal += b.pages;
    if (s === 'checked') pagesChecked += b.pages;
  }
  return { total: batches.length, byState, pagesChecked, pagesTotal };
}
