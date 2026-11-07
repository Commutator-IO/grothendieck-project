#!/usr/bin/env node
/**
 * Publishes the reconstructed Buffalo blackboards (Michel, 1 November 2026).
 *
 *   npm run buffalo-boards
 *
 * The boards are written in the git-ignored transcripts-buffalo/ beside the transcripts they are
 * drawn from; only the boards are copied, to public/buffalo-boards/, where the Buffalo tab loads
 * them. A board is a note of what the lecturer writes, never the transcript itself, so the
 * « Local only » clause of its note is replaced by the publication's.
 */
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { burstsByVideo, setWritingTimes } from './lib/chalk.mjs';

const root = resolve(import.meta.dirname, '..');
const src = resolve(root, 'transcripts-buffalo');
const out = resolve(root, 'public/buffalo-boards');
mkdirSync(out, { recursive: true });

// Writing times from the chalk (#109): see scripts/lib/chalk.mjs.
const bursts = burstsByVideo();
const writingTimes = (board) => setWritingTimes(board.items, bursts.get(board.video));

let n = 0;
let timed = 0;
let total = 0;
/**
 * `--times` re-times the published boards in place and touches nothing else: the board checks
 * correct items in public/buffalo-boards directly, and a full regeneration from
 * transcripts-buffalo would undo those corrections.
 */
if (process.argv.includes('--times')) {
  for (const f of readdirSync(out)) {
    if (!/^[\w-]{11}-\d+\.json$/.test(f)) continue;
    const b = JSON.parse(readFileSync(resolve(out, f), 'utf8'));
    timed += writingTimes(b);
    total += b.items.length;
    writeFileSync(resolve(out, f), JSON.stringify(b));
    n++;
  }
  console.log(`${n} published boards re-timed; ${timed} of ${total} items timed by the chalk`);
  process.exit(0);
}
for (const f of readdirSync(src)) {
  if (!/^[\w-]{11}-\d+\.json$/.test(f)) continue;
  const b = JSON.parse(readFileSync(resolve(src, f), 'utf8'));
  b.$why = b.$why.replace(/\s*Local only.*$/s, ' Published with the index of results; the transcript stays local.');
  timed += writingTimes(b);
  total += b.items.length;
  writeFileSync(resolve(out, f), JSON.stringify(b));
  n++;
}
console.log(`${n} boards → public/buffalo-boards/; ${timed} of ${total} items timed by the chalk`);
