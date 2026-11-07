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
import { existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const root = resolve(import.meta.dirname, '..');
const src = resolve(root, 'transcripts-buffalo');
const out = resolve(root, 'public/buffalo-boards');
mkdirSync(out, { recursive: true });

/**
 * Writing times from the chalk (#109). computations/buffalo-chalk/taps.json lists chalk-tap
 * candidates per tape side, in seconds of the video. Taps 4 s apart or less form a burst of
 * writing; a burst needs three taps. An item gets `w`, the start of the burst nearest to its
 * spoken time `t` among those starting from 20 s before to 10 s after it, so the board shows the
 * item when the chalk moves rather than when the words come. Items with no burst nearby keep
 * `t`, and `w` never goes backwards from one item to the next.
 */
const tapsPath = resolve(root, 'computations/buffalo-chalk/taps.json');
const taps = new Map();
if (existsSync(tapsPath)) {
  for (const s of JSON.parse(readFileSync(tapsPath, 'utf8')).sides) {
    if (!taps.has(s.video)) taps.set(s.video, []);
    taps.get(s.video).push(...s.taps);
  }
  for (const v of taps.values()) v.sort((a, b) => a - b);
}
function bursts(ts) {
  const out = [];
  let i = 0;
  while (i < ts.length) {
    let j = i;
    while (j + 1 < ts.length && ts[j + 1] - ts[j] <= 4) j++;
    if (j - i + 1 >= 3) out.push(ts[i]);
    i = j + 1;
  }
  return out;
}
function writingTimes(board) {
  const all = taps.get(board.video);
  if (!all) return 0;
  const starts = bursts(all.filter((x) => x >= board.start - 20 && x <= board.end + 10));
  let last = -Infinity;
  let n = 0;
  for (const item of board.items) {
    const near = starts.filter((s) => s >= item.t - 20 && s <= item.t + 10 && s >= last);
    delete item.w;
    if (near.length) {
      const best = near.reduce((a, b) => (Math.abs(b - item.t) < Math.abs(a - item.t) ? b : a));
      item.w = Math.round(best);
      last = best;
      n++;
    }
  }
  return n;
}

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
