/**
 * Writing times from the chalk (#109), shared by the blackboards and the index of results.
 *
 * computations/buffalo-chalk/taps.json lists chalk-tap candidates per tape side, in seconds of
 * the video. Taps 4 s apart or less form a burst of writing; a burst needs three taps. A
 * statement spoken at `t` is given `w`, the start of the burst nearest to `t` among those from
 * 20 s before to 10 s after it, so that it is shown, or played, when the chalk moves rather than
 * when the words come. Statements with no burst nearby keep `t` alone, and `w` never goes
 * backwards from one statement to the next.
 */
import { existsSync, readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const tapsPath = resolve(import.meta.dirname, '../../computations/buffalo-chalk/taps.json');

/** Burst starts per video id, sorted. Empty if taps.json is absent. */
export function burstsByVideo() {
  const taps = new Map();
  if (!existsSync(tapsPath)) return taps;
  for (const s of JSON.parse(readFileSync(tapsPath, 'utf8')).sides) {
    if (!taps.has(s.video)) taps.set(s.video, []);
    taps.get(s.video).push(...s.taps);
  }
  const out = new Map();
  for (const [v, ts] of taps) {
    ts.sort((a, b) => a - b);
    const starts = [];
    let i = 0;
    while (i < ts.length) {
      let j = i;
      while (j + 1 < ts.length && ts[j + 1] - ts[j] <= 4) j++;
      if (j - i + 1 >= 3) starts.push(ts[i]);
      i = j + 1;
    }
    out.set(v, starts);
  }
  return out;
}

/**
 * Sets `w` on each of `items` (objects with a spoken time `t`, in order, all from one video)
 * from the burst starts of that video; removes a stale `w`. Returns how many were timed.
 */
export function setWritingTimes(items, starts) {
  let last = -Infinity;
  let n = 0;
  for (const item of items) {
    delete item.w;
    if (!starts) continue;
    const near = starts.filter((s) => s >= item.t - 20 && s <= item.t + 10 && s >= last);
    if (!near.length) continue;
    const best = near.reduce((a, b) => (Math.abs(b - item.t) < Math.abs(a - item.t) ? b : a));
    item.w = Math.round(best);
    last = best;
    n++;
  }
  return n;
}
