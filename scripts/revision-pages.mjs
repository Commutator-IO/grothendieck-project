#!/usr/bin/env node
/**
 * Which pages have already been read again on the facsimile (#145)?
 *
 *   npm run revised -- 79 19 20 67 188     what the registry holds for these pages
 *   npm run revised -- 79                  every pass recorded for the folder
 *   npm run revised -- --todo 79 19 20 67  only the pages with no pass of scope
 *                                          "statements", "full" or "blind"
 *
 * The registry is docs/review/revision-145/pages.json. A revision pass adds its
 * pages there; a new pass starts from `--todo`, so that a page is not read
 * twice at the same depth. "flags" (only the \uncertain and \ill places were
 * looked at) does not count as read: the page still wants a comparison.
 */
import { readFileSync } from 'node:fs';

const file = new URL('../docs/review/revision-145/pages.json', import.meta.url);
const { entries } = JSON.parse(readFileSync(file, 'utf8'));

const expand = (s) =>
  s === 'all'
    ? null
    : s.split(',').flatMap((part) => {
        const [a, b] = part.trim().split(/[-–]/).map(Number);
        return Array.from({ length: (b ?? a) - a + 1 }, (_, i) => a + i);
      });

const args = process.argv.slice(2);
const todo = args[0] === '--todo';
if (todo) args.shift();
const [cote, ...rest] = args;
if (!cote) {
  console.error('usage: npm run revised -- [--todo] <cote> [pages…]');
  process.exit(1);
}
const mine = entries.filter((e) => e.cote === cote);
const deep = new Set(['statements', 'full', 'blind']);

if (rest.length === 0) {
  for (const e of mine) console.log(`batch ${e.batch}  pp. ${e.pages}  ${e.scope}  ${e.date}  ${e.model}  (${e.source})`);
  if (mine.length === 0) console.log(`folder ${cote}: nothing recorded`);
  process.exit(0);
}

// A whole-batch entry ("all") needs the batch of the page: read it from the transcription.
const batchOf = (page) => {
  for (const e of mine.filter((x) => x.pages === 'all')) {
    const n = String(e.batch).padStart(2, '0');
    try {
      const tex = readFileSync(new URL(`../transcripts/${cote}/batch-${n}.fr.tex`, import.meta.url), 'utf8');
      if (tex.includes(`\\page{${page}}`)) return e.batch;
    } catch { /* batch file absent */ }
  }
  return null;
};

const left = [];
for (const p of rest.map(Number)) {
  const b = batchOf(p);
  const hits = mine.filter((e) => (e.pages === 'all' ? e.batch === b : expand(e.pages).includes(p)));
  const done = hits.some((e) => deep.has(e.scope));
  if (todo) {
    if (!done) left.push(p);
  } else {
    console.log(`p. ${p}: ${hits.length ? hits.map((e) => `${e.scope} ${e.date} ${e.model}`).join('; ') : 'not recorded'}`);
  }
}
if (todo) console.log(left.join(' '));
