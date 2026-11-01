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

const root = resolve(import.meta.dirname, '..');
const src = resolve(root, 'transcripts-buffalo');
const out = resolve(root, 'public/buffalo-boards');
mkdirSync(out, { recursive: true });

let n = 0;
for (const f of readdirSync(src)) {
  if (!/^[\w-]{11}-\d+\.json$/.test(f)) continue;
  const b = JSON.parse(readFileSync(resolve(src, f), 'utf8'));
  b.$why = b.$why.replace(/\s*Local only.*$/s, ' Published with the index of results; the transcript stays local.');
  writeFileSync(resolve(out, f), JSON.stringify(b));
  n++;
}
console.log(`${n} boards → public/buffalo-boards/`);
