#!/usr/bin/env node
/**
 * How the Buffalo transcriptions converge, in counts only (the transcripts themselves stay
 * local, in the git-ignored transcripts-buffalo/).
 *
 *   node scripts/buffalo-stats.mjs
 *
 * For each tape side: the words of the edited transcript, its doubtful hearings `[?]`, its
 * inaudible stretches `[inaudible…]` and its supplied words `[…]`; and the share of its words
 * that differ from the first machine pass, YouTube's automatic captions (or, for topos 2/4,
 * which has none, the Whisper transcription), measured by a word-level diff. Each run appends a
 * snapshot to the history when the counts have changed, so the curve builds up release by
 * release. Writes src/content/buffalo-stats.json, which the /buffalo/ tab reads.
 */
import { execFileSync } from 'node:child_process';
import { existsSync, mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const SRC = resolve(ROOT, 'transcripts-buffalo');
const OUT = resolve(ROOT, 'src/content/buffalo-stats.json');
if (!existsSync(SRC)) {
  console.log('No transcripts-buffalo/ here: nothing to count.');
  process.exit(0);
}
const CAT = JSON.parse(readFileSync(resolve(ROOT, 'src/content/buffalo.json'), 'utf8'));
const courseOf = new Map();
for (const c of CAT.courses) for (const v of c.videos) courseOf.set(v.id, c);

const words = (s) => s.toLowerCase().match(/[\p{L}\p{N}]+/gu) ?? [];

/** The edited transcript of a side: its counts, and its words for the comparison. */
function transcript(file) {
  let s = readFileSync(join(SRC, file), 'utf8');
  const at = s.indexOf('-->');
  s = at >= 0 ? s.slice(at + 3) : s.replace(/^#.*\n/, '');
  s = s.replace(/<!--[\s\S]*?-->/g, ' ').replace(/\*\*\[[\d:]+\]\*\*/g, ' ');
  const doubtful = (s.match(/\[\?\]/g) ?? []).length;
  const inaudible = (s.match(/\[inaudible[^\]]*\]/gi) ?? []).length;
  const supplied = (s.match(/\[(?!\?\]|inaudible)[^\]]+\]/gi) ?? []).length;
  const text = s.replace(/\[\?\]/g, ' ').replace(/\[inaudible[^\]]*\]/gi, ' ').replace(/[[\]*_]/g, ' ');
  return { doubtful, inaudible, supplied, tokens: words(text) };
}

/** The first machine pass of the same side. */
function firstPass(video, start) {
  const caps = readdirSync(join(SRC, 'captions')).find((f) => f.startsWith(`${video}-`) && f.endsWith('.txt') && Number(f.slice(video.length + 1, -4)) === start);
  if (caps) {
    const s = readFileSync(join(SRC, 'captions', caps), 'utf8').replace(/^#.*$/gm, '').replace(/\[\d+(?::\d\d)+\]/g, ' ');
    return { source: 'captions', tokens: words(s) };
  }
  const dir = join(SRC, 'whisper', 'full');
  const w = existsSync(dir) && readdirSync(dir).find((f) => f.startsWith(`${video}-`) && f.endsWith('.json') && Number(f.slice(video.length + 1, -5)) === start);
  if (w) return { source: 'whisper', tokens: words(JSON.parse(readFileSync(join(dir, w), 'utf8')).segments.map((x) => x.text).join(' ')) };
  return null;
}

/** Words of `b` that a minimal word-level diff does not match in `a` (POSIX diff, Myers). */
const scratch = mkdtempSync(join(tmpdir(), 'buffalo-stats-'));
function unmatched(a, b) {
  writeFileSync(join(scratch, 'a'), a.join('\n') + '\n');
  writeFileSync(join(scratch, 'b'), b.join('\n') + '\n');
  let out = '';
  try {
    out = execFileSync('/usr/bin/diff', [join(scratch, 'a'), join(scratch, 'b')], { encoding: 'utf8', maxBuffer: 1 << 28 });
  } catch (e) {
    out = e.stdout ?? '';
  }
  return out.split('\n').filter((l) => l.startsWith('> ')).length;
}

const sides = [];
for (const f of readdirSync(SRC).filter((f) => /^[\w-]{11}-\d+\.en\.md$/.test(f))) {
  const video = f.slice(0, 11);
  const start = Number(f.slice(12, -6));
  const t = transcript(f);
  const p = firstPass(video, start);
  sides.push({
    video,
    course: courseOf.get(video)?.id ?? '?',
    words: t.tokens.length,
    doubtful: t.doubtful,
    inaudible: t.inaudible,
    supplied: t.supplied,
    source: p?.source ?? null,
    changed: p ? unmatched(p.tokens, t.tokens) : null,
  });
}
rmSync(scratch, { recursive: true, force: true });

const sum = (xs, k) => xs.reduce((a, x) => a + (x[k] ?? 0), 0);
const courses = CAT.courses.map((c) => {
  const xs = sides.filter((s) => s.course === c.id);
  const compared = xs.filter((s) => s.changed !== null);
  return {
    id: c.id,
    title: c.title,
    sides: xs.length,
    words: sum(xs, 'words'),
    doubtful: sum(xs, 'doubtful'),
    inaudible: sum(xs, 'inaudible'),
    supplied: sum(xs, 'supplied'),
    firstPass: [...new Set(compared.map((s) => s.source))],
    changedShare: Number((sum(compared, 'changed') / Math.max(1, sum(compared, 'words'))).toFixed(4)),
  };
});
const total = {
  sides: sides.length,
  words: sum(sides, 'words'),
  doubtful: sum(sides, 'doubtful'),
  inaudible: sum(sides, 'inaudible'),
  supplied: sum(sides, 'supplied'),
  changedShare: Number((sum(sides.filter((s) => s.changed !== null), 'changed') / Math.max(1, sum(sides.filter((s) => s.changed !== null), 'words'))).toFixed(4)),
  // The first pass differs: captions where YouTube made them, Whisper for topos 2/4.
  bySource: Object.fromEntries(['captions', 'whisper'].map((src) => {
    const xs = sides.filter((x) => x.source === src);
    return [src, { sides: xs.length, changedShare: Number((sum(xs, 'changed') / Math.max(1, sum(xs, 'words'))).toFixed(4)) }];
  })),
};

// The doubtful places put on the local review tab, after the triage of 13 November 2026.
let review = null;
const rf = resolve(ROOT, 'public/transcripts-bourbaki/review.json');
if (existsSync(rf)) {
  const docs = JSON.parse(readFileSync(rf, 'utf8')).docs.filter((d) => d.id.startsWith('buffalo-'));
  const checks = docs.flatMap((d) => d.checks);
  review = { checks: checks.length, mathematical: checks.filter((c) => !c.minor).length };
}

const today = new Date().toISOString().slice(0, 10);
const old = existsSync(OUT) ? JSON.parse(readFileSync(OUT, 'utf8')) : { history: [] };
const snap = { date: today, words: total.words, doubtful: total.doubtful, inaudible: total.inaudible, per100: Number((100 * total.doubtful / Math.max(1, total.words)).toFixed(2)), changedShare: total.changedShare };
const last = old.history.at(-1);
const history = last && last.words === snap.words && last.doubtful === snap.doubtful && last.inaudible === snap.inaudible
  ? old.history
  : [...old.history.filter((h) => h.date !== today), snap];

writeFileSync(
  OUT,
  `${JSON.stringify(
    {
      $why: 'Generated by `node scripts/buffalo-stats.mjs` from the local transcripts-buffalo/ — counts only, no text. Do not edit by hand. The history gains a snapshot whenever the counts change.',
      built: today,
      total,
      courses,
      review,
      history,
    },
    null,
    1,
  )}\n`,
);
console.log(JSON.stringify({ total, courses: courses.map((c) => [c.id, c.sides, c.words, c.doubtful, c.changedShare, c.firstPass]) }));
