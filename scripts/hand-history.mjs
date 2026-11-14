#!/usr/bin/env node
/**
 * How the edition converges: snapshots of the Montpellier transcriptions taken from the git
 * history, every fourteen days since the first batch, with the share of words left unread or
 * doubtful and the lines revised since the previous snapshot.
 *
 *   node scripts/hand-history.mjs        (also run by `npm run hand`)
 *
 * Writes src/content/hand-history.json, which the /hand/ tab reads. When releases of the
 * transcriptions are tagged (`transcripts-v*`), each tag becomes a snapshot too, so the
 * curve can be read release by release.
 *
 * The counts are a lighter version of scripts/hand.mjs (notes and formulas left out, words as
 * letter runs): consistent from one snapshot to the next, not identical to the tab's totals.
 */
import { execFileSync } from 'node:child_process';
import { writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const OUT = resolve(ROOT, 'src/content/hand-history.json');
const BATCH = /^transcripts\/[^/]+\/batch-\d+\.fr\.tex$/;
const git = (args, input) =>
  execFileSync('git', args, { cwd: ROOT, maxBuffer: 1 << 30, input, encoding: input === undefined ? 'utf8' : undefined });

/** Index just past the brace group opening at `i`. */
function closeBrace(s, i) {
  let depth = 0;
  for (let j = i; j < s.length; j++) {
    if (s[j] === '\\') { j++; continue; }
    if (s[j] === '{') depth++;
    else if (s[j] === '}' && --depth === 0) return j + 1;
  }
  return s.length;
}
function strip(s, name) {
  let out = '';
  let at = 0;
  const re = new RegExp(`\\\\${name}\\{`, 'g');
  let m;
  while ((m = re.exec(s))) {
    const end = closeBrace(s, m.index + m[0].length - 1);
    out += s.slice(at, m.index);
    at = end;
    re.lastIndex = end;
  }
  return out + s.slice(at);
}
const mathless = (s) =>
  s
    .replace(/\\begin\{(tikzcd|tikzpicture|array|cases|aligned|align\*?|equation\*?|gather\*?|[pbvB]?matrix)\}[\s\S]*?\\end\{\1\}/g, ' ')
    .replace(/\\\[[\s\S]*?\\\]/g, ' ')
    .replace(/(?<!\\)\$(?:\\\$|[^$])*?\$/g, ' ');

function measure(src) {
  const at = src.indexOf('\\begin{document}');
  if (at < 0) return null;
  const body = src.slice(at).replace(/(?<!\\)%.*$/gm, '');
  const his = strip(strip(body, 'note'), 'drawing');
  const words = mathless(his)
    .replace(/\\[a-zA-Z]+\*?/g, ' ')
    .match(/[\p{L}][\p{L}'’-]*/gu)?.length ?? 0;
  return { words, ill: (his.match(/\\ill\{\}/g) ?? []).length, uncertain: (his.match(/\\uncertain\{/g) ?? []).length };
}

/** The batch files of a commit, read in one `git cat-file --batch`. */
function snapshot(commit) {
  const paths = git(['ls-tree', '-r', '--name-only', commit, '--', 'transcripts']).split('\n').filter((p) => BATCH.test(p));
  const buf = git(['cat-file', '--batch'], paths.map((p) => `${commit}:${p}`).join('\n') + '\n');
  const files = new Map();
  let i = 0;
  for (const p of paths) {
    const nl = buf.indexOf(10, i);
    const size = Number(buf.subarray(i, nl).toString().split(' ')[2]);
    files.set(p, buf.subarray(nl + 1, nl + 1 + size).toString('utf8'));
    i = nl + 1 + size + 1;
  }
  return files;
}

const first = git(['log', '--reverse', '--format=%ad', '--date=short', '--', 'transcripts']).split('\n')[0];
const today = new Date().toISOString().slice(0, 10);
const points = [];
for (let t = Date.parse(first); t < Date.parse(today); t += 14 * 86400000) points.push({ date: new Date(t).toISOString().slice(0, 10) });
points.push({ date: today });
for (const tag of git(['tag', '--list', 'transcripts-v*']).split('\n').filter(Boolean))
  points.push({ date: git(['log', '-1', '--format=%ad', '--date=short', tag]).trim(), tag });
points.sort((a, b) => a.date.localeCompare(b.date));

const snapshots = [];
let prev = null;
for (const p of points) {
  const commit = git(['rev-list', '-1', ...(p.tag ? [p.tag] : [`--before=${p.date}T23:59:59`, 'HEAD'])]).trim();
  if (!commit) continue;
  if (prev && prev.commit === commit) {
    // A tag on the commit of the fortnightly point just taken names that point.
    if (p.tag) snapshots.at(-1).tag = p.tag;
    continue;
  }
  const files = snapshot(commit);
  let words = 0, ill = 0, uncertain = 0, lines = 0;
  for (const src of files.values()) {
    const m = measure(src);
    if (!m) continue;
    words += m.words; ill += m.ill; uncertain += m.uncertain;
  }
  // Lines revised since the previous snapshot, in the files that existed at both.
  let revised = null;
  let share = null;
  if (prev) {
    revised = 0;
    for (const row of git(['diff', '--numstat', prev.commit, commit, '--', 'transcripts']).split('\n')) {
      const [a, d, path] = row.split('\t');
      if (!path || !BATCH.test(path) || !prev.files.has(path) || !files.has(path)) continue;
      revised += (Number(a) || 0) + (Number(d) || 0);
    }
    for (const [path, src] of files) if (prev.files.has(path)) lines += src.split('\n').length;
    share = lines ? Number((revised / lines).toFixed(4)) : null;
  }
  snapshots.push({
    date: p.date,
    ...(p.tag ? { tag: p.tag } : {}),
    commit: commit.slice(0, 8),
    batches: files.size,
    words,
    ill,
    uncertain,
    per100: Number((100 * (ill + uncertain) / Math.max(1, words + ill)).toFixed(2)),
    revised,
    revisedShare: share,
  });
  prev = { commit, files };
}

writeFileSync(
  OUT,
  `${JSON.stringify(
    {
      $why: 'Generated by `node scripts/hand-history.mjs` from the git history of transcripts/*/batch-*.fr.tex — do not edit by hand. One snapshot every fourteen days, and one per tag transcripts-v*.',
      built: today,
      snapshots,
    },
    null,
    1,
  )}\n`,
);
console.log(snapshots.map((s) => `${s.date} ${s.batches} batches, ${s.per100}/100 unread or doubtful, ${s.revised ?? '—'} lines revised`).join('\n'));
