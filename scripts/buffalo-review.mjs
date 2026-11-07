#!/usr/bin/env node
/**
 * Refreshes the Buffalo checks of the local review tab (dev server only).
 *
 *   npm run buffalo-review
 *
 * Reads the local transcripts (transcripts-buffalo/*.en.md, git-ignored) and writes their
 * checks into public/transcripts-bourbaki/review.json, the ignored file the review tab reads,
 * keeping every non-Buffalo document as it is. Two kinds of check:
 *
 *   - each doubtful hearing `[?]` still in a transcript, played from the paragraph's timestamp,
 *     with what Whisper heard when the second pass recorded it;
 *   - each blackboard item marked `u` (a probable oral slip of the lecturer, from the Lean
 *     checks of docs/buffalo-corrections.md), played from its spoken time, to confirm by ear
 *     that the slip is his and not the transcript's;
 *   - each blackboard item marked `uncertain` (shown with a « ? » on the board), to confirm.
 *
 * A check keeps its id when the same question comes back, so answers already given in the
 * browser (saved under those ids) stay attached; a new question gets a new id.
 */
import { existsSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const root = resolve(import.meta.dirname, '..');
const SRC = resolve(root, 'transcripts-buffalo');
const FILE = resolve(root, 'public/transcripts-bourbaki/review.json');
if (!existsSync(SRC)) {
  console.log('No transcripts-buffalo/ here — nothing to review.');
  process.exit(0);
}

const old = existsSync(FILE) ? JSON.parse(readFileSync(FILE, 'utf8')) : { docs: [] };
const oldDocs = new Map(old.docs.map((d) => [d.id, d]));
const hms = (s) => s.split(':').map(Number).reduce((a, b) => a * 60 + b, 0);
const plain = (s) => s.replace(/<!--[\s\S]*?-->/g, '').replace(/\s+/g, ' ').trim();

const docs = [];
let doubts = 0;
let slips = 0;
let boards = 0;
let kept = 0;
for (const f of readdirSync(SRC).filter((x) => /^[\w-]{11}-\d+\.en\.md$/.test(x)).sort()) {
  const stem = f.replace(/\.en\.md$/, '');
  const video = stem.slice(0, 11);
  const side = stem.slice(12).padStart(5, '0');
  const id = `buffalo-${video}-${side}`;
  const md = readFileSync(resolve(SRC, f), 'utf8');
  const head = /^# (.+)$/m.exec(md)?.[1] ?? stem;
  const whisper = /Second pass on the doubtful hearings: Whisper/.test(md);
  const body = md.slice(md.indexOf('-->') + 3);
  const prev = oldDocs.get(id);
  const byQ = new Map((prev?.checks ?? []).map((c) => [c.q, c.id]));
  let next = Math.max(0, ...(prev?.checks ?? []).map((c) => Number(c.id.split('-').pop()) || 0)) + 1;
  const used = new Set();
  // Old doubts by minute and rank within it, for questions whose context wording changed.
  const byT = new Map();
  for (const c of prev?.checks ?? []) {
    if (!c.q.startsWith('Doubtful')) continue;
    if (!byT.has(c.t)) byT.set(c.t, []);
    byT.get(c.t).push(c.id);
  }
  const rankAt = new Map();
  const checkId = (q, t) => {
    let k = byQ.get(q);
    if ((!k || used.has(k)) && t !== undefined) {
      const r = rankAt.get(t) ?? 0;
      rankAt.set(t, r + 1);
      k = byT.get(t)?.[r];
    }
    if (k && !used.has(k)) {
      used.add(k);
      kept++;
      return k;
    }
    const n = `b${video}-${side}-${next++}`;
    used.add(n);
    return n;
  };
  const checks = [];

  // Doubtful hearings, in order; the time is that of the paragraph holding the mark.
  const stamps = [...body.matchAll(/\*\*\[(\d+:\d\d:\d\d)\]\*\*/g)].map((m) => [m.index, hms(m[1])]);
  for (const m of body.matchAll(/\[\?\]( *<!-- *whisper: *([\s\S]*?) *-->)?/g)) {
    const at = stamps.filter(([i]) => i < m.index).pop()?.[1] ?? 0;
    const before = plain(body.slice(Math.max(0, m.index - 260), m.index)).slice(-220);
    const heard = m[2] ? ` Whisper heard: « ${plain(m[2])} ».` : '';
    const q = `Doubtful hearing in this minute: … ${before} [?]${heard} What does he say?`;
    checks.push({ id: checkId(q, at), t: at, page: 0, batch: 0, q });
    doubts++;
  }

  // Probable oral slips on the boards of this side.
  const board = resolve(SRC, `${video}-${String(Number(side)).padStart(4, "0")}.json`);
  const boardAlt = resolve(SRC, `${stem}.json`);
  const bf = existsSync(boardAlt) ? boardAlt : existsSync(board) ? board : null;
  if (bf) {
    for (const it of JSON.parse(readFileSync(bf, 'utf8')).items ?? []) {
      if (!it.u && !it.uncertain) continue;
      const q = it.u
        ? `Probable oral slip (blackboard item, corrected after the Lean checks): « ${plain(it.text)} ». Does he say it as the board has it, and is the slip his rather than the transcript's?`
        : `Uncertain blackboard item: « ${plain(it.text)} ». Is this what he says and writes here?`;
      checks.push({ id: checkId(q), t: it.t, page: 0, batch: 0, q });
      if (it.u) slips++;
      else boards++;
    }
  }
  checks.sort((a, b) => a.t - b.t);
  if (!checks.length) continue;
  docs.push({
    id,
    title: `${head}${whisper ? ' · checked with Whisper' : ''}`,
    video,
    pdf: '',
    item: `https://www.youtube.com/watch?v=${video}`,
    checks,
  });
}

const others = old.docs.filter((d) => !d.id.startsWith('buffalo-'));
writeFileSync(
  FILE,
  JSON.stringify({ built: new Date().toISOString().slice(0, 10), docs: [...others, ...docs] }),
);
console.log(
  `${docs.length} Buffalo sides: ${doubts} doubtful hearings, ${slips} probable oral slips, ${boards} uncertain board items; ${kept} checks kept their id`,
);
