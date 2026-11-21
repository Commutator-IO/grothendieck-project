#!/usr/bin/env node
/**
 * The doubtful readings of the local transcriptions of the journal « Survivre et vivre » (#166) and of
 * Gaeta's notes (#167), added to the local review tab (dev server only):
 *
 *   node scripts/transcription-review.mjs
 *
 * Reads transcripts-survivre/<issue>/batch-01.fr.tex and transcripts-gaeta/ag/batch-NN.en.tex, one check per
 * \ill{} and \uncertain{}, and merges them as documents into public/transcripts-bourbaki/review.json (git-ignored,
 * the file BourbakiReview reads), replacing the documents of the same kind it wrote before. The scans are copied
 * into public/csg-scans/ (git-ignored) so that the tab can show the page beside the rendered transcription.
 */
import { copyFileSync, existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const ROOT = resolve(import.meta.dirname, '..');
const FILE = resolve(ROOT, 'public/transcripts-bourbaki/review.json');
const SCANS = resolve(ROOT, 'public/csg-scans');
const ARCH = resolve(ROOT, 'archives/csg');
mkdirSync(SCANS, { recursive: true });

// Survivre issue (folder of transcripts-survivre) → scan.
const SCAN = { 1: 'U22.1', '2-3': 'U22.2_3', 4: 'U22.4', 5: 'U22.5', 7: 'U22.7', 8: 'U22.8', 9: 'U22.9', 10: 'U22.10', 12: 'U22.12', 14: 'U22.14', 15: 'U22.15' };
const TITLE = {
  1: 'n° 1, août 1970', '2-3': 'n° 2/3, sept.-oct. 1970', 4: 'n° 4, novembre 1970', 5: 'n° 5, décembre 1970', 7: 'n° 7, février-mai 1971',
  8: 'n° 8, juin-juillet 1971', 9: 'n° 9, août-septembre 1971', 10: 'n° 10, octobre 1971-janvier 1972', 12: 'n° 12, juin 1972',
  14: 'n° 14, octobre-novembre 1972', 15: 'n° 15, janvier-février 1973',
};

const plain = (s) =>
  s
    .replace(/\\(?:ill|uncertain|supplied|add|struck|emph|textit|underline)\{((?:[^{}]|\{[^{}]*\})*)\}/g, '$1')
    .replace(/\\(?:note|marginal|drawing|page)\{[^{}]*\}/g, ' ')
    .replace(/\\[a-zA-Z]+\*?\{?/g, ' ')
    .replace(/[{}$]/g, ' ')
    .replace(/\s+/g, ' ')
    .trim();

function checks(file, batch, prefix) {
  const src = readFileSync(file, 'utf8');
  const body = src.slice(src.indexOf('\\begin{document}'));
  let page = 1;
  let piece = '';
  const out = [];
  let n = 0;
  const LINES = body.split('\n');
  for (let li = 0; li < LINES.length; li++) {
    const raw = LINES[li];
    const sec = /\\(?:sub)?section\*?\{(.*)\}\s*$/.exec(raw);
    if (sec) piece = plain(sec[1]).replace(/\s+/g, ' ').slice(0, 60);
    const pg = /\\page\{(\d+)\}/.exec(raw);
    if (pg) page = Number(pg[1]);
    const re = /\\(ill|uncertain)\{((?:[^{}]|\{[^{}]*\})*)\}/g;
    let m;
    while ((m = re.exec(raw))) {
      n++;
      const prevText = plain(LINES.slice(Math.max(0, li - 2), li).filter((l) => !l.startsWith('%')).join(' '));
      const nextText = plain(LINES.slice(li + 1, li + 3).filter((l) => !l.startsWith('%')).join(' '));
      const before = `${prevText} ${plain(raw.slice(0, m.index))}`.trim().split(/\s+/).slice(-7).join(' ');
      const after = `${plain(raw.slice(m.index + m[0].length))} ${nextText}`.trim().split(/\s+/).slice(0, 5).join(' ');
      const word = m[2] || '…';
      out.push({
        id: `${prefix}-b${batch}-${n}`,
        label: `${piece ? `${piece} · ` : ''}« ${before.split(' ').slice(-3).join(' ')} [${word}] ${after.split(' ').slice(0, 3).join(' ')} »`.replace(/\s+/g, ' '),
        page,
        batch,
        q: `${m[1] === 'ill' ? 'Illegible in the transcription' : 'Doubtful reading'}: « … ${before} [${word}] ${after} … ». ${m[1] === 'ill' ? 'Can the page be read here? What does it say?' : `Does the page read « ${word} »?`}`,
      });
    }
  }
  return out;
}

const docs = [];
// Survivre
const SV = resolve(ROOT, 'transcripts-survivre');
if (existsSync(SV)) {
  for (const d of readdirSync(SV, { withFileTypes: true })) {
    if (!d.isDirectory() || d.name === 'preamble') continue;
    const f = resolve(SV, d.name, 'batch-01.fr.tex');
    if (!existsSync(f) || !SCAN[d.name]) continue;
    const scan = `${SCAN[d.name]}.pdf`;
    if (existsSync(resolve(ARCH, scan))) copyFileSync(resolve(ARCH, scan), resolve(SCANS, scan));
    docs.push({ id: `survivre-${d.name}`, title: `Survivre et vivre, ${TITLE[d.name]} (pieces of A. Grothendieck)`, base: 'transcripts-survivre', lang: 'fr', pdf: `/csg-scans/${scan}`, item: `/csg-scans/${scan}`, notice: 'Scan', checks: checks(f, 1, `sv${d.name}`) });
  }
}
// Gaeta
const GA = resolve(ROOT, 'transcripts-gaeta/ag');
if (existsSync(GA)) {
  if (existsSync(resolve(ARCH, 'U26.pdf'))) copyFileSync(resolve(ARCH, 'U26.pdf'), resolve(SCANS, 'U26.pdf'));
  const all = [];
  for (const f of readdirSync(GA).filter((x) => /^batch-\d+\.en\.tex$/.test(x)).sort()) all.push(...checks(resolve(GA, f), Number(/\d+/.exec(f)[0]), 'ga'));
  docs.push({ id: 'gaeta-ag', title: "Gaeta, Introduction to Functorial Algebraic Geometry (notes of the 1973 Buffalo course)", base: 'transcripts-gaeta', lang: 'en', pdf: '/csg-scans/U26.pdf', item: 'https://webusers.imj-prg.fr/~leila.schneps/grothendieckcircle/FuncAlg.pdf', notice: 'Second scan', checks: all });
}

const review = existsSync(FILE) ? JSON.parse(readFileSync(FILE, 'utf8')) : { built: '', docs: [] };
// Survivre and Gaeta first in the list.
review.docs = [...docs.filter((d) => d.checks.length).sort((a, b) => parseInt(a.id.replace(/\D*/, ''), 10) - parseInt(b.id.replace(/\D*/, ''), 10) || a.id.localeCompare(b.id)), ...review.docs.filter((d) => !/^(survivre|gaeta)-/.test(d.id))];
review.built = new Date().toISOString().slice(0, 10);
writeFileSync(FILE, `${JSON.stringify(review, null, 1)}\n`);
console.error(`${docs.map((d) => `${d.id}: ${d.checks.length}`).join(', ')}`);
