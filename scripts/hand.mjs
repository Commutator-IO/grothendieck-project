#!/usr/bin/env node
/**
 * Measures the hand, batch by batch, for the page that shows it.
 *
 *   npm run hand
 *
 * Reads every transcripts/<folder>/batch-NN.fr.tex and writes
 * src/content/hand.json: for each batch, how much of it was read, how much was
 * not, what he struck and added, what he wrote in the margin, how many
 * diagrams and drawings, how much of it is formulas, and in which language.
 *
 * What these numbers are. They count the transcription's apparatus, not ink:
 * an `\ill{}` is a word a first pass could not read, which says as much about
 * the pass as about the hand, and a folder read twice would count differently.
 * They are comparable across folders because the same skill, with the same
 * rules, produced every file — which is also the limit of what they show.
 *
 * Kept apart on purpose:
 *   - the transcriber's `\note{}` is ours, not his, and is left out of every
 *     count except the drawings (a drawing is recorded as a note);
 *   - `\marginal{}` is his, and is counted both as his words and as a margin.
 */
import { readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const T = resolve(ROOT, 'transcripts');
const OUT = resolve(ROOT, 'src/content/hand.json');

const catalogue = readFileSync(resolve(ROOT, 'src/content/catalogue.ts'), 'utf8');
const COTE = new Map();
for (const m of catalogue.matchAll(/"id": "([^"]+)",\s*"file": "[^"]+",\s*"date": "([^"]*)",\s*"title": "((?:[^"\\]|\\.)*)"/g))
  COTE.set(m[1], { date: m[2], title: m[3].replace(/\\"/g, '"') });
/** Midpoint of the years in the inventory's dating, or null for « s.d. ». */
function year(id) {
  const ys = [...(COTE.get(id)?.date ?? '').matchAll(/\b(19\d\d)\b/g)].map((m) => Number(m[1]));
  return ys.length ? (Math.min(...ys) + Math.max(...ys)) / 2 : null;
}
const byShelfmark = (a, b) => {
  const [a0, a1 = '0'] = a.split('-');
  const [b0, b1 = '0'] = b.split('-');
  return Number(a0) - Number(b0) || Number(a1) - Number(b1);
};

/** Index just past the brace group opening at `i` (s[i] === '{'). */
function closeBrace(s, i) {
  let depth = 0;
  for (let j = i; j < s.length; j++) {
    if (s[j] === '\\') {
      j++;
      continue;
    }
    if (s[j] === '{') depth++;
    else if (s[j] === '}' && --depth === 0) return j + 1;
  }
  return s.length;
}

/** Every `\name{…}` group in `s`, as [start, end, content]. */
function groups(s, name) {
  const out = [];
  const re = new RegExp(`\\\\${name}\\{`, 'g');
  let m;
  while ((m = re.exec(s))) {
    const open = m.index + m[0].length - 1;
    const end = closeBrace(s, open);
    out.push([m.index, end, s.slice(open + 1, end - 1)]);
    re.lastIndex = end;
  }
  return out;
}

/** `s` with every `\name{…}` group removed. */
function strip(s, name) {
  let out = '';
  let at = 0;
  for (const [a, b] of groups(s, name)) {
    out += s.slice(at, a);
    at = b;
  }
  return out + s.slice(at);
}

const MATH_ENVS = ['tikzcd', 'array', 'cases', 'aligned', 'align\\*?', 'equation\\*?', 'gather\\*?', '[pbvB]?matrix', 'smallmatrix'];
function mathless(s) {
  let t = s;
  for (const e of MATH_ENVS) t = t.replace(new RegExp(`\\\\begin\\{(${e})\\}[\\s\\S]*?\\\\end\\{\\1\\}`, 'g'), ' ');
  return t
    .replace(/\\\[[\s\S]*?\\\]/g, ' ')
    .replace(/\\\([\s\S]*?\\\)/g, ' ')
    .replace(/\$\$[\s\S]*?\$\$/g, ' ')
    .replace(/(?<!\\)\$(?:\\\$|[^$])*?\$/g, ' ');
}

const STOP = {
  fr: ['le', 'la', 'les', 'des', 'est', 'et', 'que', 'on', 'pour', 'une', 'dans', 'qui', 'sur', 'pas', 'donc', 'où'],
  en: ['the', 'of', 'and', 'is', 'that', 'we', 'for', 'this', 'which', 'are', 'with', 'be', 'it'],
  de: ['der', 'die', 'das', 'und', 'ist', 'nicht', 'mit', 'von', 'ein', 'eine', 'auf', 'sich', 'dass'],
};

const FIGURE = /^\s*(?:\[?\s*)?(figure|dessin|drawing|croquis|sketch|schéma|diagramme dessiné|a drawing|un dessin)/i;

const batches = [];
for (const d of readdirSync(T, { withFileTypes: true })) {
  if (!d.isDirectory() || !COTE.has(d.name)) continue;
  for (const f of readdirSync(resolve(T, d.name))) {
    const m = /^batch-(\d+)\.fr\.tex$/.exec(f);
    if (!m) continue;
    const src = readFileSync(resolve(T, d.name, f), 'utf8');
    const at = src.indexOf('\\begin{document}');
    if (at < 0) continue;
    // Comments out; an escaped \% stays.
    const body = src.slice(at).replace(/(?<!\\)%.*$/gm, '');
    const notes = groups(body, 'note').map((g) => g[2]);
    const his = strip(body, 'note');
    const count = (name) => groups(his, name).length;
    const prose = mathless(his);
    const words = prose
      .replace(/\\(ill|uncertain|struck|add|marginal|emph|textbf|textit|texttt|underline|section\*?|subsection\*?|item)\b/g, ' ')
      .replace(/\\[a-zA-Z]+\*?(\[[^\]]*\])?/g, ' ')
      .replace(/[{}]/g, ' ')
      .match(/[\p{L}][\p{L}'’-]*/gu) ?? [];
    const lower = words.map((w) => w.toLowerCase());
    const lang = Object.fromEntries(Object.entries(STOP).map(([k, list]) => [k, lower.filter((w) => list.includes(w)).length]));
    const pages = new Set([...his.matchAll(/\\page\{([^}]*)\}/g)].map((p) => p[1]));
    const mathChars = his.length - mathless(his).length;
    batches.push({
      folder: d.name,
      batch: Number(m[1]),
      pages: pages.size,
      words: words.length,
      ill: (his.match(/\\ill\{\}/g) ?? []).length,
      uncertain: count('uncertain'),
      struck: count('struck'),
      add: count('add'),
      marginal: count('marginal'),
      diagrams: (his.match(/\\begin\{tikzcd\}/g) ?? []).length,
      drawings: notes.filter((n) => FIGURE.test(n)).length,
      math: Number((mathChars / Math.max(1, his.length)).toFixed(3)),
      lang,
    });
  }
}
batches.sort((a, b) => byShelfmark(a.folder, b.folder) || a.batch - b.batch);

// Per folder: the sums, and the inventory's dating for the chronology.
const KEYS = ['pages', 'words', 'ill', 'uncertain', 'struck', 'add', 'marginal', 'diagrams', 'drawings'];
const folders = [...new Set(batches.map((b) => b.folder))].map((id) => {
  const bs = batches.filter((b) => b.folder === id);
  const sum = Object.fromEntries(KEYS.map((k) => [k, bs.reduce((a, b) => a + b[k], 0)]));
  const lang = Object.fromEntries(Object.keys(STOP).map((k) => [k, bs.reduce((a, b) => a + b.lang[k], 0)]));
  const top = Object.entries(lang).sort((a, b) => b[1] - a[1]);
  return {
    id,
    title: COTE.get(id).title,
    date: COTE.get(id).date,
    year: year(id),
    batches: bs.length,
    ...sum,
    // The share of formulas, weighted by the batches' lengths in words.
    math: Number((bs.reduce((a, b) => a + b.math * (b.words + 1), 0) / bs.reduce((a, b) => a + b.words + 1, 0)).toFixed(3)),
    // A language counts when its function words are at least a fifth of the
    // leading one's: a German quotation in a French folder does not make it
    // bilingual, a letter in English does.
    languages: top.filter(([, n]) => n > 0 && n >= top[0][1] / 5).map(([k]) => k),
  };
});

const lexicon = JSON.parse(
  readFileSync(resolve(ROOT, '.claude/skills/transcribe-grothendieck/references/lexicon.json'), 'utf8'),
);

const out = {
  $why:
    'Generated by `npm run hand` from transcripts/*/batch-*.fr.tex — do not edit by hand. Counts of the transcription apparatus, not of ink.',
  built: new Date().toISOString().slice(0, 10),
  folders,
  batches,
  // His abbreviations, from the lexicon the transcription pass reads.
  abbreviations: Object.entries(lexicon.abbreviations)
    .slice(0, 40)
    .map(([form, n]) => ({ form, n })),
};
writeFileSync(OUT, `${JSON.stringify(out, null, 1)}\n`);
const t = Object.fromEntries(KEYS.map((k) => [k, folders.reduce((a, f) => a + f[k], 0)]));
process.stdout.write(
  `${batches.length} batches, ${folders.length} folders — ${t.words} words, ${t.ill} \\ill, ${t.uncertain} \\uncertain, ${t.struck} \\struck, ${t.diagrams} diagrams, ${t.drawings} drawings → src/content/hand.json\n`,
);
