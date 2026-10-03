#!/usr/bin/env node
/**
 * One LaTeX file per folder, with no batches: the transcriptions of a
 * shelfmark joined into a single document, for sending by mail.
 *
 *   npm run bundle:tex            # every transcribed folder
 *   npm run bundle:tex -- 19 134-2
 *
 * Writes exports/tex/<folder>.fr.tex, flat, beside a copy of the shared
 * preamble in exports/tex/preamble/ (its paths rewritten for that layout), so
 * that each file compiles where it lands (`cd exports/tex && tectonic 19.fr.tex`). exports/ is git-ignored: these files
 * are derived, and the transcriptions are not published (BnF, 2026-09-29).
 *
 * The document is the batches' bodies in order, under the first batch's
 * metadata with \pages spanning the whole folder and no \batch — the preamble
 * then drops the « (lot N) » from the title block. Each batch's header
 * comment is kept, in order, as the file's header: it is where the passes
 * record what they read, who read it and what was revised.
 */
import { cpSync, existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const ROOT = resolve(import.meta.dirname, '..');
const T = resolve(ROOT, 'transcripts');
const OUT = resolve(ROOT, 'exports', 'tex');

const byShelfmark = (a, b) => {
  const [a0, a1 = '0'] = a.split('-');
  const [b0, b1 = '0'] = b.split('-');
  return Number(a0) - Number(b0) || Number(a1) - Number(b1) || a.localeCompare(b);
};

const wanted = process.argv.slice(2);
const folders = readdirSync(T, { withFileTypes: true })
  .filter((d) => d.isDirectory() && d.name !== 'preamble')
  .map((d) => d.name)
  .filter((f) => !f.startsWith('_')) // _specimen: the skill's worked example, not a folder
  .filter((f) => !wanted.length || wanted.includes(f))
  .filter((f) => readdirSync(resolve(T, f)).some((n) => /^batch-\d+\.fr\.tex$/.test(n)))
  .sort(byShelfmark);

mkdirSync(OUT, { recursive: true });
cpSync(resolve(T, 'preamble'), resolve(OUT, 'preamble'), { recursive: true });
// Flat layout: the files sit beside preamble/, not one level below it.
const sty = resolve(OUT, 'preamble', 'grothendieck.sty');
writeFileSync(sty, readFileSync(sty, 'utf8').replaceAll('../preamble/', 'preamble/'));

function parse(src, file) {
  const begin = src.indexOf('\\begin{document}');
  const end = src.lastIndexOf('\\end{document}');
  if (begin < 0 || end < 0) throw new Error(`${file}: no document environment`);
  const head = src.slice(0, begin);
  const comment = head.split('\n').filter((l) => l.startsWith('%')).join('\n');
  const meta = head.split('\n').filter((l) => !l.startsWith('%') && l.trim()).join('\n');
  const pages = /\\pages\{(\d+)\}\{(\d+)\}/.exec(meta);
  return { comment, meta, body: src.slice(begin + '\\begin{document}'.length, end).trim(), pages };
}

let n = 0;
for (const folder of folders) {
  const files = readdirSync(resolve(T, folder))
    .filter((f) => /^batch-\d+\.fr\.tex$/.test(f))
    .sort();
  const parts = files.map((f) => ({ f, ...parse(readFileSync(resolve(T, folder, f), 'utf8'), `${folder}/${f}`) }));
  const firsts = parts.map((p) => (p.pages ? Number(p.pages[1]) : Infinity));
  const lasts = parts.map((p) => (p.pages ? Number(p.pages[2]) : -Infinity));
  const first = Math.min(...firsts);
  const last = Math.max(...lasts);

  const meta = parts[0].meta
    .split('\n')
    .filter((l) => !/^\\batch\{/.test(l.trim()))
    .join('\n')
    .replace(/\\pages\{\d+\}\{\d+\}/, `\\pages{${first}}{${last}}`)
    .replaceAll('\\input{../preamble/', '\\input{preamble/')


  const header = [
    `% Fonds Alexandre Grothendieck, shelfmark ${folder}: the transcriptions of the whole folder`,
    `% (pages ${first}-${last}), joined from ${files.length} batch file${files.length > 1 ? 's' : ''} of`,
    '% https://github.com/Commutator-IO/grothendieck-project (transcripts/' + folder + '/) by',
    '% scripts/bundle-tex.mjs. Demonstration edition, not authorised, not for publication.',
    '% The header comments of the batch files follow, in order.',
    ...parts.flatMap((p) => ['%', `% ---- ${p.f} ----`, p.comment]),
  ].join('\n');

  const body = parts.map((p) => p.body).join('\n\n');
  writeFileSync(resolve(OUT, `${folder}.fr.tex`), `${header}\n${meta}\n\n\\begin{document}\n\n${body}\n\n\\end{document}\n`);
  n++;
}

if (!existsSync(resolve(OUT, 'preamble', 'grothendieck.sty'))) throw new Error('preamble not copied');
console.log(`${n} folders → exports/tex/<folder>.fr.tex (preamble in exports/tex/preamble/)`);
