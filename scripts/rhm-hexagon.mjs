#!/usr/bin/env node
/**
 * The single ZIP of the RHM article for a Hexagon deposit (#120): the TeX
 * sources of the pdfLaTeX variant, and no Lean code.
 *
 *   npm run rhm:hexagon
 *
 * Writes exports/rhm-hexagon-<date>-<commit>.zip (exports/ is git-ignored)
 * with, flat at its root: article-hexagon.tex (the file to compile),
 * article.tex, article.bib, fig-carte.tex, halbib.sty, rhmunsrtnat.bst, and
 * article-hexagon.bbl when it exists beside the sources (compile first, so
 * that the deposit does not depend on a BibTeX run on the other side).
 *
 * Hexagon accepts TeX sources and refuses code such as Lean formalisations
 * as part of a submission (hexagonmath.org/about, read on 10 November 2026):
 * the article links the repository and the Palomar entry instead. So the
 * script refuses to build if a .lean file or a Lean listing would go in, and
 * it checks that the variant keeps no link to the project's site in its
 * « cote, lot, page » references.
 */
import { execFileSync } from 'node:child_process';
import { copyFileSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';

const ROOT = resolve(import.meta.dirname, '..');
const SRC = resolve(ROOT, 'docs', 'rhm');
const OUT = resolve(ROOT, 'exports');

const FILES = ['article-hexagon.tex', 'article.tex', 'article.bib', 'fig-carte.tex', 'halbib.sty', 'rhmunsrtnat.bst'];
const OPTIONAL = ['article-hexagon.bbl'];

const fail = (msg) => {
  console.error(`rhm-hexagon: ${msg}`);
  process.exit(1);
};

for (const f of FILES) if (!existsSync(join(SRC, f))) fail(`missing ${f}`);

// Every file the article reads must be in the archive.
const tex = readFileSync(join(SRC, 'article.tex'), 'utf8');
for (const m of tex.matchAll(/\\(?:input|include|includegraphics)(?:\[[^\]]*\])?\{([^}]+)\}/g)) {
  const name = m[1];
  if (![name, `${name}.tex`].some((n) => FILES.includes(n))) fail(`article.tex reads « ${name} », which is not in the archive list`);
}

// No Lean code: neither a file nor a listing.
if (FILES.concat(OPTIONAL).some((f) => f.endsWith('.lean'))) fail('a .lean file is in the list');
for (const f of FILES.filter((f) => f.endsWith('.tex'))) {
  const src = readFileSync(join(SRC, f), 'utf8');
  if (/\\begin\{(?:lstlisting|minted|verbatim|Verbatim)\}|\\lstinputlisting|\\inputminted/.test(src)) fail(`${f} carries a code listing`);
}

// The Hexagon branch must define the Montpellier links and the Lean links.
if (!/\\ifdefined\\hexagon[\s\S]*?grothendieck\.umontpellier\.fr\/#1\.pdf/.test(tex)) fail('article.tex has no Hexagon branch for \\lot');
if (/\\nolinkurl\{lean\/Grothendieck\/Folder/.test(tex)) fail('a Lean file is named without \\leanfile');

const date = new Date().toISOString().slice(0, 10);
const commit = execFileSync('git', ['rev-parse', '--short', 'HEAD'], { cwd: ROOT, encoding: 'utf8' }).trim();
const zip = join(OUT, `rhm-hexagon-${date}-${commit}.zip`);
mkdirSync(OUT, { recursive: true });
rmSync(zip, { force: true });

const work = mkdtempSync(join(tmpdir(), 'rhm-hexagon-'));
const packed = [];
for (const f of FILES.concat(OPTIONAL)) {
  if (!existsSync(join(SRC, f))) continue;
  copyFileSync(join(SRC, f), join(work, f));
  packed.push(f);
}
execFileSync('zip', ['-q', '-X', zip, ...packed], { cwd: work });
rmSync(work, { recursive: true, force: true });

console.log(`${zip}\n  ${packed.join(', ')}`);
if (!packed.includes('article-hexagon.bbl')) {
  console.log('  no article-hexagon.bbl: compile first (pdflatex, bibtex, pdflatex twice) if the deposit should not depend on BibTeX');
}
