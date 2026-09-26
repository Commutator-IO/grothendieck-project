#!/usr/bin/env node
/**
 * The preview images a link to the site shows on LinkedIn, Mastodon and the
 * rest (og:image): 1200 × 627, typeset by LaTeX from the transcriptions.
 *
 *   node scripts/og.mjs
 *
 * public/og/diagrams.png — the richest commutative diagram of the fonds, in
 * tikz-cd, as the gallery ranks it (scripts/diagrams.mjs);
 * public/og/formulas.png — the richest displayed formula (scripts/formulas.mjs).
 * No page of the fonds is reproduced: what is drawn is the transcription's
 * TeX, set by TeX. Committed, because the deploy runner is not where they need
 * to change; rerun when the richest changes.
 *
 * Needs tectonic and pdftoppm.
 */
import { execFileSync } from 'node:child_process';
import { mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { symbols } from './lib/symbols.mjs';

const ROOT = resolve(import.meta.dirname, '..');
const T = resolve(ROOT, 'transcripts');
const OUT = resolve(ROOT, 'public/og');
const TMP = resolve(ROOT, 'node_modules/.cache/og');
mkdirSync(OUT, { recursive: true });
mkdirSync(TMP, { recursive: true });

const folders = readdirSync(T, { withFileTypes: true })
  .filter((d) => d.isDirectory() && !d.name.startsWith('_') && d.name !== 'preamble')
  .map((d) => d.name);

const diagrams = [];
const formulas = [];
for (const f of folders) {
  for (const name of readdirSync(resolve(T, f)).filter((n) => /^batch-\d+\.fr\.tex$/.test(n))) {
    const src = readFileSync(resolve(T, f, name), 'utf8');
    const at = src.indexOf('\\begin{document}');
    if (at < 0) continue;
    const body = src.slice(at).replace(/(?<!\\)%.*$/gm, '');
    const pageOf = (i) => [...body.slice(0, i).matchAll(/\\page\{([^}]*)\}/g)].pop()?.[1];
    for (const m of body.matchAll(/\\begin\{tikzcd\}[\s\S]*?\\end\{tikzcd\}/g)) {
      const inner = m[0].replace(/^\\begin\{tikzcd\}(\[[^\]]*\])?/, '').replace(/\\end\{tikzcd\}$/, '');
      const arrows = (inner.match(/\\arrow\[/g) ?? []).length;
      const nodes = inner.split(/\\\\(?![a-zA-Z])/).flatMap((r) => r.split('&')).filter((c) => c.replace(/\\arrow\[[^\]]*\]/g, '').trim()).length;
      const labels = [...inner.matchAll(/\\arrow\[([^\]]*)\]/g)].flatMap((a) => [...a[1].matchAll(/"((?:[^"\\]|\\.)*)"/g)].map((q) => q[1]));
      const syms = symbols(inner.replace(/\\arrow\[[^\]]*\]/g, ' ') + ' ' + labels.join(' ')).size;
      diagrams.push({ f, page: pageOf(m.index), raw: m[0], score: nodes + arrows + 2 * syms, nodes, arrows });
    }
    for (const m of body.matchAll(/(?<!\\)\\\[([\s\S]*?)(?<!\\)\\\]|\\begin\{(equation\*?|align\*?|gather\*?)\}([\s\S]*?)\\end\{\2\}/g)) {
      const inner = (m[1] ?? m[3]).trim();
      const size = (inner.match(/\\[a-zA-Z]+|[A-Za-z0-9+\-=<>|/*!()[\]]/g) ?? []).length;
      formulas.push({ f, page: pageOf(m.index), raw: m[2] ? m[0] : `\\[${inner}\\]`, score: 2 * symbols(inner).size + size / 4 });
    }
  }
}
const top = (l) => l.sort((a, b) => b.score - a.score)[0];

// The transcription's apparatus, in the form the preamble gives it, reduced
// to what a picture can show: an illegible word as an ellipsis, a doubtful
// one as itself, a struck one struck.
const PREAMBLE = String.raw`\documentclass{article}
\usepackage[paperwidth=16in,paperheight=8.36in,margin=0.55in]{geometry}
\usepackage{XCharter}\usepackage{amsmath,amssymb,mathrsfs}\usepackage{tikz-cd}\usepackage{xcolor}\usepackage{adjustbox}\usepackage{varwidth}
\pagestyle{empty}\setlength{\parindent}{0pt}
\newcommand{\ill}[1]{\textcolor{black!45}{[\ldots]}}\newcommand{\uncertain}[1]{#1}\newcommand{\struck}[1]{\textcolor{black!40}{#1}}
\newcommand{\add}[1]{#1}\newcommand{\supplied}[1]{[#1]}\newcommand{\note}[1]{}\newcommand{\marginal}[1]{}
\definecolor{ink}{RGB}{19,18,16}\definecolor{muted}{RGB}{114,109,95}\definecolor{brand}{RGB}{56,83,157}
\begin{document}\color{ink}`;

function build(name, head, sub, body) {
  const tex = `${PREAMBLE}
{\\fontsize{30}{36}\\selectfont\\textbf{${head}}}\\\\[6pt]
{\\fontsize{19}{24}\\selectfont\\textcolor{muted}{${sub}}}
\\vfill
\\newsavebox\\fig\\begin{lrbox}{\\fig}\\begin{varwidth}{60in}\\centering ${body}\\end{varwidth}\\end{lrbox}
\\begin{center}\\adjustbox{width=13.8in,max totalheight=4.3in}{\\usebox\\fig}\\end{center}
\\vfill
{\\fontsize{17}{20}\\selectfont\\textcolor{brand}{grothendieck.commutator.io}\\hfill\\textcolor{muted}{A machine transcription, beside Montpellier's facsimile}}
\\end{document}
`;
  writeFileSync(resolve(TMP, `${name}.tex`), tex);
  execFileSync('tectonic', ['-X', 'compile', `${name}.tex`, '--outdir', '.'], { cwd: TMP, stdio: ['ignore', 'pipe', 'pipe'] });
  // 16in × 8.36in at 75 dpi is 1200 × 627, LinkedIn's size.
  execFileSync('pdftoppm', ['-png', '-r', '75', '-singlefile', `${name}.pdf`, resolve(OUT, name)], { cwd: TMP });
  rmSync(resolve(TMP, `${name}.pdf`), { force: true });
}

const d = top(diagrams);
build(
  'diagrams',
  'The commutative diagrams of Grothendieck’s working notes',
  `${diagrams.length.toLocaleString('en-GB')} diagrams, one at a time — the richest: folder ${d.f}, p.~${d.page}, ${d.nodes} objects and ${d.arrows} arrows`,
  d.raw,
);
const fm = top(formulas);
build(
  'formulas',
  'The displayed formulas of Grothendieck’s working notes',
  `${formulas.length.toLocaleString('en-GB')} formulas, the richest first — here folder ${fm.f}, p.~${fm.page}`,
  fm.raw,
);
process.stdout.write(`og: diagrams.png (folder ${d.f} p. ${d.page}), formulas.png (folder ${fm.f} p. ${fm.page}) → public/og/\n`);
