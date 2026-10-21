#!/usr/bin/env node
/**
 * Draws the CICM paper's data figure from the committed Lean files.
 *
 *   node docs/cicm/figures.mjs
 *
 * Writes fig-themes.tex beside this file: the number of top-level `theorem`
 * declarations per theme, the themes being the parts of the Lean appendix
 * (docs/lean/article.tex), each part listing the folders whose proofs it
 * explains. The counts are taken from the files as committed at HEAD
 * (`git show HEAD:lean/Grothendieck/…`), not from the working tree, so that
 * work in progress by other agents is not counted. A part with no proof is
 * drawn with a zero bar: those are the themes Mathlib does not yet reach.
 * fig-pipeline.tex is drawn by hand, because it states decisions and not data.
 */
import { execFileSync } from 'node:child_process';
import { readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const here = import.meta.dirname;
const root = resolve(here, '../..');
const git = (...a) => execFileSync('git', a, { cwd: root, encoding: 'utf8', maxBuffer: 1 << 28 });
const today = new Date().toISOString().slice(0, 10);

// Theorems per file, at HEAD.
const files = git('ls-tree', '--name-only', 'HEAD', 'lean/Grothendieck/').trim().split('\n');
const count = {};
for (const f of files) {
  const n = git('show', `HEAD:${f}`).split('\n').filter((l) => l.startsWith('theorem')).length;
  count[f.replace(/^.*\//, '').replace(/\.lean$/, '')] = n;
}
const total = Object.values(count).reduce((a, b) => a + b, 0);

// Section name in the appendix -> Lean file stem.
const stem = (s) => (s.startsWith('bourbaki-') ? 'Bourbaki' + s.slice(9) : 'Folder' + s.replace(/-/g, '_'));

// The appendix's parts, in its order, with English names.
const english = {
  'Cycles algébriques et conjectures standard': 'Algebraic cycles, standard conjectures',
  Motifs: 'Motives',
  'Théorie de Hodge': 'Hodge theory',
  'Cohomologie étale et $\\ell$-adique': 'Étale and $\\ell$-adic cohomology',
  'Groupes $p$-divisibles et groupes formels': '$p$-divisible and formal groups',
  'Algèbre universelle et théories': 'Universal algebra',
  'Analyse fonctionnelle': 'Functional analysis',
  'Théorie de la dualité': 'Duality',
  Descente: 'Descent',
  'Topos et sites': 'Topoi and sites',
  'Variétés abéliennes et schémas de Picard': 'Abelian varieties, Picard schemes',
  'Catégories tensorielles et dualité tannakienne': 'Tensor categories, Tannaka duality',
  'Algèbre commutative': 'Commutative algebra',
  'Catégories et foncteurs': 'Categories and functors',
  'Géométrie formelle, modules et représentabilité': 'Formal geometry, representability',
  'K-théorie, classes de Chern et Riemann--Roch': 'K-theory, Riemann--Roch',
  'Cohomologie cristalline et de de Rham': 'Crystalline and de Rham cohomology',
  'Schémas en groupes et groupes algébriques': 'Group schemes, algebraic groups',
  'Surfaces de Riemann, uniformisation et modules des courbes': 'Riemann surfaces, moduli of curves',
  'Champs, gerbes et catégories fibrées': 'Stacks, gerbes, fibred categories',
  'Topologie combinatoire, surfaces et cartes': 'Combinatorial topology, maps',
  'Jeux et combinatoire': 'Games and combinatorics',
  'Groupes fondamentaux et théorie de Galois': 'Fundamental groups, Galois theory',
  'Polyèdres et géométrie convexe': 'Polyhedra, convex geometry',
  "Théorie de l'homotopie et catégories tests": 'Homotopy theory, test categories',
  'Topologie modérée et espaces stratifiés': 'Tame topology, stratified spaces',
  'Géométrie anabélienne et dessins': 'Anabelian geometry, dessins',
  'Ordres et géométrie des formes': 'Orders and shapes',
};

const tex = readFileSync(resolve(root, 'docs/lean/article.tex'), 'utf8');
const parts = [];
const seen = new Set();
for (const line of tex.split('\n')) {
  let m = line.match(/^\\part\{(.*)\}\s*$/);
  if (m) {
    const name = english[m[1]];
    if (!name) throw new Error(`no English name for part « ${m[1]} »`);
    parts.push({ name, folders: [], n: 0 });
    continue;
  }
  if (line.startsWith('\\part*')) break; // the closing « Bilan »
  m = line.match(/^\\input\{sections\/([^/}]+)\}/);
  if (m && parts.length) {
    const s = stem(m[1]);
    if (!(s in count)) continue; // a section whose proof is not yet committed
    parts.at(-1).folders.push(m[1]);
    parts.at(-1).n += count[s];
    seen.add(s);
  }
}
const missing = Object.keys(count).filter((s) => !seen.has(s));
if (missing.length) process.stderr.write(`figures: not in any part: ${missing.join(', ')}\n`);
const inParts = parts.reduce((a, p) => a + p.n, 0);

// Horizontal bars, in the appendix's order (top to bottom).
const rows = [...parts].reverse();
const coords = rows.map((p) => `(${p.n},{${p.name}})`).join(' ');
const sym = rows.map((p) => `{${p.name}}`).join(',');
const empty = parts.filter((p) => p.n === 0).length;
const out = `% Drawn by docs/cicm/figures.mjs on ${today} from lean/Grothendieck/*.lean at HEAD
% and the parts of docs/lean/article.tex. Do not edit by hand.
\\begin{figure}[t]\\centering
\\begin{tikzpicture}
\\begin{axis}[xbar, y=8.2pt, bar width=5pt, width=0.62\\textwidth,
  xmin=0, enlarge y limits={abs=6pt}, xlabel={theorems}, xlabel style={font=\\scriptsize},
  symbolic y coords={${sym}}, ytick=data,
  yticklabel style={font=\\scriptsize}, xticklabel style={font=\\scriptsize},
  nodes near coords, nodes near coords style={font=\\tiny},
  axis x line*=bottom, axis y line*=left, every axis plot/.append style={fill=black!35, draw=black!60}]
\\addplot[fill=black!35, draw=black!60] coordinates {${coords}};
\\end{axis}
\\end{tikzpicture}
\\caption{Lean theorems per theme, the themes being the ${parts.length} parts of the written-out appendix in their order (${inParts} of the ${total} theorems at HEAD; ${missing.length ? `the files ${missing.join(', ')} belong to no part` : 'every file belongs to a part'}). The ${empty} parts at zero hold only statements left unproved. Drawn by \\texttt{docs/cicm/figures.mjs} on ${today}.}\\label{fig:themes}
\\end{figure}
`;
writeFileSync(resolve(here, 'fig-themes.tex'), out);
process.stdout.write(`figures: ${files.length} files, ${total} theorems, ${parts.length} parts (${empty} empty), ${inParts} in parts\n`);
