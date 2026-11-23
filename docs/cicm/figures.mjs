#!/usr/bin/env node
/**
 * Draws the CICM paper's data figure and writes its counts, all from one commit.
 *
 *   node docs/cicm/figures.mjs
 *
 * Every figure is read at SNAPSHOT (`git show SNAPSHOT:…`), never from the
 * working tree, so that the paper describes one state of the repository and
 * work in progress by other agents is not counted. Moving SNAPSHOT is a
 * deliberate step: rerun this script, then reread the prose that comments on
 * the numbers.
 *
 * Writes beside this file:
 * - fig-themes.tex: the number of top-level `theorem` declarations per theme,
 *   the themes being the parts of the Lean appendix (docs/lean/article.tex),
 *   each part listing the folders whose proofs it explains. A part with no
 *   proof is drawn with a zero bar: those are the themes Mathlib does not yet
 *   reach.
 * - fig-counts.tex: the counts the text cites, as macros (\cnt…): Lean files,
 *   lines and declarations, the proof cards and their verdicts, the boxed
 *   statements of the appendix by label, its page count (pdfinfo), commits,
 *   findings, the transcription totals and the review answers.
 * fig-pipeline.tex is drawn by hand, because it states decisions and not data.
 */
import { execFileSync } from 'node:child_process';
import { writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { resolve } from 'node:path';

const here = import.meta.dirname;
const root = resolve(here, '../..');
const git = (...a) => execFileSync('git', a, { cwd: root, encoding: 'utf8', maxBuffer: 1 << 28 });
const SNAPSHOT = '017e99bb7f3afb7fe4840c72fcc2914d92af50ab';
// The Lean proofs of the fonds live in GrothendieckArchivesProofs since 22 November 2026 (#17);
// PROOFS is a clone of it (set PROOFS_REPO), read at PROOFS_SNAPSHOT. The history of `lean/` in
// this repository up to LEAN_LAST (the commit before the move) is counted with it.
const PROOFS_REPO = process.env.PROOFS_REPO ?? resolve(root, '../GrothendieckArchivesProofs');
const PROOFS_SNAPSHOT = '2500b677a0b6bafc24d131faf4aa032919acfa06';
const LEAN_LAST = '03e68ee4^';
const pgit = (...a) => execFileSync('git', ['-C', PROOFS_REPO, ...a], { encoding: 'utf8', maxBuffer: 1 << 28 });
const pat = (path) => pgit('show', `${PROOFS_SNAPSHOT}:${path}`);
const at = (path) => git('show', `${SNAPSHOT}:${path}`);
const short = SNAPSHOT.slice(0, 7);
const months = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];
const longDate = (iso) => `${Number(iso.slice(8, 10))} ${months[Number(iso.slice(5, 7)) - 1]} ${iso.slice(0, 4)}`;
const snapDate = longDate(git('log', '-1', '--format=%cs', SNAPSHOT).trim());
const sum = (xs) => xs.reduce((a, b) => a + b, 0);
const startsWith = (text, word) => text.split('\n').filter((l) => l.startsWith(word)).length;

// Theorems per file. A folder has one file `Folder<cote>.lean` or several
// (`Folder101Ext.lean`…), and some files belong to no folder (`IhesSGA6_2_3.lean`,
// `EffectiveVenken.lean`); the shared `Attr.lean` is not a proof.
const files = pgit('ls-tree', '-r', '--name-only', PROOFS_SNAPSHOT, 'Grothendieck/').trim().split('\n').filter((f) => !/\/Attr\.lean$/.test(f));
const count = {};
let lines = 0;
let lemmas = 0;
let privates = 0;
for (const f of files) {
  const text = pat(f);
  count[f.replace(/^.*\//, '').replace(/\.lean$/, '')] = startsWith(text, 'theorem ');
  lines += text.split('\n').length - (text.endsWith('\n') ? 1 : 0);
  lemmas += startsWith(text, 'lemma ');
  privates += startsWith(text, 'private theorem ');
}
const total = sum(Object.values(count));

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

const tex = at('docs/lean/article.tex');
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
    // the folder's own file and its sub-files (Folder101 -> Folder101Ext, not Folder1012)
    const mine = Object.keys(count).filter((k) => k === s || (k.startsWith(s) && /[A-Z]/.test(k[s.length])));
    if (!mine.length) continue; // a section whose proof is not yet committed
    parts.at(-1).folders.push(m[1]);
    for (const k of mine) {
      parts.at(-1).n += count[k];
      seen.add(k);
    }
  }
}
const sections = parts.flatMap((p) => p.folders);
const missing = Object.keys(count).filter((s) => !seen.has(s));
if (missing.length) process.stderr.write(`figures: not in any part: ${missing.join(', ')}\n`);
const inParts = parts.reduce((a, p) => a + p.n, 0);

// Horizontal bars, in the appendix's order (top to bottom).
const rows = [...parts].reverse();
const coords = rows.map((p) => `(${p.n},{${p.name}})`).join(' ');
const sym = rows.map((p) => `{${p.name}}`).join(',');
const empty = parts.filter((p) => p.n === 0).length;
const out = `% Drawn by docs/cicm/figures.mjs from Grothendieck/ of GrothendieckArchivesProofs at ${PROOFS_SNAPSHOT.slice(0, 7)}
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
\\caption{Lean theorems per theme, the themes being the ${parts.length} parts of the written-out appendix in their order (${inParts.toLocaleString('en-US')} of the ${total.toLocaleString('en-US')} theorems; ${missing.length ? `${missing.length} files with ${(total - inParts).toLocaleString('en-US')} theorems, mostly sub-files of folders the appendix has not yet written up, belong to no part` : 'every file belongs to a part'}). The ${empty} parts at zero hold only statements left unproved.}\\label{fig:themes}
\\end{figure}
`;
writeFileSync(resolve(here, 'fig-themes.tex'), out);

// Proof cards and their verdicts (src/content/proofs.ts).
const proofs = at('src/content/proofs.ts');
// A card carries one verdict, or several when its statements differ; a card
// counts once under each verdict it carries.
const verdicts = [...proofs.matchAll(/^    verdict: (.*),$/gm)].map((m) => [...m[1].matchAll(/'([^']*)'/g)].map((v) => v[1]));
const verdict = (v) => verdicts.filter((vs) => vs.includes(v)).length;

// Boxed statements of the appendix, in the sections of its parts, by label.
// The label rule is the appendix's (docs/lean/article.tex, before part I).
const boxes = [];
for (const s of sections) {
  for (const m of at(`docs/lean/sections/${s}.tex`).matchAll(/\\begin\{(theoreme|contrexemple|enonce|lemme)\}(?:\[([^\]]*)\])?/g)) {
    boxes.push({ env: m[1], label: m[2] ?? '' });
  }
}
const box = (env, test = () => true) => boxes.filter((b) => b.env === env && test(b.label)).length;
const his = (l) => l.startsWith('Grothendieck,');
const edition = (l) => !his(l) && /[ée]dition/.test(l);
const after = (l) => !his(l) && !edition(l) && /^[Dd]'après/.test(l);
for (const b of boxes) if (b.env === 'theoreme' && !his(b.label) && !edition(b.label) && !after(b.label)) process.stderr.write(`figures: theorem with no label class: ${b.label}\n`);

// Appendix pages, from the committed PDF.
const pdf = resolve(tmpdir(), `cicm-lean-${short}.pdf`);
writeFileSync(pdf, execFileSync('git', ['show', `${SNAPSHOT}:docs/lean/article.pdf`], { cwd: root, maxBuffer: 1 << 28 }));
const pages = Number(execFileSync('pdfinfo', [pdf], { encoding: 'utf8' }).match(/^Pages:\s+(\d+)/m)[1]);

// Findings (src/content/findings.ts), transcription totals (hand.json), review answers.
const findings = at('src/content/findings.ts');
const status = (s) => [...findings.matchAll(new RegExp(`status: '${s}'`, 'g'))].length;
const hand = JSON.parse(at('src/content/hand.json')).folders;
const answered = Object.entries(JSON.parse(at('src/content/review-answered.json')).items).filter(([, v]) => v.issue);
const settled = (v) => ['applied', 'confirmed', 'corrected'].includes(v.result);
const kind = (k) => answered.filter(([id]) => id.split('-')[0] === k);

const n = (x) => x.toLocaleString('en-US');
const macros = {
  Snapshot: `\\texttt{${short}}`,
  SnapshotDate: snapDate,
  Files: n(files.length),
  FolderFiles: n(files.filter((f) => /\/Folder/.test(f)).length),
  OtherFiles: n(files.filter((f) => !/\/Folder/.test(f)).length),
  FoldersProved: n(sections.length),
  Lines: n(lines),
  Theorems: n(total),
  Lemmas: n(lemmas),
  PrivateTheorems: n(privates),
  Commits: n(Number(git('rev-list', '--count', LEAN_LAST, '--', 'lean').trim()) + Number(pgit('rev-list', '--count', PROOFS_SNAPSHOT).trim())),
  FirstCommit: longDate(git('log', '--reverse', '--format=%cs', LEAN_LAST, '--', 'lean/Grothendieck').split('\n')[0]),
  ProofsSnapshot: `\\texttt{${PROOFS_SNAPSHOT.slice(0, 7)}}`,
  Cards: n(verdicts.length),
  Holds: n(verdict('holds')),
  MoreGenerally: n(verdict('holds, more generally')),
  Partly: n(verdict('partly proved')),
  Dropped: n(verdict('the reading dropped a hypothesis')),
  GlossFalse: n(verdict('holds; the gloss was false')),
  FalsePage: n(verdict('false on the page')),
  ConjRefuted: n(verdict('conjecture of the page refuted')),
  SeveralVerdicts: n(verdicts.filter((vs) => vs.length > 1).length),
  ThmHis: n(box('theoreme', his)),
  ThmAfter: n(box('theoreme', after)),
  ThmEdition: n(box('theoreme', edition)),
  Theoremes: n(box('theoreme')),
  Counterexamples: n(box('contrexemple')),
  Enonces: n(box('enonce')),
  Lemmes: n(box('lemme')),
  AppendixPages: n(pages),
  Findings: n(status('[a-z]+')),
  FindingFolders: n(new Set([...findings.matchAll(/^\s+cote: '([^']*)'/gm)].map((m) => m[1])).size),
  Unsearched: n(status('unsearched')),
  Candidates: n(status('candidate')),
  Matched: n(status('matched')),
  Refuted: n(status('refuted')),
  Confirmed: n(status('confirmed')),
  HandFolders: n(hand.length),
  Batches: n(sum(hand.map((f) => f.batches))),
  Pages: n(sum(hand.map((f) => f.pages))),
  Drawings: n(sum(hand.map((f) => f.drawings))),
  ReviewIssues: n(new Set(answered.map(([, v]) => v.issue)).size),
  ReviewItems: n(answered.length),
  ReviewSettled: n(answered.filter(([, v]) => settled(v)).length),
  ReviewDates: n(kind('date').filter(([, v]) => settled(v)).length),
  ReviewInsertions: n([...kind('supplied'), ...kind('add')].filter(([, v]) => settled(v)).length),
};
const counts = `% Written by docs/cicm/figures.mjs from the repository at ${short}. Do not edit by hand.
${Object.entries(macros).map(([k, v]) => `\\newcommand{\\cnt${k}}{${v}}`).join('\n')}
`;
writeFileSync(resolve(here, 'fig-counts.tex'), counts);
process.stdout.write(`figures: at ${short}, ${files.length} files, ${total} theorems, ${parts.length} parts (${empty} empty), ${inParts} in parts, ${verdicts.length} cards, ${pages} appendix pages\n`);
