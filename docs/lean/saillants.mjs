// Writes saillants.tex: the proofs that say more than the page, by a criterion
// stated in the text and applied here, not by a choice of the edition. A card
// of src/content/proofs.ts is kept when
//   1. its verdict is « plus général », « faux sur la page » or « conjecture de
//      la page réfutée » (a proof that only confirms the page, or corrects the
//      reading rather than the page, is left out), and
//   2. a finding of src/content/findings.ts proved in the same Lean file is
//      still open in the literature (candidate, unsearched) or refuted: a
//      finding the search found in print (matched, confirmed) does not count.
// Rows are grouped by verdict, then in the order of the cards.
//
//   node docs/lean/saillants.mjs
//
// Rerun it with recapitulatif.mjs whenever a card or a finding changes.
import { existsSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const here = import.meta.dirname;
const read = (p) => readFileSync(resolve(here, p), 'utf8');
const proofs = read('../../src/content/proofs.ts');
const findings = read('../../src/content/findings.ts');

/** A string field of an object literal, in either quote. */
const field = (block, name) => {
  const m = new RegExp(`\\b${name}: (?:'((?:[^'\\\\]|\\\\.)*)'|"((?:[^"\\\\]|\\\\.)*)")`).exec(block);
  return m ? (m[1] ?? m[2]) : null;
};

const GROUPS = [
  ['false on the page', 'La page est fausse telle qu\'énoncée', 'faux sur la page'],
  ['conjecture of the page refuted', 'Une conjecture de la page est réfutée', 'conjecture réfutée'],
  ['holds, more generally', 'La preuve généralise la page', 'plus général'],
];
const OPEN = new Set(['candidate', 'unsearched', 'refuted']);
const STATUS = { candidate: 'piste ouverte', unsearched: 'piste ouverte', refuted: 'piste réfutée' };

// Findings by Lean file: the statuses of the mathematical rows proved there.
const byFile = new Map();
for (const block of findings.split(/\n\s*\{\n(?=\s*id: )/).slice(1)) {
  if (field(block, 'kind') !== 'mathematical') continue;
  const lean = /\blean: \{\s*file: (?:'([^']+)'|"([^"]+)")/.exec(block);
  if (!lean) continue;
  const file = lean[1] ?? lean[2];
  (byFile.get(file) ?? byFile.set(file, []).get(file)).push({ id: field(block, 'id'), status: field(block, 'status') });
}

// A cote with no section of its own is discussed in a thematic file under
// sections/autres/: its title is the last heading before the \verifie that
// names its Lean file.
const thematic = readdirSync(resolve(here, 'sections/autres')).map((f) => readFileSync(resolve(here, 'sections/autres', f), 'utf8'));
function titleOf(cote, leanFile, ids) {
  const own = resolve(here, 'sections', `${cote}.tex`);
  if (existsSync(own)) return { title: /\\section\[(?:Cote [^:]+ : )?([^\]]+)\]/.exec(readFileSync(own, 'utf8'))?.[1], ref: `\\ref{sec:${cote}}` };
  // The statement box that carries the \verifie: « [Grothendieck, pages 55 à
  // 58, unicité du recollement\piste{…}] » gives « unicité du recollement ».
  for (const tex of thematic) {
    const box = new RegExp(String.raw`\\begin\{[a-z]+\*?\}\[((?:[^\[\]]|\[[^\]]*\])*)\]\s*\\verifie(?:\[[^\]]*\])?\{${leanFile}\}`).exec(tex);
    if (!box) continue;
    const title = box[1]
      .replace(/\\piste\{[^}]*\}/g, '')
      .replace(/^(?:Grothendieck|D'après)[^,]*,\s*/, '')
      .replace(/^(?:pages?|p\.)[^,]*,\s*/i, '')
      .trim();
    return { title, ref: '' };
  }
  // Failing that, the box that carries the finding's \piste.
  for (const tex of thematic)
    for (const id of ids) {
      const box = new RegExp(String.raw`\\begin\{[a-z]+\*?\}\[((?:[^\[\]]|\[[^\]]*\])*\\piste\{${id}\}(?:[^\[\]]|\[[^\]]*\])*)\]`).exec(tex);
      if (box) return { title: box[1].replace(/\\piste\{[^}]*\}/g, '').replace(/^(?:Grothendieck|D'après)[^,]*,\s*/, '').replace(/^(?:pages?|p\.)[^,]*,\s*/i, '').trim(), ref: '' };
    }
  return { title: null, ref: '' };
}

const rows = Object.fromEntries(GROUPS.map(([v]) => [v, new Map()]));
const list = proofs.slice(proofs.indexOf('PROOFS'));
for (const block of list.split(/\n  \{\n/).slice(1)) {
  const vm = /\bverdict: (\[[^\]]*\]|'[^']+'|"[^"]+")/.exec(block);
  if (!vm) continue;
  const verdicts = [...vm[1].matchAll(/['"]([^'"]+)['"]/g)].map((x) => x[1]);
  const group = GROUPS.find(([v]) => verdicts.includes(v));
  if (!group) continue;
  const file = field(block, 'lean');
  const open = (byFile.get(file) ?? []).filter((f) => OPEN.has(f.status));
  if (!open.length) continue;
  const cote = field(block, 'folder');
  const page = field(block, 'page');
  const leanFile = file.replace(/^lean\/Grothendieck\//, '').replace(/\.lean$/, '');
  const { title, ref } = titleOf(cote, leanFile, open.map((f) => f.id));
  const statement = title ? title.charAt(0).toLocaleUpperCase('fr') + title.slice(1) : '—';
  const status = [...new Set(open.map((f) => STATUS[f.status]))].join(', ');
  // Two cards of one cote under one verdict make one row, their pages joined.
  const row = rows[group[0]].get(cote);
  if (row) row.pages.push(page);
  else rows[group[0]].set(cote, { pages: [page], statement, status, leanFile, ref });
}

const line = (cote, r) =>
  `${cote} & ${r.pages.join(' ; ').replace(/–/g, '--')} & ${r.statement} & ${r.status} & \\href{\\leanblobmain/${r.leanFile}.lean}{\\texttt{\\detokenize{${r.leanFile}}}} & ${r.ref}\\\\`;
const body = GROUPS.filter(([v]) => rows[v].size)
  .map(([v, head]) => `\\multicolumn{6}{@{}l}{\\textit{${head}} (${rows[v].size})}\\\\[1pt]\n${[...rows[v]].map(([c, r]) => line(c, r)).join('\n')}`)
  .join('\n');
const total = GROUPS.reduce((s, [v]) => s + rows[v].size, 0);

const out = `% Engendré par saillants.mjs : ne pas modifier à la main.
\\section*{Ce que les preuves ajoutent à la page}\\addcontentsline{toc}{section}{Ce que les preuves ajoutent à la page}

Les démonstrations qui disent plus que la page, retenues par un critère et non par un choix de l'édition. Une démonstration figure ici si son verdict est \\emph{plus général}, \\emph{faux sur la page} ou \\emph{conjecture de la page réfutée}, et si une piste qu'elle démontre reste ouverte dans la littérature ou a été réfutée : une piste que la recherche a retrouvée imprimée n'est pas comptée. Ce n'est pas un classement par importance, et une piste ouverte n'est pas une affirmation de nouveauté. Les contre-exemples reposent sur les hypothèses telles que la lecture les donne ; celles des cotes où la page est dite fausse restent à relire sur le fac-similé.

{\\small\\setlength{\\tabcolsep}{4pt}
\\begin{longtable}{@{}>{\\raggedright\\arraybackslash}p{1.2cm}>{\\raggedright\\arraybackslash}p{1.8cm}>{\\raggedright\\arraybackslash}p{6.2cm}>{\\raggedright\\arraybackslash}p{2.2cm}p{2.6cm}r@{}}
\\toprule
Cote & Pages & Énoncé & Piste & Fichier Lean & \\S\\\\
\\midrule
\\endhead
${body}
\\bottomrule
\\end{longtable}}
`;
writeFileSync(resolve(here, 'saillants.tex'), out);
process.stdout.write(`saillants.tex: ${total} rows\n`);
