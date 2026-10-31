// Writes annexe-nonverifies.tex: one row per \nonverifie of the appendix, in
// the order the sections are \input by article.tex, so that row N cites the
// label nv:N that the N-th \nonverifie sets (see the macro in article.tex).
//
//   node docs/lean/nonverifies.mjs
//
// Rerun it whenever a \nonverifie is added or removed, then recompile twice.
import { readFileSync, writeFileSync, existsSync } from 'node:fs';
import { resolve } from 'node:path';

const here = import.meta.dirname;
const article = readFileSync(resolve(here, 'article.tex'), 'utf8');
const inputs = [...article.matchAll(/\\input\{(sections\/[^}]+)\}/g)].map((m) => m[1] + '.tex');

/** Removes \cmd{...} with balanced braces. */
function dropCommand(s, cmd) {
  let out = '';
  let i = 0;
  for (;;) {
    const j = s.indexOf(`\\${cmd}{`, i);
    if (j < 0) return out + s.slice(i);
    out += s.slice(i, j);
    let k = j + cmd.length + 2;
    for (let depth = 1; depth; k++) depth += s[k] === '{' ? 1 : s[k] === '}' ? -1 : 0;
    i = k;
  }
}

/** The cote a statement belongs to, from its \piste identifier or its section. */
function coteOf(title, file, section) {
  const piste = title.match(/\\piste(?:resolue)?\{(\d+(?:-\d+)?)-[a-z]/);
  if (piste) return piste[1];
  const label = section?.match(/^sec:(.+)$/);
  return label ? label[1] : file.replace(/^sections\/|\.tex$/g, '');
}

function clean(title) {
  let t = dropCommand(dropCommand(title, 'piste'), 'pisteresolue');
  t = t.replace(/\s*;\s*voir aussi[^;]*$/, '');
  t = t.replace(/^Grothendieck,\s*/, '');
  return t.trim();
}

// How each statement is checked other than by Lean (issue #91): from
// verification.json and the finding's status in src/content/findings.ts.
const verification = JSON.parse(readFileSync(resolve(here, 'verification.json'), 'utf8'));
const findings = readFileSync(resolve(here, '../../src/content/findings.ts'), 'utf8');
function statusOf(id) {
  const i = findings.indexOf(`id: '${id}'`);
  return i < 0 ? null : /status: '(\w+)'/.exec(findings.slice(i))?.[1];
}
function checkOf(ids) {
  if (ids.some((id) => verification.problem.includes(id))) return 'problème ouvert';
  const comp = ids.map((id) => verification.computation[id]).find(Boolean);
  if (comp) return `calcul (\\texttt{computations/${comp}})`;
  const st = ids.map(statusOf);
  if (st.includes('matched') || st.includes('confirmed')) return 'publié';
  if (st.includes('refuted')) return 'réfuté';
  return '---';
}

const rows = [];
for (const file of inputs) {
  const path = resolve(here, file);
  if (!existsSync(path)) continue;
  const src = readFileSync(path, 'utf8');
  const section = src.match(/\\label\{(sec:[^}]+)\}/)?.[1];
  for (const m of src.matchAll(/\\nonverifie/g)) {
    const line = src.slice(src.lastIndexOf('\n', m.index) + 1, m.index);
    const title = line.match(/\\begin\{\w+\*?\}\[(.*)\]\s*$/)?.[1] ?? '';
    const ids = [...title.matchAll(/\\piste(?:resolue)?\{([^}]+)\}/g)].map((x) => x[1]);
    rows.push({ cote: coteOf(title, file, section), statement: clean(title) || '(sans titre)', check: checkOf(ids) });
  }
}

const body = rows
  .map((r, i) => `${r.cote} & ${r.statement} & ${r.check} & \\pageref{nv:${i + 1}}\\\\`)
  .join('\n');

writeFileSync(
  resolve(here, 'annexe-nonverifies.tex'),
  `% Engendré par nonverifies.mjs — ne pas éditer à la main.
\\section*{Énoncés non vérifiés en Lean}\\addcontentsline{toc}{section}{Énoncés non vérifiés en Lean}

Les ${rows.length} énoncés marqués \\textcolor{piste}{\\ensuremath{\\lozenge}} dans la marge, dans l'ordre du texte : la cote, l'énoncé tel que le titre le donne, la vérification autre que Lean, la page. La vérification est \\emph{publié} quand la recherche bibliographique a trouvé l'énoncé imprimé, \\emph{réfuté} quand un contre-exemple le contredit, \\emph{problème ouvert} quand il est posé dans l'article des problèmes ouverts, \\emph{calcul} quand un programme le teste sur de petits cas ; un tiret signale qu'aucune vérification n'est prévue.

{\\small
\\begin{longtable}{@{}l>{\\raggedright\\arraybackslash}p{0.52\\linewidth}>{\\raggedright\\arraybackslash}p{0.2\\linewidth}r@{}}
\\toprule
Cote & Énoncé & Vérification & Page\\\\
\\midrule
\\endhead
${body}
\\bottomrule
\\end{longtable}}
`,
);
process.stdout.write(`${rows.length} statements → annexe-nonverifies.tex\n`);
