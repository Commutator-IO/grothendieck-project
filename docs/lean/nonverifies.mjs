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

const rows = [];
for (const file of inputs) {
  const path = resolve(here, file);
  if (!existsSync(path)) continue;
  const src = readFileSync(path, 'utf8');
  const section = src.match(/\\label\{(sec:[^}]+)\}/)?.[1];
  for (const m of src.matchAll(/\\nonverifie/g)) {
    const line = src.slice(src.lastIndexOf('\n', m.index) + 1, m.index);
    const title = line.match(/\\begin\{\w+\*?\}\[(.*)\]\s*$/)?.[1] ?? '';
    rows.push({ cote: coteOf(title, file, section), statement: clean(title) || '(sans titre)' });
  }
}

const body = rows
  .map((r, i) => `${r.cote} & ${r.statement} & \\pageref{nv:${i + 1}}\\\\`)
  .join('\n');

writeFileSync(
  resolve(here, 'annexe-nonverifies.tex'),
  `% Engendré par nonverifies.mjs — ne pas éditer à la main.
\\section*{Énoncés non vérifiés en Lean}\\addcontentsline{toc}{section}{Énoncés non vérifiés en Lean}

Les ${rows.length} énoncés marqués \\textcolor{piste}{\\ensuremath{\\lozenge}} dans la marge, dans l'ordre du texte : la cote, l'énoncé tel que le titre le donne, la page.

{\\small
\\begin{longtable}{@{}l>{\\raggedright\\arraybackslash}p{0.72\\linewidth}r@{}}
\\toprule
Cote & Énoncé & Page\\\\
\\midrule
\\endhead
${body}
\\bottomrule
\\end{longtable}}
`,
);
process.stdout.write(`${rows.length} statements → annexe-nonverifies.tex\n`);
