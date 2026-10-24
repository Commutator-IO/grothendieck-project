// Writes recapitulatif.tex: the summary table that opens the appendix, one row
// per section, in the order article.tex \inputs them, under the name of each
// part. The statement is the section's short title; the verdicts are those of
// its cards in src/content/proofs.ts (the two Bourbaki sections have no card
// and take theirs from BOURBAKI below); the file is the one its \verifie names.
//
//   node docs/lean/recapitulatif.mjs
//
// Rerun it whenever a section is added, retitled or changes verdict, then
// recompile.
import { readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const here = import.meta.dirname;
const article = readFileSync(resolve(here, 'article.tex'), 'utf8');
const proofs = readFileSync(resolve(here, '../../src/content/proofs.ts'), 'utf8');

const VERDICT = {
  holds: 'confirmé tel que lu',
  'holds, more generally': 'plus général',
  'partly proved': 'partiel',
  'false on the page': 'faux sur la page (contre-exemple)',
  'the reading dropped a hypothesis': 'correction de la lecture (hypothèse omise)',
  'holds; the gloss was false': 'correction de la lecture (glose fausse)',
};
const BOURBAKI = {
  'bourbaki-288': 'holds, more generally',
  'bourbaki-457': 'false on the page',
};

const verdicts = {};
for (const m of proofs.matchAll(/folder: '([^']+)',[\s\S]*?verdict: '([^']+)'/g)) {
  (verdicts[m[1]] ??= []).push(m[2]);
}

/** The argument of \cmd[...] with balanced brackets, starting at the [. */
function bracketArg(s, start) {
  let depth = 0;
  for (let k = start; k < s.length; k++) {
    if (s[k] === '[') depth++;
    else if (s[k] === ']' && --depth === 0) return s.slice(start + 1, k);
  }
  throw new Error('unbalanced');
}

const rows = [];
for (const m of article.matchAll(/\\part\{([^}]*(?:\{[^}]*\}[^}]*)*)\}|\\input\{sections\/([^}]+)\}/g)) {
  if (m[1] !== undefined) {
    rows.push(`\\multicolumn{5}{@{}l}{\\textit{${m[1]}}}\\\\[1pt]`);
    continue;
  }
  const name = m[2];
  if (name.includes('/') || name === 'reste') continue;
  const tex = readFileSync(resolve(here, 'sections', name + '.tex'), 'utf8');
  const short = bracketArg(tex, tex.indexOf('\\section[') + '\\section'.length);
  const bare = short.replace(/^(Cote [^:]+|Rédaction Bourbaki [^:]+) : /, '');
  const statement = bare.charAt(0).toLocaleUpperCase('fr') + bare.slice(1);
  const cote = name.startsWith('bourbaki-') ? `Bourbaki ${name.slice(9)}` : name;
  const [, base = '\\leanblob', file] = tex.match(/\\verifie(?:\[([^\]]*)\])?\{([^}]+)\}/);
  const vs = [...new Set(verdicts[name] ?? [BOURBAKI[name]])];
  if (!vs.length || vs.some((v) => !VERDICT[v])) throw new Error(`verdict of ${name}: ${vs}`);
  rows.push(
    `${cote} & ${statement} & ${vs.map((v) => VERDICT[v]).join(' ; ')} & \\href{${base}/${file}.lean}{\\texttt{\\detokenize{${file}}}} & \\ref{sec:${name}}\\\\`,
  );
}
// Parts with no section of their own (the empty ones) leave a heading with no row.
const kept = rows.filter((r, i) => !(r.startsWith('\\multicolumn') && (i + 1 === rows.length || rows[i + 1].startsWith('\\multicolumn'))));

const out = `% Engendré par recapitulatif.mjs : ne pas modifier à la main.
\\section*{Tableau récapitulatif}\\addcontentsline{toc}{section}{Tableau récapitulatif}

Une ligne par section, dans l'ordre des parties : la cote, l'énoncé démontré en quelques mots, le verdict, le fichier Lean et la section. \\emph{Confirmé tel que lu} : l'énoncé tient sous les hypothèses que la lecture écrit ; \\emph{plus général} : il tient sous des hypothèses plus faibles ; \\emph{partiel} : une partie seulement est démontrée, ou dans un modèle, ce que la section précise ; \\emph{correction de la lecture} : la lecture omettait une hypothèse de la page ou glosait faussement un énoncé juste ; \\emph{faux sur la page} : un contre-exemple réfute l'affirmation du feuillet.

\\begin{landscape}
{\\small\\setlength{\\tabcolsep}{4pt}
\\begin{longtable}{@{}>{\\raggedright\\arraybackslash}p{1.8cm}>{\\raggedright\\arraybackslash}p{12cm}>{\\raggedright\\arraybackslash}p{3.4cm}p{3.4cm}r@{}}
\\toprule
Cote & Énoncé & Verdict & Fichier Lean & \\S\\\\
\\midrule
\\endhead
${kept.join('\n')}
\\bottomrule
\\end{longtable}}
\\end{landscape}
`;
writeFileSync(resolve(here, 'recapitulatif.tex'), out);
process.stdout.write(`recapitulatif.tex: ${kept.filter((r) => !r.startsWith('\\multicolumn')).length} rows\n`);
