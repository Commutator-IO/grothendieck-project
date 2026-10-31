// Checks the page references of the Lean article against the transcriptions
// and the findings. Three tests:
//   1. every \lot{cote}{batch}{page} names a page that the transcription of
//      that batch holds (transcripts/<cote>/batch-NN.fr.tex has \page{page});
//   2. a statement box whose title gives its pages (« pages 38 à 42 ») and
//      names a finding (\piste{id}) agrees with that finding's pages field;
//   3. the \lot that follows a box points inside the pages its title gives.
// It prints the disagreements; it changes nothing.
//
//   node scripts/check-page-refs.mjs
import { existsSync, readdirSync, readFileSync } from 'node:fs';
import { join, resolve } from 'node:path';

const root = resolve(import.meta.dirname, '..');
const T = join(root, 'transcripts');
const findings = readFileSync(join(root, 'src/content/findings.ts'), 'utf8');

const pagesOfBatch = new Map();
function batchPages(cote, batch) {
  const key = `${cote}/${batch}`;
  if (!pagesOfBatch.has(key)) {
    const f = join(T, cote, `batch-${String(batch).padStart(2, '0')}.fr.tex`);
    const set = new Set();
    if (existsSync(f)) for (const m of readFileSync(f, 'utf8').matchAll(/\\page\{(\d+)\}/g)) set.add(Number(m[1]));
    pagesOfBatch.set(key, existsSync(f) ? set : null);
  }
  return pagesOfBatch.get(key);
}

/** « pages 38 à 42 », « page 13 », « pages 3 et 9 », « pages 2, 3 et 20 » → numbers */
function pagesIn(text) {
  const m = /\bpages?\s+([\d\s,àet–-]+?)(?=[,;)\]]|\s+[a-zA-Zé$\\]|$)/i.exec(text);
  if (!m) return null;
  const out = [];
  for (const part of m[1].split(/,|\bet\b/)) {
    const r = part.trim().split(/\s*(?:à|–|-)\s*/).map(Number);
    if (r.length === 2 && r[0] && r[1]) for (let p = r[0]; p <= r[1]; p++) out.push(p);
    else if (r[0]) out.push(r[0]);
  }
  return out.length ? out : null;
}

function findingPages(id) {
  const i = findings.indexOf(`id: '${id}'`);
  if (i < 0) return null;
  const m = /pages: '([^']*)'/.exec(findings.slice(i, i + 400));
  return m ? pagesIn(`pages ${m[1].replace(/–/g, ' à ')}`) : null;
}

const files = [];
for (const d of ['docs/lean/sections', 'docs/lean/sections/autres'])
  for (const f of readdirSync(join(root, d))) if (f.endsWith('.tex')) files.push(join(d, f));

const issues = [];
for (const f of files) {
  const src = readFileSync(join(root, f), 'utf8');
  // 1. every \lot
  for (const m of src.matchAll(/\\lot\{([^}]+)\}\{(\d+)\}\{(\d+)\}/g)) {
    const [, cote, batch, page] = m;
    const set = batchPages(cote, Number(batch));
    if (set === null) issues.push(`${f}: \\lot{${cote}}{${batch}}{${page}}: no transcription batch ${batch} for folder ${cote}`);
    else if (!set.has(Number(page))) issues.push(`${f}: \\lot{${cote}}{${batch}}{${page}}: page ${page} is not in batch ${batch}`);
  }
  // 2 and 3: boxes « [Grothendieck, pages … , title\piste{id}] »
  for (const m of src.matchAll(/\\begin\{\w+\*?\}\[((?:[^[\]]|\[[^\]]*\])*)\]/g)) {
    const title = m[1];
    const pages = pagesIn(title);
    if (!pages) continue;
    const cote = /\\piste(?:resolue)?\{(\d+(?:-\d+)?)-/.exec(title)?.[1];
    for (const id of [...title.matchAll(/\\piste(?:resolue)?\{([^}]+)\}/g)].map((x) => x[1])) {
      const fp = findingPages(id);
      if (fp && !fp.some((p) => pages.includes(p)))
        issues.push(`${f}: box « ${title.slice(0, 70)} » gives pages ${pages[0]}–${pages.at(-1)}, finding ${id} gives ${fp[0]}–${fp.at(-1)}`);
    }
    // the first \lot after the end of this box
    const end = src.indexOf('\\end{encadre}', m.index);
    const next = end < 0 ? null : /\\lot\{([^}]+)\}\{(\d+)\}\{(\d+)\}/.exec(src.slice(end, end + 1500));
    const nextBox = end < 0 ? -1 : src.indexOf('\\begin{encadre}', end);
    if (next && cote && next[1] === cote && (nextBox < 0 || end + next.index < nextBox)) {
      const p = Number(next[3]);
      if (p < pages[0] - 1 || p > pages.at(-1) + 1)
        issues.push(`${f}: box « ${title.slice(0, 70)} » gives pages ${pages[0]}–${pages.at(-1)}, its link \\lot{${next[1]}}{${next[2]}}{${p}} points to p. ${p}`);
    }
  }
}
process.stdout.write(issues.length ? issues.join('\n') + `\n${issues.length} disagreements\n` : 'no disagreement\n');
