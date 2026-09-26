#!/usr/bin/env node
/**
 * Gathers the displayed formulas of the transcriptions into a gallery.
 *
 *   node scripts/formulas.mjs
 *
 * Every formula set apart from the text — \[…\], equation, align, gather —
 * one slide each, a carousel per folder and one of the richest across the
 * fonds, rendered by the reading views' own shell (scripts/render.mjs), so a
 * formula looks here as it does on its page, apparatus included: an \ill{}
 * inside a subscript stays an illegible subscript.
 *
 * Writes public/transcripts/formulas/<folder>.html and richest.html (derived,
 * unversioned, built in the deploy after the reading views) and the census
 * src/content/formulas.json the /formulas/ page reads.
 *
 * « Richest » is measured, not judged: the distinct symbols a formula uses
 * (scripts/lib/symbols.mjs — a letter in a given alphabet, a named symbol, an
 * operator) and its size in symbols written. It finds the formulas that carry
 * the most, not the most important ones, which no count can find.
 */
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { escapeHtml, readingPage } from './render.mjs';
import { CAROUSEL_STYLE, carouselNav, withSlides } from './lib/carousel.mjs';
import { symbols } from './lib/symbols.mjs';

const ROOT = resolve(import.meta.dirname, '..');
const T = resolve(ROOT, 'transcripts');
const OUT = resolve(ROOT, 'public/transcripts/formulas');
const JSON_OUT = resolve(ROOT, 'src/content/formulas.json');

const catalogue = readFileSync(resolve(ROOT, 'src/content/catalogue.ts'), 'utf8');
const COTE = new Map();
for (const m of catalogue.matchAll(/"id": "([^"]+)",\s*"file": "[^"]+",\s*"date": "([^"]*)",\s*"title": "((?:[^"\\]|\\.)*)"/g))
  COTE.set(m[1], { date: m[2], title: m[3].replace(/\\"/g, '"') });
const byShelfmark = (a, b) => {
  const [a0, a1 = '0'] = a.split('-');
  const [b0, b1 = '0'] = b.split('-');
  return Number(a0) - Number(b0) || Number(a1) - Number(b1);
};

/** Symbols written, counted as symbols() counts them but with repeats. */
const size = (tex) => (tex.match(/\\[a-zA-Z]+|[A-Za-z0-9+\-=<>|/*!()[\]]/g) ?? []).length;

/**
 * The display, as the reading views give it to KaTeX: a \[…\] by its
 * content, an environment whole inside \[…\] — so that each line of a
 * gather or an align keeps its own \tag, which aligned and gathered refuse.
 */
const display = (env, body, raw) => (env ? raw : body);

const STYLE = `
  .dg { margin: 0 0 1.4rem; padding: .9rem 1rem 1rem; border: 1px solid var(--rule); border-radius: 10px; background: #fff; }
  .dg figcaption { display: flex; justify-content: space-between; gap: 1rem; font-size: 12px; color: var(--ink3); margin-bottom: .5rem; }
  .dg figcaption a { color: var(--ink2); text-decoration: none; font-weight: 600; }
  .dg figcaption a:hover { text-decoration: underline; }
  .dg-n { font-variant-numeric: tabular-nums; color: var(--ink4); text-align: right; }
  .dg .ltx_p { margin: 0; text-align: center; overflow-x: auto; font-size: 20px; }
  .dg .tr-src { font-size: 11px; color: var(--ink4); }
  .dg .tr-src pre { white-space: pre-wrap; text-align: left; font-size: 11.5px; }
${CAROUSEL_STYLE}`;

const figureOf = (d, i, n, withFolder) =>
  `<figure class="dg" id="d${i + 1}">` +
  `<figcaption><a href="/#${d.folder}/${d.batch}" target="_top">${withFolder ? `n° ${d.folder} · ` : ''}batch ${d.batch}${d.page ? ` · p. ${escapeHtml(d.page)}` : ''} — lire la page</a>` +
  `<span class="dg-n">${i + 1} / ${n} · ${d.symbols} symboles distincts, ${d.size} écrits</span></figcaption>` +
  `<div class="ltx_p">\\[${escapeHtml(display(d.env, d.body, d.raw))}\\]</div>` +
  `<details class="tr-src"><summary>LaTeX</summary><pre>${escapeHtml(d.raw)}</pre></details></figure>`;

const page = (meta, name, items, withFolder) =>
  withSlides(
    readingPage({
      meta,
      lang: 'fr',
      name,
      html: carouselNav(items.length, 'Formules') + items.map((d, i) => figureOf(d, i, items.length, withFolder)).join('\n'),
      extraStyle: STYLE,
    }),
  );

const folders = readdirSync(T, { withFileTypes: true })
  .filter((d) => d.isDirectory() && COTE.has(d.name))
  .map((d) => d.name)
  .sort(byShelfmark);

mkdirSync(OUT, { recursive: true });
const ALL = [];
const census = [];
for (const f of folders) {
  const found = [];
  for (const name of readdirSync(resolve(T, f)).filter((n) => /^batch-\d+\.fr\.tex$/.test(n)).sort()) {
    const batch = Number(/batch-(\d+)/.exec(name)[1]);
    const src = readFileSync(resolve(T, f, name), 'utf8');
    const at = src.indexOf('\\begin{document}');
    if (at < 0) continue;
    const body = src.slice(at).replace(/(?<!\\)%.*$/gm, '');
    const pages = [...body.matchAll(/\\page\{([^}]*)\}/g)].map((m) => ({ at: m.index, n: m[1] }));
    // \[ opens a display only when it is not the tail of a \\[4pt] line
    // break, which the arrays of this fonds are full of.
    const re = /(?<!\\)\\\[([\s\S]*?)(?<!\\)\\\]|\\begin\{(equation\*?|align\*?|gather\*?)\}([\s\S]*?)\\end\{\2\}/g;
    for (const m of body.matchAll(re)) {
      const inner = (m[1] ?? m[3]).trim();
      if (!inner) continue;
      found.push({
        folder: f,
        batch,
        page: pages.filter((p) => p.at < m.index).pop()?.n ?? null,
        env: m[2] ?? null,
        body: inner,
        raw: m[0],
        symbols: symbols(inner).size,
        size: size(inner),
      });
    }
  }
  if (!found.length) continue;
  ALL.push(...found);
  const cote = COTE.get(f);
  const seen = found.map((d) => Number(d.page)).filter(Number.isFinite);
  writeFileSync(
    resolve(OUT, `${f}.html`),
    page(
      { folder: f, first: Math.min(...seen), last: Math.max(...seen), title: cote.title, dating: cote.date, watermark: 'Édition de démonstration' },
      `${found.length} formule${found.length > 1 ? 's' : ''}`,
      found,
      false,
    ),
  );
  census.push({
    id: f,
    title: cote.title,
    date: cote.date,
    n: found.length,
    maxSymbols: Math.max(...found.map((d) => d.symbols)),
  });
}

// Distinct symbols first — the variety a reader must hold — and then size,
// which alone would crown the longest computation rather than the densest.
const richness = (d) => 2 * d.symbols + d.size / 4;
const RICHEST = [...ALL].sort((a, b) => richness(b) - richness(a)).slice(0, 200);
writeFileSync(
  resolve(OUT, 'richest.html'),
  page(
    { folder: 'tous', first: 1, last: RICHEST.length, title: 'les formules les plus riches du fonds', dating: '', watermark: 'Édition de démonstration' },
    `${RICHEST.length} formules`,
    RICHEST,
    true,
  ).replace(/Cote n° tous(, | · )pages 1–\d+/g, 'Tout le fonds'),
);

writeFileSync(
  JSON_OUT,
  `${JSON.stringify(
    {
      $why: 'Generated by `node scripts/formulas.mjs` from the displayed formulas of transcripts/*/batch-*.fr.tex — do not edit by hand.',
      built: new Date().toISOString().slice(0, 10),
      total: ALL.length,
      medianSymbols: [...ALL].map((d) => d.symbols).sort((a, b) => a - b)[Math.floor(ALL.length / 2)],
      folders: census,
      richest: RICHEST.slice(0, 12).map((d, i) => ({ i: i + 1, folder: d.folder, batch: d.batch, page: d.page, symbols: d.symbols, size: d.size })),
    },
    null,
    1,
  )}\n`,
);
process.stdout.write(`${ALL.length} formulas in ${census.length} folders → public/transcripts/formulas/, src/content/formulas.json\n`);
