#!/usr/bin/env node
/**
 * Gathers every commutative diagram in the transcriptions into a gallery.
 *
 *   node scripts/diagrams.mjs
 *
 * The diagrams are the language of this fonds, and they are scattered: 1,330
 * of them across the folders read so far, each on its page, between a line of
 * prose and a formula. This puts them side by side, one page per folder, each
 * diagram captioned with the batch and page it stands on and linked back to
 * the reading beside its facsimile.
 *
 * Writes two things:
 *   - public/transcripts/diagrams/<folder>.html — the gallery of one folder,
 *     rendered by the same renderDiagram and in the same reading-view shell
 *     as the transcriptions (scripts/render.mjs), so a diagram looks here
 *     exactly as it does on its page. Derived and unversioned, like the
 *     reading views beside it.
 *   - src/content/diagrams.json — the census the site's /diagrams/ page reads:
 *     per folder how many diagrams and on which pages, and per diagram its
 *     size in nodes and arrows.
 *
 * Nothing is read but the transcription's own tikzcd: a diagram the transcriber
 * described in a note rather than drew is not a diagram here.
 */
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { escapeHtml, readingPage, renderDiagram } from './render.mjs';
import { symbols } from './lib/symbols.mjs';
import { CAROUSEL_STYLE, carouselNav, withSlides } from './lib/carousel.mjs';

const ROOT = resolve(import.meta.dirname, '..');
const T = resolve(ROOT, 'transcripts');
const OUT = resolve(ROOT, 'public/transcripts/diagrams');
const JSON_OUT = resolve(ROOT, 'src/content/diagrams.json');

const catalogue = readFileSync(resolve(ROOT, 'src/content/catalogue.ts'), 'utf8');
const COTE = new Map();
for (const m of catalogue.matchAll(/"id": "([^"]+)",\s*"file": "[^"]+",\s*"date": "([^"]*)",\s*"title": "((?:[^"\\]|\\.)*)"/g))
  COTE.set(m[1], { date: m[2], title: m[3].replace(/\\"/g, '"') });
const byShelfmark = (a, b) => {
  const [a0, a1 = '0'] = a.split('-');
  const [b0, b1 = '0'] = b.split('-');
  return Number(a0) - Number(b0) || Number(a1) - Number(b1);
};

/** Nodes and arrows of one diagram, counted from its source. */
function size(raw) {
  const body = raw.replace(/^\\begin\{tikzcd\}(\[[^\]]*\])?/, '').replace(/\\end\{tikzcd\}$/, '');
  const arrows = (body.match(/\\arrow\[/g) ?? []).length;
  const rows = body.split(/\\\\(?![a-zA-Z])/).filter((r) => r.trim());
  const nodes = rows
    .flatMap((r) => r.split('&'))
    .map((c) => c.replace(/\\arrow\[[^\]]*\]/g, '').trim())
    .filter(Boolean).length;
  // The symbols of the nodes and of the arrows' labels — not the arrows'
  // options, which say how an arrow is drawn, not what it names.
  const labels = [...body.matchAll(/\\arrow\[([^\]]*)\]/g)].flatMap((m) => [...m[1].matchAll(/"((?:[^"\\]|\\.)*)"/g)].map((q) => q[1]));
  const syms = symbols(body.replace(/\\arrow\[[^\]]*\]/g, ' ') + ' ' + labels.join(' ')).size;
  return { nodes, arrows, rows: rows.length, symbols: syms };
}



const DG_STYLE = `
  .dg { margin: 0 0 1.4rem; padding: .9rem 1rem 1rem; border: 1px solid var(--rule); border-radius: 10px;
        break-inside: avoid; }
  .dg figcaption { display: flex; justify-content: space-between; font-size: 12px; color: var(--ink3);
                   margin-bottom: .5rem; }
  .dg figcaption a { color: var(--ink2); text-decoration: none; font-weight: 600; }
  .dg figcaption a:hover { text-decoration: underline; }
  .dg-n { font-variant-numeric: tabular-nums; color: var(--ink4); }
  .dg .ltx_p { margin: 0; text-align: center; overflow-x: auto; }
  /* The reading views set a diagram as a block, left-aligned, and draw its
     arrows in an SVG laid over the box from its top-left corner. Centred as
     a block here, the grid moved and the arrows stayed at the left edge of a
     full-width box, drawn away from the nodes they join. Shrink-wrapped, the
     box is the grid, and the arrows fall where they belong. */
  .dg .tr-cd { display: inline-block; text-align: left; vertical-align: top; }
  /* The arrow layer sits at z-index -1, under the nodes. Without a stacking
     context of its own it went under the card's white background too, and
     every arrow was painted and hidden. */
  .dg .tr-cd { isolation: isolate; }
${CAROUSEL_STYLE}`;

// One diagram per slide leaves room to draw it larger, and larger is what
// makes a diagram legible: the node text and the gaps between nodes grow
// together, so the arrows lengthen and their labels clear the nodes. A
// square of four nodes is drawn at 1.7 times the reading view's size; a
// diagram of eight rows or columns stays at 1, or it would not fit.
const scale = (d) => {
  const cols = Math.max(...d.raw.replace(/^\\begin\{tikzcd\}(\[[^\]]*\])?/, '').split(/\\\\(?![a-zA-Z])/).map((r) => r.split('&').length));
  const dim = Math.max(cols, d.rows);
  return dim <= 2 ? 1.7 : dim <= 3 ? 1.5 : dim <= 4 ? 1.3 : dim <= 6 ? 1.15 : 1;
};
const enlarge = (htmlOf, k) =>
  htmlOf
    .replace(/column-gap:([\d.]+)rem;row-gap:([\d.]+)rem/, (_, c, r) => `column-gap:${(c * k).toFixed(2)}rem;row-gap:${(r * k).toFixed(2)}rem`)
    .replace('<span class="tr-cd" ', `<span class="tr-cd" style="font-size:${(15.5 * k).toFixed(1)}px" `);

/** The reading view of the batch, at the page's own anchor (id="page-N"). */
const transcriptHref = (d) =>
  `/transcripts/${d.folder}/batch-${String(d.batch).padStart(2, '0')}.fr.html${d.page ? `#page-${encodeURIComponent(d.page)}` : ''}`;
/** One slide: the caption names the folder only on the pages that mix folders. */
const figureOf = (d, i, n, withFolder) =>
  `<figure class="dg" id="slide-${i + 1}">` +
  `<figcaption><span>${withFolder ? `n° ${d.folder} · ` : ''}batch ${d.batch}${d.page ? ` · p. ${escapeHtml(d.page)}` : ''} — ` +
  // The transcription at its page, and the batch beside Montpellier's facsimile.
  `<a href="${transcriptHref(d)}" target="_blank" rel="noopener">the transcription${d.page ? `, p. ${escapeHtml(d.page)}` : ''} ↗</a> · ` +
  `<a href="/#${d.folder}/${d.batch}${d.page ? `/p${encodeURIComponent(d.page)}` : ''}" target="_top">beside the facsimile</a></span>` +
  `<span class="dg-n">${i + 1} / ${n}${withFolder ? ` · ${d.nodes} nodes, ${d.arrows} arrows, ${d.symbols} symbols` : ''}</span></figcaption>` +
  `<div class="ltx_p">${enlarge(renderDiagram(d.raw), scale(d))}</div></figure>`;

const ALL = [];
const folders = readdirSync(T, { withFileTypes: true })
  .filter((d) => d.isDirectory() && COTE.has(d.name))
  .map((d) => d.name)
  .sort(byShelfmark);

mkdirSync(OUT, { recursive: true });
const census = [];
let total = 0;
for (const f of folders) {
  const found = [];
  const batches = readdirSync(resolve(T, f))
    .filter((n) => /^batch-\d+\.fr\.tex$/.test(n))
    .sort();
  for (const name of batches) {
    const batch = Number(/batch-(\d+)/.exec(name)[1]);
    const src = readFileSync(resolve(T, f, name), 'utf8');
    const at = src.indexOf('\\begin{document}');
    if (at < 0) continue;
    // Comments out, an escaped \% kept: a diagram commented out is not one.
    const body = src.slice(at).replace(/(?<!\\)%.*$/gm, '');
    const pages = [...body.matchAll(/\\page\{([^}]*)\}/g)].map((m) => ({ at: m.index, n: m[1] }));
    for (const m of body.matchAll(/\\begin\{tikzcd\}[\s\S]*?\\end\{tikzcd\}/g)) {
      const page = pages.filter((p) => p.at < m.index).pop()?.n ?? null;
      found.push({ folder: f, batch, page, raw: m[0], ...size(m[0]) });
    }
  }
  if (!found.length) continue;
  total += found.length;
  ALL.push(...found);

  const cote = COTE.get(f);
  const html =
    carouselNav(found.length, 'Diagrams') +
    found.map((d, i) => figureOf(d, i, found.length, false)).join('\n');
  const pagesSeen = found.map((d) => Number(d.page)).filter(Number.isFinite);
  writeFileSync(
    resolve(OUT, `${f}.html`),
    withSlides(readingPage({
      meta: {
        folder: f,
        first: Math.min(...pagesSeen),
        last: Math.max(...pagesSeen),
        title: cote.title,
        dating: cote.date,
        watermark: 'Édition de démonstration',
      },
      lang: 'fr',
      name: `${found.length} commutative diagram${found.length > 1 ? 's' : ''}`,
      html,
      extraStyle: DG_STYLE,
    })),
  );

  const byBatch = {};
  for (const d of found) byBatch[d.batch] = (byBatch[d.batch] ?? 0) + 1;
  census.push({
    id: f,
    title: cote.title,
    date: cote.date,
    n: found.length,
    byBatch,
    diagrams: found.map((d) => ({ batch: d.batch, page: d.page, nodes: d.nodes, arrows: d.arrows, rows: d.rows, symbols: d.symbols })),
  });
}

// The richest across the fonds: by what a reader has to take in — nodes,
// arrows, and twice the distinct symbols, since a square of four letters
// and a square of four different categories are not the same drawing.
const richness = (d) => d.nodes + d.arrows + 2 * d.symbols;
const RICHEST = [...ALL].sort((a, b) => richness(b) - richness(a)).slice(0, 60);
writeFileSync(
  resolve(OUT, 'richest.html'),
  withSlides(
    readingPage({
      meta: { folder: 'tous', first: 1, last: RICHEST.length, title: 'by nodes, arrows and distinct symbols', dating: '', watermark: 'Édition de démonstration' },
      lang: 'fr',
      name: `the ${RICHEST.length} richest commutative diagrams`,
      html: carouselNav(RICHEST.length, 'Diagrams') + RICHEST.map((d, i) => figureOf(d, i, RICHEST.length, true)).join('\n'),
      extraStyle: DG_STYLE,
    }).replace(/Cote n° tous(, | · )pages 1–\d+/g, 'The whole fonds'),
  ),
);

writeFileSync(
  JSON_OUT,
  `${JSON.stringify(
    {
      $why: 'Generated by `node scripts/diagrams.mjs` from the tikzcd environments of transcripts/*/batch-*.fr.tex — do not edit by hand.',
      built: new Date().toISOString().slice(0, 10),
      total,
      folders: census,
    },
    null,
    1,
  )}\n`,
);
process.stdout.write(
  `${total} diagrams in ${census.length} folders → public/transcripts/diagrams/, src/content/diagrams.json\n`,
);
