#!/usr/bin/env node
/**
 * Builds two maps for the Maps page, the same way as the people network
 * (scripts/lib/network.mjs): fixed positions, modularity clusters, computed
 * once.
 *
 *   npm run fonds-maps
 *
 * 1. src/content/math-map.json — the mathematics of the fonds. Each
 *    modernised reading closes on a \keywords{} line; every keyword is filed
 *    under the coarse terms of src/content/math-vocabulary.json whose patterns
 *    it matches, and two terms are linked when the same folder carries both
 *    (fractional counting, as for the people). Each term also gets the mean of
 *    its folders' datings, parsed from the inventory — which brackets nearly
 *    every date as inferred, and the figure says so.
 *
 * 2. src/content/citation-map.json — folders and the texts of his they cite.
 *    References to SGA, EGA and FGA are read from the transcribed leaves only:
 *    header comments and the transcriber's \note{} are cut out first, so what
 *    is counted is what is on the page (his text, and letters to him in the
 *    folder). Folders and cited volumes are nodes of one network, joined by
 *    how often a folder cites the volume, so every link says why it is there.
 *
 * Both are incomplete by construction — the first covers only the folders
 * with a modernised reading, the second only references in these forms — and
 * both are rebuilt by running this again.
 */
import { readdirSync, readFileSync, writeFileSync, existsSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { layout, louvain, rankClusters } from './lib/network.mjs';
import { leaves, REF, ROMAN, unit } from './lib/cites.mjs';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const T = resolve(ROOT, 'transcripts');
const built = new Date().toISOString().slice(0, 10);

/* ---------- the inventory: titles and datings ---------- */
const catalogue = readFileSync(resolve(ROOT, 'src/content/catalogue.ts'), 'utf8');
const COTE = new Map();
for (const m of catalogue.matchAll(/"id": "([^"]+)",\s*"file": "[^"]+",\s*"date": "([^"]*)",\s*"title": "((?:[^"\\]|\\.)*)"/g))
  COTE.set(m[1], { date: m[2], title: m[3].replace(/\\"/g, '"') });
const shortTitle = (id) =>
  (COTE.get(id)?.title ?? '').replace(/\s*:\s*notes manuscrites.*$/i, '').replace(/\s*:.*$/, '');
/** Midpoint of the years in the inventory's dating, or null for « s.d. ». */
function year(id) {
  const ys = [...(COTE.get(id)?.date ?? '').matchAll(/\b(19\d\d)\b/g)].map((m) => Number(m[1]));
  return ys.length ? (Math.min(...ys) + Math.max(...ys)) / 2 : null;
}
const byShelfmark = (a, b) => {
  const [a0, a1 = '0'] = a.split('-');
  const [b0, b1 = '0'] = b.split('-');
  return Number(a0) - Number(b0) || Number(a1) - Number(b1);
};
const folders = readdirSync(T, { withFileTypes: true })
  .filter((d) => d.isDirectory() && COTE.has(d.name))
  .map((d) => d.name)
  .sort(byShelfmark);

/** Fractional co-occurrence of items within groups: 1/(n−1) per pair. */
function cooccurrence(groups) {
  const w = new Map();
  const shared = new Map();
  for (const [g, items] of groups) {
    const list = [...new Set(items)].sort();
    if (list.length < 2) continue;
    for (let i = 0; i < list.length; i++)
      for (let j = i + 1; j < list.length; j++) {
        const k = `${list[i]}\u0000${list[j]}`;
        w.set(k, (w.get(k) ?? 0) + 1 / (list.length - 1));
        shared.set(k, [...(shared.get(k) ?? []), g]);
      }
  }
  return { w, shared };
}

/* ---------- 1. the map of the mathematics ---------- */
const vocab = JSON.parse(readFileSync(resolve(ROOT, 'src/content/math-vocabulary.json'), 'utf8')).terms.map((t) => ({
  term: t.term,
  short: t.short ?? t.term,
  res: t.patterns.map((p) => new RegExp(p, 'i')),
}));
const termsOf = new Map(); // folder → terms
const keywordsOf = new Map(); // folder → term → keywords
const unmapped = {};
let nKeywords = 0;
let nMapped = 0;
for (const f of folders) {
  const file = resolve(T, f, `${f}.modern.tex`);
  if (!existsSync(file)) continue;
  const m = /\\keywords\{([^}]*)\}/.exec(readFileSync(file, 'utf8'));
  if (!m) continue;
  const ks = m[1].split(',').map((k) => k.trim()).filter(Boolean);
  const byTerm = new Map();
  for (const k of ks) {
    nKeywords++;
    const hit = vocab.filter((v) => v.res.some((r) => r.test(k))).map((v) => v.term);
    if (hit.length) nMapped++;
    else (unmapped[f] ??= []).push(k);
    for (const t of hit) byTerm.set(t, [...(byTerm.get(t) ?? []), k]);
  }
  if (byTerm.size) {
    termsOf.set(f, [...byTerm.keys()]);
    keywordsOf.set(f, Object.fromEntries(byTerm));
  }
}
{
  const { w, shared } = cooccurrence(termsOf);
  const terms = vocab.map((v) => v.term).filter((t) => [...termsOf.values()].some((ts) => ts.includes(t)));
  const idx = new Map(terms.map((t, i) => [t, i]));
  const links = [...w].map(([k, wt]) => {
    const [a, b] = k.split('\u0000');
    return { s: idx.get(a), t: idx.get(b), w: wt, folders: shared.get(k).sort(byShelfmark) };
  });
  // Association strength (VOSviewer's normalisation): observed co-occurrence
  // against what the two subjects' sizes would give by chance. Subjects that
  // are everywhere are linked to everything; only the links stronger than
  // chance shape the layout and are drawn. The communities use them all.
  const strength = terms.map((_, i) => links.reduce((a, l) => a + (l.s === i || l.t === i ? l.w : 0), 0));
  const total = links.reduce((a, l) => a + l.w, 0);
  for (const l of links) l.a = (2 * total * l.w) / (strength[l.s] * strength[l.t]);
  const strong = links.filter((l) => l.a >= 1);
  const cl = louvain(terms.length, links);
  const place = layout(terms.length, strong.map((l) => ({ ...l, w: l.a })), { W: 1000, H: 620, spread: 1.35, foot: 40 });
  const { rank } = rankClusters(cl);
  const nodes = terms.map((t, i) => {
    const fs = folders.filter((f) => termsOf.get(f)?.includes(t));
    const ys = fs.map(year).filter((y) => y !== null);
    return {
      term: t,
      short: vocab.find((v) => v.term === t).short,
      x: Math.round(place[i].x),
      y: Math.round(place[i].y),
      cluster: rank[i],
      folders: fs.map((f) => ({ id: f, title: shortTitle(f), keywords: keywordsOf.get(f)[t], year: year(f) })),
      year: ys.length ? Math.round(ys.reduce((a, b) => a + b, 0) / ys.length) : null,
      dated: ys.length,
    };
  });
  writeFileSync(
    resolve(ROOT, 'src/content/math-map.json'),
    `${JSON.stringify(
      {
        $why: 'Generated by `npm run fonds-maps` from the \\keywords of the modernised readings and src/content/math-vocabulary.json — do not edit by hand.',
        built,
        width: 1000,
        height: 620,
        coverage: { folders: termsOf.size, keywords: nKeywords, mapped: nMapped },
        nodes,
        links: strong.map((l) => ({ s: l.s, t: l.t, w: Number(l.w.toFixed(3)), a: Number(l.a.toFixed(2)), folders: l.folders })),
        unmapped,
      },
      null,
      1,
    )}\n`,
  );
  process.stdout.write(
    `math map: ${nodes.length} terms, ${links.length} links, from ${termsOf.size} folders; ${nMapped}/${nKeywords} keywords mapped\n`,
  );
}

/* ---------- 2. folders and the texts they cite ---------- */
const cites = new Map(); // folder → unit → [refs]
// 162-1 is a register of papers he lent: its references are loans, not citations.
const NOT_CITING = new Set(['162-1']);
for (const f of folders.filter((x) => !NOT_CITING.has(x))) {
  for (const b of readdirSync(resolve(T, f)).filter((n) => /^batch-\d+\.fr\.tex$/.test(n)).sort()) {
    const text = leaves(readFileSync(resolve(T, f, b), 'utf8'));
    for (const m of text.matchAll(REF)) {
      const u = unit(m);
      if (!u) continue;
      if (!cites.has(f)) cites.set(f, new Map());
      const byUnit = cites.get(f);
      byUnit.set(u.unit, [...(byUnit.get(u.unit) ?? []), u.ref]);
    }
  }
}
{
  const fs = [...cites.keys()].sort(byShelfmark);
  const order = (u) => {
    const [k, v = ''] = u.split(' ');
    return (k === 'EGA' ? 0 : k === 'SGA' ? 100 : 200) + (v.startsWith('0_') ? ROMAN[v.slice(2)] - 10 : ROMAN[v] ?? (Number(v) || 0));
  };
  const units = [...new Set(fs.flatMap((f) => [...cites.get(f).keys()]))].sort((a, b) => order(a) - order(b));
  const ids = [...fs.map((f) => `f:${f}`), ...units.map((u) => `t:${u}`)];
  const idx = new Map(ids.map((id, i) => [id, i]));
  const links = fs.flatMap((f) =>
    [...cites.get(f)].map(([u, refs]) => ({ s: idx.get(`f:${f}`), t: idx.get(`t:${u}`), w: 1 + Math.log2(refs.length), n: refs.length })),
  );
  const cl = louvain(ids.length, links);
  const place = layout(ids.length, links, { W: 1000, H: 620, spread: 1.15, foot: 50 });
  const { rank } = rankClusters(cl);
  const nodes = ids.map((id, i) => {
    const kind = id.startsWith('f:') ? 'folder' : 'text';
    const key = id.slice(2);
    const base = { id: key, kind, x: Math.round(place[i].x), y: Math.round(place[i].y), cluster: rank[i] };
    if (kind === 'folder') {
      const c = cites.get(key);
      return {
        ...base,
        title: shortTitle(key),
        cites: Object.fromEntries([...c].map(([u, refs]) => [u, [...new Set(refs)]])),
        n: [...c.values()].reduce((a, r) => a + r.length, 0),
      };
    }
    return { ...base, n: fs.reduce((a, f) => a + (cites.get(f).get(key)?.length ?? 0), 0), by: fs.filter((f) => cites.get(f).has(key)) };
  });
  writeFileSync(
    resolve(ROOT, 'src/content/citation-map.json'),
    `${JSON.stringify(
      {
        $why: 'Generated by `npm run fonds-maps` from the transcriptions (header comments and \\note{} removed) — do not edit by hand.',
        built,
        width: 1000,
        height: 620,
        nodes,
        links: links.map((l) => ({ s: l.s, t: l.t, n: l.n })),
      },
      null,
      1,
    )}\n`,
  );
  process.stdout.write(`citation map: ${fs.length} folders, ${units.length} texts (${units.join(', ')}), ${links.length} links\n`);
}
