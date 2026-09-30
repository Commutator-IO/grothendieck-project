#!/usr/bin/env node
/**
 * The catalogue of Daniel Quillen's research notebooks, as the Clay
 * Mathematics Institute serves them.
 *
 *   node scripts/quillen-catalogue.mjs
 *
 * Walks the Clay's file listing under claymath.org/library/Quillen/ — one
 * directory per year of the working papers, 1968–2003, plus the lecture notes
 * and a « misc » folder — and writes src/content/quillen.json: every PDF with
 * its source URL, its year or group, and its size as the listing gives it.
 * Page counts come from the files' own structure, read by HTTP range requests
 * — the trailer, the cross-reference table, the catalogue and the page tree,
 * a few kilobytes per notebook out of 6 GB — or from a private copy where one
 * exists to count them in
 * (QUILLEN_MIRROR, default archives/quillen, written by quillen-mirror.mjs; laid out as `index.json`
 * there says); nothing on the site depends on that copy, and nothing of it is
 * served.
 *
 * The site shows the Clay's own files, framed from claymath.org — the server
 * allows it, so no relay is needed — and stores none of them.
 */

import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { resolve, join } from 'node:path';

const ROOT = resolve(import.meta.dirname, '..');
/**
 * Glenys Luke's index of the notebooks, which the Clay publishes: for each
 * notebook, its dates and what it works on. It is the collection's own
 * organisation, so the page follows it — each notebook shows the start of its
 * entry, credited, with the whole index one click away.
 */
const LUKE = 'https://www.claymath.org/wp-content/uploads/2023/04/Quillen-index-Luke.pdf';
const BASE = 'https://www.claymath.org/library/Quillen/';
const MIRROR = process.env.QUILLEN_MIRROR ?? join(ROOT, 'archives', 'quillen');

const units = { '': 1, K: 1e3, M: 1e6, G: 1e9 };
const bytes = (s) => {
  const m = /([\d.]+)\s*([KMG]?)/.exec(s ?? '');
  return m ? Math.round(Number(m[1]) * units[m[2]]) : 0;
};

async function listing(url) {
  const r = await fetch(url, { headers: { 'User-Agent': 'grothendieck-archives catalogue' } });
  if (!r.ok) throw new Error(`${url}: HTTP ${r.status}`);
  return r.text();
}

/** Every file under a directory of the Apache listing, depth first. */
async function walk(url, out = []) {
  const html = await listing(url);
  for (const row of html.match(/<tr>[\s\S]*?<\/tr>/g) ?? []) {
    const href = /href="([^"?/][^"]*)"/.exec(row)?.[1];
    if (!href) continue;
    const cells = [...row.matchAll(/<td[^>]*>([\s\S]*?)<\/td>/g)].map((m) => m[1].replace(/<[^>]+>/g, '').trim());
    if (href.endsWith('/')) await walk(url + href, out);
    else out.push({ url: url + href, size: bytes(cells[cells.length - 2]) });
  }
  return out;
}

/** Where a file sits: its year, or the lecture notes, or the miscellany. */
function place(url) {
  const rel = decodeURIComponent(url.slice(BASE.length));
  const file = rel.split('/').pop();
  const year = /^Working_papers\/quillen (\d{4})\//.exec(rel)?.[1];
  // One folder of 1986 notebooks is filed inside the 1981 directory; the
  // notebooks keep the year their names give, and say where they are filed.
  const own = /^(\d{4})-/.exec(file)?.[1];
  if (year) {
    return { group: own ?? year, filed: own && own !== year ? year : undefined, label: file.replace(/\.pdf$/i, '') };
  }
  if (rel.startsWith('Working_papers/Lecture_notes/')) return { group: 'lectures', label: file.replace(/\.pdf$/i, '') };
  return { group: 'misc', label: file.replace(/\.pdf$/i, '') };
}

/** Page counts from the private copy, where there is one. */
function pagesFrom(url) {
  const idx = join(MIRROR, 'index.json');
  if (!existsSync(idx)) return null;
  if (!pagesFrom.map) pagesFrom.map = new Map(JSON.parse(readFileSync(idx, 'utf8')).map((f) => [f.url, f.path]));
  const p = pagesFrom.map.get(url);
  if (!p || !existsSync(join(MIRROR, p))) return null;
  try {
    return Number(/^Pages:\s+(\d+)/m.exec(execFileSync('pdfinfo', [join(MIRROR, p)], { encoding: 'utf8' }))?.[1]) || null;
  } catch {
    return null;
  }
}

/**
 * A remote PDF's page count, from its structure alone.
 *
 * The Clay's scans (a Ricoh copier's) end on a classic cross-reference table
 * and have been saved incrementally, so the page tree's root is not near the
 * end: follow startxref and each /Prev back, keep the newest offset of every
 * object, then read the catalogue, its /Pages and that node's /Count. Four or
 * five range requests; null for anything else (an xref stream, a table that
 * runs past the fetched window), which leaves the count unknown rather than
 * guessed. Checked against pdfinfo on the notebooks of 1968.
 */
async function remotePages(url) {
  const get = async (spec) => {
    const r = await fetch(url, { headers: { 'User-Agent': 'grothendieck-archives catalogue', Range: `bytes=${spec}` } });
    if (r.status !== 206) throw new Error(`${url}: HTTP ${r.status} to a range request`);
    return Buffer.from(await r.arrayBuffer()).toString('latin1');
  };
  const tail = await get('-65536');
  const sx = [...tail.matchAll(/startxref\s+(\d+)/g)].pop();
  if (!sx) return null;
  const offsets = new Map();
  let root = null;
  const seen = new Set();
  for (let x = Number(sx[1]); x && !seen.has(x); ) {
    seen.add(x);
    const s = await get(`${x}-${x + 65535}`);
    if (!s.startsWith('xref')) return null;
    let pos = 4;
    for (;;) {
      pos += /^\s*/.exec(s.slice(pos))[0].length;
      const head = /^(\d+) (\d+)\s*[\r\n]+/.exec(s.slice(pos));
      if (!head) break;
      pos += head[0].length;
      const [first, count] = [Number(head[1]), Number(head[2])];
      if (pos + count * 20 > s.length) return null;
      for (let k = 0; k < count; k++) {
        const m = /^(\d{10}) \d{5} n/.exec(s.slice(pos + k * 20, pos + k * 20 + 18));
        if (m && !offsets.has(first + k)) offsets.set(first + k, Number(m[1]));
      }
      pos += count * 20;
    }
    const trailer = /trailer\s*<<([\s\S]*?)>>/.exec(s.slice(pos))?.[1];
    if (!trailer) return null;
    root ??= /\/Root\s+(\d+)\s+\d+\s+R/.exec(trailer)?.[1];
    x = Number(/\/Prev\s+(\d+)/.exec(trailer)?.[1] ?? 0);
  }
  const obj = async (n) => {
    const off = n && offsets.get(Number(n));
    return off === undefined || !off ? null : (/obj([\s\S]*?)endobj/.exec(await get(`${off}-${off + 4095}`))?.[1] ?? null);
  };
  const catalogue = await obj(root);
  const tree = await obj(catalogue && /\/Pages\s+(\d+)\s+\d+\s+R/.exec(catalogue)?.[1]);
  const count = tree && /\/Count\s+(\d+)/.exec(tree)?.[1];
  return count ? Number(count) : null;
}

/** Runs `f` over `xs`, `n` at a time — polite to the Clay's server. */
async function pooled(xs, n, f) {
  const out = Array.from({ length: xs.length });
  let next = 0;
  await Promise.all(
    Array.from({ length: n }, async () => {
      while (next < xs.length) {
        const i = next++;
        out[i] = await f(xs[i]);
      }
    }),
  );
  return out;
}

const natural = (a, b) => a.localeCompare(b, 'en', { numeric: true });

/**
 * Luke's entries, keyed as the catalogue labels its files.
 *
 * The index is set per year (« Contents 1968 ») and each entry opens on the
 * notebook's name alone on its line. The year of the heading wins over the
 * one in the name, which the index sometimes mistypes (« 1986-9 » among the
 * notebooks of 1968); a line naming several notebooks (« 1976-1, 1976-2,
 * 1976-3 ») gives its entry to each; « Lecure » and « Lectyre » are read as
 * « Lecture ».
 */
async function lukeIndex() {
  const r = await fetch(LUKE, { headers: { 'User-Agent': 'grothendieck-archives catalogue' } });
  if (!r.ok) throw new Error(`${LUKE}: HTTP ${r.status}`);
  const tmp = join(ROOT, 'node_modules', '.cache', 'quillen-index.pdf');
  execFileSync('mkdir', ['-p', join(ROOT, 'node_modules', '.cache')]);
  writeFileSync(tmp, Buffer.from(await r.arrayBuffer()));
  const text = execFileSync('pdftotext', ['-layout', tmp, '-'], { encoding: 'utf8' });
  const entries = new Map();
  let year = null;
  let keys = [];
  for (const line of text.split('\n')) {
    const heading = /^\s*Contents\s+(\d{4})\s*$/.exec(line);
    if (heading) {
      year = heading[1];
      keys = [];
      continue;
    }
    const t = line.trim();
    const names = /^((?:19|20)\d\d-[^:]*?)(?::)?$/.test(t) && t.length < 60 && !/[.;]\s/.test(t.slice(8))
      ? t.replace(/:$/, '').split(/,\s*/)
      : null;
    if (names && names.every((n) => /^(19|20)\d\d-/.test(n))) {
      keys = names.map((n) => `${year ?? n.slice(0, 4)}-${n.slice(5)}`.replace(/Lec(?:ure|tyre)/, 'Lecture'));
      for (const k of keys) entries.set(k, []);
      continue;
    }
    if (keys.length && t && !/^\d{1,3}$/.test(t)) for (const k of keys) entries.get(k).push(t);
  }
  return entries;
}

const squash = (s) => s.toLowerCase().replace(/[\s_]+/g, '');

/** A notebook's entry: the same name, or a name the index shortens (« 1983-Lecture Notes 5 » for « … 5 Quillen »). */
function entryFor(label, entries, byName) {
  const own = byName.get(squash(label));
  if (own) return own;
  for (const [k, v] of entries) {
    const q = squash(k);
    if (q.length > 8 && squash(label).startsWith(q) && /\d$/.test(q) && !/\d/.test(squash(label).slice(q.length, q.length + 1))) return v;
    if (squash(label).startsWith(q) && /[a-z]$/.test(q)) return v;
  }
  return null;
}

const files = (await walk(BASE)).filter((f) => /\.pdf$/i.test(f.url));
// Some year directories hold a copy of another year's folder (quillen 1987/
// quillen 1981/…). Where the same notebook also sits in its own year, that
// copy is the one kept; a notebook found only elsewhere keeps where it is
// filed, which the page says.
const byId = new Map();
let doubles = 0;
for (const f of files) {
  const p = place(f.url);
  const id = `${p.group}/${p.label}`;
  const nb = { id, ...p, url: f.url, bytes: f.size };
  const had = byId.get(id);
  if (had) {
    doubles += 1;
    if (had.filed && !nb.filed) byId.set(id, nb);
  } else byId.set(id, nb);
}
const entries = await lukeIndex();
const byName = new Map([...entries].map(([k, v]) => [squash(k), v]));
const notebooks = (
  await pooled([...byId.values()], 6, async (nb) => {
    const lines = entryFor(nb.label, entries, byName);
    let pages = pagesFrom(nb.url);
    if (!pages) pages = await remotePages(nb.url).catch(() => null);
    return { ...nb, pages, index: lines ? lines.join(' ').replace(/\s+/g, ' ').trim() : null };
  })
).sort((a, b) => natural(a.group, b.group) || natural(a.label, b.label));

const out = {
  $why: 'Generated by `node scripts/quillen-catalogue.mjs` from the Clay Mathematics Institute file listing — do not edit by hand.',
  built: new Date().toISOString().slice(0, 10),
  source: 'https://www.claymath.org/online-resources/quillen-notebooks/',
  files: BASE,
  index: LUKE,
  notebooks,
};
writeFileSync(resolve(ROOT, 'src/content/quillen.json'), JSON.stringify(out, null, 1) + '\n');
const counted = notebooks.filter((n) => n.pages).length;
const indexed = notebooks.filter((n) => n.index).length;
process.stdout.write(
  `${notebooks.length} PDFs (${doubles} copies filed under another year left out), ` +
    `${(notebooks.reduce((s, n) => s + n.bytes, 0) / 1e9).toFixed(2)} GB, ${counted} with a page count, ${indexed} with an entry in Luke's index → src/content/quillen.json\n`,
);
