#!/usr/bin/env node
/**
 * The inventory of the Fonds Grothendieck–Illusie at the IHÉS, for the
 * Illusie tab (#85).
 *
 *   node scripts/illusie-catalogue.mjs
 *
 * The IHÉS keeps the scans of this fonds on a bare file server,
 * repo-archives.ihes.fr/FONDS_GROTHENDIECK_ILLUSIE/, and has not put it in its
 * public catalogue. This script walks the directory listings there — one
 * request at a time, a second apart — and, for each item directory (one that
 * holds `<name>.xml`), reads that Omeka XML record: title, creator, recipient,
 * date. Pages are counted from the listing (the jpg views, or the tif masters
 * where there are no jpg), never by downloading a scan or a PDF. The OCR files
 * (`*_txt.xml`) are not read.
 *
 * Writes src/content/illusie.json: metadata only, with each item's IHÉS
 * directory. Nothing of the scans is copied, framed or relayed; the page only
 * links out, pending the IHÉS's answer on the use of the fonds.
 */

import { writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const ROOT = resolve(import.meta.dirname, '..');
const OUT = resolve(ROOT, 'src/content/illusie.json');
const BASE = 'https://repo-archives.ihes.fr/FONDS_GROTHENDIECK_ILLUSIE/';
const UA = 'grothendieck.commutator.io inventory (+https://grothendieck.commutator.io/illusie/)';
const DELAY = 1000;

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

/** One polite GET: a second after the previous one, retried a few times. */
async function get(url) {
  for (let i = 0; i < 4; i++) {
    await sleep(DELAY * (i + 1));
    try {
      const r = await fetch(url, { headers: { 'User-Agent': UA } });
      if (r.ok) return { ok: true, text: await r.text() };
      if (r.status === 404) return { ok: false, status: 404 };
    } catch {
      /* retry */
    }
  }
  return { ok: false, status: 'no answer' };
}

/** The entries of an Apache listing: sub-directories and files. */
async function listing(url) {
  const r = await get(url);
  if (!r.ok) throw new Error(`${url}: ${r.status}`);
  const hrefs = [...r.text.matchAll(/href="([^"?/][^"]*)"/g)].map((m) => decodeURIComponent(m[1]));
  return { dirs: hrefs.filter((h) => h.endsWith('/')).map((h) => h.slice(0, -1)), files: hrefs.filter((h) => !h.endsWith('/')) };
}

const decode = (s) =>
  s
    .replace(/<!\[CDATA\[([\s\S]*?)\]\]>/g, '$1')
    .replace(/&lt;/g, '<')
    .replace(/&gt;/g, '>')
    .replace(/&quot;/g, '"')
    .replace(/&apos;/g, "'")
    .replace(/&#(\d+);/g, (_, n) => String.fromCodePoint(Number(n)))
    .replace(/&amp;/g, '&')
    .replace(/\s+/g, ' ')
    .trim();

/** The Omeka record's fields, by name; a name may repeat (two « Type »). */
function fields(xml) {
  const out = new Map();
  for (const m of xml.matchAll(/<element\b[^>]*>([\s\S]*?)<\/element>/g)) {
    const name = /<name>([\s\S]*?)<\/name>/.exec(m[1])?.[1];
    if (!name) continue;
    const texts = [...m[1].matchAll(/<text>([\s\S]*?)<\/text>/g)].map((t) => decode(t[1])).filter(Boolean);
    if (!texts.length) continue;
    const k = decode(name);
    out.set(k, [...(out.get(k) ?? []), ...texts]);
  }
  return out;
}

/** « 02/12/1969 » → « 1969-12-02 »; a bare year stays a year; else null. */
function iso(raw) {
  if (!raw) return null;
  let m = /^(\d{1,2})\/(\d{1,2})\/(\d{4})$/.exec(raw);
  if (m) return `${m[3]}-${m[2].padStart(2, '0')}-${m[1].padStart(2, '0')}`;
  m = /^(\d{1,2})\/(\d{4})$/.exec(raw);
  if (m) return `${m[2]}-${m[1].padStart(2, '0')}`;
  m = /^(\d{4})$/.exec(raw);
  return m ? m[1] : null;
}

const SERIES = [
  { id: '1ILL_Correspondance', label: 'Correspondence (Illusie gift, 1ILL)' },
  { id: '2ILL_Papiers_Grothendieck', label: 'Papers of Grothendieck (Illusie gift, 2ILL)' },
  { id: '3ILL_Papiers_Illusie', label: 'Papers of Illusie (Illusie gift, 3ILL)' },
  { id: 'FG_IL_1_Correspondance_Grothendieck_Illusie', label: 'FG_IL 1 · Correspondence Grothendieck–Illusie' },
  { id: 'FG_IL_2_Correspondance_Grothendieck_Collegues', label: 'FG_IL 2 · Correspondence of Grothendieck with colleagues' },
  { id: 'FG_IL_3_Notes_Mathematiques', label: 'FG_IL 3 · Mathematical notes' },
  { id: 'FG_IL_4_Ecrits_Mathematiques', label: 'FG_IL 4 · Mathematical writings (EGA)' },
  { id: 'FG_IL_5_Ecrits_Mathematiques_SGA', label: 'FG_IL 5 · Mathematical writings (SGA)' },
];

const items = [];
const unreadable = [];
let requests = 0;

async function visit(series, path) {
  const url = BASE + path.map(encodeURIComponent).join('/') + '/';
  const name = path[path.length - 1];
  const { dirs, files } = await listing(url);
  requests++;
  const xmlName = `${name}.xml`;
  const jpg = files.filter((f) => /\.jpe?g$/i.test(f)).length;
  const tif = files.filter((f) => /\.tiff?$/i.test(f)).length;
  const hasXml = files.includes(xmlName);
  if (hasXml || jpg || tif) {
    const rec = { id: name, series, title: null, creator: null, recipient: null, date: null, sort: null, pages: jpg || tif, url };
    if (hasXml) {
      const r = await get(url + encodeURIComponent(xmlName));
      requests++;
      const f = r.ok ? fields(r.text.replace(/^﻿/, '')) : null;
      if (!f || !f.get('Title')) {
        unreadable.push({ id: name, why: r.ok ? 'no Title in the record' : `HTTP ${r.status}` });
        rec.metadata = false;
      } else {
        const one = (...ks) => ks.map((k) => f.get(k)?.[0]).find(Boolean) ?? null;
        rec.title = one('Title');
        rec.creator = one('Creator');
        rec.recipient = one('Recipient', 'Destinataire');
        rec.date = one('Date');
        rec.sort = iso(rec.date) ?? one('Coverage', 'Année');
        if (!rec.pages) {
          const n = Number.parseInt(one('Nb de vues') ?? '', 10);
          if (n) rec.pages = n;
        }
      }
    } else {
      unreadable.push({ id: name, why: 'no XML record in the directory' });
      rec.metadata = false;
    }
    items.push(rec);
    process.stdout.write(`${name}  ${rec.pages} p.  ${rec.title ?? '(no metadata)'}\n`);
  }
  for (const d of dirs) await visit(series, [...path, d]);
}

const top = await listing(BASE);
for (const s of top.dirs) {
  if (!SERIES.some((x) => x.id === s)) console.warn(`unknown series ${s}: walked, labelled by its directory name`);
  await visit(s, [s]);
}

const known = new Set(SERIES.map((s) => s.id));
const series = [...SERIES.filter((s) => top.dirs.includes(s.id)), ...top.dirs.filter((d) => !known.has(d)).map((d) => ({ id: d, label: d }))];

writeFileSync(
  OUT,
  JSON.stringify(
    {
      $why: 'Inventory of the Fonds Grothendieck–Illusie (IHÉS), built by scripts/illusie-catalogue.mjs from the Omeka XML records and directory listings on repo-archives.ihes.fr. Metadata only: no scan, image, PDF or OCR text is stored, framed or relayed; « url » is the item’s directory on the IHÉS server. « metadata: false » marks an item whose record could not be read.',
      built: new Date().toISOString().slice(0, 10),
      source: BASE,
      series,
      unreadable,
      items,
    },
    null,
    1,
  ) + '\n',
);
const pages = items.reduce((n, i) => n + i.pages, 0);
console.log(`\n${items.length} items, ${pages} pages, ${unreadable.length} unreadable → src/content/illusie.json (${requests} requests)`);
for (const s of series) {
  const its = items.filter((i) => i.series === s.id);
  console.log(`  ${s.id}: ${its.length} items, ${its.reduce((n, i) => n + i.pages, 0)} p.`);
}
