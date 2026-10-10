#!/usr/bin/env node
/**
 * The Bourbaki archive's catalogue, for the Bourbaki tab.
 *
 *   node scripts/bourbaki-catalogue.mjs
 *
 * Reads the public Omeka API of https://archives-bourbaki.ahp-numerique.fr/
 * (items, 50 a page) and writes src/content/bourbaki.json: one record per
 * document, with its type, title, date, authors, the archive's identifier and
 * a link to its page there. Nothing of the documents themselves is copied:
 * the scans are the archive's and are read on its site.
 *
 * Each record also says whether it meets the Grothendieck fonds, and why —
 * only on evidence that can be pointed at:
 *   - « author »: Grothendieck is among the document's creators;
 *   - « present »: he is listed among those present (congress reports);
 *   - « named »: the archive's own title or description names him;
 *   - « fonds »: a rédaction whose number a leaf of the fonds carries — he
 *     wrote on its back (src/content/dated-leaves.json, records of kind
 *     « paper », issue #41), or a transcription names it (« rédaction n° 339 »).
 * A shared subject alone is not evidence.
 */
import { readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const ROOT = resolve(import.meta.dirname, '..');
const OUT = resolve(ROOT, 'src/content/bourbaki.json');
const BASE = 'https://archives-bourbaki.ahp-numerique.fr';

async function getJson(url) {
  for (let i = 0; i < 4; i++) {
    try {
      const r = await fetch(url);
      if (r.ok) return r.json();
    } catch {
      /* retry */
    }
    await new Promise((res) => setTimeout(res, 1500 * (i + 1)));
  }
  throw new Error(`no answer from ${url}`);
}

const strip = (s) =>
  s
    .replace(/<br\s*\/?>/gi, ' ')
    .replace(/<[^>]+>/g, '')
    .replace(/&nbsp;/g, ' ')
    .replace(/&amp;/g, '&')
    .replace(/\s+/g, ' ')
    .trim();

// Collections, for a readable name.
const collections = new Map();
for (const c of await getJson(`${BASE}/api/collections`)) {
  const t = c.element_texts.find((e) => e.element.name === 'Title');
  collections.set(c.id, t ? t.text : `Collection ${c.id}`);
}

const items = [];
for (let page = 1; ; page++) {
  const batch = await getJson(`${BASE}/api/items?per_page=50&page=${page}`);
  if (!batch.length) break;
  items.push(...batch);
  process.stdout.write(`\r${items.length} items`);
}
process.stdout.write('\n');

/* ---------- the fonds' side: rédaction numbers it carries ---------- */
const fondsRedactions = new Map(); // number → [{folder, why}]
const note = (n, folder, why) => {
  if (!fondsRedactions.has(n)) fondsRedactions.set(n, []);
  const list = fondsRedactions.get(n);
  if (!list.some((x) => x.folder === folder)) list.push({ folder, why });
};
const leaves = JSON.parse(readFileSync(resolve(ROOT, 'src/content/dated-leaves.json'), 'utf8')).records;
for (const r of leaves.filter((l) => l.kind === 'paper')) {
  for (const m of `${r.written} ${r.context}`.matchAll(/(?:n[°o]\s*|rédaction\s+)(\d{2,4})/gi))
    note(Number(m[1]), r.folder, `he wrote on the back of it (folder ${r.folder}, p. ${r.page})`);
}
const T = resolve(ROOT, 'transcripts');
for (const folder of readdirSync(T)) {
  if (folder.startsWith('_') || folder === 'preamble') continue;
  let files;
  try {
    files = readdirSync(resolve(T, folder)).filter((f) => /^batch-\d+\.fr\.tex$/.test(f));
  } catch {
    continue;
  }
  for (const f of files) {
    const src = readFileSync(resolve(T, folder, f), 'utf8');
    for (const m of src.matchAll(/[Rr]édaction\s+n[°o]\s*(\d{2,4})/g)) note(Number(m[1]), folder, `named in the transcription of folder ${folder}`);
  }
}

/* ---------- records ---------- */
const records = items.map((it) => {
  const all = (name) => it.element_texts.filter((e) => e.element.name === name).map((e) => strip(e.text));
  const one = (name) => all(name)[0] ?? null;
  const title = one('Title') ?? `Document ${it.id}`;
  const creators = all('Creator');
  const present = all('Présent');
  const description = one('Description') ?? '';
  const num = /^Rédaction\s+n[°o]\s*(\d+)/i.exec(title)?.[1];
  const why = [];
  if (creators.some((c) => /grothendieck/i.test(c))) why.push({ kind: 'author', text: 'Grothendieck is an author' });
  if (present.some((c) => /grothendieck/i.test(c))) why.push({ kind: 'present', text: 'Grothendieck is listed as present' });
  if (!why.length && /grothendieck/i.test(`${title} ${description}`)) why.push({ kind: 'named', text: 'the archive’s description names Grothendieck' });
  if (num && fondsRedactions.has(Number(num)))
    for (const x of fondsRedactions.get(Number(num))) why.push({ kind: 'fonds', text: x.why, folder: x.folder });
  return {
    id: it.id,
    type: it.item_type?.name ?? 'Autre',
    title,
    number: num ? Number(num) : null,
    date: one('Date'),
    creators,
    identifier: one('Identifier'),
    form: one('Type'),
    book: one('Livre'),
    pages: one('Pagination fichier'),
    collection: it.collection ? collections.get(it.collection.id) ?? null : null,
    summary: description.slice(0, 300),
    url: `${BASE}/items/show/${it.id}`,
    grothendieck: why,
  };
});
records.sort((a, b) => a.type.localeCompare(b.type) || (a.number ?? 1e9) - (b.number ?? 1e9) || a.id - b.id);

writeFileSync(
  OUT,
  JSON.stringify(
    {
      $why: 'Catalogue of the Bourbaki archive (archives-bourbaki.ahp-numerique.fr, Omeka API), built by scripts/bourbaki-catalogue.mjs. « grothendieck » lists only the evidence the script can point at: his name among the authors or those present, the archive naming him, or a rédaction whose number a leaf of the fonds carries. Nothing of the documents is copied.',
      built: new Date().toISOString().slice(0, 10),
      source: BASE,
      records,
    },
    null,
    1,
  ) + '\n',
);
const hit = records.filter((r) => r.grothendieck.length);
console.log(`${records.length} documents → src/content/bourbaki.json; ${hit.length} meet the fonds`);
