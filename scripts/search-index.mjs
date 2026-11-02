#!/usr/bin/env node
/**
 * Writes `public/search-index.json`: one record per document of every source
 * the site catalogues, for the metadata search on /search/ (#108).
 *
 * Metadata only. Each record carries a title, a dating, a shelfmark, the
 * holder, some tags and, where the site's own registers have one, a short
 * summary — and the link to the document at its holder. Nothing is read from
 * transcripts/, transcripts-*\/ or a modernised reading: the folders' notices
 * carry the Résumé of their modernised reading, and it is left out on purpose;
 * a folder is found here by its inventory title, its group and its keywords.
 * The rights answer (#31) has not come, and a client-side index ships every
 * word it holds to the browser.
 *
 * Sources: the Montpellier inventory and notices, the letters' register, the
 * Bourbaki catalogue (AHP), the Quillen file list with Glenys Luke's index
 * (Clay), the Fonds Grothendieck–Illusie inventory (IHÉS), the index of the
 * Buffalo lectures (ours, one record per tape side), the BnF boxes and the
 * candidate findings.
 *
 * Run by `npm run search-index`, and by `npm run dev` and `npm run build`.
 */

import { readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const ROOT = resolve(import.meta.dirname, '..');
const json = (p) => JSON.parse(readFileSync(resolve(ROOT, 'src/content', p), 'utf8'));
// Node 22 strips the types of these two modules; they hold data and type-only imports.
const { COTES, GROUPS } = await import(resolve(ROOT, 'src/content/catalogue.ts'));
const { FINDINGS } = await import(resolve(ROOT, 'src/content/findings.ts'));
const { BNF_BOXES } = await import(resolve(ROOT, 'src/content/bnf-boxes.ts'));

const HOLDER = {
  montpellier: 'Université de Montpellier',
  bourbaki: 'Archives Henri Poincaré (AHP), Nancy',
  quillen: 'Clay Mathematics Institute',
  ihes: 'IHÉS, Bures-sur-Yvette',
  buffalo: 'YouTube (« Erwin Schulhoff » channel)',
  bnf: 'Bibliothèque nationale de France',
};
const facsimile = (cote) => `https://grothendieck.umontpellier.fr/${cote}.pdf`;
const folderPage = (cote, batch = 1) => `/#${cote}/${batch}`;

/**
 * The years an archivist's dating spans: « 1965-1969 », « [à partir de 1958] »,
 * « [années 1960-1970] », « [avant 1970] », « s.d. ». An open end (« à partir
 * de ») is closed at the last year written; « années 1970 » runs to 1979;
 * « avant 1970 » has no lower bound.
 */
export function years(s) {
  if (!s) return [null, null];
  const ys = [...String(s).matchAll(/(1[89]\d\d|20\d\d)/g)].map((m) => Number(m[1]));
  if (!ys.length) return [null, null];
  let from = Math.min(...ys);
  let to = Math.max(...ys);
  if (new RegExp(`années\\s+${to}`).test(s) && to % 10 === 0) to += 9;
  if (ys.length === 1 && /avant/.test(s)) from = null;
  return [from, to];
}

const clip = (s, n = 600) => {
  if (!s) return null;
  const t = s.replace(/\s+/g, ' ').trim();
  if (t.length <= n) return t;
  const cut = t.slice(0, n);
  const end = Math.max(cut.lastIndexOf('. '), cut.lastIndexOf('; '));
  return `${end > n / 2 ? cut.slice(0, end + 1) : cut.replace(/\s+\S*$/, '')} …`;
};
const uniq = (xs) => [...new Set(xs.filter(Boolean).map((x) => String(x).trim()).filter(Boolean))];
const tidyTag = (t) => t.replace(/--/g, '–');

const records = [];
const push = (r) =>
  records.push({
    id: r.id,
    source: r.source,
    title: r.title,
    yearFrom: r.yearFrom ?? null,
    yearTo: r.yearTo ?? r.yearFrom ?? null,
    date: r.date ?? null,
    shelfmark: r.shelfmark ?? null,
    holder: r.holder,
    tags: uniq(r.tags ?? []),
    summary: r.summary ?? null,
    url: r.url ?? null,
    siteUrl: r.siteUrl ?? null,
  });

/* Montpellier: the inventory, with the notices' group, typology and keywords. */
const notices = new Map(json('notices.json').notices.map((n) => [n.cote, n]));
const groupOf = new Map(GROUPS.flatMap((g) => g.cotes.map((c) => [c, g])));
for (const c of COTES) {
  const n = notices.get(c.id);
  const g = groupOf.get(c.id) ?? groups(c.group);
  const [yearFrom, yearTo] = years(c.date);
  const p = n?.physical;
  const facts = [
    g?.title && g.id !== c.id ? `Group « ${g.title} »` : null,
    n?.typology ? n.typology.replace(/\.$/, '') : null,
    `${c.pages} pages${p?.transcribed ? `, ${p.transcribed} transcribed by the project` : ''}`,
    n?.languages?.length ? n.languages.join(', ') : null,
  ].filter(Boolean);
  push({
    id: `montpellier:${c.id}`,
    source: 'montpellier',
    title: c.title.replace(/\s*\.$/, ''),
    yearFrom,
    yearTo,
    date: c.date || 's.d.',
    shelfmark: `Folder ${c.id}`,
    holder: HOLDER.montpellier,
    tags: [...(n?.subjects ?? []).map(tidyTag), ...(n?.names ?? [])],
    summary: `${facts.join('. ')}.`,
    url: facsimile(c.id),
    siteUrl: folderPage(c.id),
  });
}
function groups(id) {
  return GROUPS.find((g) => g.id === id);
}

/* Letters: the register; seen from Grothendieck. Private people stay unnamed (the register says so). */
const DIR = { from: 'from Grothendieck', to: 'to Grothendieck', other: 'between others, or unclear' };
for (const [i, l] of json('letters.json').records.entries()) {
  const who = l.correspondent ?? null;
  const title =
    l.direction === 'from'
      ? `Letter from Grothendieck to ${who ?? 'an unnamed correspondent'}`
      : l.direction === 'to'
        ? `Letter to Grothendieck from ${who ?? 'an unnamed correspondent'}`
        : `Letter${who ? `, ${who}` : ''}${l.correspondentNote && !who ? ` (${l.correspondentNote})` : ''}`;
  const y = l.iso ? Number(l.iso.slice(0, 4)) : null;
  push({
    id: `letter:${l.folder}:${l.pages}:${i}`,
    source: 'letter',
    title,
    yearFrom: y,
    yearTo: y,
    date: l.date ?? (l.dating === 'none' ? 'undated' : null),
    shelfmark: `Folder ${l.folder}, pp. ${l.pages}`,
    holder: HOLDER.montpellier,
    tags: [DIR[l.direction], who, l.place, l.form, { fr: 'French', en: 'English', de: 'German' }[l.language]],
    summary: l.summary,
    url: facsimile(l.folder),
    siteUrl: folderPage(l.folder, l.batch),
  });
}

/* Bourbaki: the AHP catalogue; its summaries are the archive's. */
for (const r of json('bourbaki.json').records) {
  const [yearFrom, yearTo] = years(r.date);
  push({
    id: `bourbaki:${r.id}`,
    source: 'bourbaki',
    title: r.title,
    yearFrom,
    yearTo,
    date: r.date,
    shelfmark: r.identifier ?? (r.number != null ? `Rédaction n° ${r.number}` : null),
    holder: HOLDER.bourbaki,
    tags: [r.type, r.book, ...(r.creators ?? []), r.grothendieck?.length ? 'Grothendieck' : null],
    summary: clip(r.summary),
    url: r.url,
    siteUrl: `/bourbaki/#doc/${r.id}`,
  });
}

/* Quillen: the Clay's file list, with Glenys Luke's index. */
const Q = json('quillen.json');
for (const n of Q.notebooks) {
  const y = /^\d{4}$/.test(n.group) ? Number(n.group) : /^(\d{4})/.exec(n.label) ? Number(n.label.slice(0, 4)) : null;
  push({
    id: `quillen:${n.id}`,
    source: 'quillen',
    title: `Quillen notebook ${n.label}`,
    yearFrom: y,
    yearTo: y,
    date: y ? String(y) : null,
    shelfmark: n.label,
    holder: HOLDER.quillen,
    tags: [n.group === 'lectures' ? 'lecture notes' : n.group === 'misc' ? 'miscellaneous' : 'research notebook', `${n.pages} pages`],
    summary: clip(n.index, 900),
    url: n.url,
    siteUrl: `/quillen/#${n.id}`,
  });
}

/* IHÉS: the Fonds Grothendieck–Illusie inventory. */
const I = json('illusie.json');
const series = new Map(I.series.map((s) => [s.id, s.label]));
const cap = (s) => (s ? s.charAt(0) + s.slice(1).toLowerCase() : null);
for (const it of I.items) {
  const [yearFrom, yearTo] = years(it.sort ?? it.date);
  push({
    id: `ihes:${it.id}`,
    source: 'ihes',
    title: it.title ?? it.id,
    yearFrom,
    yearTo,
    date: it.date,
    shelfmark: it.id,
    holder: HOLDER.ihes,
    tags: [series.get(it.series), cap(it.creator), cap(it.recipient), it.pages ? `${it.pages} pages` : null],
    summary: null,
    url: it.url,
    siteUrl: `/illusie/#${it.id}/1`,
  });
}

/* Buffalo: our index of results, one record per tape side; the math stays in $…$. */
const courses = new Map(json('buffalo.json').courses.map((c) => [c.id, c.title]));
const BI = json('buffalo-index.json');
for (const [course, idx] of Object.entries(BI)) {
  let topic = null;
  let session = null;
  let side = null;
  let cur = null;
  const flush = () => cur && cur.entries.length && sides.push(cur);
  const sides = [];
  for (const it of idx.items) {
    if (it.k === 'topic') {
      topic = it.text;
      if (cur) cur.topics.push(topic);
    } else if (it.k === 'session') {
      session = it.text;
      flush();
      cur = null;
    } else if (it.k === 'side') {
      side = it.text;
      flush();
      cur = { session, side, topics: topic ? [topic] : [], entries: [], names: [] };
    } else if (it.k === 'entry') {
      cur ??= { session, side, topics: topic ? [topic] : [], entries: [], names: [] };
      cur.entries.push(it);
      if (it.name && !it.name.includes('$')) cur.names.push(it.name);
    }
  }
  flush();
  for (const s of sides) {
    const first = s.entries[0];
    push({
      id: `buffalo:${course}:${first.v}:${first.t}`,
      source: 'buffalo',
      title: `${courses.get(course) ?? course} · ${[s.session, s.side].filter(Boolean).join(', ')}`,
      yearFrom: 1973,
      yearTo: 1973,
      date: s.session?.replace(/^Session of /, '') ?? '1973',
      shelfmark: `${first.v} · ${first.ts}`,
      holder: HOLDER.buffalo,
      tags: [...s.topics, ...s.names],
      summary: s.entries.map((e) => e.text.replace(/<[^>]+>/g, '')).join(' · '),
      url: `https://www.youtube.com/watch?v=${first.v}&t=${first.t}s`,
      siteUrl: `/buffalo/#${first.v}@${first.t}`,
    });
  }
}

/* BnF: the 43 boxes of NAF 29093, as the BnF's notice gives them. */
const BNF = 'https://archivesetmanuscrits.bnf.fr/ark:/12148/cc126317b';
for (const b of BNF_BOXES) {
  const [yearFrom, yearTo] = years(b.years);
  push({
    id: `bnf:${b.box}`,
    source: 'bnf',
    title: b.title,
    yearFrom,
    yearTo,
    date: b.years,
    shelfmark: `NAF 29093 (${b.box})`,
    holder: HOLDER.bnf,
    tags: [b.maths === 'whole' ? 'mathematics' : b.maths === 'part' ? 'some mathematics' : null, `${b.leaves} leaves`],
    summary: null,
    url: BNF,
    siteUrl: '/timeline/',
  });
}

/* Findings: the edition's candidate findings, dated by their folder. */
const byCote = new Map(COTES.map((c) => [c.id, c]));
for (const f of FINDINGS) {
  const c = byCote.get(f.cote);
  const [yearFrom, yearTo] = years(c?.date);
  push({
    id: `finding:${f.id}`,
    source: 'finding',
    title: clip(f.claim, 200),
    yearFrom,
    yearTo,
    date: c?.date ?? null,
    shelfmark: `Folder ${f.cote}, pp. ${f.pages}`,
    holder: HOLDER.montpellier,
    tags: [f.kind, f.status],
    summary: f.claim.length > 200 ? f.claim : null,
    url: c ? facsimile(f.cote) : null,
    siteUrl: `/findings/#${f.id}`,
  });
}

const out = { built: new Date().toISOString().slice(0, 10), count: records.length, records };
const path = resolve(ROOT, 'public/search-index.json');
const text = JSON.stringify(out);
writeFileSync(path, text);
const by = records.reduce((m, r) => ((m[r.source] = (m[r.source] ?? 0) + 1), m), {});
console.log(`search-index: ${records.length} records, ${(text.length / 1024).toFixed(0)} KB →`, by);
