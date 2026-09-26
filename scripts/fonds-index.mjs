#!/usr/bin/env node
/**
 * Builds the index of the whole fonds: people, his published works cited, and
 * subjects, each leading to the folders and batches where they occur.
 *
 *   npm run fonds-index
 *
 * Writes src/content/fonds-index.json from three sources that already exist
 * and are already checked, so the index adds no reading of its own:
 *
 *   - people: src/content/people-evidence.json — a letter, a text of theirs,
 *     or his naming them where the words make it an attribution; each record
 *     carries the file and line, so the batch is known;
 *   - works cited: the same citations of EGA, SGA and FGA the citation map
 *     counts (scripts/lib/cites.mjs), batch by batch;
 *   - subjects: the `\keywords{}` of the modernised readings, grouped under the
 *     thirty subjects of src/content/math-vocabulary.json. These are per folder,
 *     not per batch — a modernised reading covers the folder whole — and only
 *     folders that have one carry subjects.
 */
import { existsSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { leaves, REF, ROMAN, unit } from './lib/cites.mjs';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const T = resolve(ROOT, 'transcripts');
const OUT = resolve(ROOT, 'src/content/fonds-index.json');

const catalogue = readFileSync(resolve(ROOT, 'src/content/catalogue.ts'), 'utf8');
const COTE = new Set([...catalogue.matchAll(/"id": "([^"]+)",\s*"file":/g)].map((m) => m[1]));
const byShelfmark = (a, b) => {
  const [a0, a1 = '0'] = a.split('-');
  const [b0, b1 = '0'] = b.split('-');
  return Number(a0) - Number(b0) || Number(a1) - Number(b1);
};
const folders = readdirSync(T, { withFileTypes: true })
  .filter((d) => d.isDirectory() && COTE.has(d.name))
  .map((d) => d.name)
  .sort(byShelfmark);

/** term → folder → { batches:Set, extra:Set } */
function collector() {
  const m = new Map();
  return {
    add(term, folder, batch, extra) {
      if (!m.has(term)) m.set(term, new Map());
      const byF = m.get(term);
      if (!byF.has(folder)) byF.set(folder, { batches: new Set(), extra: new Set() });
      const e = byF.get(folder);
      if (batch) e.batches.add(batch);
      if (extra) e.extra.add(extra);
    },
    out(sortKey = (t) => t) {
      return [...m]
        .map(([term, byF]) => ({
          term,
          sort: sortKey(term),
          folders: [...byF]
            .sort((a, b) => byShelfmark(a[0], b[0]))
            .map(([id, e]) => ({ id, batches: [...e.batches].sort((a, b) => a - b), extra: [...e.extra].sort() })),
        }))
        .sort((a, b) => a.sort.localeCompare(b.sort, 'fr'));
    },
  };
}

/* ---------- people ---------- */
const people = collector();
const KIND = { letter: 'letter', typescript: 'their text', named: 'named' };
for (const r of JSON.parse(readFileSync(resolve(ROOT, 'src/content/people-evidence.json'), 'utf8')).records) {
  const b = /batch-(\d+)\.fr\.tex/.exec(r.where);
  people.add(r.person, r.folder, b ? Number(b[1]) : null, KIND[r.kind]);
}
// Sorted by surname, particles and all: « de Jong » under J, as the MGP and
// most indexes of mathematics file him.
const surname = (n) => {
  const parts = n.split(' ');
  let i = parts.length - 1;
  while (i > 0 && /^(de|van|von|der|du|le|la)$/i.test(parts[i - 1])) i--;
  return parts.slice(i).join(' ').replace(/^(de|van|von|der|du|le|la)\s+/i, '');
};

/* ---------- works cited ---------- */
const works = collector();
const NOT_CITING = new Set(['162-1']);
for (const f of folders.filter((x) => !NOT_CITING.has(x))) {
  for (const name of readdirSync(resolve(T, f)).filter((n) => /^batch-\d+\.fr\.tex$/.test(n))) {
    const batch = Number(/batch-(\d+)/.exec(name)[1]);
    const text = leaves(readFileSync(resolve(T, f, name), 'utf8'));
    for (const m of text.matchAll(REF)) {
      const u = unit(m);
      if (u) works.add(u.unit, f, batch, u.ref === u.unit ? null : u.ref);
    }
  }
}
const workOrder = (u) => {
  const [k, v = ''] = u.split(' ');
  const n = v.startsWith('0_') ? ROMAN[v.slice(2)] - 10 : (ROMAN[v] ?? (Number(v) || 0));
  return `${k === 'EGA' ? 0 : k === 'SGA' ? 1 : 2}${String(n + 20).padStart(3, '0')}`;
};

/* ---------- subjects ---------- */
const vocab = JSON.parse(readFileSync(resolve(ROOT, 'src/content/math-vocabulary.json'), 'utf8')).terms.map((t) => ({
  term: t.term,
  res: t.patterns.map((p) => new RegExp(p, 'i')),
}));
const subjects = new Map(); // subject → keyword → Set(folder)
let withKeywords = 0;
for (const f of folders) {
  const file = resolve(T, f, `${f}.modern.tex`);
  if (!existsSync(file)) continue;
  const m = /\\keywords\{([^}]*)\}/.exec(readFileSync(file, 'utf8'));
  if (!m) continue;
  withKeywords++;
  for (const raw of m[1].split(',')) {
    const k = raw.replace(/\s+/g, ' ').trim();
    if (!k) continue;
    const hit = vocab.filter((v) => v.res.some((r) => r.test(k))).map((v) => v.term);
    for (const s of hit.length ? hit : ['Other subjects']) {
      if (!subjects.has(s)) subjects.set(s, new Map());
      const byK = subjects.get(s);
      const key = k.toLowerCase();
      if (!byK.has(key)) byK.set(key, { keyword: k, folders: new Set() });
      byK.get(key).folders.add(f);
    }
  }
}

const out = {
  $why:
    'Generated by `npm run fonds-index` from people-evidence.json, the citations in the batches and the \\keywords of the modernised readings — do not edit by hand.',
  built: new Date().toISOString().slice(0, 10),
  coverage: { folders: folders.length, withKeywords },
  people: people.out(surname),
  works: works.out(workOrder),
  subjects: [...subjects]
    .map(([term, byK]) => ({
      term,
      keywords: [...byK.values()]
        .map((k) => ({ keyword: k.keyword, folders: [...k.folders].sort(byShelfmark) }))
        .sort((a, b) => a.keyword.localeCompare(b.keyword, 'en')),
    }))
    .sort((a, b) => (a.term === 'Other subjects') - (b.term === 'Other subjects') || a.term.localeCompare(b.term, 'en')),
};
writeFileSync(OUT, `${JSON.stringify(out, null, 1)}\n`);
process.stdout.write(
  `${out.people.length} people, ${out.works.length} works, ${out.subjects.length} subjects (${out.subjects.reduce((a, s) => a + s.keywords.length, 0)} keywords from ${withKeywords} folders) → src/content/fonds-index.json\n`,
);
