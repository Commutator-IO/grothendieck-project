#!/usr/bin/env node
/**
 * One TEI file per folder, with no batches: the exported batches of a
 * shelfmark joined into a single document, for sending by mail.
 *
 *   npm run tei                   # first: the per-batch export it reads
 *   npm run bundle:tei            # every transcribed folder
 *   npm run bundle:tei -- 19 134-2
 *
 * Reads public/transcripts/<folder>/batch-NN.fr.xml (written by npm run tei)
 * and writes exports/tei/<folder>.fr.xml, checked well-formed by xmllint.
 * exports/ is git-ignored: these files are derived, and the transcriptions
 * are not published (BnF, 2026-09-29).
 *
 * The header is the first batch's, with the page span and the msContents
 * summary set to the whole folder. The responsibility statements of every
 * batch are kept: a pass or revision that recurs (same name, same statement)
 * keeps one id; one that differs from batch to batch gets the batch's number
 * as a suffix, and the resp/who pointers of that batch's body and changes are
 * renamed with it, so every reading stays credited to the pass that made it.
 * The revisionDesc is the union of the batches' changes, newest first. The
 * body is the batches' bodies in order, without the <div type="batch">
 * wrapper: the batch is a unit of work, not of the folder.
 */
import { execFileSync } from 'node:child_process';
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const ROOT = resolve(import.meta.dirname, '..');
const SRC = resolve(ROOT, 'public', 'transcripts');
const OUT = resolve(ROOT, 'exports', 'tei');

const byShelfmark = (a, b) => {
  const [a0, a1 = '0'] = a.split('-');
  const [b0, b1 = '0'] = b.split('-');
  return Number(a0) - Number(b0) || Number(a1) - Number(b1) || a.localeCompare(b);
};

const wanted = process.argv.slice(2);
const folders = readdirSync(SRC, { withFileTypes: true })
  .filter((d) => d.isDirectory())
  .map((d) => d.name)
  .filter((f) => !f.startsWith('_')) // _specimen: the skill's worked example, not a folder
  .filter((f) => !wanted.length || wanted.includes(f))
  .filter((f) => readdirSync(resolve(SRC, f)).some((n) => /^batch-\d+\.fr\.xml$/.test(n)))
  .sort(byShelfmark);
if (!folders.length) throw new Error('no exported batches: run npm run tei first');

mkdirSync(OUT, { recursive: true });

const between = (s, a, b, file) => {
  const i = s.indexOf(a);
  const j = s.indexOf(b, i);
  if (i < 0 || j < 0) throw new Error(`${file}: missing ${a}…${b}`);
  return s.slice(i + a.length, j);
};
const RESP = /\s*<respStmt>\s*<resp>([\s\S]*?)<\/resp>\s*<(name|orgName)([^>]*) xml:id="([^"]+)"([^>]*)>([\s\S]*?)<\/\2>\s*<\/respStmt>/g;

/** Top-level nodes of an XML fragment: [{start, end, tag}] (tag null for text and comments). */
function nodes(xml) {
  const out = [];
  let depth = 0;
  let start = 0;
  let tag = null;
  for (const m of xml.matchAll(/<!--[\s\S]*?-->|<(\/?)([\w:]+)[^>]*?(\/?)>|[^<]+/g)) {
    const [all, close, name, self] = m;
    if (depth === 0) {
      start = m.index;
      tag = name && !close ? name : null;
    }
    if (name && !close && !self) depth++;
    else if (name && close) depth--;
    if (depth === 0 && all.trim()) out.push({ start, end: m.index + all.length, tag });
  }
  return out;
}

/**
 * Appends frag at the end of xml, inside the last <div> (and its last <div>,
 * and so on) when xml ends with one: a section that runs across a batch
 * boundary continues in the same <div>, and the schema allows no <p> after a
 * sibling <div>.
 */
function appendInto(xml, frag) {
  const ns = nodes(xml);
  const lastNode = ns[ns.length - 1];
  if (!lastNode || lastNode.tag !== 'div') return `${xml}\n${frag}`;
  const node = xml.slice(lastNode.start, lastNode.end);
  const open = node.slice(0, node.indexOf('>') + 1);
  const inner = node.slice(open.length, node.lastIndexOf('</div>'));
  return xml.slice(0, lastNode.start) + open + appendInto(inner.replace(/\s+$/, ''), frag) + '\n</div>' + xml.slice(lastNode.end);
}

/** Joins batch bodies: leading non-<div> nodes of a body go into the open section. */
function join(bodies) {
  let merged = '';
  for (const body of bodies) {
    const ns = nodes(body);
    const k = ns.findIndex((x) => x.tag === 'div');
    const lead = k < 0 ? body : body.slice(0, ns[k].start);
    const rest = k < 0 ? '' : body.slice(ns[k].start);
    merged = lead.trim() ? appendInto(merged, lead.trim()) : merged;
    if (rest.trim()) merged = `${merged}\n${rest.trim()}`;
  }
  return merged.trim();
}

let n = 0;
for (const folder of folders) {
  const files = readdirSync(resolve(SRC, folder))
    .filter((f) => /^batch-\d+\.fr\.xml$/.test(f))
    .sort();
  const docs = files.map((f) => ({ f, n: Number(/(\d+)/.exec(f)[1]), xml: readFileSync(resolve(SRC, folder, f), 'utf8') }));

  // Responsibility statements: one id per distinct (statement, name).
  const resp = new Map(); // key → {id, xml}
  const byId = new Map(); // id → key, for collisions
  const changes = [];
  const bodies = [];
  let first = Infinity;
  let last = -Infinity;
  for (const d of docs) {
    const rename = new Map();
    const title = between(d.xml, '<titleStmt>', '</titleStmt>', d.f);
    for (const m of title.matchAll(RESP)) {
      const [, what, tag, , id, , who] = m;
      const key = `${tag}|${what}|${who}`;
      let entry = resp.get(key);
      if (!entry) {
        const nid = byId.has(id) ? `${id}-b${String(d.n).padStart(2, '0')}` : id;
        entry = { id: nid, xml: m[0].replace(`xml:id="${id}"`, () => `xml:id="${nid}"`) };
        resp.set(key, entry);
        byId.set(nid, key);
      }
      rename.set(id, entry.id);
    }
    const repoint = (s) => s.replace(/(resp|who)="#([^"]+)"/g, (all, attr, id) => `${attr}="#${rename.get(id) ?? id}"`);
    for (const c of between(d.xml, '<revisionDesc>', '</revisionDesc>', d.f).match(/<change[\s\S]*?<\/change>/g) ?? [])
      changes.push(repoint(c));
    const span = /pages (\d+)–(\d+)/.exec(between(d.xml, '<title>', '</title>', d.f));
    if (span) {
      first = Math.min(first, Number(span[1]));
      last = Math.max(last, Number(span[2]));
    }
    const body = between(d.xml, '<body>', '</body>', d.f)
      .replace(/^\s*<div type="batch" n="\d+">/, '')
      .replace(/<\/div>\s*$/, '');
    bodies.push(repoint(body).trim());
  }

  // Header: the first batch's, with the folder's span and every statement.
  const head = docs[0].xml;
  const titleStmt = between(head, '<titleStmt>', '</titleStmt>', docs[0].f);
  const kept = titleStmt.replace(RESP, () => '');
  const newTitle = kept.replace(/pages \d+–\d+/, `pages ${first}–${last}`) + [...resp.values()].map((e) => e.xml).join('') + '\n      ';
  const uniq = [...new Set(changes)].sort((a, b) => (/when="([^"]+)"/.exec(b)?.[1] ?? '').localeCompare(/when="([^"]+)"/.exec(a)?.[1] ?? ''));
  const lang = docs.some((d) => d.xml.includes('<language ident="en">'))
    ? head.includes('<language ident="en">')
      ? head
      : head.replace(
          /(<language ident="fr">[^<]*<\/language>)/,
          `$1\n        <language ident="en">anglais : le compte rendu des révisions, cité de l'en-tête de la source</language>`,
        )
    : head;
  let out = lang
    .replace(titleStmt, () => newTitle)
    .replace(/<revisionDesc>[\s\S]*?<\/revisionDesc>/, () => `<revisionDesc>\n      ${uniq.join('\n      ')}\n    </revisionDesc>`)
    .replace(/<summary>Pages \d+ à \d+ de la cote,/, `<summary>Pages ${first} à ${last} de la cote,`)
    .replace(/ ; lot \d+ de vingt pages\./, ` ; la cote entière, réunie de ${docs.length} lot${docs.length > 1 ? 's' : ''} de vingt pages.`)
    .replace(/<body>[\s\S]*<\/body>/, () => `<body>\n${join(bodies)}\n    </body>`);
  out = out.replace(
    '<TEI ',
    `<!-- Fonds Alexandre Grothendieck, cote ${folder} : la cote entière, réunie par scripts/bundle-tei.mjs. Édition de démonstration, non autorisée, non destinée à la publication. -->\n<TEI `,
  );

  const file = resolve(OUT, `${folder}.fr.xml`);
  writeFileSync(file, out);
  execFileSync('xmllint', ['--noout', file]);
  n++;
}
console.log(`${n} folders → exports/tei/<folder>.fr.xml (well-formed, checked by xmllint)`);
