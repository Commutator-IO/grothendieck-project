#!/usr/bin/env node
/**
 * Where each proof lives: the file and line of every Lean declaration the site links to,
 * read from a checkout of Commutator-IO/GrothendieckArchivesProofs, into
 * src/content/lean-lines.json.
 *
 *   npm run lean-lines                    the checkout beside this repository
 *   LEAN_PROOFS=/path npm run lean-lines  another checkout
 *
 * The links are pinned to the checkout's commit, so a line number stays right after the file
 * changes; rerun this after the proofs move, then `npm run buffalo-index`. Two sources name
 * declarations: the proof cards (src/content/proofs.ts: a file and its theorems' short names)
 * and the Buffalo status files (docs/buffalo-*\/lean/PartNN.json: full names). The checkout is
 * not available in CI, so the output is committed, and the deploy only reads it.
 */
import { execFileSync } from 'node:child_process';
import { readFileSync, readdirSync, statSync, writeFileSync } from 'node:fs';
import { join, relative, resolve } from 'node:path';

const root = resolve(import.meta.dirname, '..');
const repo = process.env.LEAN_PROOFS ?? resolve(root, '../GrothendieckArchivesProofs');
const sha = execFileSync('git', ['-C', repo, 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim();
const dirty = execFileSync('git', ['-C', repo, 'status', '--porcelain', '--untracked-files=no'], { encoding: 'utf8' }).trim();
if (dirty) throw new Error(`${repo} has uncommitted changes: the links would point at lines GitHub does not have`);

/** Every .lean file of the checkout, outside .lake. */
function* leanFiles(dir) {
  for (const name of readdirSync(dir)) {
    if (name.startsWith('.')) continue;
    const p = join(dir, name);
    if (statSync(p).isDirectory()) yield* leanFiles(p);
    else if (name.endsWith('.lean')) yield p;
  }
}

// Declarations by full name, and by file and short name. Namespaces are followed through
// `namespace X` / `end X`; sections do not change names. Good enough for this repository's
// style (one declaration keyword at the start of a line, after its attributes and modifiers).
const DECL = /^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s+([^\s:({[]+)/;
const byName = new Map();
const byFile = new Map();
for (const f of leanFiles(repo)) {
  const path = relative(repo, f);
  const stack = [];
  const lines = readFileSync(f, 'utf8').split('\n');
  const local = new Map();
  lines.forEach((l, i) => {
    const ns = /^namespace\s+(\S+)/.exec(l);
    if (ns) return void stack.push(ns[1]);
    const end = /^end\s+(\S+)/.exec(l);
    if (end && stack.at(-1) === end[1]) return void stack.pop();
    const d = DECL.exec(l);
    if (!d) return;
    let name = d[2].replace(/^_root_\./, '');
    const full = d[2].startsWith('_root_.') ? name : [...stack, name].join('.');
    if (!byName.has(full)) byName.set(full, [path, i + 1]);
    const short = name.split('.').at(-1);
    if (!local.has(short)) local.set(short, i + 1);
    if (!local.has(name)) local.set(name, i + 1);
  });
  byFile.set(path, local);
}

/** A short name declared in exactly one file, with that file and line. */
const shortIndex = new Map();
for (const [path, local] of byFile) for (const [k, line] of local) shortIndex.set(k, shortIndex.has(k) ? null : [path, line]);
const unique = (k) => shortIndex.get(k) ?? null;

const REPO = 'https://github.com/Commutator-IO/GrothendieckArchivesProofs';
const out = { sha, files: {}, names: {} };
/** The proof cards by folder, for the badges of the transcription and modernised reading. */
const pages = {};
let missing = 0;

// The proof cards: `lean: 'lean/Grothendieck/…/FolderN.lean'` and `theorems: [...]`, as written in proofs.ts.
const proofs = readFileSync(resolve(root, 'src/content/proofs.ts'), 'utf8');
// One card per `{ folder: … }` object; its lean and theorems fields may sit in either order.
const cards = proofs.slice(proofs.indexOf('export const PROOFS')).split(/\n  \{\n/).slice(1).map((c) => `\n${c}`);
for (const card of cards) {
  const file = /\n\s*lean:\s*(['"])(.+?)\1,/.exec(card);
  const ths = /\n\s*theorems:\s*\[([\s\S]*?)\],/.exec(card);
  if (!file || !ths) { console.warn(`card without lean or theorems: ${card.slice(0, 80)}`); missing++; continue; }
  const m = [null, file[2], ths[1]];
  const field = (k) => new RegExp(`\\n\\s*${k}:\\s*(['"])((?:(?!\\1)[^\\\\]|\\\\.)*)\\1`).exec(card)?.[2];
  const vfield = /\n\s*verdict:\s*(\[[\s\S]*?\]|'[^']*'|"[^"]*")/.exec(card)?.[1] ?? '';
  const verdict = [...vfield.matchAll(/'([^']*)'|"([^"]*)"/g)].map((x) => x[1] ?? x[2]).join('; ');
  const pending = { folder: field('folder'), batch: Number(/\n\s*batch:\s*(\d+)/.exec(card)?.[1]), page: field('page'), name: field('name'), verdict };
  const path = m[1].replace(/^lean\//, '');
  const local = byFile.get(path);
  if (!local) { console.warn(`card file not in the checkout: ${path}`); missing++; continue; }
  const want = [...m[2].matchAll(/'((?:[^'\\]|\\.)*)'|"((?:[^"\\]|\\.)*)"/g)].map((x) => (x[1] ?? x[2]).replace(/\\(.)/g, '$1'));
  const lines = (out.files[path] ??= {});
  for (const t of want) {
    // In the card's file first; else a full name, or a short name found in exactly one other file
    // (a card lists the lemmas it rests on, some of which live in the files it imports).
    const line = local.get(t) ?? local.get(t.split('.').at(-1));
    const elsewhere = byName.get(t) ?? unique(t.split('.').at(-1));
    if (line) lines[t] = [path, line];
    else if (elsewhere) lines[t] = elsewhere;
    else { console.warn(`${path}: no declaration ${t}`); missing++; }
  }
  // For the reading views: the card's pages, and where its main theorem is. A card lists the
  // lemmas first and the result last, so the last of its theorems found in its own file.
  const first = want.map((t) => lines[t]).filter((x) => x && x[0] === path).at(-1) ?? want.map((t) => lines[t]).find(Boolean);
  if (pending.folder && pending.page) {
    (pages[pending.folder] ??= []).push({
      batch: pending.batch,
      page: pending.page,
      name: pending.name,
      verdict: pending.verdict,
      href: first ? `${REPO}/blob/${sha}/${first[0]}#L${first[1]}` : `${REPO}/blob/${sha}/${path}`,
    });
  }
}

// The Buffalo status files: full names.
for (const course of ['buffalo-topos', 'buffalo-ag', 'buffalo-groupes']) {
  const dir = resolve(root, 'docs', course, 'lean');
  for (const f of readdirSync(dir).filter((n) => /^Part\d+\.json$/.test(n))) {
    for (const e of JSON.parse(readFileSync(join(dir, f), 'utf8'))) {
      for (const n of e.lean ?? []) {
        const hit = byName.get(n);
        if (hit) out.names[n] = hit;
        else { missing++; if (missing < 40) console.warn(`${course}/${f}: no declaration ${n}`); }
      }
    }
  }
}

writeFileSync(resolve(root, 'src/content/lean-lines.json'), JSON.stringify(out));
writeFileSync(resolve(root, 'src/content/lean-pages.json'), JSON.stringify(pages));
console.log(`lean-lines: ${Object.values(out.files).reduce((n, o) => n + Object.keys(o).length, 0)} card theorems, ${Object.keys(out.names).length} Buffalo declarations, ${missing} not found, at ${sha.slice(0, 7)}`);
