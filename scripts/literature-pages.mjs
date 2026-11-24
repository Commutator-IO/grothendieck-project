#!/usr/bin/env node
/**
 * The findings found later in the literature (status « matched »), by folder and page, for the
 * badges of the reading views: src/content/literature-pages.json, which src/lib/leanBadges.ts
 * reads beside the Lean cards. Run by `npm run dev` and `npm run build`, so it follows
 * src/content/findings.ts without being committed by hand.
 *
 *   npm run literature-pages
 */
import { readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { FINDINGS } from '../src/content/findings.ts';

const root = resolve(import.meta.dirname, '..');

/**
 * A short label for a source: « Isbell 1981 », « Bloch et al. 2012 », « SGA 4 ». The year is the
 * arXiv identifier's when there is one, else the first year in parentheses, else the first year
 * after the authors; a title or a sentence gives null, and the next source is tried.
 */
function shortSource(ref) {
  const parts = ref.split(/,| — /).map((x) => x.trim());
  const head = parts[0];
  if (/^(SGA|EGA|FGA|SGA)\s*[\dIVX]*/.test(head) && head.length < 12) return head;
  const isAuthor = (x) => /^([A-ZÀ-Ý]\.\s?(-?[A-Z]\.\s?)*)?[A-ZÀ-Ý][\p{L}'’-]+(\s[A-ZÀ-Ý][\p{L}'’-]+)?$/u.test(x);
  if (!isAuthor(head)) return null;
  const surname = head.split(/\s+/).filter((w) => !/^[A-Z]\.(-?[A-Z]\.)*$/.test(w)).join(' ');
  const more = parts.length > 1 && isAuthor(parts[1]) && /^[A-Z]\./.test(parts[1]);
  const arxiv = /arXiv:\s?(\d\d)(\d\d)\./.exec(ref);
  const year = arxiv ? `20${arxiv[1]}` : (/\((?:[^()]*\s)?(1[89]\d\d|20\d\d)\)/.exec(ref) ?? /\b(1[89]\d\d|20\d\d)\b(?![.\d])/.exec(parts.slice(1).join(', ')))?.[1];
  return `${surname}${more ? ' et al.' : ''}${year ? ` ${year}` : ''}`;
}

const out = {};
for (const n of FINDINGS) {
  if (n.kind !== 'mathematical' || n.status !== 'matched' || !n.cote || !n.pages) continue;
  const refs = n.literature ?? [];
  (out[n.cote] ??= []).push({
    id: n.id,
    page: n.pages,
    name: refs.map(shortSource).find(Boolean) ?? 'in print',
    refs: refs.slice(0, 2).map((r) => (r.length > 120 ? `${r.slice(0, 118)}…` : r)),
  });
}
writeFileSync(resolve(root, 'src/content/literature-pages.json'), JSON.stringify(out));
console.log(`literature-pages: ${Object.values(out).flat().length} findings in ${Object.keys(out).length} folders`);

// His own printed texts (src/content/publications.json): a folder holding a draft of a published
// passage, statements shared with one, or what the print only announces. Their pages are written
// for a reader (« batch 2, pp. 27–36 », « batches 3–4 »): the pages when given, else the first
// page of each batch named (batches of twenty).
const PUB = JSON.parse(readFileSync(resolve(root, 'src/content/publications.json'), 'utf8'));
const TEXT = Object.fromEntries(PUB.texts.map((t) => [t.id, t]));
const KIND = { draft: 'are a draft of the printed passage', partial: 'share statements with the printed passage', open: 'prove what the print only announces or leaves open', edition: 'are edited in print' };
const SHORT = { ptt: 'PTT', fga: 'FGA', chern: 'Classes de Chern', sga1: 'SGA 1', ega3: 'EGA III', sga3: 'SGA 3', ega4: 'EGA IV', dix: 'Dix exposés', lm: 'Longue Marche', ps: 'Pursuing Stacks' };
function pagesOf(spec) {
  const pp = /pp?\.\s*([\d–,\s-]+)/.exec(spec);
  if (pp) return pp[1].replace(/[\s,]+$/, '').trim();
  const b = /batch(?:es)?\s+([\d–\s,and-]+)/.exec(spec);
  if (!b) return null;
  const nums = b[1].split(/,|and/).flatMap((r) => {
    const [x, y] = r.split(/[–-]/).map((n) => Number.parseInt(n, 10));
    return Number.isFinite(x) ? (Number.isFinite(y) ? Array.from({ length: y - x + 1 }, (_, i) => x + i) : [x]) : [];
  });
  return nums.map((n) => `${(n - 1) * 20 + 1}`).join(', ') || null;
}
const prints = {};
for (const l of PUB.links) {
  const page = pagesOf(l.pages);
  const t = TEXT[l.text];
  if (!page || !t) continue;
  (prints[l.folder] ??= []).push({
    page,
    // « 0_IV » is EGA's chapter 0 of volume IV, printed with the IV as a subscript.
    name: l.where === t.title || l.where === SHORT[l.text] ? SHORT[l.text] ?? t.title : `${SHORT[l.text] ?? t.title} ${l.where.replace('0_IV', '0ᵢᵥ')}`,
    kind: KIND[l.kind] ?? l.kind,
    note: l.note.length > 220 ? `${l.note.slice(0, 218)}…` : l.note,
    href: t.url,
  });
}
writeFileSync(resolve(root, 'src/content/print-pages.json'), JSON.stringify(prints));
console.log(`print-pages: ${Object.values(prints).flat().length} of ${PUB.links.length} links to his printed texts, in ${Object.keys(prints).length} folders`);
