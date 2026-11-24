#!/usr/bin/env node
/**
 * The findings found later in the literature (status « matched »), by folder and page, for the
 * badges of the reading views: src/content/literature-pages.json, which src/lib/leanBadges.ts
 * reads beside the Lean cards. Run by `npm run dev` and `npm run build`, so it follows
 * src/content/findings.ts without being committed by hand.
 *
 *   npm run literature-pages
 */
import { writeFileSync } from 'node:fs';
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
