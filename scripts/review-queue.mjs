#!/usr/bin/env node
/**
 * Builds the queue of the review page (/review/) from issue #35.
 *
 *   gh issue view 35 --json body -q .body > /tmp/35.md
 *   node scripts/review-queue.mjs /tmp/35.md
 *
 * Reads the issue body from a file — never the network — together with
 * transcripts/, src/content/dated-leaves.json and src/content/letters.json,
 * and writes two files:
 *
 *   src/content/review-queue.json     the checks: where, what is asked
 *   src/content/review-snippets.json  the current reading around each doubt
 *
 * They are apart because of the rights hold (#31): the page loads the snippets
 * only when the build may show transcriptions (VITE_RENDER_TRANSCRIPTS), so a
 * build with the switch off carries none of them. A snippet is at most fifteen
 * words.
 *
 * A box covers either named places (« 105 « 06/09/82 » », « 109 pp. 9–10 »)
 * — one item each, read only while the box is unchecked — or a kind of error
 * spread over the corpus (§1 the unread words of a batch, §2 the
 * \add/\supplied residue), for which a few occurrences are sampled from the
 * current transcriptions whether or not the box is ticked: a ticked box says
 * the batch was sampled, not that every sampled spot was answered. An item
 * leaves the queue when its id is in src/content/review-answered.json (the
 * issue that answered it), or when an applied answer removed its mark. Boxes that name no place (« spot-check the skips ») and the
 * comparison of folder 12 with a transcription made elsewhere are left out:
 * neither is a question about one spot of a page. They are listed on stderr.
 */
import { existsSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join, resolve } from 'node:path';

const ROOT = resolve(import.meta.dirname, '..');
const T = join(ROOT, 'transcripts');
const bodyFile = process.argv[2];
if (!bodyFile) {
  console.error('usage: node scripts/review-queue.mjs <issue-35-body.md>');
  process.exit(1);
}
const body = readFileSync(bodyFile, 'utf8');
const MAX_WORDS = 15;
const SAMPLES = { ill: 3, uncertain: 2, add: 8, supplied: 8 };
const answeredItems = JSON.parse(readFileSync(join(ROOT, 'src/content/review-answered.json'), 'utf8')).items;
const answered = new Set(Object.keys(answeredItems));

const leaves = JSON.parse(readFileSync(join(ROOT, 'src/content/dated-leaves.json'), 'utf8')).records;
const letters = JSON.parse(readFileSync(join(ROOT, 'src/content/letters.json'), 'utf8')).records;
const isCote = (c) => existsSync(join(T, c));
const batchOf = (p) => Math.max(1, Math.ceil(p / 20));
const skipped = [];

/* ---------- reading a transcription ---------- */

const fileCache = new Map();
function lines(cote, batch) {
  const f = join(T, cote, `batch-${String(batch).padStart(2, '0')}.fr.tex`);
  if (!fileCache.has(f)) fileCache.set(f, existsSync(f) ? readFileSync(f, 'utf8').split('\n') : null);
  return fileCache.get(f);
}

/** The page each line stands on, from \page{} and \pagerange{}{} markers. */
function pagesOf(ls) {
  let p = null;
  return ls.map((l) => {
    const m = /\\page(?:range)?\{(\d+)\}/.exec(l);
    if (m) p = Number(m[1]);
    return p;
  });
}

/** Display environments, whose lines are formulas rather than prose. */
function proseMask(ls) {
  let depth = 0;
  return ls.map((l) => {
    const t = l.trim();
    if (/\\begin\{(equation|align|gather|multline|tikzcd|array|eqnarray|displaymath|tikzpicture|CD)\*?\}|^\\\[/.test(t)) depth++;
    const prose = depth === 0 && !t.startsWith('%') && !t.startsWith('\\');
    if (/\\end\{(equation|align|gather|multline|tikzcd|array|eqnarray|displaymath|tikzpicture|CD)\*?\}|\\\]\s*$/.test(t)) depth = Math.max(0, depth - 1);
    return prose;
  });
}

/** The argument of a macro at `i` (the opening brace), with its end. */
function braced(s, i) {
  let d = 0;
  for (let j = i; j < s.length; j++) {
    if (s[j] === '\\') {
      j++;
      continue;
    }
    if (s[j] === '{') d++;
    else if (s[j] === '}' && --d === 0) return { arg: s.slice(i + 1, j), end: j + 1 };
  }
  return { arg: s.slice(i + 1), end: s.length };
}

/**
 * A line as tokens: words, formulas, illegible words, doubtful readings, his
 * insertions, our supplies, struck text. `glue` marks a token written against
 * the previous one with no space (an inserted prefix).
 */
function tokenize(s, keepNotes = false) {
  const out = [];
  let buf = '';
  // Whether the text being gathered in `buf` began flush against a macro.
  let flush0 = false;
  const flush = () => {
    const glued = flush0 && !/^\s/.test(buf);
    buf
      .split(/\s+/)
      .filter(Boolean)
      .forEach((w, i) => out.push({ k: 'w', s: w, glue: glued && i === 0 }));
    buf = '';
    flush0 = false;
  };
  const plain = (x) => tokenize(x, keepNotes).map((t) => (t.k === 'ill' ? '[…]' : t.s)).join(' ');
  const kinds = { ill: 'ill', uncertain: 'unc', add: 'add', supplied: 'sup', struck: 'struck' };
  for (let i = 0; i < s.length; ) {
    const c = s[i];
    if (c === '%' && s[i - 1] !== '\\') break;
    if (c === '$') {
      const glued = buf.length > 0 && !/\s$/.test(buf);
      flush();
      const j = s.indexOf('$', i + 1);
      const tex = s.slice(i + 1, j < 0 ? undefined : j).trim();
      out.push({ k: 'm', s: tex.length > 40 ? '…' : tex, glue: glued });
      i = j < 0 ? s.length : j + 1;
      flush0 = true;
      continue;
    }
    if (c === '~') {
      buf += ' ';
      i++;
      continue;
    }
    if (c === '\\') {
      const m = /^\\([a-zA-Z]+)\*?/.exec(s.slice(i));
      if (!m) {
        i += 2;
        continue;
      }
      const name = m[1];
      const j = i + m[0].length;
      if (s[j] !== '{') {
        if (name === 'dots' || name === 'ldots') buf += '…';
        i = j;
        continue;
      }
      let { arg, end } = braced(s, j);
      if (name === 'pagerange' && s[end] === '{') end = braced(s, end).end;
      const glued = buf.length > 0 && !/\s$/.test(buf);
      flush();
      if (name in kinds) out.push({ k: kinds[name], s: name === 'ill' ? '' : plain(arg), glue: glued });
      else if (!(keepNotes && name === 'note') && !['note', 'page', 'pagerange', 'label', 'footnote', 'marginpar'].includes(name)) {
        for (const t of tokenize(arg, keepNotes)) out.push(t);
      }
      i = end;
      flush0 = true;
      continue;
    }
    buf += c;
    i++;
  }
  flush();
  return out;
}

/** At most fifteen words around token `at`: the doubtful one highlighted. */
function snippet(toks, at) {
  const shown = (t) => (t.k === 'ill' ? '[…]' : t.k === 'm' ? `$${t.s}$` : t.k === 'struck' ? `⟨struck: ${t.s.split(' ').slice(0, 3).join(' ')}⟩` : t.s);
  const words = (t) => (t.k === 'w' || t.k === 'm' || t.k === 'ill' ? 1 : shown(t).split(/\s+/).length);
  let lo = at;
  let hi = at;
  let n = words(toks[at]);
  if (n > MAX_WORDS) return null;
  // Grow both sides alternately until fifteen words.
  for (let side = 0, stuck = 0; stuck < 2; side ^= 1) {
    const k = side ? hi + 1 : lo - 1;
    if (k < 0 || k >= toks.length || n + words(toks[k]) > MAX_WORDS) {
      stuck++;
      continue;
    }
    stuck = 0;
    n += words(toks[k]);
    if (side) hi = k;
    else lo = k;
  }
  const join = (a, b) =>
    toks
      .slice(a, b)
      .map((t, i) => (i > 0 && t.glue ? '' : ' ') + shown(t))
      .join('')
      .trim();
  return {
    before: (lo > 0 ? '… ' : '') + join(lo, at),
    word: shown(toks[at]),
    glueBefore: !!toks[at].glue && at > lo,
    glueAfter: !!toks[at + 1]?.glue && hi > at,
    after: join(at + 1, hi + 1) + (hi < toks.length - 1 ? ' …' : ''),
  };
}

/** Occurrences of token kind `k` in the prose of a batch, readable around. */
function occurrences(cote, batch, test) {
  const ls = lines(cote, batch);
  if (!ls) return [];
  const pages = pagesOf(ls);
  const prose = proseMask(ls);
  const out = [];
  ls.forEach((l, li) => {
    if (!prose[li] || pages[li] == null) return;
    const toks = tokenize(l);
    toks.forEach((t, i) => {
      if (!test(t, toks, i)) return;
      const near = toks.slice(Math.max(0, i - 3), i + 4);
      // Context a reader can find on the page: no other gap close by.
      if (near.filter((x) => x.k === 'ill').length > (t.k === 'ill' ? 1 : 0)) return;
      if (near.filter((x) => x.k === 'w').length < 4) return;
      const s = snippet(toks, i);
      if (s) out.push({ page: pages[li], line: li + 1, snippet: s });
    });
  });
  return out;
}

/** `n` items spread evenly over a list. */
const spread = (xs, n) => (xs.length <= n ? xs : Array.from({ length: n }, (_, i) => xs[Math.floor(((i + 0.5) * xs.length) / n)]));

/**
 * The sample of a batch, kept as it was before answers were applied: an
 * applied answer removed its mark, so a placeholder stands where the mark was
 * (after the other occurrences of its page) and the spread picks the same
 * occurrences as before; the placeholders are then dropped. An answer that
 * left a mark on the spot (a doubt narrowed to one word) is `markKept`: the
 * mark is still an occurrence, excluded by its id, and needs no stand-in.
 */
function sampleOf(prefix, occ, n) {
  const gone = Object.entries(answeredItems)
    .filter(([id, a]) => a.result === 'applied' && !a.markKept && id.startsWith(`${prefix}-p`))
    .map(([id]) => Number(/-p(\d+)$/.exec(id)?.[1]))
    .filter(Boolean);
  const xs = [...occ];
  for (const page of gone) {
    const at = xs.findIndex((o) => o.page > page);
    xs.splice(at < 0 ? xs.length : at, 0, { page, gone: true });
  }
  return spread(xs, n).filter((o) => !o.gone);
}

/** A snippet around `needle`, on a given line or near it, else on the page. */
function snippetAt(cote, batch, { line, page, needle }) {
  const ls = lines(cote, batch);
  if (!ls || !needle) return null;
  const pages = pagesOf(ls);
  const near = line ? [0, -1, 1, -2, 2, -3, 3].map((d) => line - 1 + d).filter((i) => i >= 0 && i < ls.length) : [];
  const onPage = page == null ? [] : ls.map((_, i) => i).filter((i) => pages[i] === page);
  const norm = (x) => x.replace(/[\s«»()]/g, '').toLowerCase();
  const want = norm(needle);
  for (const li of [...near, ...onPage]) {
    if (!norm(ls[li]).includes(want.slice(0, 5))) continue;
    const toks = tokenize(ls[li], true);
    const i = toks.findIndex((t) => t.s && (want.startsWith(norm(t.s)) || norm(t.s).startsWith(want.slice(0, 5))) && norm(t.s).length >= Math.min(3, want.length));
    if (i >= 0) {
      const sn = snippet(toks, i);
      if (sn) return { snippet: sn, page: pages[li] };
    }
  }
  return null;
}

/* ---------- the issue ---------- */

const items = [];
const snippets = {};
const ids = new Set();
function push(it, snip) {
  if (it.kind === 'letter' && it.page && items.some((x) => x.kind === 'letter' && x.cote === it.cote && x.page === it.page)) return;
  let id = it.id;
  for (let n = 2; ids.has(id); n++) id = `${it.id}-${n}`;
  ids.add(id);
  if (answered.has(id)) return;
  const page = it.page ?? null;
  const batch = it.batch ?? (page ? batchOf(page) : 1);
  const edition = it.edition ?? 'fr';
  items.push({
    id,
    section: it.section,
    kind: it.kind,
    cote: it.cote,
    batch,
    page,
    question: it.question,
    context: it.context ?? null,
    link: `/#${it.cote}/${batch}/${edition}${page ? `/p${page}` : ''}`,
  });
  if (snip) snippets[id] = snip;
}

// The questions name no word of the reading: that is in the snippet, which a
// build with the transcriptions switched off does not carry.
const QUESTIONS = {
  ill: 'An unread word: can you read it on the page?',
  uncertain: () => 'A doubtful reading: is the marked word what the page has?',
  add: () => 'The marked word is given as his insertion. Is it in his ink, or a word the transcriber supplied?',
  supplied: () => 'The marked word is given as supplied by the transcriber. Is it on the page, inserted in his hand?',
};

let section = '';
let sub = '';
for (const raw of body.split('\n')) {
  const h = /^(#{1,3})\s+(.*)$/.exec(raw);
  if (h) {
    if (h[1].length === 1) section = h[2];
    else if (/^\d+\./.test(h[2]) || h[1].length === 2) sub = h[2];
    else sub = h[2];
    if (h[1] === '#') sub = '';
    continue;
  }
  const box = /^\s*- \[([ xX])\]\s+(.*)$/.exec(raw);
  if (!box) {
    if (/^\*\*(Arguments|References)/.test(raw)) sub = `${sub.split(' · ')[0]} · ${raw.replace(/\*/g, '')}`;
    continue;
  }
  const text = box[2].trim();
  const fromMoved = /Moved from #48/.test(section);
  const n = fromMoved ? `#48 ${sub.split(' · ')[0]}` : sub;
  // A ticked box closes a named spot; the sampled kinds (§1, §2) stay open
  // until each item is answered.
  const sampled = !fromMoved && (sub.startsWith('1.') || sub.startsWith('2.'));
  if (box[1] !== ' ' && !sampled) continue;

  // §1 — the unread words of the densest batches.
  if (!fromMoved && sub.startsWith('1.')) {
    const cote = /^(\S+)/.exec(text)[1];
    // « 58 batch 1 — 689 · batch 2 — 570 — sampled …: batch 1 p. 4 … »: the
    // batches are those given with their count, once each.
    for (const batch of new Set([...text.matchAll(/batch (\d+) — \d/g)].map((m) => Number(m[1])))) {
      for (const o of sampleOf(`ill-${cote}-${batch}`, occurrences(cote, batch, (t) => t.k === 'ill'), SAMPLES.ill))
        push({ id: `ill-${cote}-${batch}-p${o.page}`, section: n, kind: 'ill', cote, batch, page: o.page, question: QUESTIONS.ill, context: `One of the densest batches for unread words (#35 §1).` }, o.snippet);
      for (const o of sampleOf(`unc-${cote}-${batch}`, occurrences(cote, batch, (t) => t.k === 'unc' && t.s.split(' ').length <= 3 && t.s.length > 1), SAMPLES.uncertain))
        push({ id: `unc-${cote}-${batch}-p${o.page}`, section: n, kind: 'uncertain', cote, batch, page: o.page, question: QUESTIONS.uncertain(o.snippet.word), context: `Doubtful readings in the same batch (#35 §1).` }, o.snippet);
    }
    continue;
  }

  // §2 — his insertions and ours, sampled over the corpus, one per folder.
  if (!fromMoved && sub.startsWith('2.')) {
    const kind = /free-standing/.test(text) ? 'add' : /glued/.test(text) ? 'supplied' : null;
    if (!kind) {
      skipped.push(text);
      continue;
    }
    const FUNCTION = /^(même|de|la|le|les|est|et|que|on|un|une|des|du|à|en|pas|ne|se|il|\(|\))$/;
    const found = [];
    for (const cote of readdirSync(T).sort((a, b) => a.localeCompare(b, 'en', { numeric: true }))) {
      if (!isCote(cote) || !/^\d/.test(cote)) continue;
      const batches = readdirSync(join(T, cote)).map((f) => /^batch-(\d+)\.fr\.tex$/.exec(f)?.[1]).filter(Boolean).map(Number);
      let hit = null;
      for (const batch of batches.sort((a, b) => a - b)) {
        const test =
          kind === 'add'
            ? (t) => t.k === 'add' && !t.glue && FUNCTION.test(t.s)
            : (t, toks, i) => t.k === 'sup' && t.s.endsWith('-') && toks[i + 1]?.glue;
        const o = occurrences(cote, batch, test)[0];
        if (o) {
          hit = { ...o, cote, batch };
          break;
        }
      }
      if (hit) found.push(hit);
    }
    for (const o of spread(found, SAMPLES[kind]))
      push({ id: `${kind}-${o.cote}-${o.batch}-p${o.page}`, section: n, kind, cote: o.cote, batch: o.batch, page: o.page, question: QUESTIONS[kind](o.snippet.word), context: kind === 'add' ? 'A free-standing \\add{} that may be a supply (#35 §2).' : 'A glued \\supplied{} that may be his insertion (#35 §2).' }, o.snippet);
    continue;
  }

  // §3 — dates on the leaves.
  if (!fromMoved && sub.startsWith('3.')) {
    const m = /^\*\*(.+?)\*\*\s*(?:\(([^)]*)\))?\s*—\s*(.*)$/.exec(text);
    if (!m) {
      skipped.push(text);
      continue;
    }
    const label = m[1];
    const clauses = m[3].split(/;\s*/);
    for (const clause of clauses) {
      const lead = /^(\d+(?:-\d+)?)\b(.*)$/.exec(clause.trim());
      if (lead && isCote(lead[1])) {
        const cote = lead[1];
        const rest = lead[2];
        const batch = Number(/batch (\d+)/.exec(rest)?.[1]) || null;
        const page = Number(/pp?\. (\d+)/.exec(rest)?.[1]) || null;
        const quote = /«\s*([^»]+?)\s*»/.exec(rest)?.[1] ?? null;
        const norm = (x) => x.replace(/\s+/g, '').toLowerCase();
        const rec =
          leaves.find((r) => r.folder === cote && quote && norm(r.written).includes(norm(quote).slice(0, 8))) ??
          leaves.find((r) => r.folder === cote && page && String(r.page).split(/[-–]/)[0] === String(page)) ??
          (batch ? leaves.find((r) => r.folder === cote && r.batch === batch) : null) ??
          (!page && !batch ? leaves.find((r) => r.folder === cote) : null);
        const p = page ?? (rec ? Number(String(rec.page).split(/[-–]/)[0]) || null : null);
        const b = batch ?? rec?.batch ?? (p ? batchOf(p) : 1);
        const line = rec && rec.folder === cote && Number(rec.where.split(':')[1]);
        const s = snippetAt(cote, b, { line: line || null, page: p, needle: quote ?? rec?.written ?? null });
        push({ id: `date-${cote}-p${p ?? b}`, section: n, kind: 'date', cote, batch: b, page: p, question: `${label[0].toUpperCase()}${label.slice(1)}: ${clause.trim()}`, context: rec ? `Recorded as « ${rec.written} » (${rec.hand}, ${rec.kind}).` : null }, s?.snippet ?? null);
        continue;
      }
      // « the day-only dates of 154 (24.12, 25.12), 67 (…) » — cotes named in passing.
      const cotes = [...clause.replace(/\([^)]*\)/g, '').replace(/«[^»]*»/g, '').matchAll(/(?<![.\d])(\d{1,3}(?:-\d)?)(?![.\d])/g)].map((x) => x[1]).filter(isCote);
      if (!cotes.length) {
        skipped.push(`${label}: ${clause}`);
        continue;
      }
      for (const cote of new Set(cotes)) {
        const yearless = leaves.filter((r) => r.folder === cote && !/\d{4}|\.\d\d$|\/\d\d$/.test(r.written.replace(/^(\d+\.\d+)$/, '$1')));
        const recs = yearless.length ? yearless : leaves.filter((r) => r.folder === cote).slice(0, 1);
        for (const rec of recs.slice(0, 3)) {
          const p = Number(String(rec.page).split(/[-–]/)[0]) || null;
          const s = snippetAt(cote, rec.batch, { line: Number(rec.where.split(':')[1]), page: p, needle: rec.written });
          push({ id: `date-${cote}-p${p ?? rec.batch}`, section: n, kind: 'date', cote, batch: rec.batch, page: p, question: `${label[0].toUpperCase()}${label.slice(1)}: « ${rec.written} » — is the year on the leaf, or taken from a neighbour?`, context: `Recorded as ${rec.iso} (${rec.hand}, ${rec.kind}).` }, s?.snippet ?? null);
        }
      }
    }
    continue;
  }

  // §4 — the letters.
  if (!fromMoved && sub.startsWith('4.')) {
    const m = /^\*\*(.+?)\*\*\s*—\s*(.*)$/.exec(text);
    if (m) {
      for (const part of m[1].split(/,\s*(?=\d)/)) {
        const lead = /^(\d+(?:-\d+)?)(?:\s+pp?\.\s*(\d+))?/.exec(part.trim());
        if (!lead || !isCote(lead[1])) continue;
        const cote = lead[1];
        const page = Number(lead[2]) || null;
        const rec = letters.find((r) => r.folder === cote && (!page || String(r.pages).split(/[-–]/)[0] === String(page))) ?? null;
        const p = page ?? (rec ? Number(String(rec.pages).split(/[-–]/)[0]) || null : null);
        const b = rec?.batch ?? (p ? batchOf(p) : 1);
        const s = rec ? snippetAt(cote, b, { line: Number(rec.where.split(':')[1]), page: p, needle: rec.date }) : null;
        push({ id: `letter-${cote}-p${p ?? b}`, section: n, kind: 'letter', cote, batch: b, page: p, question: `${part.trim()} — ${m[2]}`, context: rec ? `Register: ${rec.direction} ${rec.correspondent ?? 'an unnamed correspondent'}, ${rec.date ?? 'undated'}, ${rec.form}, ${rec.language}.` : null }, s?.snippet ?? null);
      }
      continue;
    }
    const named = [...text.matchAll(/\*\*(\d+(?:-\d+)?)\*\*\s*«\s*([^»]+?)\s*»/g)];
    if (named.length) {
      for (const [, cote, what] of named)
        push({ id: `letter-${cote}-missing`, section: n, kind: 'letter', cote, batch: 1, page: null, question: `The inventory lists « ${what} » in folder ${cote}, and the transcriptions found no such letter. Is it in the folder, and on which page?` }, null);
      continue;
    }
    if (/unnamed as a private person/.test(text)) {
      for (const rec of letters.filter((r) => !r.correspondent)) {
        const wl = Number(rec.where.split(':')[1]);
        const ls = lines(rec.folder, rec.batch);
        const p = Number(String(rec.pages).split(/[-–]/)[0]) || (ls && wl ? pagesOf(ls)[wl - 1] : null) || null;
        push({ id: `letter-${rec.folder}-p${p}`, section: n, kind: 'letter', cote: rec.folder, batch: rec.batch, page: p, question: 'The correspondent is left unnamed as a private person. Is the writer or addressee in fact a public figure?', context: rec.correspondentNote ?? null }, null);
      }
      continue;
    }
    skipped.push(text);
    continue;
  }

  // #48 §2 — the edition's own arguments and the references cited from memory.
  if (fromMoved && sub.startsWith('2.')) {
    const arg = /^\*\*(\d+(?:-\d+)?)(?:,\s*pp?\.\s*([\d–, -]+))?:\*\*\s*(.*)$/.exec(text);
    if (arg && isCote(arg[1])) {
      const page = Number(/\d+/.exec(arg[2] ?? '')?.[0]) || null;
      push({ id: `argument-${arg[1]}-p${page ?? 0}`, section: n, kind: 'argument', cote: arg[1], page, edition: 'modern', question: arg[3], context: `A footnote of the modernised reading gives an argument of the edition's own, unchecked (#48 → #35).` }, null);
      continue;
    }
    const refs = /\(([\d, ]+)\)\s*$/.exec(text);
    if (refs) {
      const cotes = refs[1].split(/,\s*/).filter(isCote);
      if (cotes.length) {
        push({ id: `reference-${cotes.join('-')}`, section: n, kind: 'reference', cote: cotes[0], page: null, edition: 'modern', question: `References cited from memory in the modernised readings of ${cotes.join(', ')}: ${text.replace(/\s*\([\d, ]+\)\s*$/, '')}. Do they say what the footnotes say?`, context: null }, null);
        continue;
      }
    }
  }
  skipped.push(`${n}: ${text.slice(0, 100)}`);
}

writeFileSync(
  join(ROOT, 'src/content/review-queue.json'),
  `${JSON.stringify({ $why: 'Open checks of issue #35, one per spot of a page, built by scripts/review-queue.mjs from the issue body and the transcriptions. The current readings are in review-snippets.json, loaded only when the build shows transcriptions.', built: new Date().toISOString().slice(0, 10), items }, null, 1)}\n`,
);
writeFileSync(join(ROOT, 'src/content/review-snippets.json'), `${JSON.stringify(snippets, null, 1)}\n`);
console.error(`${items.length} items, ${Object.keys(snippets).length} with a snippet.`);
if (skipped.length) console.error(`Not turned into items (no single spot of a page):\n  ${skipped.join('\n  ')}`);
