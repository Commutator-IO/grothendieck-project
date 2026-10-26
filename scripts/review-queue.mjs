#!/usr/bin/env node
/**
 * Builds the queue of the review page (/review/) from the checklist of
 * issue #35, kept in the repository since #35 was closed (2026-10-20):
 *
 *   node scripts/review-queue.mjs            # reads docs/review/issue-35.md
 *   node scripts/review-queue.mjs <file.md>  # or another copy of the list
 *
 * Tick a box in docs/review/issue-35.md (or list the item in
 * src/content/review-answered.json) when a check is applied.
 *
 * Reads the issue body from a file — never the network — together with
 * transcripts/, src/content/dated-leaves.json and src/content/letters.json,
 * and writes two files:
 *
 *   src/content/review-queue.json     the checks: where, what is asked
 *
 * Each item carries a `prompt` (one plain question for the reader), a `hint`
 * (where on the facsimile to look), `choices` (the answers offered as
 * buttons), and, where it helps, the register `entry` of a letter or the
 * edition's `claim` to check; #35's own wording is kept as `details`.
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
const bodyFile = process.argv[2] ?? join(ROOT, 'docs/review/issue-35.md');
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
    prompt: it.prompt,
    hint: it.hint,
    choices: it.choices,
    entry: it.entry ?? null,
    claim: it.claim ?? null,
    details: it.details ?? null,
    context: it.context ?? null,
    link: `/#${it.cote}/${batch}/${edition}${page ? `/p${page}` : ''}`,
  });
  if (snip) snippets[id] = snip;
}

/* ---------- what is asked ---------- */

// The prompts name no word of the transcription beyond a date or a label as
// written: the passage is in the snippet, which a build with the
// transcriptions switched off does not carry. Each choice is a button; its
// `verdict` colours the answer, `ask` opens a field for the reader's words.
const C = (value, verdict, ask) => ({ value, verdict, ...(ask ? { ask } : {}) });
const pagesText = (ps) =>
  ps.length === 1
    ? `p. ${ps[0]}`
    : ps.length > 2 && ps.every((x, i) => i === 0 || x === ps[i - 1] + 1)
      ? `pp. ${ps[0]}–${ps.at(-1)}`
      : `pp. ${ps.slice(0, -1).join(', ')} and ${ps.at(-1)}`;
const firstPage = (r) => Number(String(r.page ?? r.pages).split(/[-–]/)[0]) || null;
const MONTHS = 'January February March April May June July August September October November December'.split(' ');
const human = (iso) => {
  const [y, m, d] = String(iso).split('-');
  return [d ? Number(d) : null, m ? MONTHS[Number(m) - 1] : null, y].filter(Boolean).join(' ');
};
const slug = (w) =>
  w
    .toLowerCase()
    .normalize('NFD')
    .replace(/[̀-ͯ]/g, '')
    .replace(/([a-z]{3})[a-z]*/g, '$1')
    .replace(/[^a-z0-9]/g, '');
/**
 * A record gets its date in the id when one clause gives several items, or
 * when it is not the first record of its page: the plain id stays with the
 * record it named before, so an answer kept in a browser keeps its item.
 */
const dateId = (cote, rec, p, split) =>
  `date-${cote}-p${p}${split || leaves.find((r) => r.folder === cote && firstPage(r) === p) !== rec ? `-${slug(rec.written)}` : ''}`;
const looksLike = (rec) =>
  rec?.kind === 'stamp'
    ? 'a printed banner or stamp with a date'
    : rec?.hand === 'typed' || rec?.kind === 'typescript'
      ? 'a typed date'
      : rec?.hand === 'his'
        ? 'a date in his hand'
        : 'a date';
const facsimileAt = (ps) => `Look on the facsimile at ${pagesText(ps)}`;

const ASK = {
  ill: {
    prompt: 'Can you read the illegible word, shown as […] in the highlighted spot?',
    choices: [C('I can read it', 'other', 'What the word reads'), C('Illegible to me too', 'illegible')],
  },
  uncertain: {
    prompt: 'Is the highlighted word what the page has?',
    choices: [C('Yes, the page has it', 'right'), C('The page has something else', 'other', 'What you read on the page (a few words)')],
  },
  add: {
    prompt: 'Is the highlighted word written in his hand as an insertion, above the line or in the margin?',
    choices: [C('Yes, inserted in his hand', 'right'), C('No, it is not on the page', 'other'), C('Something else', 'other', 'What the page has')],
  },
  supplied: {
    prompt: 'Is the highlighted word on the page, inserted in his hand, or did the transcriber supply it?',
    choices: [C('Supplied: it is not on the page', 'right'), C('On the page, in his hand', 'other'), C('Something else', 'other', 'What the page has')],
  },
};
const sampledAsk = (kind, o) => ({
  ...ASK[kind],
  hint: `${facsimileAt([o.page])} and find the quoted words; the highlighted one is the spot to check.`,
});

/** The pages a date not settled on one leaf may stand on. */
function candidates(rec, clause) {
  const ctx = /\bon ((?:\d+, )*\d+ or \d+)/.exec(rec.context ?? '');
  if (ctx) return ctx[1].split(/, | or /).map(Number);
  const or = /pp?\. (\d+) or pp?\. (\d+)/.exec(clause);
  if (or) return [Number(or[1]), Number(or[2])];
  const [a, b] = String(rec.page).split(/[-–]/).map(Number);
  if (b && b > a && b - a <= 12) return Array.from({ length: b - a + 1 }, (_, i) => a + i);
  return [a];
}

/** One item of §3: what to ask about one record, by the kind of doubt #35 names. */
function dateAsk(label, rec, p, clause, pages) {
  const w = rec.written;
  const look = looksLike(rec);
  if (/page not settled/i.test(label)) {
    const cands = candidates(rec, clause);
    if (cands.length > 1)
      return {
        page: cands[0],
        prompt: `On which page is the date « ${w} » written? Look at ${pagesText(cands)}.`,
        choices: [...cands.map((c) => C(`p. ${c}`, 'right')), C('Not on these pages', 'other', 'Where it is, if you found it')],
        hint: `${facsimileAt(cands)} for ${look}.`,
      };
    return {
      page: cands[0],
      prompt: `Is the date « ${w} » written on p. ${cands[0]}?`,
      choices: [C(`Yes, on p. ${cands[0]}`, 'right'), C('On another page', 'other', 'Which page')],
      hint: `${facsimileAt(cands)} and the pages around it for ${look}.`,
    };
  }
  if (/neighbouring leaf/i.test(label))
    return {
      prompt: `Is a year written with the date « ${w} » on p. ${p} (it is dated ${String(rec.iso).slice(0, 4)} from a neighbouring leaf)?`,
      choices: [C('No year on the leaf', 'right'), C('A year is written', 'other', 'The year as written')],
      hint: `${facsimileAt([p])} for ${look}, and for a year anywhere near it.`,
    };
  if (/paraphrased/i.test(label))
    return {
      prompt: `How is the date written on ${pagesText(pages)}? It is recorded, in paraphrase, as « ${w} ».`,
      choices: [C(`Exactly « ${w} »`, 'right'), C('Otherwise', 'other', 'The date exactly as written'), C('No date there', 'other')],
      hint: `${facsimileAt(pages)} for ${look}, and copy it letter for letter.`,
    };
  if (/labels/i.test(label))
    return {
      prompt: `On p. ${p}, is « ${w} » the date the page was written, or a label added to it (a title, a filing mark)?`,
      choices: [C('The date of writing', 'right'), C('A label or title', 'other'), C('Something else', 'other', 'What it is')],
      hint: `${facsimileAt([p])} for « ${w} »${/hand/.test(clause) ? ', and whether it is in his hand' : ''}.`,
    };
  return {
    prompt: `Is the date on p. ${p} « ${w} », meaning ${human(rec.iso)}?`,
    choices: [C('Yes', 'right'), C('No, something else', 'other', 'What the date reads, and what it means')],
    hint: `${facsimileAt([p])} for ${look}; check each figure${/\d+[./-]\d+[./-]\d+/.test(w) ? ', and which is the day and which the month' : ''}.`,
  };
}

const LANGUAGE = { fr: 'French', en: 'English', de: 'German', unknown: 'not stated' };
/** A register entry as the reading to check: who writes, to whom, when, where. */
function entryOf(rec) {
  if (!rec) return null;
  const who = rec.correspondent ?? (rec.correspondentNote ? `unnamed: ${rec.correspondentNote}` : 'unnamed');
  const parties =
    rec.direction === 'from'
      ? [['From', 'Grothendieck'], ['To', who]]
      : rec.direction === 'to'
        ? [['From', who], ['To', 'Grothendieck']]
        : [['Correspondent', who], ['Direction', 'between others, or unclear']];
  return [...parties, ['Date', rec.date ?? 'undated'], ['Place', rec.place ?? 'not given'], ['Form', rec.form], ['Language', LANGUAGE[rec.language] ?? rec.language], ['Pages', String(rec.pages ?? '?')]];
}
const letterPages = (rec, p) => {
  const ps = String(rec?.pages ?? p ?? '');
  if (/,/.test(ps)) return [...ps.matchAll(/\d+/g)].map((x) => Number(x[0]));
  const [a, b] = ps.split(/[-–]/).map(Number);
  return b && b > a ? Array.from({ length: b - a + 1 }, (_, i) => a + i) : a ? [a] : [];
};
const LETTER = {
  prompt: 'Is this a letter, and is the entry right? Check who writes, to whom, the date and the place.',
  choices: [C('Yes, the entry is right', 'right'), C('Not a letter', 'other', 'What it is instead'), C('Something in the entry is wrong', 'other', 'What is wrong: writer, addressee, date or place')],
};
const letterHint = (cote, ps) => (ps.length ? `${facsimileAt(ps)} for the heading, the salutation, the signature, and any date or place.` : `Leaf through the facsimile of folder ${cote} for the heading, the salutation and the signature.`);

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

  // #90 — the hypotheses a counterexample of the edition's is set against: read
  // on the facsimile before the verdict is taken to hold of the page.
  // #90 — pages whose own evidence disagrees with the inventory's dating
  // (src/content/proposed-datings.json): a question for a reader of the hand.
  if (section.startsWith('Datings against the inventory')) {
    const dat = /^\*\*(\d+(?:-\d+)?)(?:,\s*pp?\.\s*([\d–, -]+))?:\*\*\s*(.*)$/.exec(text);
    if (dat && isCote(dat[1])) {
      const ps = (dat[2] ?? '').split(/,\s*/).flatMap((r) => {
        const [a, b] = r.split('–').map(Number);
        return b > a ? Array.from({ length: b - a + 1 }, (_, i) => a + i) : a ? [a] : [];
      });
      push({
        id: `dating-${dat[1]}-p${ps[0] ?? 0}`,
        section: n,
        kind: 'date',
        cote: dat[1],
        page: ps[0] ?? null,
        prompt: `Do these pages of folder ${dat[1]} disagree with the inventory's dating, as the edition reads them?`,
        choices: [C('Yes, the evidence is read right', 'right'), C('No, a date or name is misread', 'other', 'What the page has'), C('The pages are not what the edition says', 'other', 'What they are')],
        hint: `${ps.length ? facsimileAt(ps) : `Leaf through the facsimile of folder ${dat[1]}`}: read the dates, names and citations the box quotes, and the versos.`,
        claim: `${dat[3][0].toUpperCase()}${dat[3].slice(1)}`,
        details: text.replace(/\*\*/g, ''),
        context: 'A dating proposed from the leaves’ own evidence disagrees with the inventory; the inventory is kept, and a confirmed disagreement is recorded beside it (#90).',
      }, null);
      continue;
    }
  }

  // A finding recorded as stated without proof: is an argument written nearby?
  if (section.startsWith('Statements recorded as stated without proof')) {
    const st = /^\*\*(\d+(?:-\d+)?)(?:,\s*pp?\.\s*([\d–, -]+))?:\*\*\s*(.*)$/.exec(text);
    if (st && isCote(st[1])) {
      const ps = (st[2] ?? '').split(/,\s*/).flatMap((r) => {
        const [a, b] = r.split('–').map(Number);
        return b > a ? Array.from({ length: b - a + 1 }, (_, i) => a + i) : a ? [a] : [];
      });
      const fid = /\(finding `([^`]+)`\)/.exec(st[3])?.[1];
      push({
        id: `unproved-${fid ?? `${st[1]}-p${ps[0] ?? 0}`}`,
        section: n,
        kind: 'unproved',
        cote: st[1],
        page: ps[0] ?? null,
        prompt: `Is an argument for this statement of folder ${st[1]} written on the leaves?`,
        choices: [C('No, it is only stated', 'right'), C('Yes, an argument or a sketch', 'other', 'Where: page, verso or margin'), C('A special case only', 'other', 'Which case, and where')],
        hint: `${ps.length ? facsimileAt(ps) : `Leaf through the facsimile of folder ${st[1]}`}, and at the leaves just after, the versos and the margins.`,
        claim: `${st[3][0].toUpperCase()}${st[3].slice(1)}`.replace(/\s*\(finding `[^`]+`\)\.?$/, '.'),
        details: text.replace(/\*\*/g, ''),
        context: 'The finding is recorded as stated without proof; an argument on the leaves would make it partly proved (2026-10-26).',
      }, null);
      continue;
    }
  }

  // A finding too imprecise to state: what the leaves can still fix.
  if (section.startsWith('Statements too imprecise')) {
    const imp = /^\*\*(\d+(?:-\d+)?)(?:,\s*pp?\.\s*([\d–, -]+))?:\*\*\s*(.*)$/.exec(text);
    if (imp && isCote(imp[1])) {
      const ps = (imp[2] ?? '').split(/,\s*/).flatMap((r) => {
        const [a, b] = r.split('–').map(Number);
        return b > a ? Array.from({ length: b - a + 1 }, (_, i) => a + i) : a ? [a] : [];
      });
      push({
        id: `imprecise-${imp[1]}-p${ps[0] ?? 0}`,
        section: n,
        kind: 'imprecise',
        cote: imp[1],
        page: ps[0] ?? null,
        prompt: `Can the leaves of folder ${imp[1]} fix what the reading left open?`,
        choices: [C('Yes, here is what the page has', 'other', 'The words, the count or the leaves'), C('The page is as the reading says', 'right'), C('The page cannot settle it', 'illegible')],
        hint: `${ps.length ? facsimileAt(ps) : `Leaf through the facsimile of folder ${imp[1]}`}: read or count what the box names.`,
        claim: `${imp[3][0].toUpperCase()}${imp[3].slice(1)}`,
        details: text.replace(/\*\*/g, ''),
        context: 'A finding stays too imprecise to search or formalise until these leaves are read (2026-10-26).',
      }, null);
      continue;
    }
  }

  if (section.startsWith('Hypotheses behind')) {
    const hyp = /^\*\*(\d+(?:-\d+)?)(?:,\s*pp?\.\s*([\d–, -]+))?:\*\*\s*(.*)$/.exec(text);
    if (hyp && isCote(hyp[1])) {
      // « 3–5 » is the range 3, 4, 5; « 35, 37 » the two pages.
      const ps = (hyp[2] ?? '').split(/,\s*/).flatMap((r) => {
        const [a, b] = r.split('–').map(Number);
        return b > a ? Array.from({ length: b - a + 1 }, (_, i) => a + i) : a ? [a] : [];
      });
      push({
        id: `hypothesis-${hyp[1]}-p${ps[0] ?? 0}`,
        section: n,
        kind: 'hypothesis',
        cote: hyp[1],
        page: ps[0] ?? null,
        prompt: `Is this statement of folder ${hyp[1]} written on the page with exactly these hypotheses?`,
        choices: [C('Yes, read as on the page', 'right'), C('A hypothesis is missing from the reading', 'other', 'Which, and where on the page'), C('A word is misread', 'other', 'Which word, and what the page has')],
        hint: `${ps.length ? facsimileAt(ps) : `Leaf through the facsimile of folder ${hyp[1]}`}: read the statement, the lines just before it and the margins.`,
        claim: `${hyp[3][0].toUpperCase()}${hyp[3].slice(1)}`,
        details: text.replace(/\*\*/g, ''),
        context: 'A finding’s verdict on this statement rests on a counterexample of the edition’s own, which a misread hypothesis would make beside the point (#90).',
      }, null);
      continue;
    }
  }

  // §1 — the unread words of the densest batches.
  if (!fromMoved && sub.startsWith('1.')) {
    const cote = /^(\S+)/.exec(text)[1];
    // « 58 batch 1 — 689 · batch 2 — 570 — sampled …: batch 1 p. 4 … »: the
    // batches are those given with their count, once each.
    for (const batch of new Set([...text.matchAll(/batch (\d+) — \d/g)].map((m) => Number(m[1])))) {
      for (const o of sampleOf(`ill-${cote}-${batch}`, occurrences(cote, batch, (t) => t.k === 'ill'), SAMPLES.ill))
        push({ id: `ill-${cote}-${batch}-p${o.page}`, section: n, kind: 'ill', cote, batch, page: o.page, ...sampledAsk('ill', o), context: `One of the densest batches for unread words (#35 §1).` }, o.snippet);
      for (const o of sampleOf(`unc-${cote}-${batch}`, occurrences(cote, batch, (t) => t.k === 'unc' && t.s.split(' ').length <= 3 && t.s.length > 1), SAMPLES.uncertain))
        push({ id: `unc-${cote}-${batch}-p${o.page}`, section: n, kind: 'uncertain', cote, batch, page: o.page, ...sampledAsk('uncertain', o), context: `Doubtful readings in the same batch (#35 §1).` }, o.snippet);
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
      push({ id: `${kind}-${o.cote}-${o.batch}-p${o.page}`, section: n, kind, cote: o.cote, batch: o.batch, page: o.page, ...sampledAsk(kind, o), context: kind === 'add' ? 'A free-standing \\add{} that may be a supply (#35 §2).' : 'A glued \\supplied{} that may be his insertion (#35 §2).' }, o.snippet);
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
    const Label = `${label[0].toUpperCase()}${label.slice(1)}`;
    // One item per record: a clause naming several dates gives several items.
    const dateItem = (cote, rec, clause, pages, split) => {
      const p0 = pages[0] ?? firstPage(rec);
      const ask = dateAsk(label, rec, p0, clause, pages.length ? pages : [p0]);
      const p = ask.page ?? p0;
      const b = rec.batch ?? (p ? batchOf(p) : 1);
      const s = snippetAt(cote, b, { line: Number(rec.where.split(':')[1]) || null, page: p, needle: rec.written });
      push({ id: dateId(cote, rec, p, split), section: n, kind: 'date', cote, batch: b, page: p, prompt: ask.prompt, hint: ask.hint, choices: ask.choices, details: `${Label}: ${clause.trim()}`, context: `Recorded as « ${rec.written} » (${rec.hand}, ${rec.kind}${rec.iso ? `, ${rec.iso}` : ''}).` }, s?.snippet ?? null);
    };
    for (const clause of m[3].split(/;\s*/)) {
      const lead = /^(\d+(?:-\d+)?)\b(.*)$/.exec(clause.trim());
      if (lead && isCote(lead[1])) {
        const cote = lead[1];
        const rest = lead[2];
        const batch = Number(/batch (\d+)/.exec(rest)?.[1]) || null;
        const many = /batches (\d+)[–-](\d+)/.exec(rest);
        const pages = many ? [] : [...(/pp?\. ([\d, –]+)/.exec(rest)?.[1] ?? '').matchAll(/\d+/g)].map((x) => Number(x[0]));
        const page = pages[0] ?? null;
        const quote = /«\s*([^»]+?)\s*»/.exec(rest)?.[1] ?? null;
        const norm = (x) => x.replace(/\s+/g, '').toLowerCase();
        let recs;
        if (many)
          // « 154 batches 5–9 »: a few of the dates in those batches given in words.
          recs = spread(leaves.filter((r) => r.folder === cote && r.batch >= Number(many[1]) && r.batch <= Number(many[2]) && !/[-–]/.test(String(r.page)) && /[A-Z][a-z]+ \d{4}/.test(r.written)), 3);
        else if (/page not settled/i.test(label) && batch && !quote) recs = leaves.filter((r) => r.folder === cote && r.batch === batch && /[-–]/.test(String(r.page)));
        else
          recs = [
            leaves.find((r) => r.folder === cote && quote && norm(r.written).includes(norm(quote).slice(0, 8))) ??
              leaves.find((r) => r.folder === cote && page && firstPage(r) === page) ??
              (batch ? leaves.find((r) => r.folder === cote && r.batch === batch) : null) ??
              (!page && !batch ? leaves.find((r) => r.folder === cote) : null),
          ].filter(Boolean);
        if (!recs.length) skipped.push(`${label}: ${clause}`);
        for (const rec of recs) dateItem(cote, rec, clause, many ? [] : pages, recs.length > 1 && !many);
        continue;
      }
      // « the day-only dates of 154 (24.12, 25.12), 67 (…) » — cotes named in passing.
      const cotes = [...clause.replace(/\([^)]*\)/g, '').replace(/«[^»]*»/g, '').matchAll(/(?<![.\d])(\d{1,3}(?:-\d)?)(?![.\d])/g)].map((x) => x[1]).filter(isCote);
      if (!cotes.length) {
        skipped.push(`${label}: ${clause}`);
        continue;
      }
      for (const cote of new Set(cotes)) {
        const borrowed = leaves.filter((r) => r.folder === cote && /year from (a )?neighbouring leaf/.test(r.context ?? ''));
        for (const rec of borrowed.length ? borrowed : leaves.filter((r) => r.folder === cote).slice(0, 1)) dateItem(cote, rec, clause, []);
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
        const ask = rec
          ? LETTER
          : {
              prompt: 'Is this a letter? If so, note who writes, to whom, the date and the place.',
              choices: [C('Yes, a letter', 'other', 'Who writes, to whom, the date and the place'), C('Not a letter', 'other', 'What it is instead')],
            };
        push({ id: `letter-${cote}-p${p ?? b}`, section: n, kind: 'letter', cote, batch: b, page: p, ...ask, hint: letterHint(cote, letterPages(rec, p)), entry: entryOf(rec), details: `${part.trim()} — ${m[2]}`, context: null }, s?.snippet ?? null);
      }
      continue;
    }
    const named = [...text.matchAll(/\*\*(\d+(?:-\d+)?)\*\*\s*«\s*([^»]+?)\s*»/g)];
    if (named.length) {
      for (const [, cote, what] of named)
        push({
          id: `letter-${cote}-missing`,
          section: n,
          kind: 'letter',
          cote,
          batch: 1,
          page: null,
          prompt: `Is there a letter in folder ${cote} (the inventory lists « ${what} »), and on which page?`,
          choices: [C('Yes, I found it', 'other', 'The page, and who writes to whom'), C('No letter in the folder', 'right')],
          hint: `Leaf through the facsimile of folder ${cote} for a page with a salutation, a signature or an envelope; the transcriptions found none.`,
          details: `The inventory lists « ${what} » in folder ${cote}, and the transcriptions found no such letter.`,
        }, null);
      continue;
    }
    if (/unnamed as a private person/.test(text)) {
      for (const rec of letters.filter((r) => !r.correspondent)) {
        const wl = Number(rec.where.split(':')[1]);
        const ls = lines(rec.folder, rec.batch);
        const p = Number(String(rec.pages).split(/[-–]/)[0]) || (ls && wl ? pagesOf(ls)[wl - 1] : null) || null;
        push({
          id: `letter-${rec.folder}-p${p}`,
          section: n,
          kind: 'letter',
          cote: rec.folder,
          batch: rec.batch,
          page: p,
          prompt: 'Is the unnamed correspondent of this letter a public figure (a mathematician, an official), who should then be named?',
          choices: [C('A private person: leave unnamed', 'right'), C('A public figure', 'other', 'Who, and in what role')],
          hint: `${letterHint(rec.folder, letterPages(rec, p))} A letterhead or a title under the signature can tell.`,
          entry: entryOf(rec),
          details: text,
        }, null);
      }
      continue;
    }
    skipped.push(text);
    continue;
  }

  // #48 §2 — the edition's own arguments and the references cited from memory:
  // questions for a mathematician, not for a reader of the hand.
  if (fromMoved && sub.startsWith('2.')) {
    const arg = /^\*\*(\d+(?:-\d+)?)(?:,\s*pp?\.\s*([\d–, -]+))?:\*\*\s*(.*)$/.exec(text);
    if (arg && isCote(arg[1])) {
      const page = Number(/\d+/.exec(arg[2] ?? '')?.[0]) || null;
      const ps = arg[2]?.trim();
      const at = ps ? ` at ${/–/.test(ps) ? `pp. ${ps}` : pagesText([...ps.matchAll(/\d+/g)].map((x) => Number(x[0])))}` : '';
      push({
        id: `argument-${arg[1]}-p${page ?? 0}`,
        section: n,
        kind: 'argument',
        cote: arg[1],
        page,
        edition: 'modern',
        prompt: `Does this argument, given in a footnote of the modernised reading of folder ${arg[1]}${at}, hold?`,
        choices: [C('It holds', 'right'), C('It does not hold', 'other', 'What fails, in a few words')],
        hint: `Open the modernised reading of folder ${arg[1]}${at} and read the footnote; the facsimile shows what his page itself says.`,
        claim: `${arg[3][0].toUpperCase()}${arg[3].slice(1)}`,
        details: text.replace(/\*\*/g, ''),
        context: `A footnote of the modernised reading gives an argument of the edition's own, unchecked (#48 → #35).`,
      }, null);
      continue;
    }
    const refs = /\(([\d, ]+)\)\s*$/.exec(text);
    if (refs) {
      const cotes = refs[1].split(/,\s*/).filter(isCote);
      if (cotes.length) {
        push({
          id: `reference-${cotes.join('-')}`,
          section: n,
          kind: 'reference',
          cote: cotes[0],
          page: null,
          edition: 'modern',
          prompt: 'Are these references right: author, title, year, and the place in the work they are cited for?',
          choices: [C('They are right', 'right'), C('One is not right', 'other', 'Which one, and what is wrong')],
          hint: `The footnotes of the modernised reading${cotes.length > 1 ? 's' : ''} of ${cotes.join(', ')} cite them from memory; check each against the work itself.`,
          claim: text.replace(/\s*\([\d, ]+\)\s*$/, ''),
          details: `References cited from memory in the modernised readings of ${cotes.join(', ')} (#48 → #35).`,
        }, null);
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
