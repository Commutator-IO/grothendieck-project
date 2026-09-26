#!/usr/bin/env node
/**
 * Exports each transcription to TEI P5, mechanically, from its `.tex`.
 *
 *   npm run tei                  every transcription
 *   npm run tei -- 19            one folder
 *
 * Why a second serialisation of the same file. The `.tex` is the source of
 * record and stays so: it is what gets corrected and compiled, and this script
 * reads nothing else — not the facsimile, not the HTML. But LaTeX with eight
 * private macros is legible only to this repository. TEI is what an archive,
 * a library deposit (HAL, Nakala) or another editor can take in without our
 * rendering chain, and its header carries what our header comment carries —
 * which model read the pages, on what date, under what legal status — in a
 * form a machine can read. A transcription that can be cited only through
 * this site is a transcription that dies with it.
 *
 * The mapping is one-to-one with the apparatus, and no richer:
 *
 *   \page{47}          <pb n="47" facs="…#page=48"/>   archivists' number; the
 *                                                     PDF page is one ahead
 *   \ill{}             <gap reason="illegible"/>
 *   \uncertain{x}      <unclear>x</unclear>
 *   \supplied{x}       <supplied resp="#pass">x</supplied>   the transcriber's
 *   \add{x}            <add>x</add>                        Grothendieck's own
 *   \struck{x}         <del>x</del>
 *   \note{x}           <note type="editorial" resp="#pass">x</note>
 *   \marginal{x}       <note type="authorial" place="margin">x</note>
 *   $…$  \[…\]  envs   <formula notation="TeX">…</formula>, display marked
 *   tikzcd             <figure type="diagram"><formula notation="tikz-cd">
 *
 * The transcription chose not to be a diplomatic edition, and the export
 * holds that line: it encodes what the macros encode and nothing about the
 * paper. Mathematics is carried as TeX inside <formula>, untouched — TEI does
 * not try to encode it, and an apparatus mark *inside* a formula (an illegible
 * exponent) stays inside the TeX, where KaTeX and the PDF both read it.
 *
 * Same discipline as scripts/render.mjs: the subset is the documented one,
 * and anything outside it is refused: an unknown environment, a control
 * sequence that would stand in the TEI as literal text, a pass record in the
 * header that cannot be read. A refused file is reported and the run exits
 * non-zero, so the deploy stops. Output goes to public/transcripts/, derived
 * and unversioned like the HTML and the PDF.
 *
 * Every file names the schema it is written against — the RELAX NG derived
 * from tei/grothendieck.odd, in an <?xml-model?> — and the ODD itself, in
 * <schemaRef>. The ODD declares exactly the elements this script emits, and
 * scripts/tei-validate.mjs (`npm run tei:validate`) holds every file to it
 * and to unmodified tei_all on every deploy. xmllint, where it exists, checks
 * well-formedness here as the files are written.
 */

import { copyFile, mkdir, readdir, readFile, writeFile } from 'node:fs/promises';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { resolve, basename } from 'node:path';
import { ODD_URL, RNG_URL } from './tei-validate.mjs';

const exec = promisify(execFile);

const ROOT = resolve(import.meta.dirname, '..');
const SOURCE = resolve(ROOT, 'transcripts');
const OUT = resolve(ROOT, 'public', 'transcripts');
const MONTPELLIER = 'https://grothendieck.umontpellier.fr';
const SITE = 'https://grothendieck.commutator.io';
const REPO = 'https://github.com/Commutator-IO/grothendieck-project';
const TEI_NS = 'http://www.tei-c.org/ns/1.0';
// The customisation every file is written against, and its derived schema:
// tei/grothendieck.odd, published under /tei/ and checked by
// scripts/tei-validate.mjs, which writes the schema.
const ODD_SOURCE = resolve(ROOT, 'tei', 'grothendieck.odd');

// ---------------------------------------------------------------------------
// Lifting math out and putting it back, as the renderer does.

const escapeXml = (s) =>
  s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
const escapeAttr = (s) => escapeXml(s).replace(/"/g, '&quot;');

// A private-use codepoint delimits the marker, for the reasons render.mjs
// gives: it cannot occur in a transcription, and if it ever leaked it would
// show as a missing glyph rather than hide.
const marker = (i) => `\ue000MATH${i}\ue000`;
const MARKED = () => /\ue000MATH(\d+)\ue000/g;

/**
 * Ends a block after every heading's closing brace \u2014 the same function as in
 * scripts/render.mjs, which says why: a `\note{}` on the line under a
 * `\section{}` used to fall inside the heading. The two must cut blocks
 * identically, or check-tei reports the difference.
 */
function isolateHeadings(text) {
  const re = /\\(?:sub)?section\*?\{/g;
  let out = '';
  let from = 0;
  let m;
  while ((m = re.exec(text))) {
    let depth = 1;
    let i = m.index + m[0].length;
    for (; i < text.length && depth; i++) {
      if (text[i] === '\\') i++;
      else if (text[i] === '{') depth++;
      else if (text[i] === '}') depth--;
    }
    out += `${text.slice(from, m.index)}\n\n${text.slice(m.index, i)}\n\n`;
    from = i;
    re.lastIndex = i;
  }
  return out + text.slice(from);
}

function liftMath(tex) {
  const held = [];
  const keep = (raw, display) => {
    held.push({ raw, display });
    return marker(held.length - 1);
  };
  const out = tex
    .replace(/\\begin\{tikzcd\}[\s\S]*?\\end\{tikzcd\}/g, (m) => keep(m, 'diagram'))
    .replace(
      /\\begin\{(equation\*?|align\*?|gather\*?|cases|matrix|pmatrix|bmatrix|array|aligned)\}[\s\S]*?\\end\{\1\}/g,
      (m) => keep(m, true),
    )
    .replace(/\\\[([\s\S]*?)\\\]/g, (_, m) => keep(m, true))
    .replace(/\$\$([\s\S]*?)\$\$/g, (_, m) => keep(m, true))
    .replace(/\\\(([\s\S]*?)\\\)/g, (_, m) => keep(m, false))
    .replace(/(?<!\\)\$((?:[^$\\]|\\.)+)\$/g, (_, m) => keep(m, false));
  return { text: out, held };
}

function dropMathBack(xml, held) {
  // Nesting points backwards (an inner environment is lifted, and numbered,
  // before the display that contains it), so the recursion ends.
  const expand = (raw) => raw.replace(MARKED(), (_, i) => expand(held[Number(i)].raw));
  return xml.replace(MARKED(), (_, i) => {
    const { raw, display } = held[Number(i)];
    const body = escapeXml(expand(raw).trim());
    if (display === 'diagram') {
      return `<figure type="diagram"><formula notation="tikz-cd">${body}</formula></figure>`;
    }
    return display
      ? `<formula notation="TeX" rend="display">${body}</formula>`
      : `<formula notation="TeX">${body}</formula>`;
  });
}

// ---------------------------------------------------------------------------
// Inline text.

/**
 * Macros taking one argument, matched by brace counting: a note about
 * mathematics contains mathematics, and a regex stopping at the first `}`
 * would cut it in half.
 */
const BRACED = [
  ['uncertain', (a) => `<unclear>${a}</unclear>`],
  ['supplied', (a) => `<supplied resp="#pass">${a}</supplied>`],
  ['add', (a) => `<add>${a}</add>`],
  ['struck', (a) => `<del>${a}</del>`],
  ['note', (a) => `<note type="editorial" resp="#pass">${a}</note>`],
  ['marginal', (a) => `<note type="authorial" place="margin">${a}</note>`],
  ['emph', (a) => `<hi rend="italic">${a}</hi>`],
  ['textit', (a) => `<hi rend="italic">${a}</hi>`],
  ['textbf', (a) => `<hi rend="bold">${a}</hi>`],
  ['texttt', (a) => `<hi rend="monospace">${a}</hi>`],
  ['textsuperscript', (a) => `<hi rend="sup">${a}</hi>`],
  // Not \keywords, \underline or the resume environment. The first and last
  // belong to the modernised readings, which this script does not export; an
  // \underline in prose is a slip (it is legitimate only inside mathematics,
  // under an apparatus macro, where it stays in the TeX). Mapping them made
  // the export able to emit <seg>, <div type="summary"> and <hi
  // rend="underline">, which no batch does and tei/grothendieck.odd does not
  // declare; unmapped, each is refused if it ever turns up.
  ['selectlanguage', () => ''],
];

function expandBraced(text) {
  let out = text;
  for (const [name, wrap] of BRACED) {
    const open = `\\${name}{`;
    let i;
    while ((i = out.indexOf(open)) !== -1) {
      let depth = 0;
      let j = i + open.length - 1;
      for (; j < out.length; j++) {
        if (out[j] === '{') depth++;
        else if (out[j] === '}' && --depth === 0) break;
      }
      const arg = out.slice(i + open.length, j);
      out = out.slice(0, i) + wrap(arg) + out.slice(j + 1);
    }
  }
  return out;
}

/** Inline macros with no argument, applied to already-escaped text. */
const INLINE = [
  [/\\ill\{\}|\\ill(?![a-zA-Z])/g, '<gap reason="illegible"/>'],
  [/\\l?dots(\{\})?/g, '…'],
  [/\\og\{?\}?\s*/g, '« '],
  [/\s*\\fg\{?\}?/g, ' »'],
  [/\\guillemotleft\{?\}?\s*/g, '« '],
  [/\s*\\guillemotright\{?\}?/g, ' »'],
  [/\\textbar(\{\})?/g, '|'],
  // A horizontal rule in the running text is his blank or ditto line —
  // « C′ ——— quadruples » — and reads as a dash.
  [/\\rule\{[^{}]*\}\{[^{}]*\}/g, '—'],
  // Vertical spacing and paragraph control: layout, not content.
  [/\\(?:medskip|smallskip|bigskip|noindent|par|newpage|clearpage)(?![a-zA-Z])(\{\})?/g, ''],
  // An explicit line break in prose. Must come before the control-space rule,
  // whose class would otherwise take the second backslash for a control space.
  [/\\\\(\[[^\]]*\])?/g, '<lb/>'],
  [/\\[ ,;:!]/g, ' '],
  [/(?<!\\)\\(?=\r?\n)/g, ' '],
  [/\\q?quad(\{\})?/g, '  '],
  [/\\%/g, '%'],
  [/\\&amp;/g, '&amp;'],
  [/\\_/g, '_'],
  [/\\#/g, '#'],
  [/\\\{/g, '{'],
  [/\\\}/g, '}'],
  [/---/g, '—'],
  [/--/g, '–'],
  [/~/g, ' '],
];

/** Reads a leading `[...]` off an \item body, matching brackets. */
function takeBracketed(text) {
  if (text[0] !== '[') return null;
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    if (text[i] === '[') depth++;
    else if (text[i] === ']') {
      depth--;
      if (depth === 0) return { arg: text.slice(1, i), rest: text.slice(i + 1) };
    }
  }
  return null;
}

function makeInline(unknown) {
  return function inline(text) {
    let out = expandBraced(escapeXml(text));
    for (const [re, to] of INLINE) out = out.replace(re, to);
    // Whatever control sequence is still standing was not in the subset.
    // Collected for the whole file, so that main() can name every one of them
    // in a single refusal rather than stop at the first.
    for (const m of out.matchAll(/\\([a-zA-Z]+)/g)) unknown.add(m[1]);
    return out.trim();
  };
}

// ---------------------------------------------------------------------------
// Environments and blocks.

/**
 * Lifts block environments out whole, matching begin to end by depth.
 *
 * A non-greedy regex stops at the first `\end{itemize}`, which for a list
 * nested in a list is the inner one — the outer list's tail then leaks into
 * the surrounding paragraph as raw `\item` text. Folders 44, 161-2 and 161-3
 * all nest an enumeration inside an item, so the environments are scanned
 * with a counter instead, and lists render recursively.
 */
function liftEnvs(text) {
  const kept = [];
  let out = '';
  let i = 0;
  const openRe = /\\begin\{(itemize|enumerate|quote)\}/g;
  for (;;) {
    openRe.lastIndex = i;
    const m = openRe.exec(text);
    if (!m) {
      out += text.slice(i);
      break;
    }
    out += text.slice(i, m.index);
    // Scan forward for the matching \end, counting every block environment.
    const tok = /\\(begin|end)\{(itemize|enumerate|quote)\}/g;
    tok.lastIndex = m.index + m[0].length;
    let depth = 1;
    let end = -1;
    let t;
    while ((t = tok.exec(text))) {
      depth += t[1] === 'begin' ? 1 : -1;
      if (depth === 0) {
        end = t.index + t[0].length;
        break;
      }
    }
    if (end === -1) throw new Error(`unclosed \\begin{${m[1]}}`);
    kept.push(text.slice(m.index, end));
    out += `\n\nENVBLOCK${kept.length - 1}\n\n`;
    i = end;
  }
  return { text: out, kept };
}

/** Splits a list body on the `\item`s at its own depth only. */
function splitItems(body) {
  const items = [];
  let depth = 0;
  let cur = null;
  const tok = /\\(begin|end)\{(itemize|enumerate|quote)\}|\\item(?![a-zA-Z])/g;
  let t;
  while ((t = tok.exec(body))) {
    if (t[1] === 'begin') depth++;
    else if (t[1] === 'end') depth--;
    else if (depth === 0) {
      if (cur !== null) items.push(body.slice(cur, t.index));
      cur = t.index + t[0].length;
    }
  }
  if (cur !== null) items.push(body.slice(cur));
  return items;
}

/**
 * The models that have read pages of the fonds, by the name the headers give
 * them. A revision line of the short form — `% Revised 2026-09-23 (Opus 5.5)`
 * — names the model without its identifier, and the identifier is taken from
 * here; a model not listed is refused, not guessed.
 */
const MODELS = {
  'Fable 5': 'claude-fable-5',
  'Fable 5.1': 'claude-fable-5-1',
  'Opus 5': 'claude-opus-5',
  'Opus 5.5': 'claude-opus-5-5',
};

/**
 * Every pass the header comment records: the first, and each revision since.
 *
 * The first pass is one line, `% Pass: Opus 5.5 (claude-opus-5-5), 2026-09-22
 * — first pass, …`. A revision is a line in one of two forms, the long one
 * like the pass line (`% Revised: Opus 5.5 (claude-opus-5-5), 2026-09-22 — …`
 * or `% Revision: …`) and the short one most revisions were written in
 * (`% Revised 2026-09-23 (Opus 5.5), after the find-novelty pass: …`). What
 * the revision did is the rest of that line and of the comment paragraph it
 * opens, up to a blank comment line or the next record.
 *
 * The export used to read the first `% Pass:` line and nothing else, so a
 * file revised three times said it had been read once. And a record this
 * cannot read is refused rather than skipped: any comment line opening on
 * `Pass:`, `Revised` or `Revision` is a record, and a record the TEI header
 * silently drops is the failure this function exists to end.
 */
function readPasses(tex) {
  const head = tex.slice(0, tex.indexOf('\\begin{document}')).split('\n');
  const ids = { ...MODELS };
  const LONG = /^%\s*(Pass|Revised|Revision):\s*([^(\n]+?)\s*\(([^)\n]+)\)\s*,\s*(\d{4}-\d{2}-\d{2})\s*(?:—\s*)?(.*)$/;
  const SHORT = /^%\s*Revised\s+(\d{4}-\d{2}-\d{2})\s*\(([^)\n]+)\)\s*[,:.]?\s*(.*)$/;
  const RECORD = /^%\s*(Pass:|Revised\b|Revision\b)/;
  const records = [];
  for (let i = 0; i < head.length; i++) {
    if (!RECORD.test(head[i])) continue;
    let rec;
    const long = LONG.exec(head[i]);
    const short = !long && SHORT.exec(head[i]);
    if (long) {
      const [, kind, model, id, date, text] = long;
      if (ids[model] && ids[model] !== id) {
        throw new Error(`header line ${i + 1}: ${model} is ${ids[model]}, not ${id}`);
      }
      ids[model] = id;
      rec = { first: kind === 'Pass', model, id, date, text: [text] };
    } else if (short) {
      const [, date, model, text] = short;
      rec = { first: false, model, id: null, date, text: [text] };
    } else {
      throw new Error(
        `header line ${i + 1} is a pass record the export cannot read:\n    ${head[i].slice(0, 100)}\n` +
          '  write it as « % Revised: <model> (<id>), <YYYY-MM-DD> — <what changed> » ' +
          '(or % Pass: in the same form, for the first pass)',
      );
    }
    for (let j = i + 1; j < head.length && /^%\s*\S/.test(head[j]) && !RECORD.test(head[j]); j++) {
      rec.text.push(head[j].replace(/^%\s*/, ''));
    }
    records.push(rec);
  }
  for (const r of records) {
    r.id ??= ids[r.model];
    if (!r.id) throw new Error(`a revision names ${r.model}, which is not a model the export knows (MODELS in scripts/tei.mjs)`);
    r.text = r.text.join(' ').replace(/\s+/g, ' ').trim();
  }
  const firsts = records.filter((r) => r.first);
  if (firsts.length > 1) throw new Error(`${firsts.length} % Pass: lines — a file has one first pass`);
  return { pass: firsts[0] ?? null, revisions: records.filter((r) => !r.first) };
}

function readMeta(tex) {
  const one = (name) => new RegExp(`\\\\${name}\\{([^{}]*)\\}`).exec(tex)?.[1] ?? '';
  const pages = /\\pages\{(\d+)\}\{(\d+)\}/.exec(tex);
  // The header comment names the passes. It is the only place the models are
  // recorded, which is why the export copies them into a structured header.
  const { pass, revisions } = readPasses(tex);
  return {
    folder: one('folder'),
    batch: one('batch'),
    title: one('foldertitle'),
    dating: one('dating'),
    watermark: one('watermark').replace(/\\\\/g, ' — '),
    first: pages?.[1] ?? '',
    last: pages?.[2] ?? '',
    model: pass?.model ?? '',
    modelId: pass?.id ?? '',
    passDate: pass?.date ?? '',
    revisions,
  };
}

function convert(tex) {
  const body = /\\begin\{document\}([\s\S]*)\\end\{document\}/.exec(tex);
  if (!body) throw new Error('no \\begin{document} … \\end{document}');
  const meta = readMeta(tex);
  const unknown = new Set();
  const inline = makeInline(unknown);

  const { text, held } = liftMath(body[1]);
  const stripped = text.replace(/(?<!\\)%.*$/gm, '');

  const pbFor = (n) =>
    `<pb n="${n}" facs="${MONTPELLIER}/${escapeAttr(meta.folder)}.pdf#page=${Number(n) + 1}"/>`;

  /** One environment block, already known to be a block environment. */
  function renderEnv(block) {
    const list = /^\\begin\{(itemize|enumerate)\}([\s\S]*)\\end\{\1\}$/.exec(block);
    if (list) {
      const items = splitItems(list[2])
        .map((raw) => {
          const bodyText = raw.trim();
          const label = takeBracketed(bodyText);
          if (!label) return `<item>${renderItem(bodyText)}</item>`;
          // His own numbering, where a list carries one, goes in a <label>
          // before the item — TEI's shape for a list whose marks are content.
          // `\item[{[1]}]` braces the label to protect its brackets; the
          // braces are TeX's, not his.
          const lab = label.arg.replace(/^\{([\s\S]*)\}$/, '$1');
          return `<label>${inline(lab)}</label><item>${renderItem(label.rest)}</item>`;
        })
        .join('\n');
      return `<list rend="${list[1]}">\n${items}\n</list>`;
    }
    const quote = /^\\begin\{quote\}([\s\S]*)\\end\{quote\}$/.exec(block);
    if (quote) return `<quote>${renderItem(quote[1])}</quote>`;
    throw new Error(`unexpected environment block: ${block.slice(0, 40)}`);
  }

  /**
   * An item's body: mixed content when it is one run of text, paragraphs and
   * nested lists when it is more. TEI allows both inside <item>.
   */
  function renderItem(raw) {
    const parts = renderBlocks(raw, false, true);
    return parts.join('\n');
  }

  /**
   * Cuts text into blocks and renders each. `top` allows sections; `mixed`
   * leaves a lone text block unwrapped (for item and quote bodies).
   */
  function renderBlocks(src, top, mixed = false) {
    const { text: lifted, kept } = liftEnvs(src);
    const blocks = isolateHeadings(lifted)
      // A page marker always starts a block, even mid-paragraph: a page turns
      // where the paper turns, not where the argument does.
      .replace(/\\page\{/g, '\n\n\\page{')
      .split(/\n\s*\n+/)
      .map((b) => b.trim())
      .filter(Boolean);

    const single = mixed && blocks.length === 1 && !/^ENVBLOCK\d+$/.test(blocks[0]);
    const out = [];
    let depth = 0;
    const closeTo = (d) => {
      while (depth > d) {
        out.push('</div>');
        depth--;
      }
    };

    for (let block of blocks) {
      let pb = '';
      const page = /^\\page\{(\d+)\}\s*/.exec(block);
      if (page) {
        pb = pbFor(page[1]);
        block = block.slice(page[0].length);
      }
      if (!block.trim()) {
        if (pb) out.push(pb);
        continue;
      }

      const env = /^ENVBLOCK(\d+)$/.exec(block);
      if (env) {
        out.push(pb + renderEnv(kept[Number(env[1])].trim()));
        continue;
      }

      const section = top && /^\\(sub)?section\*?\{([\s\S]*)\}$/.exec(block);
      if (section) {
        const d = section[1] ? 2 : 1;
        closeTo(d - 1);
        // A subsection with no enclosing section still needs its parent depth.
        while (depth < d - 1) {
          out.push('<div>');
          depth++;
        }
        out.push(`<div type="${section[1] ? 'subsection' : 'section'}">`);
        depth++;
        out.push(`${pb}<head>${inline(section[2])}</head>`);
        continue;
      }

      // An environment that was not lifted is one the subset does not know.
      const stray = /\\begin\{([a-z*]+)\}/.exec(block);
      if (stray) {
        throw new Error(
          `unsupported environment \\begin{${stray[1]}} — extend scripts/tei.mjs, ` +
            'or keep the transcription inside the documented subset',
        );
      }

      out.push(single ? pb + inline(block) : `${pb}<p>${inline(block)}</p>`);
    }
    closeTo(0);
    return out;
  }

  const xmlBody = dropMathBack(renderBlocks(stripped, true).join('\n'), held);
  return { xml: document(meta, xmlBody), meta, unknown };
}

// ---------------------------------------------------------------------------
// The header, and the document around the body.

function document(meta, body) {
  const t = (s) => escapeXml(s);
  const today = new Date().toISOString().slice(0, 10);
  const title = `Fonds Grothendieck, cote n° ${meta.folder}, pages ${meta.first}–${meta.last} — transcription`;
  const modelLine = meta.model
    ? `<name xml:id="pass" type="model">${t(meta.model)}${meta.modelId ? ` (${t(meta.modelId)})` : ''}</name>`
    : `<name xml:id="pass" type="model">modèle non enregistré dans l'en-tête</name>`;

  // Each revision points at the model that made it: #pass when it is the
  // model of the first pass, and otherwise a name of its own, declared once
  // per model in a respStmt of its own.
  const who = (r) => (r.id === meta.modelId ? '#pass' : `#rev-${r.id}`);
  const dates = (rs) => rs.map((r) => `<date when="${t(r.date)}">${t(r.date)}</date>`).join(', ');
  const byPass = meta.revisions.filter((r) => who(r) === '#pass');
  const others = [...new Map(meta.revisions.filter((r) => who(r) !== '#pass').map((r) => [r.id, r])).values()];
  const reviserLines = others
    .map((m) => {
      const theirs = meta.revisions.filter((r) => r.id === m.id);
      return `
        <respStmt>
          <resp>révision automatique, non vérifiée contre les pages par une personne (${dates(theirs)})</resp>
          <name xml:id="rev-${t(m.id)}" type="model">${t(m.model)} (${t(m.id)})</name>
        </respStmt>`;
    })
    .join('');
  // Most recent first, as the Guidelines ask of revisionDesc. A revision's
  // account is the header comment's own words, which are English.
  const changes = [
    `<change when="${today}" who="#ed">Export TEI depuis la source LaTeX.</change>`,
    ...meta.revisions
      .map((r, i) => ({ r, i }))
      .sort((a, b) => b.r.date.localeCompare(a.r.date) || b.i - a.i)
      .map(({ r }) => `<change when="${t(r.date)}" who="${who(r)}" xml:lang="en">${t(r.text || 'Revised.')}</change>`),
    ...(meta.passDate
      ? [`<change when="${t(meta.passDate)}" who="#pass">Première passe de transcription.</change>`]
      : []),
  ];

  return `<?xml version="1.0" encoding="UTF-8"?>
<?xml-model href="${RNG_URL}" type="application/xml" schematypens="http://relaxng.org/ns/structure/1.0"?>
<TEI xmlns="${TEI_NS}" xml:lang="fr">
  <teiHeader>
    <fileDesc>
      <titleStmt>
        <title>${t(title)}</title>
        <author>Alexandre Grothendieck</author>
        <respStmt>
          <resp>transcription automatique — première passe, non vérifiée contre les pages par une personne${
            meta.passDate ? ` (<date when="${t(meta.passDate)}">${t(meta.passDate)}</date>)` : ''
          }${byPass.length ? ` ; révisée par le même modèle (${dates(byPass)})` : ''}</resp>
          ${modelLine}
        </respStmt>${reviserLines}
        <respStmt>
          <resp>procédure, outillage, export TEI</resp>
          <orgName xml:id="ed">grothendieck.commutator.io (Commutator, Paris)</orgName>
        </respStmt>
      </titleStmt>
      <editionStmt>
        <edition>${t(meta.watermark || 'Édition de démonstration')}</edition>
      </editionStmt>
      <publicationStmt>
        <publisher>Commutator</publisher>
        <pubPlace>Paris</pubPlace>
        <date when="${today}">${today}</date>
        <availability status="restricted">
          <p>Le fonds Alexandre Grothendieck est sous droits. Cette transcription
          est une édition de démonstration, non autorisée, produite par une
          machine et non vérifiée ; aucune image du fonds n'est reproduite. La
          source LaTeX dont ce fichier dérive est publiée sous ${t(REPO)}.</p>
        </availability>
        <ref target="${SITE}/">${SITE}</ref>
      </publicationStmt>
      <sourceDesc>
        <msDesc>
          <msIdentifier>
            <country>France</country>
            <settlement>Montpellier</settlement>
            <repository>Université de Montpellier</repository>
            <collection>Fonds Alexandre Grothendieck (archives mathématiques, 1949–1991)</collection>
            <idno type="cote">${t(meta.folder)}</idno>
          </msIdentifier>
          ${meta.title ? `<head>${t(meta.title)}</head>` : ''}
          <msContents>
            <summary>Pages ${t(meta.first)} à ${t(meta.last)} de la cote, dans la
            numérotation des archivistes (crayon, en bas à gauche de chaque
            page)${meta.batch ? ` ; lot ${t(meta.batch)} de vingt pages` : ''}.
            Les pages absentes de la transcription ne portent pas de
            mathématiques et sont omises ; le saut dans la numérotation en est
            le seul enregistrement.</summary>
          </msContents>
          ${
            meta.dating
              ? `<history><origin><origDate>${t(meta.dating)}</origDate><note>Datation de l'inventaire de l'Université de Montpellier, reproduite telle quelle ; les crochets sont ceux des archivistes.</note></origin></history>`
              : ''
          }
          <additional>
            <surrogates>
              <bibl>
                <ref target="${MONTPELLIER}/${t(meta.folder)}.pdf">${MONTPELLIER}/${t(meta.folder)}.pdf</ref>
                <note>Fac-similé numérique de l'Université de Montpellier. Sa
                première page est une feuille de garde générée par
                l'université : la page <hi rend="italic">n</hi> des archivistes
                est la page <hi rend="italic">n</hi>+1 du PDF, et l'attribut
                <hi rend="monospace">facs</hi> de chaque
                <hi rend="monospace">pb</hi> tient compte de ce décalage.</note>
              </bibl>
            </surrogates>
          </additional>
        </msDesc>
      </sourceDesc>
    </fileDesc>
    <encodingDesc>
      <projectDesc>
        <p>Transcription mathématique du fonds, une passe de vingt pages par
        conversation avec un grand modèle multimodal, sous la procédure
        <hi rend="monospace">transcribe-grothendieck</hi> du dépôt. Le fichier
        LaTeX est la source de référence ; ce TEI en est dérivé mécaniquement
        par <hi rend="monospace">scripts/tei.mjs</hi> et n'a pas été relu.</p>
      </projectDesc>
      <editorialDecl>
        <p>L'édition n'est pas diplomatique : elle encode les mathématiques et
        l'apparat, rien du support. Correspondance avec l'apparat de la source :
        <hi rend="monospace">\\ill</hi> devient <hi rend="monospace">gap[@reason='illegible']</hi>
        (jamais deviné) ; <hi rend="monospace">\\uncertain</hi> devient
        <hi rend="monospace">unclear</hi> ; <hi rend="monospace">\\supplied</hi> devient
        <hi rend="monospace">supplied</hi> (restitué par le transcripteur) ;
        <hi rend="monospace">\\add</hi> devient <hi rend="monospace">add</hi>
        (ajout de l'auteur, en interligne ou sur un mot biffé) ;
        <hi rend="monospace">\\struck</hi> devient
        <hi rend="monospace">del</hi> (biffé par l'auteur) ;
        <hi rend="monospace">\\note</hi> devient <hi rend="monospace">note[@type='editorial']</hi>
        (du transcripteur) ; <hi rend="monospace">\\marginal</hi> devient
        <hi rend="monospace">note[@type='authorial'][@place='margin']</hi> (de l'auteur) ;
        <hi rend="monospace">\\page</hi> devient <hi rend="monospace">pb</hi>.</p>
        <p>Restitution et ajout de l'auteur n'ont longtemps fait qu'une macro. Ils
        ont été séparés le 26 septembre 2026 par une règle vérifiable dans le
        fichier, non par une relecture : un ajout accolé au mot qu'il complète
        est une restitution (<hi rend="monospace">supplied</hi>), un ajout
        isolé est de l'auteur (<hi rend="monospace">add</hi>). Certains
        <hi rend="monospace">add</hi> sont donc encore des restitutions du
        transcripteur, que seuls les fac-similés départageront.</p>
        <p>Les mathématiques sont transportées en TeX dans
        <hi rend="monospace">formula[@notation='TeX']</hi>, les diagrammes
        commutatifs en <hi rend="monospace">formula[@notation='tikz-cd']</hi>,
        sans conversion. Une marque d'apparat située à l'intérieur d'une
        formule (un exposant illisible, un symbole biffé) reste dans le TeX de
        la formule, sous les mêmes macros.</p>
        <p>Orthographe, ponctuation et lapsus de l'auteur sont conservés ; une
        faute évidente est signalée par une note, jamais corrigée.</p>
      </editorialDecl>
      <appInfo>
        <application ident="grothendieck-tei" version="2">
          <label>scripts/tei.mjs</label>
          <ref target="${REPO}">${REPO}</ref>
        </application>
      </appInfo>
      <schemaRef type="ODD" url="${ODD_URL}"/>
    </encodingDesc>
    <profileDesc>
      <langUsage>
        <language ident="fr">français, avec la notation mathématique de l'auteur</language>${
          meta.revisions.length
            ? `
        <language ident="en">anglais : le compte rendu des révisions, cité de l'en-tête de la source</language>`
            : ''
        }
      </langUsage>
    </profileDesc>
    <revisionDesc>
      ${changes.join('\n      ')}
    </revisionDesc>
  </teiHeader>
  <text>
    <body>
      <div type="batch"${meta.batch ? ` n="${t(meta.batch)}"` : ''}>
${body}
      </div>
    </body>
  </text>
</TEI>
`;
}

// ---------------------------------------------------------------------------

/** Well-formedness, where libxml2 is around; silently skipped where not. */
async function checkWellFormed(path) {
  try {
    await exec('xmllint', ['--noout', path]);
    return true;
  } catch (e) {
    if (e.code === 'ENOENT') return null;
    throw new Error(`not well-formed XML:\n${e.stderr || e.message}`);
  }
}

async function main() {
  const only = process.argv.slice(2).filter((a) => !a.startsWith('--'));

  let folders = [];
  try {
    folders = (await readdir(SOURCE, { withFileTypes: true }))
      .filter((d) => d.isDirectory())
      .map((d) => d.name);
  } catch {
    process.stdout.write('No transcripts/ directory yet — nothing to export.\n');
    return;
  }
  if (only.length) folders = folders.filter((f) => only.includes(f));

  let n = 0;
  let checked = 0;
  const refused = [];
  for (const folder of folders) {
    // Transcriptions only. The modernised reading is another edition with
    // another apparatus (footnotes), and an export of it would be a different
    // document with a different claim; it is not this script's subject.
    const files = (await readdir(resolve(SOURCE, folder))).filter((f) =>
      /^batch-\d+\.fr\.tex$/.test(f),
    );
    if (!files.length) continue;
    await mkdir(resolve(OUT, folder), { recursive: true });

    for (const file of files) {
      const tex = await readFile(resolve(SOURCE, folder, file), 'utf8');
      const target = resolve(OUT, folder, basename(file, '.tex') + '.xml');
      try {
        const { xml, unknown } = convert(tex);
        await writeFile(target, xml, 'utf8');
        const ok = await checkWellFormed(target);
        if (ok) checked++;
        // A control sequence outside the subset would stand in the TEI as
        // literal text. That is a refusal like any other: the file is written,
        // so the residue can be looked at, but the run fails.
        if (unknown.size) {
          throw new Error(
            'control sequences outside the subset, left as text: ' +
              [...unknown].map((u) => `\\${u}`).join(' '),
          );
        }
        n += 1;
      } catch (e) {
        refused.push(`${folder}/${file}`);
        process.stderr.write(`  ✗ ${folder}/${file}: ${e.message}\n`);
      }
    }
  }

  await mkdir(resolve(ROOT, 'public', 'tei'), { recursive: true });
  await copyFile(ODD_SOURCE, resolve(ROOT, 'public', 'tei', 'grothendieck.odd'));

  process.stdout.write(
    `${n} TEI files → public/transcripts/, and the ODD at /tei/grothendieck.odd` +
      (checked ? ` (${checked} checked well-formed by xmllint)` : ' (xmllint not found; not checked)') +
      '\n',
  );
  // Refused files used to be a warning on a green run, and a batch that
  // failed to convert simply had no TEI. Now the run fails, and says which.
  if (refused.length) {
    process.stderr.write(`${refused.length} file(s) refused: ${refused.join(', ')}\n`);
    process.exit(1);
  }
}

main().catch((e) => {
  process.stderr.write(`${e.message}\n`);
  process.exit(1);
});
