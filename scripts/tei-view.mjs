#!/usr/bin/env node
/**
 * Renders the reading view from the TEI export instead of from the `.tex`.
 *
 *   npm run tei-view               every exported transcription
 *   npm run tei-view -- 11         one folder
 *
 * Reads `public/transcripts/<folder>/batch-NN.fr.xml` (written by
 * scripts/tei.mjs) and writes `batch-NN.fr.tei.html` beside it. Step towards
 * COM-73 / #21: the Transcription tab is to be rendered from TEI, with the
 * apparatus toggleable. For now the file is reachable only through the hidden
 * fragment `#<cote>/<batch>/tei`, and nothing a reader sees has changed.
 *
 * **It must look identical** to the view render.mjs makes from the `.tex`, so
 * that switching is a change of source and not of design: the page shell, the
 * stylesheet, the KaTeX and diagram scripts are render.mjs's own
 * (`readingPage`, `renderDiagram`), and every TEI element maps to the class the
 * `.tex` view already uses. `scripts/check-tei.mjs` checks the claim page by
 * page.
 *
 * **It is strict, like render.mjs.** Only the elements tei.mjs emits are
 * understood; any other element, attribute value or entity throws. A view that
 * silently dropped an element it did not know would present an incomplete page
 * as a complete one.
 *
 * The apparatus is additionally tagged with `tei-*` classes, and two root
 * classes on `<html>` switch it: `.reading` hides deletions and prints
 * supplied and unclear text plain; `.no-notes` hides the transcriber's notes.
 * Nothing sets them yet except `?view=reading,no-notes` on the file's own URL,
 * for testing.
 *
 * This is the page the TEI button of the Source & print row opens. Under the
 * head line it links the XML it was rendered from, to open or to download.
 */

import { readdir, readFile, writeFile } from 'node:fs/promises';
import { resolve, basename } from 'node:path';
import { fileURLToPath } from 'node:url';
import { EDITION_LABELS, escapeHtml, readingPage, renderDiagram } from './render.mjs';

const ROOT = resolve(import.meta.dirname, '..');
const OUT = resolve(ROOT, 'public', 'transcripts');

// ---------------------------------------------------------------------------
// A strict XML reader, for the XML tei.mjs writes and nothing more general.

const ENTITIES = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'" };

function decode(s, where) {
  return s.replace(/&(#x[0-9a-fA-F]+|#\d+|[a-zA-Z]+);|&/g, (m, e) => {
    if (!e) throw new Error(`bare & in ${where}`);
    if (e[0] === '#') {
      return String.fromCodePoint(e[1] === 'x' ? parseInt(e.slice(2), 16) : Number(e.slice(1)));
    }
    if (!(e in ENTITIES)) throw new Error(`unknown entity &${e}; in ${where}`);
    return ENTITIES[e];
  });
}

/** Parses into `{ name, attrs, children }` elements and plain strings. */
export function parseXml(xml) {
  let i = 0;
  const root = { name: '#document', attrs: {}, children: [] };
  const stack = [root];
  const top = () => stack[stack.length - 1];

  while (i < xml.length) {
    const lt = xml.indexOf('<', i);
    if (lt === -1) {
      top().children.push(decode(xml.slice(i), 'text'));
      break;
    }
    if (lt > i) top().children.push(decode(xml.slice(i, lt), 'text'));

    if (xml.startsWith('<?', lt)) {
      i = xml.indexOf('?>', lt) + 2;
      continue;
    }
    if (xml.startsWith('<!--', lt)) {
      i = xml.indexOf('-->', lt) + 3;
      continue;
    }
    if (xml.startsWith('<!', lt)) throw new Error('DOCTYPE or CDATA: not emitted by tei.mjs');

    const gt = xml.indexOf('>', lt);
    if (gt === -1) throw new Error('unterminated tag');
    const tag = xml.slice(lt + 1, gt);
    i = gt + 1;

    if (tag[0] === '/') {
      const name = tag.slice(1).trim();
      const open = stack.pop();
      if (!open || open.name !== name) {
        throw new Error(`mismatched </${name}> (open: <${open?.name}>)`);
      }
      continue;
    }

    const selfClosing = tag.endsWith('/');
    const m = /^([A-Za-z][\w:.-]*)([\s\S]*?)\/?$/.exec(tag);
    if (!m) throw new Error(`malformed tag <${tag}>`);
    const attrs = {};
    const attrRe = /\s+([\w:.-]+)="([^"]*)"/g;
    let rest = m[2];
    let a;
    let consumed = '';
    while ((a = attrRe.exec(rest))) {
      attrs[a[1]] = decode(a[2], `attribute ${a[1]}`);
      consumed += a[0];
    }
    if (consumed.replace(/\s+/g, '') !== rest.replace(/\s+/g, '')) {
      throw new Error(`malformed attributes in <${tag}>`);
    }
    const el = { name: m[1], attrs, children: [] };
    top().children.push(el);
    if (!selfClosing) stack.push(el);
  }
  if (stack.length !== 1) throw new Error(`unclosed <${top().name}>`);
  return root;
}

const isEl = (n) => typeof n !== 'string';
const textOf = (n) => (typeof n === 'string' ? n : n.children.map(textOf).join(''));
const blank = (n) => typeof n === 'string' && !n.trim();

function unexpected(el, where) {
  const attrs = Object.entries(el.attrs).map(([k, v]) => ` ${k}="${v}"`).join('');
  return new Error(
    `unsupported <${el.name}${attrs}> in ${where} — extend scripts/tei-view.mjs ` +
      'together with scripts/tei.mjs',
  );
}

// ---------------------------------------------------------------------------
// The header: what the `.tex` view prints in its head line.

/** Every element the header may contain, and nothing else. */
const HEADER_ELEMENTS = new Set([
  'teiHeader', 'fileDesc', 'titleStmt', 'title', 'author', 'respStmt', 'resp', 'date',
  'name', 'orgName', 'editionStmt', 'edition', 'publicationStmt', 'publisher', 'pubPlace',
  'availability', 'p', 'ref', 'sourceDesc', 'msDesc', 'msIdentifier', 'country',
  'settlement', 'repository', 'collection', 'idno', 'head', 'msContents', 'summary',
  'history', 'origin', 'origDate', 'note', 'additional', 'surrogates', 'bibl', 'hi',
  'encodingDesc', 'projectDesc', 'editorialDecl', 'appInfo', 'application', 'label',
  'profileDesc', 'langUsage', 'language', 'revisionDesc', 'change',
]);

function find(el, name) {
  for (const c of el.children) {
    if (!isEl(c)) continue;
    if (c.name === name) return c;
    const inner = find(c, name);
    if (inner) return inner;
  }
  return null;
}

function readHeader(header, batchDiv) {
  (function walk(el) {
    if (!HEADER_ELEMENTS.has(el.name)) throw unexpected(el, 'teiHeader');
    el.children.filter(isEl).forEach(walk);
  })(header);

  const title = textOf(find(header, 'title') ?? { children: [] });
  const t = /cote n° (.+), pages (\d*)–(\d*) — transcription$/.exec(title);
  if (!t) throw new Error(`title not in the form tei.mjs writes: « ${title} »`);
  const msDesc = find(header, 'msDesc');
  const msHead = msDesc?.children.find((c) => isEl(c) && c.name === 'head');
  const dating = find(header, 'origDate');
  const edition = find(header, 'edition');
  return {
    folder: t[1],
    batch: batchDiv.attrs.n ?? '',
    title: msHead ? textOf(msHead) : '',
    dating: dating ? textOf(dating) : '',
    watermark: edition ? textOf(edition) : '',
    first: t[2],
    last: t[3],
  };
}

// ---------------------------------------------------------------------------
// The body.

const pageSpan = (n) => `<span class="tr-page" data-page="${n}" id="page-${n}">${n}</span>`;

function renderInline(nodes, where) {
  return nodes.map((n) => inlineNode(n, where)).join('');
}

function inlineNode(n, where) {
  if (typeof n === 'string') return escapeHtml(n);
  const inner = () => renderInline(n.children, `<${n.name}>`);
  switch (n.name) {
    case 'formula': {
      const tex = escapeHtml(textOf(n));
      if (n.attrs.notation !== 'TeX') throw unexpected(n, where);
      if (n.attrs.rend === 'display') return `<span class="ltx_Math ltx_display">\\[${tex}\\]</span>`;
      if (n.attrs.rend !== undefined) throw unexpected(n, where);
      return `<span class="ltx_Math">\\(${tex}\\)</span>`;
    }
    case 'figure': {
      const f = n.children.filter((c) => !blank(c));
      if (n.attrs.type !== 'diagram' || f.length !== 1 || f[0].name !== 'formula' ||
          f[0].attrs.notation !== 'tikz-cd') {
        throw unexpected(n, where);
      }
      return renderDiagram(textOf(f[0]));
    }
    case 'gap':
      if (n.attrs.reason !== 'illegible' || n.children.length) throw unexpected(n, where);
      return '<span class="tr-ill tei-gap" title="illegible">[…]</span>';
    case 'unclear':
      return `<span class="tr-uncertain tei-unclear" title="uncertain reading">${inner()}</span>`;
    case 'supplied':
      // The brackets are text, as in the `.tex` view, so the two read the same;
      // wrapped so `.reading` can drop them.
      return '<span class="tr-add tei-supplied" title="editorial addition">' +
        `<span class="tei-br">[</span>${inner()}<span class="tei-br">]</span></span>`;
    case 'del':
      return `<span class="tr-struck tei-del" title="struck out by the author">${inner()}</span>`;
    case 'note':
      if (n.attrs.type === 'editorial') {
        return `<span class="tr-note tei-note-editorial" title="transcriber's note">${inner()}</span>`;
      }
      if (n.attrs.type === 'authorial' && n.attrs.place === 'margin') {
        return `<span class="tr-marginal tei-note-margin" title="marginal note">${inner()}</span>`;
      }
      throw unexpected(n, where);
    case 'seg':
      if (n.attrs.type !== 'keywords') throw unexpected(n, where);
      return `<span class="tr-keywords"><span class="tr-keywords-k">Keywords</span> — ${inner()}</span>`;
    case 'hi':
      switch (n.attrs.rend) {
        case 'italic': return `<em class="ltx_emph">${inner()}</em>`;
        case 'bold': return `<strong class="ltx_text ltx_font_bold">${inner()}</strong>`;
        case 'monospace': return `<code class="ltx_text ltx_font_typewriter">${inner()}</code>`;
        case 'sup': return `<sup>${inner()}</sup>`;
        case 'underline': return `<u class="tei-underline">${inner()}</u>`;
        default: throw unexpected(n, where);
      }
    case 'lb':
      if (n.children.length) throw unexpected(n, where);
      return '<br>';
    default:
      throw unexpected(n, where);
  }
}

/**
 * A run of block-level children. A `<pb>` is held and printed inside the next
 * block, where render.mjs prints the `\page` prefix: inside a paragraph, a
 * heading or a quotation, before a list.
 */
function renderBlocks(children, where, state = { pending: '' }, top = true) {
  const out = [];
  const take = () => {
    const p = state.pending;
    state.pending = '';
    return p;
  };

  for (let k = 0; k < children.length; k++) {
    const n = children[k];
    if (blank(n)) continue;
    if (typeof n === 'string') throw new Error(`stray text « ${n.trim().slice(0, 40)} » in ${where}`);
    switch (n.name) {
      case 'pb':
        if (!/^\d+$/.test(n.attrs.n ?? '')) throw unexpected(n, where);
        // tei.mjs writes a page marker that opens its own block (`\page{33}`
        // followed by a blank line) on a line of its own, and one that begins
        // a paragraph glued to it. render.mjs prints the first as an empty
        // paragraph carrying the number, so the same is done here; the parity
        // check fails if that serialisation ever changes.
        if (typeof children[k + 1] === 'string' && children[k + 1].includes('\n')) {
          if (state.pending) out.push(`<p class="ltx_p">${take()}</p>`);
          out.push(`<p class="ltx_p">${pageSpan(n.attrs.n)}</p>`);
          break;
        }
        // Two in a row: the first had nothing on its page, which render.mjs
        // prints as an empty paragraph carrying the marker.
        if (state.pending) out.push(`<p class="ltx_p">${take()}</p>`);
        state.pending = pageSpan(n.attrs.n);
        break;
      case 'div': {
        const type = n.attrs.type;
        if (type === 'summary') {
          if (state.pending) out.push(take());
          const inner = n.children.filter((c) => !blank(c)).map((c) => {
            if (!isEl(c) || c.name !== 'p') throw unexpected(isEl(c) ? c : { name: '#text', attrs: {} }, 'summary');
            return `<p class="ltx_p">${renderInline(c.children, '<p>')}</p>`;
          });
          out.push(`<div class="tr-resume">${inner.join('\n')}</div>`);
        } else if (type === 'section' || type === 'subsection' || type === undefined) {
          // A marker held before the division belongs to its first block.
          out.push(...renderBlocks(n.children, `<div type="${type}">`, state, false));
        } else {
          throw unexpected(n, where);
        }
        break;
      }
      case 'head': {
        const sub = /subsection/.test(where);
        const tag = sub ? 'h3' : 'h2';
        const cls = sub ? 'ltx_title_subsection' : 'ltx_title_section';
        out.push(`<${tag} class="ltx_title ${cls}">${take()}${renderInline(n.children, '<head>')}</${tag}>`);
        break;
      }
      case 'p':
        out.push(`<p class="ltx_p">${take()}${renderInline(n.children, '<p>')}</p>`);
        break;
      case 'quote':
        out.push(`<blockquote class="ltx_quote">${take()}${renderItemBody(n.children, '<quote>')}</blockquote>`);
        break;
      case 'list':
        out.push(take() + renderList(n, where));
        break;
      default:
        throw unexpected(n, where);
    }
  }
  if (top && state.pending) out.push(`<p class="ltx_p">${take()}</p>`);
  return out;
}

/** An item's or a quotation's body: mixed inline content, or blocks. */
function renderItemBody(children, where) {
  const blocky = children.some((c) => isEl(c) && ['p', 'list', 'pb'].includes(c.name));
  return blocky ? renderBlocks(children, where).join('\n') : renderInline(children, where);
}

function renderList(list, where) {
  const rend = list.attrs.rend;
  if (rend !== 'itemize' && rend !== 'enumerate') throw unexpected(list, where);
  const tag = rend === 'itemize' ? 'ul' : 'ol';
  const items = [];
  let label = null;
  let tagged = false;
  for (const c of list.children) {
    if (blank(c)) continue;
    if (!isEl(c)) throw new Error(`stray text in <list>`);
    if (c.name === 'label') {
      label = renderInline(c.children, '<label>');
    } else if (c.name === 'item') {
      const body = renderItemBody(c.children, '<item>');
      if (label === null) {
        items.push(`<li class="ltx_item">${body}</li>`);
      } else {
        tagged = true;
        items.push(`<li class="ltx_item ltx_item_tagged"><span class="ltx_tag">${label}</span>${body}</li>`);
        label = null;
      }
    } else {
      throw unexpected(c, '<list>');
    }
  }
  if (label !== null) throw new Error('<label> with no <item> after it');
  const cls = tagged ? 'ltx_itemize ltx_itemize_tagged' : 'ltx_itemize';
  return `<${tag} class="${cls}">${items.join('\n')}</${tag}>`;
}

// ---------------------------------------------------------------------------

/** The apparatus switches. Empty unless a root class is set. */
const TEI_STYLE = `  /* TEI view: the apparatus, switchable from the root. */
  .reading .tei-del { display: none; }
  .reading .tei-br { display: none; }
  .reading .tei-supplied { color: inherit; }
  .reading .tei-unclear { border-bottom: 0; }
  .no-notes .tei-note-editorial { display: none; }
  .tei-underline { text-decoration: underline; }
  /* The file this view is rendered from, one click away to open or keep. */
  .tei-source { margin: -.8rem 0 1.4rem; font-family: var(--sans); font-size: 12px;
             color: var(--ink3); }
  .tei-source a { color: #38539d; text-decoration: none; font-weight: 600; }
  .tei-source a:hover { text-decoration: underline; }
`;

/** Testing hook only: `?view=reading,no-notes` sets the root classes. */
const TEI_SCRIPT = `<script>
(function () {
  var v = new URLSearchParams(location.search).get('view');
  if (!v) return;
  v.split(',').forEach(function (c) {
    if (c === 'reading' || c === 'no-notes') document.documentElement.classList.add(c);
  });
})();
</script>
`;

export function teiToHtml(xml, file) {
  const doc = parseXml(xml);
  const tei = doc.children.find(isEl);
  if (!tei || tei.name !== 'TEI') throw new Error('root element is not <TEI>');
  const kids = tei.children.filter((c) => !blank(c));
  const [header, text] = kids;
  if (kids.length !== 2 || header.name !== 'teiHeader' || text.name !== 'text') {
    throw new Error('<TEI> must hold exactly <teiHeader> and <text>');
  }
  const body = text.children.filter((c) => !blank(c));
  if (body.length !== 1 || body[0].name !== 'body') throw new Error('<text> must hold one <body>');
  const batchDivs = body[0].children.filter((c) => !blank(c));
  if (batchDivs.length !== 1 || batchDivs[0].name !== 'div' || batchDivs[0].attrs.type !== 'batch') {
    throw new Error('<body> must hold one <div type="batch">');
  }
  const meta = readHeader(header, batchDivs[0]);
  const html = renderBlocks(batchDivs[0].children, '<div type="batch">').join('\n');
  const { lang, name } = EDITION_LABELS.fr;
  // Where a researcher gets the XML itself: opened in the browser, or saved.
  // Outside the head line, so the head stays the `.tex` view's word for word.
  const source = file
    ? `\n<p class="tei-source">TEI P5 source — <a href="./${escapeHtml(file)}" target="_blank" rel="noopener">open the XML</a>` +
      ` · <a href="./${escapeHtml(file)}" download>download ${escapeHtml(file)}</a></p>`
    : '';
  const page = readingPage({ meta, lang, name, html, extraStyle: TEI_STYLE });
  const headEnd = page.indexOf('</p>', page.indexOf('<p class="tr-head">')) + '</p>'.length;
  return (page.slice(0, headEnd) + source + page.slice(headEnd))
    .replace('</body>', `${TEI_SCRIPT}</body>`);
}

async function main() {
  const only = process.argv.slice(2).filter((a) => !a.startsWith('--'));
  let folders = (await readdir(OUT, { withFileTypes: true }))
    .filter((d) => d.isDirectory())
    .map((d) => d.name);
  if (only.length) folders = folders.filter((f) => only.includes(f));

  let n = 0;
  let failed = 0;
  for (const folder of folders) {
    const files = (await readdir(resolve(OUT, folder))).filter((f) => /^batch-\d+\.fr\.xml$/.test(f));
    for (const file of files) {
      try {
        const xml = await readFile(resolve(OUT, folder, file), 'utf8');
        await writeFile(resolve(OUT, folder, basename(file, '.xml') + '.tei.html'), teiToHtml(xml, file), 'utf8');
        n += 1;
      } catch (e) {
        failed += 1;
        process.stderr.write(`  ⚠ ${folder}/${file}: ${e.message}\n`);
      }
    }
  }
  process.stdout.write(`${n} TEI reading views → public/transcripts/${failed ? ` (${failed} failed)` : ''}\n`);
  if (failed) process.exitCode = 1;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch((e) => {
    process.stderr.write(`${e.message}\n`);
    process.exit(1);
  });
}
