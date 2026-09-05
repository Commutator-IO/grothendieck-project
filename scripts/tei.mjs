#!/usr/bin/env node
/**
 * Exports each transcription to TEI P5, mechanically, from its `.tex`.
 *
 *   npm run tei                  every transcription
 *   npm run tei -- 19            one folder
 *
 * Why a second serialisation of the same file. The `.tex` is the source of
 * record and stays so: it is what gets corrected and compiled, and this script
 * reads nothing else — not the facsimile, not the HTML. But LaTeX with seven
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
 *   \add{x}            <supplied resp="#pass">x</supplied>
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
 * Same discipline as scripts/render.mjs: the subset is the documented one, an
 * unknown environment raises, and an unknown inline macro is reported rather
 * than silently flattened. Output goes to public/transcripts/, derived and
 * unversioned like the HTML and the PDF. Every file is checked well-formed
 * with xmllint where it exists; validation against tei_all.rng is a separate
 * step (see the README) because the schema is a megabyte nobody wants vendored.
 */

import { mkdir, readdir, readFile, writeFile } from 'node:fs/promises';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { resolve, basename } from 'node:path';

const exec = promisify(execFile);

const ROOT = resolve(import.meta.dirname, '..');
const SOURCE = resolve(ROOT, 'transcripts');
const OUT = resolve(ROOT, 'public', 'transcripts');
const MONTPELLIER = 'https://grothendieck.umontpellier.fr';
const SITE = 'https://grothendieck.commutator.io';
const REPO = 'https://github.com/Commutator-IO/grothendieck-project';
const TEI_NS = 'http://www.tei-c.org/ns/1.0';

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
  ['add', (a) => `<supplied resp="#pass">${a}</supplied>`],
  ['struck', (a) => `<del>${a}</del>`],
  ['note', (a) => `<note type="editorial" resp="#pass">${a}</note>`],
  ['marginal', (a) => `<note type="authorial" place="margin">${a}</note>`],
  ['keywords', (a) => `<seg type="keywords">${a}</seg>`],
  ['emph', (a) => `<hi rend="italic">${a}</hi>`],
  ['textit', (a) => `<hi rend="italic">${a}</hi>`],
  ['textbf', (a) => `<hi rend="bold">${a}</hi>`],
  ['texttt', (a) => `<hi rend="monospace">${a}</hi>`],
  ['textsuperscript', (a) => `<hi rend="sup">${a}</hi>`],
  // He underlines a word to stress it; in prose the renderer leaves the macro
  // alone and the PDF draws the line. Here it is a rendition, not apparatus.
  ['underline', (a) => `<hi rend="underline">${a}</hi>`],
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
    // Reported once per file rather than thrown: the renderer tolerates the
    // same residue, and the two derived views should disagree about nothing.
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
  const openRe = /\\begin\{(itemize|enumerate|quote|resume)\}/g;
  for (;;) {
    openRe.lastIndex = i;
    const m = openRe.exec(text);
    if (!m) {
      out += text.slice(i);
      break;
    }
    out += text.slice(i, m.index);
    // Scan forward for the matching \end, counting every block environment.
    const tok = /\\(begin|end)\{(itemize|enumerate|quote|resume)\}/g;
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
  const tok = /\\(begin|end)\{(itemize|enumerate|quote|resume)\}|\\item(?![a-zA-Z])/g;
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

function readMeta(tex) {
  const one = (name) => new RegExp(`\\\\${name}\\{([^{}]*)\\}`).exec(tex)?.[1] ?? '';
  const pages = /\\pages\{(\d+)\}\{(\d+)\}/.exec(tex);
  // The header comment names the pass: `% Pass: Fable 5.1 (claude-fable-5-1),
  // 2026-09-03 — first pass, …`. It is the only place the model is recorded,
  // which is why the export copies it into a structured statement.
  const pass = /^%\s*Pass:\s*([^(\n]+?)\s*\(([^)\n]+)\)\s*,\s*(\d{4}-\d{2}-\d{2})/m.exec(tex);
  return {
    folder: one('folder'),
    batch: one('batch'),
    title: one('foldertitle'),
    dating: one('dating'),
    watermark: one('watermark').replace(/\\\\/g, ' — '),
    first: pages?.[1] ?? '',
    last: pages?.[2] ?? '',
    model: pass?.[1] ?? '',
    modelId: pass?.[2] ?? '',
    passDate: pass?.[3] ?? '',
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
    const resume = /^\\begin\{resume\}([\s\S]*)\\end\{resume\}$/.exec(block);
    if (resume) return `<div type="summary">\n${renderBlocks(resume[1], false).join('\n')}\n</div>`;
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
    const blocks = lifted
      // A page marker always starts a block, even mid-paragraph: a page turns
      // where the paper turns, not where the argument does.
      .replace(/\\page\{/g, '\n\n\\page{')
      .replace(/(\\(?:sub)?section\*?\{)/g, '\n\n$1')
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

  return `<?xml version="1.0" encoding="UTF-8"?>
<TEI xmlns="${TEI_NS}" xml:lang="fr">
  <teiHeader>
    <fileDesc>
      <titleStmt>
        <title>${t(title)}</title>
        <author>Alexandre Grothendieck</author>
        <respStmt>
          <resp>transcription automatique — première passe, non vérifiée contre les pages par une personne${
            meta.passDate ? ` (<date when="${t(meta.passDate)}">${t(meta.passDate)}</date>)` : ''
          }</resp>
          ${modelLine}
        </respStmt>
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
        <hi rend="monospace">unclear</hi> ; <hi rend="monospace">\\add</hi> devient
        <hi rend="monospace">supplied</hi> ; <hi rend="monospace">\\struck</hi> devient
        <hi rend="monospace">del</hi> (biffé par l'auteur) ;
        <hi rend="monospace">\\note</hi> devient <hi rend="monospace">note[@type='editorial']</hi>
        (du transcripteur) ; <hi rend="monospace">\\marginal</hi> devient
        <hi rend="monospace">note[@type='authorial'][@place='margin']</hi> (de l'auteur) ;
        <hi rend="monospace">\\page</hi> devient <hi rend="monospace">pb</hi>.</p>
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
        <application ident="grothendieck-tei" version="1">
          <label>scripts/tei.mjs</label>
          <ref target="${REPO}">${REPO}</ref>
        </application>
      </appInfo>
    </encodingDesc>
    <profileDesc>
      <langUsage>
        <language ident="fr">français, avec la notation mathématique de l'auteur</language>
      </langUsage>
    </profileDesc>
    <revisionDesc>
      ${
        meta.passDate
          ? `<change when="${t(meta.passDate)}" who="#pass">Première passe de transcription.</change>`
          : ''
      }
      <change when="${today}" who="#ed">Export TEI depuis la source LaTeX.</change>
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
        if (unknown.size) {
          process.stderr.write(
            `  ⚠ ${folder}/${file}: control sequences left as text: ` +
              [...unknown].map((u) => `\\${u}`).join(' ') + '\n',
          );
        }
        n += 1;
      } catch (e) {
        process.stderr.write(`  ⚠ ${folder}/${file}: ${e.message}\n`);
      }
    }
  }

  process.stdout.write(
    `${n} TEI files → public/transcripts/` +
      (checked ? ` (${checked} checked well-formed by xmllint)` : ' (xmllint not found; not checked)') +
      '\n',
  );
}

main().catch((e) => {
  process.stderr.write(`${e.message}\n`);
  process.exit(1);
});
