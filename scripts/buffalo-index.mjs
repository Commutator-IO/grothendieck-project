#!/usr/bin/env node
/**
 * Reads the three Buffalo indexes of results (docs/buffalo-{topos,ag,groupes}/index.tex)
 * into src/content/buffalo-index.json, which the Buffalo tab shows beside the player.
 *
 *   npm run buffalo-index
 *
 * The .tex is the source of record, as for the transcripts: the PDF is compiled from it
 * and the page is read from it, so the two cannot drift. Only the markers the indexes
 * use are read — \section or \topic (a topic), \session or \sessiondate (a day), \face
 * (a tape side), \video{id}, \entree{seconds}{h:mm:ss}{statement} — and the statements'
 * mathematics is passed through for KaTeX. \bibitem{key} and \cite{key} give the numbered references. Anything else in a statement raises.
 */
import { readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const root = resolve(import.meta.dirname, '..');
const COURSES = { topos: 'buffalo-topos', ag: 'buffalo-ag', groups: 'buffalo-groupes' };

/** The balanced {…} argument starting at s[i] === '{'; returns [content, index after]. */
function arg(s, i) {
  if (s[i] !== '{') throw new Error(`expected { at ${s.slice(i, i + 40)}`);
  let d = 0;
  for (let j = i; j < s.length; j++) {
    if (s[j] === '\\') { j++; continue; }
    if (s[j] === '{') d++;
    else if (s[j] === '}' && --d === 0) return [s.slice(i + 1, j), j + 1];
  }
  throw new Error('unbalanced braces');
}

/** Prose outside $…$ to HTML; math kept verbatim for KaTeX. */
function prose(t, cites = {}) {
  // Math out of the way first (a \q{…} may hold $…$), back in at the end; so are links and citations.
  const math = [];
  const keep = (m) => `\uE000${math.push(m) - 1}\uE000`;
  const p = t
    .replace(/\\url\{([^}]*)\}/g, (_, u) => keep(`<a href="${u}" target="_blank" rel="noopener noreferrer">${u}</a>`))
    .replace(/\\cite\{([^}]*)\}/g, (_, ks) =>
      keep(`[${ks.split(',').map((k) => cites[k.trim()] ?? (() => { throw new Error(`unknown citation ${k}`); })()).join(', ')}]`))
    .replace(/\$[^$]*\$/g, keep);
  return [p]
    .map((p) => {
      let h = p
        .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
        .replace(/---/g, '—').replace(/--/g, '–').replace(/~/g, ' ')
        .replace(/``/g, '“').replace(/''/g, '”').replace(/\\S\b/g, '§').replace(/\\,/g, ' ')
        .replace(/\\(?:ldots|dots)\b/g, '…').replace(/\\%/g, '%').replace(/\\&amp;/g, '&amp;')
        .replace(/\\(['`^"~v=])\{?([a-zA-Z])\}?/g, (_, a, c) =>
          (c + { "'": '́', '`': '̀', '^': '̂', '"': '̈', '~': '̃', v: '̌', '=': '̄' }[a]).normalize('NFC'))
        .replace(/\\(?:linebreak|newline|allowbreak)\b/g, '').replace(/\\_/g, '_').replace(/\\@/g, '').replace(/\\\//g, '').replace(/\\ /g, ' ');
      for (;;) {
        const m = /\\(q|emph|textit|textbf|mbox|text)\{/.exec(h);
        if (!m) break;
        const [inner, end] = arg(h, m.index + m[0].length - 1);
        const tag = { q: ['“', '”'], emph: ['<em>', '</em>'], textit: ['<em>', '</em>'], textbf: ['<b>', '</b>'] }[m[1]] ?? ['', ''];
        h = h.slice(0, m.index) + tag[0] + inner + tag[1] + h.slice(end);
      }
      if (/\\[a-zA-Z]/.test(h) || /[{}]/.test(h)) throw new Error(`unsupported LaTeX in: ${p}`);
      return h;
    })[0]
    .replace(/\uE000(\d+)\uE000/g, (_, n) => math[n]);
}

const out = {};
for (const [id, dir] of Object.entries(COURSES)) {
  const src = readFileSync(resolve(root, 'docs', dir, 'index.tex'), 'utf8');
  const body = src.slice(src.indexOf('\\begin{document}'));
  const items = [];
  let video = null;
  // The bibliography: \bibitem{key} text, numbered in order, as LaTeX numbers it.
  const cites = {};
  const refs = [];
  const bib = /\\begin\{thebibliography\}\{[^}]*\}([\s\S]*?)\\end\{thebibliography\}/.exec(body);
  if (bib) {
    for (const part of bib[1].split(/\\bibitem\{/).slice(1)) {
      const k = part.slice(0, part.indexOf('}'));
      cites[k] = refs.length + 1;
      refs.push([k, part.slice(part.indexOf('}') + 1).trim()]);
    }
  }
  const refsHtml = refs.map(([, r]) => prose(r, cites));
  const re = /\\(section|topic|session|sessiondate|face|video|entree)(\*?)(?:\[(\w+)\])?(?:\[([^\]]*)\])?\{/g;
  for (let m; (m = re.exec(body)); ) {
    let [a, i] = arg(body, m.index + m[0].length - 1);
    const k = m[1];
    if (k === 'section' && m[2]) continue; // \section*{Introduction}: the page has its own
    if (k === 'video') video = a;
    else if (k === 'section' || k === 'topic') items.push({ k: 'topic', text: prose(a) });
    else if (k === 'session' || k === 'sessiondate') items.push({ k: 'session', text: prose(k === 'session' ? `Session of ${a}` : a) });
    else if (k === 'face') items.push({ k: 'side', text: prose(a) });
    else {
      const [ts, j] = arg(body, i);
      const [text, l] = arg(body, j);
      if (!video) throw new Error(`${dir}: entry before any \\video`);
      items.push({ k: 'entry', v: video, t: Number(a), ts, text: prose(text, cites), ...(m[3] ? { kind: m[3] } : {}), ...(m[4] ? { name: prose(m[4]) } : {}) });
      i = l;
    }
    re.lastIndex = i;
  }
  out[id] = { pdf: `/article/${dir}.pdf`, entries: items.filter((x) => x.k === 'entry').length, items, refs: refsHtml };
  console.log(`${id}: ${out[id].entries} entries, ${items.filter((x) => x.k === 'topic').length} topics`);
}
writeFileSync(resolve(root, 'src/content/buffalo-index.json'), JSON.stringify(out));
