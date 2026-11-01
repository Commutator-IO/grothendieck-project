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
 * mathematics is passed through for KaTeX. Anything else in a statement raises.
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
function prose(t) {
  // Math out of the way first (a \q{…} may hold $…$), back in at the end.
  const math = [];
  const p = t.replace(/\$[^$]*\$/g, (m) => `\uE000${math.push(m) - 1}\uE000`);
  return [p]
    .map((p) => {
      let h = p
        .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
        .replace(/---/g, '—').replace(/--/g, '–').replace(/~/g, ' ')
        .replace(/``/g, '“').replace(/''/g, '”').replace(/\\,/g, ' ')
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
  const re = /\\(section|topic|session|sessiondate|face|video|entree)(\*?)\{/g;
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
      items.push({ k: 'entry', v: video, t: Number(a), ts, text: prose(text) });
      i = l;
    }
    re.lastIndex = i;
  }
  out[id] = { pdf: `/article/${dir}.pdf`, entries: items.filter((x) => x.k === 'entry').length, items };
  console.log(`${id}: ${out[id].entries} entries, ${items.filter((x) => x.k === 'topic').length} topics`);
}
writeFileSync(resolve(root, 'src/content/buffalo-index.json'), JSON.stringify(out));
