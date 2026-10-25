#!/usr/bin/env node
/**
 * Writes src/content/notices.json: one archival notice per folder of the
 * Montpellier fonds, on the model of the BnF's « Archives et manuscrits »
 * notices, and the books the inventory spreads over several folders.
 *
 *   npm run notices
 *
 * Nothing here is written for a particular folder. Every field is read from a
 * source that already exists in the repository:
 *
 *   - cote, title, inventory dating, page count, typology: the inventory
 *     (src/content/catalogue.ts);
 *   - pages transcribed, diagrams, drawings, share of mathematics, languages:
 *     src/content/hand.json and the \page markers of transcripts/<cote>/;
 *   - dates on the leaves (kinds « paper » and « label » left out) and the
 *     proposed datings, kept apart and never substituted for the inventory's:
 *     src/content/dated-leaves.json, src/content/proposed-datings.json;
 *   - editions: src/content/editions.json;
 *   - the content: the first paragraphs of the résumé of the modernised
 *     reading, and its \keywords as the subject index;
 *   - names: src/content/people-evidence.json and letters.json only;
 *   - the author's own tables of contents and plans, copied from the
 *     transcriptions with his numbering and page numbers.
 *
 * The transcriptions contribute nothing beyond those tables and titles. When
 * transcripts/ is absent the notices fall back on the inventory alone.
 */
import { existsSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const T = resolve(ROOT, 'transcripts');
const C = resolve(ROOT, 'src/content');
const OUT = resolve(C, 'notices.json');

const json = (f) => JSON.parse(readFileSync(resolve(C, f), 'utf8'));
const tsArray = (src, name) => {
  const i = src.indexOf(`export const ${name}`);
  const start = src.indexOf('[', src.indexOf('=', i));
  let depth = 0;
  for (let k = start; k < src.length; k++) {
    if (src[k] === '[') depth++;
    else if (src[k] === ']' && --depth === 0) return JSON.parse(src.slice(start, k + 1));
  }
  throw new Error(`${name} not found`);
};

const catalogue = readFileSync(resolve(C, 'catalogue.ts'), 'utf8');
const COTES = tsArray(catalogue, 'COTES');
const GROUPS = tsArray(catalogue, 'GROUPS');
const hand = json('hand.json');
const HAND = new Map(hand.folders.map((f) => [f.id, f]));
const LEAVES = json('dated-leaves.json').records.filter((r) => r.kind !== 'paper' && r.kind !== 'label');
const DATINGS = json('proposed-datings.json').records;
const EDITIONS = json('editions.json');
const PEOPLE = json('people-evidence.json').records;
const LETTERS = json('letters.json').records;
const findingsSrc = readFileSync(resolve(C, 'findings.ts'), 'utf8');
const proofsSrc = readFileSync(resolve(C, 'proofs.ts'), 'utf8');
const countBy = (src, re) => {
  const m = new Map();
  for (const x of src.matchAll(re)) m.set(x[1], (m.get(x[1]) ?? 0) + 1);
  return m;
};
const FINDINGS = countBy(findingsSrc, /^\s{4}cote: '([^']+)'/gm);
const PROOFS = countBy(proofsSrc, /^\s{4}folder: '([^']+)'/gm);

// ---------------------------------------------------------------------------
// LaTeX → the site's hybrid notation (Unicode operators, TeX indices), which
// lib/notation.tsx renders. Apparatus marks become ⟦?…⟧ (uncertain), ⟦-…⟧
// (struck) and ⟦…⟧ (illegible), which the page styles.

const SYM = {
  alpha: 'α', beta: 'β', gamma: 'γ', delta: 'δ', epsilon: 'ε', varepsilon: 'ε', zeta: 'ζ', eta: 'η', theta: 'θ',
  vartheta: 'ϑ', iota: 'ι', kappa: 'κ', lambda: 'λ', mu: 'μ', nu: 'ν', xi: 'ξ', pi: 'π', varpi: 'ϖ', rho: 'ρ',
  varrho: 'ϱ', sigma: 'σ', varsigma: 'ς', tau: 'τ', upsilon: 'υ', phi: 'φ', varphi: 'φ', chi: 'χ', psi: 'ψ',
  omega: 'ω', Gamma: 'Γ', Delta: 'Δ', Theta: 'Θ', Lambda: 'Λ', Xi: 'Ξ', Pi: 'Π', Sigma: 'Σ', Upsilon: 'Υ',
  Phi: 'Φ', Psi: 'Ψ', Omega: 'Ω',
  le: '≤', leq: '≤', ge: '≥', geq: '≥', ne: '≠', neq: '≠', to: '→', rightarrow: '→', longrightarrow: '⟶',
  leftarrow: '←', gets: '←', mapsto: '↦', infty: '∞', times: '×', otimes: '⊗', oplus: '⊕', subset: '⊂',
  subseteq: '⊆', supset: '⊃', supseteq: '⊇', in: '∈', notin: '∉', ni: '∋', cup: '∪', cap: '∩', bigcup: '⋃',
  bigcap: '⋂', setminus: '∖', smallsetminus: '∖', simeq: '≃', cong: '≅', approx: '≈', sim: '∼', equiv: '≡',
  prod: '∏', coprod: '∐', sum: '∑', int: '∫', oint: '∮', partial: '∂', nabla: '∇', emptyset: '∅', varnothing: '∅',
  cdot: '·', circ: '∘', bullet: '•', wedge: '∧', vee: '∨', forall: '∀', exists: '∃', neg: '¬', lnot: '¬',
  Rightarrow: '⇒', Leftarrow: '⇐', Leftrightarrow: '⇔', iff: '⇔', implies: '⇒', leftrightarrow: '↔',
  hookrightarrow: '↪', twoheadrightarrow: '↠', rightrightarrows: '⇉', pm: '±', mp: '∓', star: '⋆', ast: '∗',
  vert: '|', mid: '|', Vert: '‖', langle: '⟨', rangle: '⟩', ell: 'ℓ', hbar: 'ℏ', aleph: 'ℵ', sharp: '♯',
  flat: '♭', natural: '♮', perp: '⊥', top: '⊤', bot: '⊥', dagger: '†', prime: '′', colon: ':', ldots: '…',
  dots: '…', cdots: '⋯', dotsc: '…', dotsb: '⋯', vdots: '⋮', lbrack: '[', rbrack: ']', backslash: '\\',
  lim: 'lim', varinjlim: 'lim→', varprojlim: 'lim←', injlim: 'lim→', projlim: 'lim←', log: 'log', det: 'det',
  dim: 'dim', ker: 'Ker', sin: 'sin', cos: 'cos', exp: 'exp', sup: 'sup', inf: 'inf', max: 'max', min: 'min',
  deg: 'deg', bmod: ' mod ', pmod: ' mod ', Hom: 'Hom', quad: ' ', qquad: ' ', og: '« ',
  fg: ' »', S: '§', P: '¶', oe: 'œ', OE: 'Œ', ae: 'æ', AE: 'Æ', ss: 'ß', textendash: '–', textemdash: '—',
  degree: '°', textdegree: '°', aa: 'å', o: 'ø', i: 'ı', l: 'ł', square: '□', Box: '□', blacksquare: '■',
  triangle: '△', lozenge: '◊', checkmark: '✓', leadsto: '⇝', nearrow: '↗', searrow: '↘', uparrow: '↑',
  downarrow: '↓', amalg: '⨿', diamond: '⋄', propto: '∝', lhd: '⊲', unlhd: '⊴', triangleleft: '◁', ominus: '⊖',
  boxtimes: '⊠', sqcup: '⊔', bigsqcup: '⨆', bigoplus: '⨁', bigotimes: '⨂', vartriangle: '△', Join: '⋈',
};
const DROP = new Set([
  'note', 'footnote', 'marginal', 'label', 'cite', 'index', 'ref', 'eqref', 'page', 'watermark', 'dating',
  'foldertitle', 'keywords', 'vspace', 'hspace', 'phantom', 'hphantom', 'vphantom', 'pagerange', 'linebreak',
  'newline', 'noindent', 'medskip', 'bigskip', 'smallskip', 'par', 'centering', 'small', 'footnotesize', 'large',
  'normalsize', 'displaystyle', 'textstyle', 'scriptstyle', 'left', 'right', 'big', 'Big', 'bigg', 'Bigg', 'bigl',
  'bigr', 'Bigl', 'Bigr', 'nolimits', 'limits', 'protect', 'relax', 'allowbreak', 'nobreak', 'item',
]);
// Commands whose single argument is dropped with them (the others above take none).
const DROP_ARG = new Set(['note', 'footnote', 'marginal', 'label', 'cite', 'index', 'ref', 'eqref', 'page', 'watermark', 'dating', 'foldertitle', 'keywords', 'vspace', 'hspace', 'phantom', 'hphantom', 'vphantom', 'pagerange']);
const ACCENT = { widehat: '̂', hat: '̂', tilde: '̃', widetilde: '̃', bar: '̄', overline: '̄', check: '̌', dot: '̇', ddot: '̈', mathring: '̊', vec: '⃗', breve: '̆', acute: '́', grave: '̀' };
const TEXT_ACCENT = { "'": '́', '`': '̀', '^': '̂', '"': '̈', '~': '̃', c: '̧', '=': '̄', '.': '̇', u: '̆', v: '̌', H: '̋' };

const alphabet = (base, exceptions) => (ch) => {
  if (exceptions[ch]) return exceptions[ch];
  const c = ch.codePointAt(0);
  if (c >= 65 && c <= 90) return String.fromCodePoint(base + c - 65);
  if (c >= 97 && c <= 122) return String.fromCodePoint(base + 26 + c - 97);
  return ch;
};
const ALPHA = {
  mathbb: alphabet(0x1d538, { C: 'ℂ', H: 'ℍ', N: 'ℕ', P: 'ℙ', Q: 'ℚ', R: 'ℝ', Z: 'ℤ' }),
  mathfrak: alphabet(0x1d504, { C: 'ℭ', H: 'ℌ', I: 'ℑ', R: 'ℜ', Z: 'ℨ' }),
  mathcal: alphabet(0x1d4d0, {}),
  mathscr: alphabet(0x1d4d0, {}),
  mathbf: (ch) => ch,
};
const KEEP = new Set(['emph', 'textit', 'textbf', 'textsc', 'textrm', 'textsf', 'texttt', 'mathrm', 'mathit', 'mathsf', 'mathtt', 'operatorname', 'text', 'mbox', 'hbox', 'textup', 'textnormal', 'underline', 'uline', 'boldsymbol', 'bm', 'add', 'enquote', 'textsl', 'ensuremath', 'fbox', 'boxed', 'framebox']);

function readGroup(s, i) {
  // s[i] === '{' → [content, index after the closing brace]
  let depth = 0;
  for (let k = i; k < s.length; k++) {
    if (s[k] === '\\') { k++; continue; }
    if (s[k] === '{') depth++;
    else if (s[k] === '}' && --depth === 0) return [s.slice(i + 1, k), k + 1];
  }
  return [s.slice(i + 1), s.length];
}
function skipSpaces(s, i) {
  while (i < s.length && /[ \t]/.test(s[i])) i++;
  return i;
}
function readArg(s, i) {
  i = skipSpaces(s, i);
  if (s[i] === '{') return readGroup(s, i);
  if (s[i] === '\\') {
    const m = /^\\([A-Za-z]+|.)/.exec(s.slice(i));
    return [m[0], i + m[0].length];
  }
  const ch = String.fromCodePoint(s.codePointAt(i) ?? 32);
  return [ch, i + ch.length];
}
function readOpt(s, i) {
  const j = skipSpaces(s, i);
  if (s[j] !== '[') return [null, i];
  let depth = 0;
  for (let k = j; k < s.length; k++) {
    if (s[k] === '{') depth++;
    else if (s[k] === '}') depth--;
    else if (s[k] === ']' && depth === 0) return [s.slice(j + 1, k), k + 1];
  }
  return [null, i];
}
const accent = (body, mark) => {
  const chars = [...body];
  if (!chars.length) return mark;
  return chars.join('') + mark;
};

export function hybrid(src) {
  const out = conv(src.replace(/(^|[^\\])%.*$/gm, '$1'));
  return out
    .replace(/---/g, '—')
    .replace(/--/g, '–')
    .replace(/``/g, '“')
    .replace(/''/g, '”')
    .replace(/[ \t\r\n]+/g, ' ')
    .replace(/\s+([,.;)])/g, (m, p) => (p === ';' ? ' ;' : p))
    .replace(/\(\s+/g, '(')
    .trim();
}

function conv(s) {
  let out = '';
  const emit = (r) => {
    if (/[_^]$/.test(out) && [...r].length > 1) out += `{${r}}`;
    else out += r;
  };
  for (let i = 0; i < s.length; ) {
    const c = s[i];
    if (c === '\\') {
      const m = /^\\([A-Za-z]+|.)\*?/.exec(s.slice(i));
      if (!m) { i++; continue; }
      const name = m[1];
      let j = i + m[0].length;
      if (/^[A-Za-z]+$/.test(name) === false) {
        // one-character commands
        if (TEXT_ACCENT[name] && name !== '^' && name !== '~' && /[A-Za-z{]/.test(s[j] ?? '')) {
          const [a, k] = readArg(s, j);
          out += accent(conv(a), TEXT_ACCENT[name]);
          i = k;
          continue;
        }
        if (name === '^' || name === '~') {
          const [a, k] = readArg(s, j);
          out += accent(conv(a), TEXT_ACCENT[name]);
          i = k;
          continue;
        }
        out += { ',': ' ', ';': ' ', ':': ' ', '!': '', ' ': ' ', '\\': ' ', '{': '{', '}': '}', '%': '%', '&': '&', '_': '_', '#': '#', $: '$', '|': '‖', '/': '' }[name] ?? '';
        i = j;
        continue;
      }
      if (name === 'begin' || name === 'end') {
        const [, k] = readArg(s, j);
        i = k;
        continue;
      }
      if (name === 'uncertain') {
        const [a, k] = readArg(s, j);
        out += `⟦?${conv(a)}⟧`;
        i = k;
        continue;
      }
      if (name === 'struck') {
        const [a, k] = readArg(s, j);
        out += `⟦-${conv(a)}⟧`;
        i = k;
        continue;
      }
      if (name === 'ill') {
        let k = skipSpaces(s, j);
        if (s.slice(k, k + 2) === '{}') k += 2;
        else k = j;
        out += '⟦…⟧';
        i = k;
        continue;
      }
      if (name === 'supplied') {
        const [a, k] = readArg(s, j);
        out += `[${conv(a)}]`;
        i = k;
        continue;
      }
      if (DROP.has(name)) {
        let k = j;
        if (DROP_ARG.has(name)) {
          [, k] = readOpt(s, k);
          k = skipSpaces(s, k);
          if (s[k] === '{') [, k] = readGroup(s, k);
        }
        i = k;
        continue;
      }
      if (name === 'item') {
        i = j;
        continue;
      }
      if (KEEP.has(name)) {
        const [a, k] = readArg(s, j);
        emit(conv(a));
        i = k;
        continue;
      }
      if (name === 'textsuperscript') {
        const [a, k] = readArg(s, j);
        out += `^{${conv(a)}}`;
        i = k;
        continue;
      }
      if (name === 'textsubscript') {
        const [a, k] = readArg(s, j);
        out += `_{${conv(a)}}`;
        i = k;
        continue;
      }
      if (ALPHA[name]) {
        const [a, k] = readArg(s, j);
        emit([...conv(a)].map(ALPHA[name]).join(''));
        i = k;
        continue;
      }
      if (ACCENT[name]) {
        const [a, k] = readArg(s, j);
        emit(accent(conv(a), ACCENT[name]));
        i = k;
        continue;
      }
      if (name === 'frac' || name === 'dfrac' || name === 'tfrac') {
        const [a, k] = readArg(s, j);
        const [b, k2] = readArg(s, k);
        const A = conv(a);
        const B = conv(b);
        const VULGAR = { '1/2': '½', '1/3': '⅓', '2/3': '⅔', '1/4': '¼', '3/4': '¾' };
        const plain = `${A}/${B}`;
        emit(VULGAR[plain] ?? `${[...A].length > 1 ? `(${A})` : A}/${[...B].length > 1 ? `(${B})` : B}`);
        i = k2;
        continue;
      }
      if (name === 'sqrt') {
        const [, k0] = readOpt(s, j);
        const [a, k] = readArg(s, k0);
        const A = conv(a);
        emit(`√${[...A].length > 1 ? `(${A})` : A}`);
        i = k;
        continue;
      }
      if (name === 'xrightarrow' || name === 'xleftarrow' || name === 'overset' || name === 'underset' || name === 'stackrel') {
        const [, k0] = readOpt(s, j);
        const [a, k] = readArg(s, k0);
        if (name.startsWith('x')) {
          out += name === 'xrightarrow' ? '→' : '←';
          i = k;
        } else {
          const [b, k2] = readArg(s, k);
          emit(conv(b));
          i = k2;
          void a;
        }
        continue;
      }
      if (name === 'not') {
        const [a, k] = readArg(s, j);
        out += `${conv(a)}̸`;
        i = k;
        continue;
      }
      if (SYM[name] !== undefined) {
        let k = j;
        if (s.slice(k, k + 2) === '{}') k += 2;
        emit(SYM[name]);
        // A control word swallows the following space in TeX; keep one between words.
        if (/^[A-Za-z]/.test(SYM[name].slice(-1)) && /^ [A-Za-z0-9]/.test(s.slice(k, k + 2))) out += ' ';
        i = k;
        continue;
      }
      // Unknown command: keep its argument, if any.
      let k = skipSpaces(s, j);
      if (s[k] === '{') {
        const [a, k2] = readGroup(s, k);
        emit(conv(a));
        i = k2;
      } else i = j;
      continue;
    }
    if (c === '{') {
      const [a, k] = readGroup(s, i);
      const inner = conv(a);
      if (/[_^]$/.test(out)) out += `{${inner}}`;
      else out += inner;
      i = k;
      continue;
    }
    if (c === '}' || c === '$') { i++; continue; }
    if (c === '~') { out += ' '; i++; continue; }
    if (c === '&') { out += ' '; i++; continue; }
    out += c;
    i++;
  }
  return out;
}

// ---------------------------------------------------------------------------
// Files

const byShelfmark = (a, b) => {
  const [a0, a1 = '0'] = a.split('-');
  const [b0, b1 = '0'] = b.split('-');
  return Number(a0) - Number(b0) || Number(a1) - Number(b1);
};
const batchFiles = (cote) => {
  const dir = resolve(T, cote);
  if (!existsSync(dir)) return [];
  return readdirSync(dir)
    .filter((f) => /^batch-\d+\.fr\.tex$/.test(f))
    .sort()
    .map((f) => ({ name: f, batch: Number(/\d+/.exec(f)[0]), text: readFileSync(resolve(dir, f), 'utf8') }));
};
const modernOf = (cote) => {
  const f = resolve(T, cote, `${cote}.modern.tex`);
  return existsSync(f) ? readFileSync(f, 'utf8') : null;
};

// Strip a balanced \cmd{...} (and an optional [..]) wherever it occurs, across lines.
function stripCmd(s, names) {
  const re = new RegExp(`\\\\(${names.join('|')})\\*?(?![A-Za-z])`, 'g');
  let out = '';
  let last = 0;
  for (let m; (m = re.exec(s)); ) {
    out += s.slice(last, m.index);
    let k = m.index + m[0].length;
    [, k] = readOpt(s, k);
    k = skipSpaces(s, k);
    if (s[k] === '{') [, k] = readGroup(s, k);
    last = k;
    re.lastIndex = k;
  }
  return out + s.slice(last);
}

// ---------------------------------------------------------------------------
// The author's tables of contents and plans.
//
// Found two ways: any \section whose title names a table, a sommaire or a plan
// (« Plan des notes », « Table des matières », « V — Plan. Notations »…), and
// the tables listed below, which the transcription opens with a note rather
// than a section, or whose span the section heading does not delimit. Each
// span is copied as it stands: his numbering, his page numbers, the apparatus
// (uncertain, struck, illegible) kept, the transcribers' notes dropped.

const TOC_TITLE = /table des matières|sommaire|(^|[\s—[«(])plan(?=$|[\s.:\]»,)])/i;
const NOT_TOC = /plan (affine|projectif|complexe|tangent|réel)/i;
// Editorial « plans » that are statements, not a table: left out.
const TOC_SKIP = new Set(['98']);

const TOC_SPANS = [
  { cote: '25', file: 'batch-07.fr.tex', start: /semble être le plan actuel/, end: /^Le 25\. risque/, title: 'Plan des paragraphes 20 à 27 d’EGA IV, dans la lettre à Dieudonné' },
  { cote: '26', file: 'batch-01.fr.tex', start: /\\section\*\{V — Plan\. Notations\}/, end: /\\subsection\*\{Dactylographie, p\. 32\}/, title: 'V — Plan. Notations' },
  { cote: '26', file: 'batch-01.fr.tex', start: /\\subsection\*\{C\) Méthodes projectives/, end: /\\subsection\*\{Dactylographie, p\. 31\}/, continues: true, keepFirst: true },
  { cote: '48', file: 'batch-01.fr.tex', start: /\\section\*\{EGA Chap\.\\ VI/, end: /\\subsection\*\{Réf\.\}/, title: 'Plan EGA VII [EGA Chap. VI — Schémas en groupes et torseurs]' },
  { cote: '79', file: 'batch-01.fr.tex', start: /Table des matières de sa main/, end: /^\\subsection\{I\. Construction/, title: 'Table des matières' },
  { cote: '134-2', file: 'batch-01.fr.tex', start: /\\section\{The Modelizing Story\}/, end: /\\page\{13\}/, title: 'The Modelizing Story — plan et tables des matières provisoires' },
  { cote: '144', file: 'batch-03.fr.tex', start: /table des matières de la \\og Rétrospection/, end: /\\page\{51\}/, title: 'Table des matières de la « Rétrospection »' },
];

function tocEntries(raw) {
  let s = raw.replace(/(^|[^\\])%.*$/gm, '$1');
  s = s.replace(/\\begin\{(tikzcd|tikzpicture|tabular|array|equation\*?|align\*?|gather\*?)\}[\s\S]*?\\end\{\1\}/g, '');
  s = s.replace(/\\\[[\s\S]*?\\\]/g, '');
  s = stripCmd(s, ['note', 'footnote', 'page']);
  // A marginal that is part of the sentence (« \marginal{Premier} th. de… ») is
  // kept; one standing on its own line is an aside and goes.
  s = s.replace(/^\s*\\marginal\b/gm, '\\note');
  s = stripCmd(s, ['note']);
  s = s.replace(/\\(begin|end)\{quote\}/g, '\n\n');

  const entries = [];
  const counters = [];
  let depth = 0;
  let buf = null; // { level, label, raw }
  const flush = () => {
    if (!buf) return;
    const text = hybrid(buf.raw);
    if (text) {
      const m = /\s*(?:—|–| )\s*(?:p\.\s*)?(\d+[a-z]?(?:\s*bis)?['′]?)\s*\.?\s*$/.exec(text);
      const e = { level: buf.level };
      if (buf.label) e.label = buf.label;
      if (buf.heading) e.heading = true;
      e.text = (m ? text.slice(0, m.index) : text).replace(/ /g, ' ').replace(/\s+/g, ' ').trim();
      if (m) e.page = m[1].replace(/\s+/g, ' ');
      if (e.text || e.page) entries.push(e);
    }
    buf = null;
  };
  const lines = s.split('\n');
  for (const line of lines) {
    const t = line.trim();
    const b = /^\\begin\{(enumerate|itemize|description)\}/.exec(t);
    if (b) {
      flush();
      depth++;
      counters[depth] = { n: 0, numbered: b[1] === 'enumerate' };
      continue;
    }
    if (/^\\end\{(enumerate|itemize|description)\}/.test(t)) {
      flush();
      depth = Math.max(0, depth - 1);
      continue;
    }
    const sec = /^\\(sub)*section\*?\{/.exec(t);
    if (sec) {
      flush();
      const [title] = readGroup(t, t.indexOf('{'));
      buf = { level: 0, heading: true, raw: title };
      flush();
      continue;
    }
    const it = /^\\item\b/.exec(t);
    if (it && depth > 0) {
      flush();
      let rest = t.slice(5);
      let [label, k] = readOpt(rest, 0);
      rest = rest.slice(k);
      const ctr = counters[depth];
      ctr.n++;
      if (label === null && ctr.numbered) label = `${ctr.n}.`;
      buf = { level: depth, label: label === null ? undefined : hybrid(label), raw: rest };
      continue;
    }
    if (!t) {
      if (depth === 0) flush();
      continue;
    }
    if (buf) buf.raw += `\n${line}`;
    else buf = { level: depth, raw: line };
  }
  flush();
  // Outside any list, short lines without a page number that open a list are
  // the table's own title (« Structure à l'∞ des M_{g,ν} », « Picard »).
  for (let k = entries.length - 2; k >= 0; k--) {
    const e = entries[k];
    if (e.level === 0 && !e.page && !e.label && entries[k + 1].level > 0) e.heading = true;
  }
  // …and so are the lines that open the table, up to its first heading.
  const firstHeading = entries.findIndex((e) => e.heading);
  for (let k = 0; k < firstHeading; k++) if (entries[k].level === 0 && !entries[k].page) entries[k].heading = true;
  // A transcriber's sentence left in the body (« Au bas de la page, un schéma… »).
  return entries.filter((e) => !/^(Au bas de la page|En bas de (la )?page|Sous la liste)/i.test(e.text));
}

/**
 * The fonds pages a span covers: its \\page markers, and the page in force where
 * it starts if anything but blank lines and notes comes before its first marker.
 */
function spanPages(lines, a, b) {
  const span = lines.slice(a + 1, b).join('\n');
  const own = pagesIn(span);
  const head = stripCmd(span.split(/\\page\{/)[0], ['note']).trim();
  const inForce = pagesIn(lines.slice(0, a + 1).join('\n')).pop();
  return [...new Set([...(head && inForce ? [inForce] : []), ...own])];
}
function pagesIn(raw) {
  return [...raw.matchAll(/\\page\{([^}]+)\}/g)].map((m) => m[1]);
}

function tocsOf(cote, files) {
  const tocs = [];
  const used = new Set();
  for (const sp of TOC_SPANS.filter((x) => x.cote === cote)) {
    const f = files.find((x) => x.name === sp.file);
    if (!f) continue;
    const lines = f.text.split('\n');
    const a = lines.findIndex((l) => sp.start.test(l));
    if (a < 0) continue;
    let b = lines.findIndex((l, k) => k > a && (sp.end.test(l) || /^\\section\*?\{/.test(l.trim())));
    if (b < 0) b = lines.length;
    const startLine = sp.keepFirst ? a : a + 1;
    const raw = lines.slice(startLine, b).join('\n');
    used.add(`${f.name}:${a}`);
    const entries = tocEntries(raw);
    const pages = spanPages(lines, sp.keepFirst ? a - 1 : a, b);
    if (sp.continues && tocs.length) {
      const prev = tocs[tocs.length - 1];
      prev.entries.push(...entries);
      prev.pages = [...new Set([...prev.pages, ...pages])];
      continue;
    }
    tocs.push({ title: sp.title, batch: f.batch, pages, entries, where: `transcripts/${cote}/${f.name}:${a + 1}` });
  }
  if (!TOC_SKIP.has(cote)) {
    for (const f of files) {
      const lines = f.text.split('\n');
      lines.forEach((l, a) => {
        const m = /^\\section\*?\{(.*)\}\s*$/.exec(l.trim());
        if (!m || used.has(`${f.name}:${a}`)) return;
        const title = hybrid(m[1]);
        if (!TOC_TITLE.test(title) || NOT_TOC.test(title)) return;
        if (TOC_SPANS.some((x) => x.cote === cote && x.file === f.name && x.start.test(l))) return;
        let b = lines.findIndex((x, k) => k > a && /^\\section\*?\{/.test(x.trim()));
        if (b < 0) b = lines.length;
        const span = lines.slice(a + 1, b).join('\n');
        const entries = tocEntries(span);
        if (entries.filter((e) => !e.heading).length < 2) return;
        tocs.push({ title, batch: f.batch, pages: spanPages(lines, a, b), entries, where: `transcripts/${cote}/${f.name}:${a + 1}` });
      });
    }
  }
  for (const t of tocs) if (!t.pages.length) delete t.pages;
  return tocs;
}

// ---------------------------------------------------------------------------
// The other fields

const LANG = { fr: 'français', en: 'anglais', de: 'allemand', it: 'italien', la: 'latin', ru: 'russe' };

/** Title and typology: the inventory writes « Title : notes manuscrites (s.d.), lettre (1953). » */
function splitTitle(t) {
  const s = t.replace(/\.\s*$/, '');
  const k = s.lastIndexOf(' : ');
  const typology = /manuscrit|tapuscrit|lettre|copie|imprim|dactylo|carte|photocop|brouillon|cahier|notes|document|tiré|épreuve|coupure/i;
  if (k > 0 && typology.test(s.slice(k + 3))) return { title: s.slice(0, k), typology: s.slice(k + 3) };
  return { title: s, typology: null };
}
function support(typology) {
  if (!typology) return [];
  const out = [];
  const add = (re, label) => re.test(typology) && !out.includes(label) && out.push(label);
  add(/notes? manuscrites?|manuscrit/i, 'manuscrit');
  add(/tapuscrit|dactylographi/i, 'tapuscrit');
  add(/copies? de tapuscrit|copies? de notes|copies? de lettre|photocopie|copies?/i, 'copies');
  add(/lettres?|correspondance/i, 'lettres');
  add(/imprim|tiré à part|épreuve|coupure/i, 'imprimés');
  return out;
}

function invertName(n) {
  const name = n.replace(/^Pr\.\s+/, '').trim();
  if (/[()]/.test(name)) return null; // an institution, not a person
  const KEEP_ORDER = /^(Hoàng|Lê|Nguyễn|Trần|Phạm)\s/;
  const parts = name.split(/\s+/);
  if (parts.length < 2 || KEEP_ORDER.test(name)) return name;
  const last = parts.pop();
  return `${last}, ${parts.join(' ')}`;
}
function namesOf(cote) {
  const raw = [
    ...PEOPLE.filter((r) => r.folder === cote).map((r) => r.person),
    ...LETTERS.filter((r) => r.folder === cote && r.correspondent).map((r) => r.correspondent),
  ];
  // « A. Delzant » and « Antoine Delzant » are one person: keep the fuller form.
  const byKey = new Map();
  for (const n of raw) {
    const inv = invertName(n);
    if (!inv) continue;
    const [sur, given = ''] = inv.split(', ');
    const key = `${sur}|${given[0] ?? ''}`;
    const prev = byKey.get(key);
    if (!prev || inv.length > prev.length) byKey.set(key, inv);
  }
  return [...byKey.values()].sort((a, b) => a.localeCompare(b, 'fr'));
}

function resumeOf(modern) {
  if (!modern) return null;
  let body = /\\begin\{resume\}([\s\S]*?)\\end\{resume\}/.exec(modern)?.[1];
  if (!body) body = /\\section\*?\{Résumé\}([\s\S]*?)(\\section|\\keywords)/.exec(modern)?.[1];
  if (!body) return null;
  body = body.replace(/(^|[^\\])%.*$/gm, '$1');
  body = body.split('\\keywords')[0];
  body = stripCmd(body, ['footnote', 'note', 'marginal', 'label', 'cite']);
  const paras = body
    .split(/\n\s*\n/)
    .map((p) => hybrid(p))
    .filter((p) => p.length > 0);
  const out = [];
  let n = 0;
  for (const p of paras) {
    out.push(p);
    n += p.length;
    if (n >= 600 || out.length >= 2) break;
  }
  return out;
}
const keywordsOf = (modern) => {
  const m = modern && /\\keywords\{([^}]*)\}/.exec(modern);
  return m ? m[1].split(',').map((k) => k.trim()).filter(Boolean) : [];
};

function authorPagination(files) {
  const nums = [];
  for (const f of files) {
    for (const m of f.text.matchAll(/p\.(?:~|\s)*(\d+)['′]?\s*de l['’]auteur/g)) nums.push(Number(m[1]));
    for (const m of f.text.matchAll(/numérotée?s?\s*\(?(\d+)\)?\s*par l['’]auteur/g)) nums.push(Number(m[1]));
  }
  if (nums.length < 2) return null;
  return { max: Math.max(...nums), notes: nums.length };
}
function transcribedPages(files) {
  const set = new Set();
  for (const f of files) for (const m of f.text.matchAll(/\\page\{([^}]+)\}/g)) set.add(m[1].trim());
  return set.size;
}

const HISTORIQUE =
  'Don d’Alexandre Grothendieck à Jean Malgoire en 1990 et 1995 ; dépôt à l’université de Montpellier en 2010, don en 2012.';

const editionsFor = (cote) =>
  EDITIONS.filter((e) => e.cotes.includes(cote)).map((e) => ({
    id: e.id,
    title: e.title,
    editors: e.editors ?? null,
    year: e.year ?? null,
    venue: e.venue ?? null,
    url: e.url ?? null,
    kind: e.kind,
    documents: (e.documents ?? []).filter((d) => d.cote === cote).map((d) => ({ title: d.title, url: d.url })),
  }));

// ---------------------------------------------------------------------------
// Notices

const groupOf = new Map();
for (const g of GROUPS) for (const c of g.cotes) groupOf.set(c, g);
const haveTranscripts = existsSync(T);

const notices = COTES.slice()
  .sort((a, b) => byShelfmark(a.id, b.id))
  .map((c) => {
    const files = haveTranscripts ? batchFiles(c.id) : [];
    const modern = haveTranscripts ? modernOf(c.id) : null;
    const h = HAND.get(c.id);
    const { title, typology } = splitTitle(c.title);
    const g = groupOf.get(c.id);
    const leaves = LEAVES.filter((r) => r.folder === c.id).map((r) => ({
      page: r.page,
      written: r.written,
      iso: r.iso ?? null,
      kind: r.kind,
      hand: r.hand,
      context: r.context,
      batch: r.batch,
    }));
    const dating = DATINGS.find((r) => r.folder === c.id);
    const pagesT = files.length ? transcribedPages(files) : h?.pages ?? 0;
    const n = {
      cote: c.id,
      title,
      inventoryTitle: c.title,
      typology,
      date: c.date || 's.d.',
      leaves,
      proposed: dating
        ? { from: dating.from, to: dating.to, confidence: dating.confidence, summary: dating.summary }
        : null,
      physical: {
        support: support(typology),
        pages: c.pages,
        transcribed: pagesT,
        batches: files.length,
        author: authorPagination(files),
        diagrams: h?.diagrams ?? 0,
        drawings: h?.drawings ?? 0,
        math: h ? Math.round(h.math * 100) : null,
      },
      languages: (h?.languages ?? []).map((l) => LANG[l] ?? l),
      resume: resumeOf(modern),
      modern: Boolean(modern),
      tocs: files.length ? tocsOf(c.id, files) : [],
      historique: HISTORIQUE,
      group: g ? { id: g.id, title: g.title, date: g.date, cotes: g.cotes.filter((x) => x !== c.id) } : null,
      editions: editionsFor(c.id),
      subjects: keywordsOf(modern),
      names: namesOf(c.id),
      findings: FINDINGS.get(c.id) ?? 0,
      proofs: PROOFS.get(c.id) ?? 0,
    };
    return n;
  });

// ---------------------------------------------------------------------------
// Books that the inventory spreads over several folders.

const cote = (id) => COTES.find((c) => c.id === id);
const range = (prefix, a, b) => Array.from({ length: b - a + 1 }, (_, k) => `${prefix}-${a + k}`);
const dateOf = (typology) => /\(([^()]*\d{4}[^()]*)\)/.exec(typology ?? '')?.[1] ?? null;

function chaptersFromInventory(ids, clean) {
  return ids.map((id) => {
    const c = cote(id);
    const { title, typology } = splitTitle(c.title);
    return { cote: id, text: clean(title), pages: c.pages, date: dateOf(typology) };
  });
}

const DERIVATEURS = [
  ['157-1', 'I', 'Généralités sur les (pré)dérivateurs'],
  ['157-1', 'II', 'Cofinalité (à droite et à gauche) (préliminaire à la cofinalité cohomologique)'],
  ['157-1', 'III', 'Hom externes dans les dérivateurs'],
  ['157-1', 'IV', 'Diagrammes substantiels'],
  ['157-2', 'V', 'Catégories de chemins et localisation'],
  ['157-2', 'VI', 'HOT'],
  ['157-2', 'VII', 'Catégories de chemins (2)'],
  ['157-2', 'VIII', '1-types d’homotopie relatifs : leur intégration…'],
  ['157-3', 'IX', 'Retour sur les catégories de fractions MW^{-1}, comparaison avec Quillen'],
  ['157-3', 'X', 'Comparaison de Cat avec Δ̂'],
  ['157-3', 'XI', 'Hot-fibrations, foncteurs propres et foncteurs lisses etc. (dans Cat)'],
  ['157-3', 'XII', 'Caractérisation de W_∞. Foncteurs W-propres, foncteurs W-lisses etc. Sommes amalgamées et carrés W-cocartésiens dans Cat'],
  ['157-4', 'XIII', 'Catégories de modèles (1)'],
  ['157-4', 'XIV', 'Carrés h-cartésiens et h-cocartésiens'],
  ['157-4', 'XV', 'Théorèmes de factorisation. (Modèles (2))'],
  ['157-4', 'XVI', 'Localiseurs fondamentaux dans Cat'],
  ['157-5', 'XVII', 'Catégories à fibrations et à cofibrations. (Modèles (3))'],
  ['157-5', 'XVIII', 'Catégories et ensembles accessibles'],
  ['157-5', 'XIX', 'Modèles (4)'],
];

const books = [
  {
    id: 'geometrie-des-formes',
    title: 'Vers une géométrie des formes',
    date: '1986',
    cotes: range('156', 1, 9),
    source: 'd’après l’inventaire (titres des chapitres et dates portés sur les chemises)',
    edition: null,
    entries: chaptersFromInventory(range('156', 1, 9), (t) => t.replace(/^\[Chapitre\]\s*/, '')).map((e) => {
      const m = /^([IVX]+(?: et [IVX]+ bis)?)\.\s*(.*)$/.exec(e.text);
      return m ? { ...e, label: m[1], text: m[2] } : e;
    }),
  },
  {
    id: 'poursuite-des-champs',
    title: 'À la poursuite des champs (Pursuing Stacks)',
    date: '1983',
    cotes: range('134', 2, 8),
    source: 'd’après l’inventaire (chapitres, pages de l’auteur et dates de frappe)',
    edition: 'Édition par Georges Maltsiniotis, Société mathématique de France, Documents mathématiques 20 (vol. I, 2022), en partie ; la table des matières provisoire de l’auteur est dans la notice de la cote 134-2.',
    entries: chaptersFromInventory(range('134', 2, 8), (t) => t.replace(/^\[|\]$/g, '')).map((e) => {
      const m = /^Chapitre ([IVX]+)\s*(\([^)]*\))?\s*:\s*(.*)$/.exec(e.text);
      return m ? { ...e, label: m[1], text: m[3], range: m[2]?.replace(/[()]/g, '') ?? null } : e;
    }).map((e) => {
      // « Take off (pages 1 à 65) et table des matières provisoire »
      const m = /^(.*?)\s*\((pages [^)]*)\)\s*(.*)$/.exec(e.text);
      return m && !e.range ? { ...e, text: `${m[1]} ${m[3]}`.trim(), range: m[2] } : e;
    }),
  },
  {
    id: 'longue-marche',
    title: 'La Longue Marche à travers la théorie de Galois',
    date: '[à partir de 1978 – à partir de 1982]',
    cotes: range('140', 1, 4),
    source: 'd’après l’inventaire (parties et pages de l’auteur) ; seule la cote 140-1 est transcrite ici',
    edition:
      'Édition des § 1 à 37 par Jean Malgoire, université Montpellier II, 1995. Sa table des paragraphes n’est pas reprise ici ; une table des matières est en ligne sur le site du Grothendieck Circle.',
    editionUrl: 'https://webusers.imj-prg.fr/~leila.schneps/grothendieckcircle/unpubtexts.php',
    entries: [
      { cote: '140-1', text: '« Longue Marche » [brouillon]', pages: cote('140-1').pages, date: null },
      { cote: '140-2', text: 'La « Longue Marche » à travers la théorie de Galois…', range: 'pages 1 à 292, dont table des matières', pages: cote('140-2').pages, date: null },
      { cote: '140-3', text: 'Deuxième partie : variations sur l’équation des lacets', range: 'pages 293 à 650, dont table des matières', pages: cote('140-3').pages, date: null },
      { cote: '140-4', text: '[suite]', range: 'pages 650 bis à 787, dont table des matières', pages: cote('140-4').pages, date: null },
    ],
  },
  {
    id: 'derivateurs',
    title: 'Les Dérivateurs',
    date: 'octobre 1990 – première moitié de 1991',
    cotes: range('157', 1, 5),
    source:
      'd’après l’édition en ligne de M. Künzer, J. Malgoire et G. Maltsiniotis (table des matières établie par les éditeurs), chapitres répartis sur les cotes selon l’inventaire',
    edition: 'Manuscrit de 1976 pages selon les éditeurs, écrit entre octobre 1990 et la première moitié de 1991.',
    editionUrl: 'https://webusers.imj-prg.fr/~georges.maltsiniotis/groth/Derivateurs.html',
    entries: DERIVATEURS.map(([c, label, text]) => ({ cote: c, label, text })),
  },
].map((b) => ({ ...b, pages: b.cotes.reduce((s, id) => s + (cote(id)?.pages ?? 0), 0) }));

const out = {
  $why:
    'Generated by `npm run notices` (scripts/notices.mjs) from the inventory, the transcriptions and the registries in src/content — do not edit by hand. First pass, not checked against the facsimile.',
  built: new Date().toISOString().slice(0, 10),
  transcripts: haveTranscripts,
  books,
  notices,
};
if (!haveTranscripts && existsSync(OUT)) {
  console.log('notices: transcripts/ absent, keeping the committed notices.json');
} else {
  writeFileSync(OUT, `${JSON.stringify(out, null, 1)}\n`);
  const tocs = notices.filter((n) => n.tocs.length);
  console.log(
    `notices: ${notices.length} folders, ${books.length} books, tables of contents in ${tocs.length} folders: ${tocs.map((n) => `${n.cote} (${n.tocs.map((t) => t.entries.length).join('+')})`).join(', ')}`,
  );
}
