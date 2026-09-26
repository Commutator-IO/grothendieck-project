/**
 * The distinct symbols of a piece of TeX mathematics, for ranking diagrams and
 * formulas by how much they carry.
 *
 * A symbol is what a reader has to tell apart: a letter, a digit, an operator
 * sign, a named symbol (\otimes, \varprojlim), and a letter in a given
 * alphabet — \mathcal{C} is not C, and \underline{C} is his notation for a
 * category, so it is not \mathcal{C} either. Layout is not a symbol: \left,
 * \quad, \begin, \text and the spacing commands are dropped; a word in
 * \mathrm or \operatorname counts once, as a name.
 *
 * Shared by scripts/diagrams.mjs and scripts/formulas.mjs, so that a diagram
 * and a formula are scored the same way.
 */
const LAYOUT = new Set(
  (
    'left right big Big bigg Bigg bigl bigr Bigl Bigr biggl biggr middle quad qquad begin end arrow tag label ' +
    'hspace vspace phantom hphantom vphantom displaystyle textstyle scriptstyle scriptscriptstyle limits nolimits ' +
    'text textrm textit textbf emph mbox ensuremath substack stackrel overset underset frac dfrac tfrac binom ' +
    'sqrt nonumber notag cr hline kern mkern mathstrut strut rlap llap smash ill uncertain struck add supplied'
  ).split(' '),
);
const ALPHABETS = new Set(['mathcal', 'mathbb', 'mathfrak', 'mathscr', 'mathbf', 'mathsf', 'mathit', 'boldsymbol', 'underline', 'overline', 'widetilde', 'tilde', 'widehat', 'hat', 'bar', 'check', 'dot', 'ddot', 'vec', 'mathring']);
const NAMES = new Set(['mathrm', 'operatorname']);

/** The argument of a macro at index i (s[i] === '{'), and the index after it. */
function arg(s, i) {
  if (s[i] !== '{') return [s[i] ?? '', i + 1];
  let d = 0;
  for (let j = i; j < s.length; j++) {
    if (s[j] === '\\') {
      j++;
      continue;
    }
    if (s[j] === '{') d++;
    else if (s[j] === '}' && --d === 0) return [s.slice(i + 1, j), j + 1];
  }
  return [s.slice(i + 1), s.length];
}

export function symbols(tex) {
  const out = new Set();
  const walk = (s, wrap) => {
    for (let i = 0; i < s.length; ) {
      const c = s[i];
      if (c === '\\') {
        const m = /^\\([a-zA-Z]+|[\s\S]?)/.exec(s.slice(i));
        const name = m[1];
        i += m[0].length;
        while (s[i] === ' ') i++;
        if (ALPHABETS.has(name)) {
          const [a, j] = arg(s, i);
          walk(a, `${wrap}${name}:`);
          i = j;
        } else if (NAMES.has(name)) {
          const [a, j] = arg(s, i);
          out.add(`name:${a.replace(/\s+/g, '')}`);
          i = j;
        } else if (name === 'text' || name === 'textrm' || name === 'mbox') {
          const [, j] = arg(s, i);
          i = j;
        } else if (/^[a-zA-Z]+$/.test(name) && !LAYOUT.has(name)) {
          out.add(`${wrap}\\${name}`);
        }
        continue;
      }
      if (/[A-Za-z0-9]/.test(c) || /[+\-=<>|/*!()[\]]/.test(c)) out.add(`${wrap}${c}`);
      i++;
    }
  };
  walk(tex, '');
  return out;
}
