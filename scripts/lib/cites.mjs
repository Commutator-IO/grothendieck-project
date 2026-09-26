/**
 * What a batch cites of his published work, shared by the citation map
 * (`npm run fonds-maps`) and the index (`npm run fonds-index`), so that the
 * two can never disagree about what counts as a citation.
 */
/** The page's own text: no header comments, no transcriber's notes. */
export function leaves(s) {
  s = s
    .split('\n')
    .filter((l) => !l.trimStart().startsWith('%'))
    .join('\n');
  let out = '';
  let i = 0;
  for (;;) {
    const j = s.indexOf('\\note{', i);
    if (j < 0) return out + s.slice(i);
    out += s.slice(i, j);
    let k = j + 6;
    let d = 1;
    while (k < s.length && d > 0) {
      if (s[k] === '\\') k += 2;
      else {
        if (s[k] === '{') d++;
        else if (s[k] === '}') d--;
        k++;
      }
    }
    i = k;
  }
}
export const ROMAN = { I: 1, II: 2, III: 3, IV: 4, V: 5, VI: 6, VII: 7 };
/**
 * « SGA 4 VIII », « SGA A », « SGAD XI », « EGA IV 16.9 », « EGA 0_IV »,
 * « FGA », « TDTE ». A volume given only by a year (« SGA 1962 ») or by a
 * lone roman numeral that could be an exposé (« SGA X ») is not resolved.
 */
export const REF = /\b(SGA|EGA|FGA|TDTE)(?![A-Za-z])\s*(?:\\,|~|\\ )?\s*(0_?\{?(?:III|IV)\}?|[1-7](?![0-9])|A\b|D\b|(?:VII|VI|IV|V|III|II|I)\b)?(?:[\s,.~]|\\,|\\ )*((?:[IVX]{1,5}|[0-9]{1,2})(?:\.[0-9]+)*)?/g;
export function unit(m) {
  const [, kind, vol, rest] = m;
  if (kind === 'FGA' || kind === 'TDTE') return { unit: 'FGA', ref: m[0].trim() };
  if (kind === 'SGA') {
    let v = vol;
    if (!v && m.input.slice(m.index, m.index + 5) === 'SGAD ') v = 'D';
    if (v === 'A') v = '4';
    if (v === 'D') v = '3';
    if (v && ROMAN[v]) v = String(ROMAN[v]);
    if (!v || !/^[1-7]$/.test(v)) return null;
    return { unit: `SGA ${v}`, ref: `SGA ${v}${rest ? ` ${rest}` : ''}` };
  }
  // EGA
  if (!vol) return null;
  const v = vol.replace(/[_{}]/g, '').replace(/^0/, '0_');
  const u = v.startsWith('0_') ? `EGA ${v}` : ROMAN[v] ? `EGA ${v}` : null;
  return u ? { unit: u, ref: `${u}${rest ? ` ${rest}` : ''}` } : null;
}
