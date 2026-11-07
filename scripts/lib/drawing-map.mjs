/**
 * Which redrawn figure (#73) belongs to which `\drawing{}` of a transcription.
 *
 * `transcripts/<cote>/drawings/drawings.json` lists the figures vectorised from
 * a folder, each with the batch it comes from and the description it was made
 * from, copied from the `\drawing{}` it redraws. The ids (`08-3`) are not the
 * ordinal of the `\drawing` in the batch: some marks were skipped, so the match
 * is by the description, whitespace aside, in order of appearance. The
 * transcription is never edited; the k-th `\drawing{}` of a batch simply gets
 * the figure whose description it carries.
 */
import { existsSync, readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const squash = (s) => s.split(/\s+/).filter(Boolean).join(' ');

/** The arguments of every `\drawing{…}` in a source, in order, braces balanced. */
export function drawingArgs(source) {
  // A \drawing named in a comment (a header saying how drawings are noted) is not one.
  const tex = source.replace(/(?<!\\)%.*$/gm, '');
  const out = [];
  let i = 0;
  for (;;) {
    const j = tex.indexOf('\\drawing{', i);
    if (j < 0) return out;
    let k = j + 9;
    let depth = 1;
    while (depth && k < tex.length) {
      const c = tex[k++];
      if (c === '\\') { k++; continue; }
      if (c === '{') depth++;
      else if (c === '}') depth--;
    }
    out.push(tex.slice(j + 9, k - 1));
    i = k;
  }
}

/** The figures of a folder, or [] if it has none. */
export function folderDrawings(folderDir) {
  const f = resolve(folderDir, 'drawings', 'drawings.json');
  if (!existsSync(f)) return [];
  return JSON.parse(readFileSync(f, 'utf8')).drawings ?? [];
}

/**
 * For the batch file `batch-NN.fr.tex` of a folder, one entry per `\drawing{}`
 * of its source: the figure redrawn from it, or null.
 */
export function drawingMap(folderDir, file, tex) {
  const m = /^batch-(\d+)\.fr\.tex$/.exec(file);
  if (!m) return [];
  const pool = folderDrawings(folderDir).filter(
    (d) => d.id.split('-')[0] === m[1] && d.status !== 'failed',
  );
  const used = new Set();
  return drawingArgs(tex).map((arg) => {
    const s = squash(arg);
    const hit = pool.find((d) => !used.has(d.id) && squash(d.description) === s);
    if (!hit) return null;
    used.add(hit.id);
    return hit;
  });
}
