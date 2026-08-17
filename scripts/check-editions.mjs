#!/usr/bin/env node
/**
 * Checks the community editions this site links to, against the fonds.
 *
 *   npm run check-editions            every document
 *   npm run check-editions -- 157-1   one folder
 *
 * Three questions, none of which the site can answer from `editions.json`
 * alone, because every answer lives on somebody else's server:
 *
 * — **Is the file still there?** These are third-party URLs on WordPress
 *   installs and university home pages, and they move. A dead link in the
 *   reading pane is worse than no link, because the pane renders an empty
 *   frame rather than an error.
 * — **Can it still be framed?** A single `X-Frame-Options` header added
 *   upstream silently blanks the community pane. Nothing in this repository
 *   would notice.
 * — **How much of the folder does it cover?** This is the interesting one,
 *   and the one whose answer is most easily misread. See below.
 *
 * ## What the page ratio does and does not measure
 *
 * It compares the transcription's typeset page count with the inventory's
 * count of scanned sheets. It is a scope check, **not** a fidelity check, and
 * cannot become one: a transcription can be complete and faithful at any
 * ratio.
 *
 * Two effects push in opposite directions and neither is a defect. Typesetting
 * compresses — the Dérivateurs run at 0.44 to 0.64 across all five folders,
 * which is what a full LaTeX transcription of a manuscript looks like. And a
 * document may be an *extract*, transcribing one piece of a folder rather than
 * the whole of it, which lowers the ratio without saying anything at all about
 * the quality of the piece.
 *
 * So a low ratio means *narrow*, and a wildly high one means the mapping is
 * probably wrong. Neither means bad work, and this script says so rather than
 * printing a verdict it has not earned.
 */

import { readFile } from 'node:fs/promises';
import { resolve } from 'node:path';

const ROOT = resolve(import.meta.dirname, '..');

const editions = JSON.parse(await readFile(resolve(ROOT, 'src/content/editions.json'), 'utf8'));
const catalogue = await readFile(resolve(ROOT, 'src/content/catalogue.ts'), 'utf8');

/** The catalogue is a .ts file with a JSON array in it; read the array. */
function block(name) {
  const i = catalogue.indexOf(`export const ${name}`);
  const j = catalogue.indexOf('= [', i) + 2;
  let depth = 0;
  for (let k = j; k < catalogue.length; k += 1) {
    if (catalogue[k] === '[') depth += 1;
    else if (catalogue[k] === ']') {
      depth -= 1;
      if (depth === 0) return JSON.parse(catalogue.slice(j, k + 1));
    }
  }
  throw new Error(`${name} not found in catalogue.ts`);
}

const byId = new Map(block('COTES').map((c) => [c.id, c]));
const only = process.argv.slice(2).filter((a) => !a.startsWith('-'));

const docs = editions.flatMap((e) =>
  (e.documents ?? [])
    .filter((d) => only.length === 0 || only.includes(d.cote))
    .map((d) => ({ ...d, edition: e })),
);

if (docs.length === 0) {
  process.stdout.write('No documents to check.\n');
  process.exit(0);
}

let dead = 0;
let unframable = 0;
const perCote = new Map();

for (const d of docs) {
  let status = '';
  try {
    // HEAD rather than GET: these are university servers and the whole point
    // is to be a light check that can be run often.
    const r = await fetch(d.url, { method: 'HEAD', redirect: 'follow' });
    const type = r.headers.get('content-type') ?? '';
    const xfo = r.headers.get('x-frame-options');
    const csp = r.headers.get('content-security-policy');
    if (!r.ok) {
      status = `HTTP ${r.status}`;
      dead += 1;
    } else if (!type.includes('pdf')) {
      status = `not a PDF (${type})`;
      dead += 1;
    } else if (xfo || /frame-ancestors/i.test(csp ?? '')) {
      // Refusing to be framed is the host's decision and not a fault. What
      // would be a fault is the file being offered in the pane anyway, so the
      // check is against what the data claims rather than against the header.
      if (d.framable === false) {
        status = `ok — not framable (${xfo ?? 'CSP'}), and recorded as such`;
      } else {
        status = `NOT FRAMABLE (${xfo ?? 'CSP frame-ancestors'}) — set "framable": false`;
        unframable += 1;
      }
    } else if (d.framable === false) {
      status = 'framable after all — "framable": false is now stale';
      unframable += 1;
    } else {
      status = 'ok';
    }
  } catch (err) {
    status = `unreachable — ${err.message}`;
    dead += 1;
  }

  const flag = status.startsWith('ok') ? ' ' : '!';
  process.stdout.write(
    `${flag} ${d.cote.padEnd(7)} ${String(d.pages ?? '?').padStart(4)}p  ` +
      `${d.title.slice(0, 46).padEnd(46)} ${status}\n`,
  );

  const agg = perCote.get(d.cote) ?? { pages: 0, files: 0 };
  agg.pages += d.pages ?? 0;
  agg.files += 1;
  perCote.set(d.cote, agg);
}

process.stdout.write('\nCoverage, transcription against facsimile:\n');
for (const [cote, agg] of [...perCote].sort((a, b) => a[0].localeCompare(b[0]))) {
  const c = byId.get(cote);
  if (!c) {
    process.stdout.write(`! ${cote} is not in the inventory\n`);
    continue;
  }
  const ratio = agg.pages / c.pages;
  // Only the top end is a defect: more typeset pages than there are sheets in
  // the folder means the document is very probably mapped to the wrong one.
  // A low ratio is a narrow document and is said, not flagged.
  const note = ratio > 3 ? '  <- more than the folder holds; check the mapping' : '';
  process.stdout.write(
    `  ${cote.padEnd(7)} ${String(agg.pages).padStart(5)}p in ${String(agg.files).padStart(2)} ` +
      `file(s) vs ${String(c.pages).padStart(4)}p of facsimile   ${ratio.toFixed(2)}${note}\n`,
  );
}

process.stdout.write(
  `\n${docs.length} documents · ${dead} unreachable · ${unframable} unframable\n` +
    'The ratio is scope, not fidelity: extracts and front matter both lower it, ' +
    'and typesetting lowers it again.\n',
);

process.exit(dead + unframable > 0 ? 1 : 0);
