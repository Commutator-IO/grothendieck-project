#!/usr/bin/env node
/**
 * A private copy of Quillen's notebooks, for counting their pages.
 *
 *   node scripts/quillen-mirror.mjs [group…]
 *
 * Downloads every notebook src/content/quillen.json lists (or those of the
 * groups named) into archives/quillen/<group>/<label>.pdf — archives/ is
 * ignored by git — and writes archives/quillen/index.json, which
 * quillen-catalogue.mjs reads to add page counts. Files already there at the
 * listed size are kept. Nothing of this copy is served or committed: the site
 * frames the Clay's own files.
 */

import { createWriteStream, existsSync, mkdirSync, readFileSync, renameSync, statSync, writeFileSync } from 'node:fs';
import { resolve, join, dirname } from 'node:path';
import { Readable } from 'node:stream';
import { pipeline } from 'node:stream/promises';

const ROOT = resolve(import.meta.dirname, '..');
const MIRROR = process.env.QUILLEN_MIRROR ?? join(ROOT, 'archives', 'quillen');
const { notebooks } = JSON.parse(readFileSync(join(ROOT, 'src/content/quillen.json'), 'utf8'));
const only = new Set(process.argv.slice(2));
const wanted = notebooks.filter((n) => !only.size || only.has(n.group));

const pathOf = (n) => join(n.group, `${n.label.replace(/[/\\]/g, '_')}.pdf`);
// The listing rounds sizes (« 15M »): a file within 10 % of it is taken as whole.
const whole = (file, bytes) => existsSync(file) && (!bytes || Math.abs(statSync(file).size - bytes) < bytes * 0.1);

let done = 0;
let fetched = 0;
async function get(n) {
  const file = join(MIRROR, pathOf(n));
  if (!whole(file, n.bytes)) {
    mkdirSync(dirname(file), { recursive: true });
    const r = await fetch(n.url, { headers: { 'User-Agent': 'grothendieck-archives mirror' } });
    if (!r.ok) throw new Error(`${n.url}: HTTP ${r.status}`);
    await pipeline(Readable.fromWeb(r.body), createWriteStream(`${file}.part`));
    renameSync(`${file}.part`, file);
    fetched += 1;
  }
  done += 1;
  if (done % 20 === 0 || done === wanted.length) process.stdout.write(`${done}/${wanted.length} (${fetched} fetched)\n`);
}

const queue = [...wanted];
const failed = [];
await Promise.all(
  Array.from({ length: Number(process.env.QUILLEN_PARALLEL ?? 4) }, async () => {
    for (let n; (n = queue.shift()); ) {
      try {
        await get(n);
      } catch (e) {
        failed.push(`${n.id}: ${e.message}`);
      }
    }
  }),
);

// The index covers every notebook present, not only this run's groups.
const index = notebooks.filter((n) => existsSync(join(MIRROR, pathOf(n)))).map((n) => ({ url: n.url, path: pathOf(n) }));
writeFileSync(join(MIRROR, 'index.json'), JSON.stringify(index, null, 1) + '\n');
process.stdout.write(`${index.length} notebooks in ${MIRROR}${failed.length ? `; failed:\n${failed.join('\n')}` : ''}\n`);
