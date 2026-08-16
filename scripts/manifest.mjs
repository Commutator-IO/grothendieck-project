#!/usr/bin/env node
/**
 * Writes `public/manifest.json`: what is actually present on this machine.
 *
 * The site ships without a byte of the fonds and without a line of
 * transcription — the four notebooks come to several gigabytes, and the
 * transcripts belong to whoever produced them. This file is what the site
 * reads at load time to know which batches it can open and which editions it
 * can offer for download. Everything else renders with the command that
 * produces it, rather than with a link that would 404.
 *
 * It is derived, never edited: it records what is on disk. A transcript listed
 * here but deleted would be a download button that lies, which teaches the
 * reader to distrust every other button on the page.
 *
 *   npm run manifest
 */

import { readdir, mkdir, readFile, writeFile, stat } from 'node:fs/promises';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { resolve } from 'node:path';

const exec = promisify(execFile);

const ROOT = resolve(import.meta.dirname, '..');
const PUBLIC = resolve(ROOT, 'public');
const BATCHES = resolve(ROOT, 'archives', 'batches');
const TRANSCRIPTS = resolve(PUBLIC, 'transcripts');
const RAW = resolve(ROOT, 'archives', 'raw');
const STATUS = resolve(ROOT, 'transcripts', 'status.json');

const BATCH_SIZE = 20;
const EDITIONS = ['fr', 'modern'];

async function dirs(path) {
  try {
    return (await readdir(path, { withFileTypes: true })).filter((d) => d.isDirectory());
  } catch {
    return [];
  }
}

async function pageCount(pdf) {
  try {
    await stat(pdf);
    const { stdout } = await exec('pdfinfo', [pdf]);
    return Number(/^Pages:\s+(\d+)$/m.exec(stdout)?.[1] ?? 0);
  } catch {
    // The raw PDF may have been deleted once the batches were cut — that is a
    // legitimate way to reclaim tens of gigabytes, and the batches keep working.
    return 0;
  }
}

export async function writeManifest() {
  const facsimiles = {};
  for (const d of await dirs(BATCHES)) {
    const batches = (await readdir(resolve(BATCHES, d.name)))
      .map((f) => Number(/^batch-(\d+)\.pdf$/.exec(f)?.[1]))
      .filter(Number.isFinite)
      .sort((a, b) => a - b);
    if (batches.length) {
      facsimiles[d.name] = { pdfPages: await pageCount(resolve(RAW, `${d.name}.pdf`)), batches };
    }
  }

  /**
   * Transcripts are keyed `<folder>#<batch>` and split by extension.
   *
   * Three editions times three extensions is nine possible files per batch, and
   * almost never are all nine present: an English translation typically exists
   * long before anyone has compiled its PDF. Recording each extension
   * separately is what lets the reading view offer the HTML while the download
   * row offers only the `.tex`.
   */
  const transcripts = {};
  /**
   * Readings whose unit is the folder, not the batch.
   *
   * `folder.modern.tex` covers a shelfmark entire. Filing it under `#1` — the
   * only batch key its old name `batch-01.modern.tex` could produce — made the
   * archive page report folder 161-3 as "1/3 modernised" when all 54 of its
   * pages had been read, and left the Modernised toggle dead on batches 2 and
   * 3. Keyed by folder, it can be offered against every batch of that folder,
   * which is what it actually covers.
   */
  const folders = {};
  /**
   * Folder tags come out of the modernised readings themselves: the
   * `\keywords{...}` line each one carries at the end of its résumé. There is
   * deliberately no tags file to edit — a tag with no modernised reading
   * behind it would be a claim about content nobody has read yet. Several
   * batches of one folder union their keywords.
   */
  const tags = {};
  for (const d of await dirs(TRANSCRIPTS)) {
    for (const f of await readdir(resolve(TRANSCRIPTS, d.name))) {
      const m = /^(?:batch-(\d+)|folder)\.(fr|modern)\.(html|tex|pdf)$/.exec(f);
      if (!m) continue;
      // m[1] is undefined for `folder.*`, which is how the two are told apart.
      const entry = m[1]
        ? (transcripts[`${d.name}#${Number(m[1])}`] ??= { html: [], tex: [], pdf: [] })
        : (folders[d.name] ??= { html: [], tex: [], pdf: [] });
      if (!entry[m[3]].includes(m[2])) entry[m[3]].push(m[2]);
      if (m[2] === 'modern' && m[3] === 'tex') {
        const tex = await readFile(resolve(TRANSCRIPTS, d.name, f), 'utf8');
        for (const k of tex.matchAll(/\\keywords\{([^}]*)\}/g)) {
          const list = (tags[d.name] ??= []);
          // A keyword wrapped across a source line carries its newline here;
          // collapse any whitespace run to the single space the tag means.
          for (const t of k[1].split(',').map((s) => s.replace(/\s+/g, ' ').trim()).filter(Boolean)) {
            if (!list.includes(t)) list.push(t);
          }
        }
      }
    }
  }
  for (const entry of [...Object.values(transcripts), ...Object.values(folders)]) {
    for (const ext of ['html', 'tex', 'pdf']) {
      entry[ext].sort((a, b) => EDITIONS.indexOf(a) - EDITIONS.indexOf(b));
    }
  }

  /**
   * The declared states, carried through from the repository.
   *
   * Only the three no file can prove: a pass in flight, a human comparison
   * against the pages, a batch decided to hold nothing. `drafted` and
   * `reviewed` are never written down — they are read off the files above, so
   * they cannot go stale.
   */
  let declared = {};
  try {
    declared = JSON.parse(await readFile(STATUS, 'utf8')).status ?? {};
  } catch {
    // No status file: nothing has been claimed, which is a legitimate state.
  }

  await mkdir(PUBLIC, { recursive: true });
  await writeFile(
    resolve(PUBLIC, 'manifest.json'),
    JSON.stringify(
      {
        batchSize: BATCH_SIZE,
        generated: new Date().toISOString(),
        facsimiles,
        transcripts,
        folders,
        tags,
        declared,
      },
      null,
      2,
    ),
    'utf8',
  );

  process.stdout.write(
    `\nManifest: ${Object.keys(facsimiles).length} folders mirrored, ` +
      `${Object.keys(transcripts).length} batches transcribed, ` +
      `${Object.keys(folders).length} folders read whole, ` +
      `${Object.keys(declared).length} declared → public/manifest.json\n`,
  );
}

// Also usable on its own, after transcripts have been added or compiled.
if (import.meta.url === `file://${process.argv[1]}`) {
  writeManifest().catch((e) => {
    process.stderr.write(`${e.message}\n`);
    process.exit(1);
  });
}
