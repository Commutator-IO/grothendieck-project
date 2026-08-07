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

import { readdir, mkdir, writeFile, stat } from 'node:fs/promises';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { resolve } from 'node:path';

const exec = promisify(execFile);

const ROOT = resolve(import.meta.dirname, '..');
const PUBLIC = resolve(ROOT, 'public');
const BATCHES = resolve(ROOT, 'archives', 'batches');
const TRANSCRIPTS = resolve(PUBLIC, 'transcripts');
const RAW = resolve(ROOT, 'archives', 'raw');

const BATCH_SIZE = 20;
const EDITIONS = ['fr', 'en', 'summary'];

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
  for (const d of await dirs(TRANSCRIPTS)) {
    for (const f of await readdir(resolve(TRANSCRIPTS, d.name))) {
      const m = /^batch-(\d+)\.(fr|en|summary)\.(html|tex|pdf)$/.exec(f);
      if (!m) continue;
      const key = `${d.name}#${Number(m[1])}`;
      const entry = (transcripts[key] ??= { html: [], tex: [], pdf: [] });
      if (!entry[m[3]].includes(m[2])) entry[m[3]].push(m[2]);
    }
  }
  for (const entry of Object.values(transcripts)) {
    for (const ext of ['html', 'tex', 'pdf']) {
      entry[ext].sort((a, b) => EDITIONS.indexOf(a) - EDITIONS.indexOf(b));
    }
  }

  await mkdir(PUBLIC, { recursive: true });
  await writeFile(
    resolve(PUBLIC, 'manifest.json'),
    JSON.stringify(
      { batchSize: BATCH_SIZE, generated: new Date().toISOString(), facsimiles, transcripts },
      null,
      2,
    ),
    'utf8',
  );

  process.stdout.write(
    `\nManifest: ${Object.keys(facsimiles).length} folders mirrored, ` +
      `${Object.keys(transcripts).length} batches transcribed → public/manifest.json\n`,
  );
}

// Also usable on its own, after transcripts have been added or compiled.
if (import.meta.url === `file://${process.argv[1]}`) {
  writeManifest().catch((e) => {
    process.stderr.write(`${e.message}\n`);
    process.exit(1);
  });
}
