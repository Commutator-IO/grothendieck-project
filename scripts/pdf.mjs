#!/usr/bin/env node
/**
 * Compiles the transcripts' LaTeX into the PDFs offered for download.
 *
 *   npm run pdf              every transcript that has changed
 *   npm run pdf -- 19        one folder
 *
 * The PDF is the artifact for people who will not compile anything — a
 * supervisor, a reader on a train, an archive that wants a fixed page image.
 * It is compiled from the same `.tex` the reading view is rendered from, so
 * the three never disagree.
 *
 * A Unicode engine is required, not preferred: the transcriptions carry French
 * typography, Grothendieck's accented shorthand, and the occasional Greek or
 * German word, and `fontspec` in the preamble only works under XeTeX or LuaTeX.
 *
 * Tectonic is tried first, and is what CI uses. It is a single binary that
 * fetches the packages a document actually needs and caches them, so a runner
 * installs ~50 MB instead of a multi-gigabyte TeX Live — which is what makes it
 * reasonable to *build* these PDFs on every deploy rather than store them
 * anywhere. A local XeLaTeX is used if present, for people who already have one.
 *
 * With no engine at all this exits cleanly rather than failing the build: a
 * missing PDF costs a download button, not the site.
 */

import { execFile } from 'node:child_process';
import { mkdir, readdir, copyFile, rm, stat } from 'node:fs/promises';
import { promisify } from 'node:util';
import { resolve, basename } from 'node:path';
import { writeManifest } from './manifest.mjs';

const exec = promisify(execFile);

const ROOT = resolve(import.meta.dirname, '..');
const SOURCE = resolve(ROOT, 'transcripts');
const OUT = resolve(ROOT, 'public', 'transcripts');
const WORK = resolve(ROOT, 'archives', 'latex');

async function has(cmd) {
  try {
    await exec('which', [cmd]);
    return true;
  } catch {
    return false;
  }
}

async function mtime(path) {
  try {
    return (await stat(path)).mtimeMs;
  } catch {
    return 0;
  }
}

async function main() {
  const engine = (await has('tectonic')) ? 'tectonic' : (await has('xelatex')) ? 'xelatex' : null;
  if (!engine) {
    process.stdout.write(
      'No Unicode TeX engine found — skipping PDFs.\n' +
        'Install tectonic (`brew install tectonic`) if you want the download buttons\n' +
        'to offer PDF as well as source. pdfLaTeX will not do: the preamble uses fontspec.\n',
    );
    return;
  }

  const only = process.argv.slice(2).filter((a) => !a.startsWith('--'));
  let folders = [];
  try {
    folders = (await readdir(SOURCE, { withFileTypes: true }))
      .filter((d) => d.isDirectory())
      .map((d) => d.name);
  } catch {
    process.stdout.write('No transcripts/ directory yet — nothing to compile.\n');
    return;
  }
  if (only.length) folders = folders.filter((f) => only.includes(f));

  await mkdir(WORK, { recursive: true });
  let built = 0;

  for (const folder of folders) {
    const files = (await readdir(resolve(SOURCE, folder))).filter((f) => f.endsWith('.tex'));
    if (!files.length) continue;
    await mkdir(resolve(OUT, folder), { recursive: true });

    for (const file of files) {
      const src = resolve(SOURCE, folder, file);
      const pdf = resolve(OUT, folder, basename(file, '.tex') + '.pdf');
      // Recompiling an unchanged transcript costs seconds each and produces a
      // byte-identical file; skipping is what makes `npm run pdf` safe to run
      // after every batch.
      if ((await mtime(pdf)) > (await mtime(src))) continue;

      try {
        if (engine === 'tectonic') {
          // Tectonic reruns to convergence on its own, so the two-pass dance
          // below is unnecessary — and it halts on error by default.
          await exec(engine, ['-X', 'compile', src, '--outdir', WORK, '--keep-logs']);
        } else {
          // Twice: the second pass resolves the cross-references a long
          // transcription accumulates. `-halt-on-error` turns a broken macro
          // into a failure here rather than a silently truncated PDF.
          for (let pass = 0; pass < 2; pass++) {
            await exec(engine, [
              '-interaction=nonstopmode', '-halt-on-error',
              `-output-directory=${WORK}`, src,
            ]);
          }
        }
        await copyFile(resolve(WORK, basename(file, '.tex') + '.pdf'), pdf);
        built += 1;
        process.stdout.write(`  ${folder}/${basename(pdf)}\n`);
      } catch (e) {
        const log = /(?:^|\n)(!.*)/.exec(e.stdout ?? '')?.[1] ?? e.message;
        process.stderr.write(`  ⚠ ${folder}/${file}: ${log.slice(0, 200)}\n`);
      }
    }
  }

  await rm(WORK, { recursive: true, force: true });
  process.stdout.write(`${built} PDFs compiled with ${engine}.\n`);
  await writeManifest();
}

main().catch((e) => {
  process.stderr.write(`${e.message}\n`);
  process.exit(1);
});
