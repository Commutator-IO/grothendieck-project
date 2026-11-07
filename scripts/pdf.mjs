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
import { mkdir, readdir, copyFile, rm, stat, readFile, access } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { promisify } from 'node:util';
import { resolve, basename } from 'node:path';
import { writeManifest } from './manifest.mjs';

const exec = promisify(execFile);

const ROOT = resolve(import.meta.dirname, '..');
const SOURCE = resolve(ROOT, 'transcripts');
const OUT = resolve(ROOT, 'public', 'transcripts');
const WORK = resolve(ROOT, 'archives', 'latex');
/**
 * A content-addressed store of compiled PDFs (#123). CI starts every run on a
 * fresh runner, so the mtime test below never skips anything there and every
 * deploy used to recompile all 800 transcriptions, about 25 minutes. The
 * workflow restores this directory with actions/cache; a PDF is reused when
 * the SHA-256 of its .tex and of everything the transcriptions share
 * (transcripts/preamble/, transcripts/figures/, this script) is unchanged.
 */
const CACHE = process.env.PDF_CACHE ? resolve(process.env.PDF_CACHE) : resolve(ROOT, 'node_modules', '.cache', 'pdf');
const SHARED = [resolve(SOURCE, 'preamble'), resolve(SOURCE, 'figures')];

async function sharedDigest() {
  const h = createHash('sha256');
  h.update(await readFile(import.meta.filename));
  for (const dir of SHARED) {
    let names = [];
    try {
      names = (await readdir(dir)).sort();
    } catch {
      continue;
    }
    for (const n of names) {
      h.update(n);
      h.update(await readFile(resolve(dir, n)));
    }
  }
  return h.digest('hex');
}

async function exists(path) {
  try {
    await access(path);
    return true;
  } catch {
    return false;
  }
}

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
    // preamble/ and figures/ hold what the transcriptions share, not a folder.
    folders = (await readdir(SOURCE, { withFileTypes: true }))
      .filter((d) => d.isDirectory() && d.name !== 'preamble' && d.name !== 'figures')
      .map((d) => d.name);
  } catch {
    process.stdout.write('No transcripts/ directory yet — nothing to compile.\n');
    return;
  }
  if (only.length) folders = folders.filter((f) => only.includes(f));

  await mkdir(WORK, { recursive: true });
  await mkdir(CACHE, { recursive: true });
  const shared = await sharedDigest();
  const used = new Set();
  let built = 0;
  let reused = 0;

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
      // A batch PDF also carries the figures redrawn from its \drawing marks (#73),
      // so the folder's drawing sources and the map naming them are in its key.
      const h = createHash('sha256').update(shared).update(await readFile(src));
      const ddir = resolve(SOURCE, folder, 'drawings');
      if (await exists(ddir)) {
        for (const n of (await readdir(ddir)).filter((x) => /\.(tex|json)$/.test(x)).sort()) {
          h.update(n);
          h.update(await readFile(resolve(ddir, n)));
        }
      }
      const key = h.digest('hex');
      const cached = resolve(CACHE, `${key}.pdf`);
      used.add(`${key}.pdf`);
      if ((await mtime(pdf)) > (await mtime(src))) {
        if (!(await exists(cached))) await copyFile(pdf, cached);
        continue;
      }
      if (await exists(cached)) {
        await copyFile(cached, pdf);
        reused += 1;
        continue;
      }

      /**
       * Twice, and the first failure is not reported.
       *
       * Tectonic populates its font cache *during* a compile, and the very
       * first document it is ever asked for on a cold cache dies before it can
       * use what it has just fetched:
       *
       *     ! Font TU/lmr/m/n/12=[lmroman12-regular] ... not loadable:
       *       Metric (TFM) file or installed font not found.
       *
       * The identical command then succeeds, because the fonts are there. On a
       * developer's machine the cache is warm and this is never seen; in CI it
       * cost exactly one PDF per run — whichever document sorts first, which is
       * why `115.modern.pdf` was the one missing from the site while the
       * fourteen compiled after it were fine. Retrying is the whole fix: a
       * document that is genuinely broken fails both times and is reported
       * then, with the engine's own words.
       */
      const compile = async () => {
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
      };

      try {
        try {
          await compile();
        } catch {
          await compile();
        }
        await copyFile(resolve(WORK, basename(file, '.tex') + '.pdf'), pdf);
        await copyFile(pdf, cached);
        built += 1;
        process.stdout.write(`  ${folder}/${basename(pdf)}\n`);
      } catch (e) {
        // Both engines put the `!` line on stdout and the summary on stderr,
        // and `execFile` puts neither in `e.message` — which is why this line
        // used to report nothing but the command it had just run, truncated
        // mid-path. Read both streams, and keep enough of them to act on.
        const out = `${e.stdout ?? ''}\n${e.stderr ?? ''}`;
        const log = /(?:^|\n)(!.*(?:\n.*){0,2})/.exec(out)?.[1] ?? e.stderr ?? e.message;
        process.stderr.write(`  ⚠ ${folder}/${file}: ${log.trim().slice(0, 400)}\n`);
      }
    }
  }

  await rm(WORK, { recursive: true, force: true });
  // Keep the store to what this checkout uses, so the cache saved by CI does
  // not grow with every edit. Only on a full run: `npm run pdf -- 19` sees one
  // folder and must not evict the others.
  if (!only.length) {
    for (const name of await readdir(CACHE)) {
      if (!used.has(name)) await rm(resolve(CACHE, name), { force: true });
    }
  }
  process.stdout.write(`${built} PDFs compiled with ${engine}, ${reused} reused from the cache.\n`);
  await writeManifest();
}

main().catch((e) => {
  process.stderr.write(`${e.message}\n`);
  process.exit(1);
});
