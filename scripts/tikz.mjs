#!/usr/bin/env node
/**
 * Compiles the transcriptions' `tikzpicture`s into the SVGs the reading views
 * show.
 *
 *   npm run tikz            every picture that has no SVG yet
 *   npm run tikz -- --check fail if one is missing, compile nothing
 *
 * tikz-cd covers his arrow graphs, and render.mjs draws those itself, in the
 * browser, from the source. It cannot draw the rest of his figures: an arc of a
 * face with its vertices in two colours, a chain of faces, two pseudo-lines
 * crossing in a lens. Those are redrawn in plain TikZ, and TikZ has no
 * renderer but TeX. So each picture is compiled once, alone, in a standalone
 * document under the same setup as the PDFs (`transcripts/preamble/
 * tikz-setup.tex`), and turned into an SVG by poppler's pdftocairo.
 *
 * The SVGs are committed, in `transcripts/figures/`, named by a hash of the
 * picture's source. That is what lets the deploy render the site before it has
 * installed tectonic, and what makes a stale figure impossible: change one
 * coordinate and the name changes, so render.mjs finds no SVG and stops, with
 * the command to run. A picture whose source is unchanged is never recompiled;
 * an SVG no picture names any more is deleted.
 */

import { execFile } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdtemp, readdir, readFile, writeFile, rm, mkdir } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { resolve, join } from 'node:path';
import { promisify } from 'node:util';
import { pathToFileURL } from 'node:url';

const exec = promisify(execFile);

const ROOT = resolve(import.meta.dirname, '..');
const SOURCE = resolve(ROOT, 'transcripts');
export const FIGURES = resolve(SOURCE, 'figures');

export const PICTURE = /\\begin\{tikzpicture\}[\s\S]*?\\end\{tikzpicture\}/g;

/**
 * The name of a picture's SVG. Comments are dropped and whitespace collapsed
 * first: render.mjs lifts a picture before it strips comments, the TEI carries
 * it through XML and back, and a re-indented or re-commented picture draws the
 * same.
 */
export function pictureHash(raw) {
  const drawn = raw.replace(/(?<!\\)%.*$/gm, '').replace(/\s+/g, ' ').trim();
  return createHash('sha256').update(drawn).digest('hex').slice(0, 12);
}

/** Every picture in the transcriptions, by hash. */
async function pictures() {
  const out = new Map();
  for (const folder of await readdir(SOURCE, { withFileTypes: true })) {
    if (!folder.isDirectory() || folder.name === 'preamble' || folder.name === 'figures') continue;
    for (const file of await readdir(resolve(SOURCE, folder.name))) {
      if (!file.endsWith('.tex')) continue;
      const tex = await readFile(resolve(SOURCE, folder.name, file), 'utf8');
      for (const m of tex.matchAll(PICTURE)) {
        out.set(pictureHash(m[0]), { raw: m[0], where: `${folder.name}/${file}` });
      }
    }
  }
  return out;
}

const standalone = (raw) => `\\documentclass[tikz,border=3pt]{standalone}
\\usepackage{amsmath,amssymb}
\\usepackage{fontspec}
\\input{${join(SOURCE, 'preamble', 'tikz-setup.tex')}}
\\begin{document}
${raw}
\\end{document}
`;

async function compile(hash, raw) {
  const work = await mkdtemp(join(tmpdir(), 'tikz-'));
  try {
    await writeFile(join(work, 'p.tex'), standalone(raw));
    await exec('tectonic', ['-X', 'compile', join(work, 'p.tex'), '--outdir', work]);
    await exec('pdftocairo', ['-svg', join(work, 'p.pdf'), join(FIGURES, `${hash}.svg`)]);
  } finally {
    await rm(work, { recursive: true, force: true });
  }
}

async function main() {
  const check = process.argv.includes('--check');
  await mkdir(FIGURES, { recursive: true });
  const all = await pictures();
  const missing = [...all].filter(([h]) => !existsSync(resolve(FIGURES, `${h}.svg`)));

  if (check) {
    if (missing.length) {
      for (const [h, p] of missing) process.stderr.write(`  no SVG for ${h} (${p.where})\n`);
      process.stderr.write('Run `npm run tikz`.\n');
      process.exit(1);
    }
  } else {
    for (const [h, p] of missing) {
      try {
        await compile(h, p.raw);
        process.stdout.write(`  ${h}.svg  ${p.where}\n`);
      } catch (e) {
        process.stderr.write(`tikz: ${p.where}: the picture ${h} does not compile\n${e.stdout ?? ''}${e.stderr ?? e.message}\n`);
        process.exit(1);
      }
    }
    for (const f of await readdir(FIGURES)) {
      if (f.endsWith('.svg') && !all.has(f.slice(0, -4))) {
        await rm(resolve(FIGURES, f));
        process.stdout.write(`  removed ${f}, which no picture names\n`);
      }
    }
  }
  process.stdout.write(`${all.size} picture(s), ${check ? 0 : missing.length} compiled → transcripts/figures/\n`);
}

if (import.meta.url === pathToFileURL(process.argv[1] ?? '').href) await main();
