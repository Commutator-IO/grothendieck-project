#!/usr/bin/env node
/**
 * Cuts a batch's pages into overlapping tiles, large enough to read.
 *
 *   npm run tiles -- 29 9                    the batch's twenty pages
 *   npm run tiles -- 29 9 --pages 164-169    only the hard run
 *   npm run tiles -- 29 9 --dpi 900          when 700 is not enough
 *
 * Why this exists, measured rather than assumed. Transcribing folder 29 batch
 * 9 — sixteen pages — took about ninety `pdftoppm` renders and fifty reads,
 * against one write of the `.tex` and six verification commands. Decipherment
 * is essentially all of the work, and a large share of *that* was mechanics:
 * choosing `-x -y -W -H` by eye, guessing a region, re-cropping after cutting
 * a line of his in half. None of that is reading. This script does it once,
 * the same way every time, so a pass spends its attention on the hand.
 *
 * Two things it is deliberately not:
 *
 * — **It is not an enlargement of the evidence.** The scans are ~229 ppi
 *   native (`pdfimages -list`), so rendering a tile at 700 dpi adds no
 *   information that is not already on the film. What it adds is legibility:
 *   the same pixels, presented large, are materially easier to read, and the
 *   folder-29 thread records a pass concluding the opposite from the true
 *   premise. Both halves of that belong in one place, and this is the place.
 * — **It is not OCR, and does not want to become it.** Nothing here proposes a
 *   reading. A tool that offered one would have to be checked against the page
 *   like any other reading, and a fluent wrong word is the one failure this
 *   edition has no defence against.
 *
 * The paper's edges are found per page rather than assumed. Montpellier's
 * scans sit on a black scanner bed inside a white A4 page, and the sheet is
 * neither centred nor square from one leaf to the next; tiling the whole page
 * would spend a fifth of every batch's tiles on the bed. A 24 dpi grey render
 * is enough to find the sheet, and costs nothing.
 */

import { execFile } from 'node:child_process';
import { mkdir, readFile, rm, stat, writeFile } from 'node:fs/promises';
import { promisify } from 'node:util';
import { resolve } from 'node:path';
import { deflateSync } from 'node:zlib';

const exec = promisify(execFile);

const ROOT = resolve(import.meta.dirname, '..');
const BATCHES = resolve(ROOT, 'archives', 'batches');
const TILES = resolve(ROOT, 'archives', 'tiles');

/** Twenty pages: one transcription pass. Must agree with archive.mjs. */
const BATCH_SIZE = 20;

/** Defaults, all overridable. Three rows by two columns fits a manuscript
 *  leaf's proportions better than a square grid, and 15% overlap is enough
 *  that no line of his falls in a seam. */
const DEFAULTS = { dpi: 700, rows: 3, cols: 2, overlap: 0.15, probeDpi: 24 };

/** The left edge, where he writes sideways. Fraction of the sheet's width. */
const MARGIN_FRACTION = 0.22;

// ---------------------------------------------------------------------------
// Netpbm in, PNG out. Both by hand, so that rotating a margin strip needs no
// image library and works off macOS.

/** Parses the raw grey (P5) and colour (P6) that `pdftoppm` writes by default. */
function readNetpbm(buffer) {
  const tokens = [];
  let i = 0;
  while (tokens.length < 4) {
    while (i < buffer.length && buffer[i] <= 32) i++;
    if (buffer[i] === 0x23) {
      while (i < buffer.length && buffer[i] !== 0x0a) i++;
      continue;
    }
    const start = i;
    while (i < buffer.length && buffer[i] > 32) i++;
    tokens.push(buffer.toString('ascii', start, i));
  }
  i++; // the single whitespace byte that ends the header

  const magic = tokens[0];
  if (magic !== 'P5' && magic !== 'P6') throw new Error(`not a raw PGM/PPM: ${magic}`);
  return {
    width: Number(tokens[1]),
    height: Number(tokens[2]),
    channels: magic === 'P6' ? 3 : 1,
    data: buffer.subarray(i),
  };
}

const crc32Table = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();

function crc32(buf) {
  let c = -1;
  for (let i = 0; i < buf.length; i++) c = crc32Table[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

function pngChunk(type, payload) {
  const head = Buffer.alloc(8);
  head.writeUInt32BE(payload.length, 0);
  head.write(type, 4, 'ascii');
  const body = Buffer.concat([head.subarray(4), payload]);
  const tail = Buffer.alloc(4);
  tail.writeUInt32BE(crc32(body), 0);
  return Buffer.concat([head.subarray(0, 4), body, tail]);
}

/** Enough PNG to write back what we just read: 8-bit grey or RGB, no filter. */
function encodePng({ width, height, channels, data }) {
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(width, 0);
  ihdr.writeUInt32BE(height, 4);
  ihdr[8] = 8;
  ihdr[9] = channels === 3 ? 2 : 0;

  const stride = width * channels;
  const raw = Buffer.alloc((stride + 1) * height);
  for (let y = 0; y < height; y++) {
    raw[y * (stride + 1)] = 0; // filter: none
    data.copy(raw, y * (stride + 1) + 1, y * stride, (y + 1) * stride);
  }

  return Buffer.concat([
    Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]),
    pngChunk('IHDR', ihdr),
    pngChunk('IDAT', deflateSync(raw, { level: 6 })),
    pngChunk('IEND', Buffer.alloc(0)),
  ]);
}

/** Quarter turn. `dir` is 'cw' or 'ccw'; the margin he writes bottom-to-top
 *  comes upright with 'cw'. */
function rotate90({ width, height, channels, data }, dir) {
  const out = Buffer.alloc(width * height * channels);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const [nx, ny] = dir === 'cw' ? [height - 1 - y, x] : [y, width - 1 - x];
      const from = (y * width + x) * channels;
      const to = (ny * height + nx) * channels;
      for (let c = 0; c < channels; c++) out[to + c] = data[from + c];
    }
  }
  return { width: height, height: width, channels, data: out };
}

// ---------------------------------------------------------------------------

async function requireTools() {
  try {
    await exec('which', ['pdftoppm']);
  } catch {
    throw new Error('`pdftoppm` not found. Install poppler: brew install poppler');
  }
}

const exists = async (p) => {
  try {
    await stat(p);
    return true;
  } catch {
    return false;
  }
};

/**
 * Where the sheet sits on the page, as fractions of the rendered page.
 *
 * Three tones run down a rendered page, and only one of them is wanted: near
 * white for the generated page margin (means above ~248), near black for the
 * scanner bed the leaf lies on (below ~120), and between them the paper — a
 * flat grey around 205–220 that holds for hundreds of rows together.
 *
 * So the sheet is the **longest unbroken run of paper-toned rows**, and
 * likewise of columns. Walking inward from the edge instead looks simpler and
 * is wrong: Montpellier stamps a running header and a footer URL onto every
 * page, and a walk stops dead on the first line of that text, handing back a
 * box with the library's letterhead in it and a fifth of the tiles wasted.
 * A run long enough to be the sheet cannot be a two-line header.
 */
async function sheetBox(pdf, page, probeDpi) {
  const stem = resolve(TILES, `.probe-${process.pid}`);
  await exec('pdftoppm', [
    '-gray', '-r', String(probeDpi),
    '-f', String(page), '-l', String(page), '-singlefile',
    pdf, stem,
  ]);
  const img = readNetpbm(await readFile(`${stem}.pgm`));
  await rm(`${stem}.pgm`, { force: true });

  const { width: w, height: h, data } = img;
  const rowMean = (y) => {
    let s = 0;
    for (let x = 0; x < w; x++) s += data[y * w + x];
    return s / w;
  };
  const colMean = (x) => {
    let s = 0;
    for (let y = 0; y < h; y++) s += data[y * w + x];
    return s / h;
  };

  /** Paper: neither the page around the scan nor the bed under it. */
  const isPaper = (m) => m >= 120 && m <= 248;

  const longestRun = (mean, n) => {
    let best = [0, -1];
    let start = -1;
    for (let i = 0; i <= n; i++) {
      const paper = i < n && isPaper(mean(i));
      if (paper && start < 0) start = i;
      if (!paper && start >= 0) {
        if (i - 1 - start > best[1] - best[0]) best = [start, i - 1];
        start = -1;
      }
    }
    return best;
  };

  let [y0, y1] = longestRun(rowMean, h);
  let [x0, x1] = longestRun(colMean, w);

  // A probe pixel of bleed on each side. He writes to the very edge of the
  // sheet — folder 29 page 169 ends its last line on the paper's bottom rule —
  // and a box cut exactly at the detected edge clips it.
  const BLEED = 2;
  y0 = Math.max(0, y0 - BLEED); y1 = Math.min(h - 1, y1 + BLEED);
  x0 = Math.max(0, x0 - BLEED); x1 = Math.min(w - 1, x1 + BLEED);

  // A degenerate box means the profile was not what we expected — a very dark
  // leaf, a blank one. Fall back to the whole page rather than emit nothing.
  const ok = x1 - x0 > w * 0.3 && y1 - y0 > h * 0.3;
  return ok
    ? { x: x0 / w, y: y0 / h, w: (x1 - x0) / w, h: (y1 - y0) / h }
    : { x: 0, y: 0, w: 1, h: 1 };
}

/** The tile rectangles, in pixels at the working resolution. */
function layout(box, pageW, pageH, { rows, cols, overlap }) {
  const X = Math.round(box.x * pageW);
  const Y = Math.round(box.y * pageH);
  const W = Math.round(box.w * pageW);
  const H = Math.round(box.h * pageH);

  const span = (total, n) => (n === 1 ? total : total / (n - (n - 1) * overlap));
  const tw = Math.round(span(W, cols));
  const th = Math.round(span(H, rows));

  const tiles = [];
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      tiles.push({
        name: `r${r + 1}c${c + 1}`,
        x: X + Math.round(c * tw * (1 - overlap)),
        y: Y + Math.round(r * th * (1 - overlap)),
        w: tw,
        h: th,
      });
    }
  }

  // The left edge gets a strip of its own: he turns the sheet and writes up it,
  // and a note read sideways is a note not read. Folder 29 page 169 is the
  // case that made this non-optional.
  const margin = { name: 'margin', x: X, y: Y, w: Math.round(W * MARGIN_FRACTION), h: H };

  return { page: { x: X, y: Y, w: W, h: H }, tiles, margin };
}

async function tilePage({ pdf, pdfPage, page, dir, opts }) {
  await mkdir(dir, { recursive: true });

  const { stdout } = await exec('pdfinfo', ['-f', String(pdfPage), '-l', String(pdfPage), pdf]);
  const size = /^Page\s+\d+\s+size:\s+([\d.]+)\s+x\s+([\d.]+)/m.exec(stdout);
  if (!size) throw new Error(`page ${page}: pdfinfo gave no page size`);
  const pageW = Math.round((Number(size[1]) / 72) * opts.dpi);
  const pageH = Math.round((Number(size[2]) / 72) * opts.dpi);

  const box = await sheetBox(pdf, pdfPage, opts.probeDpi);
  const plan = layout(box, pageW, pageH, opts);

  const render = (rect, stem) =>
    exec('pdftoppm', [
      '-png', '-r', String(opts.dpi),
      '-f', String(pdfPage), '-l', String(pdfPage), '-singlefile',
      '-x', String(rect.x), '-y', String(rect.y),
      '-W', String(rect.w), '-H', String(rect.h),
      pdf, stem,
    ]);

  // The whole sheet first, at a size that fits a screen: a pass needs to see
  // the page entire before it starts reading quadrants, and the layout of a
  // leaf is itself evidence.
  await exec('pdftoppm', [
    '-png', '-r', String(Math.round(opts.dpi / 4)),
    '-f', String(pdfPage), '-l', String(pdfPage), '-singlefile',
    '-x', String(Math.round(plan.page.x / 4)), '-y', String(Math.round(plan.page.y / 4)),
    '-W', String(Math.round(plan.page.w / 4)), '-H', String(Math.round(plan.page.h / 4)),
    pdf, resolve(dir, 'sheet'),
  ]);

  for (const t of plan.tiles) await render(t, resolve(dir, t.name));

  // The margin, turned so it reads left to right, in as many pieces as there
  // are rows: one strip the height of the sheet comes out of the rotation
  // wider than a screen and no easier to read than the page it came from.
  // Grey rather than colour — the paper's tint carries nothing, and this is
  // the one image the script encodes itself.
  const stem = resolve(dir, 'margin');
  await exec('pdftoppm', [
    '-gray', '-r', String(opts.dpi),
    '-f', String(pdfPage), '-l', String(pdfPage), '-singlefile',
    '-x', String(plan.margin.x), '-y', String(plan.margin.y),
    '-W', String(plan.margin.w), '-H', String(plan.margin.h),
    pdf, stem,
  ]);
  const strip = readNetpbm(await readFile(`${stem}.pgm`));
  await rm(`${stem}.pgm`, { force: true });

  const band = Math.ceil(strip.height / opts.rows);
  for (let r = 0; r < opts.rows; r++) {
    const top = r * band;
    const rows = Math.min(band, strip.height - top);
    if (rows <= 0) break;
    const piece = {
      width: strip.width,
      height: rows,
      channels: 1,
      data: strip.data.subarray(top * strip.width, (top + rows) * strip.width),
    };
    await writeFile(resolve(dir, `margin-${r + 1}.png`), encodePng(rotate90(piece, 'cw')));
  }

  // The rectangles, so that a doubtful word can be re-cropped tighter without
  // guessing the coordinates again. This is the file to read before reaching
  // for `pdftoppm` by hand.
  await writeFile(
    resolve(dir, 'tiles.json'),
    `${JSON.stringify({ page, pdf: `${pdf.replace(ROOT + '/', '')}`, pdfPage, dpi: opts.dpi, sheet: plan.page, tiles: plan.tiles, margin: plan.margin }, null, 2)}\n`,
  );

  return plan.tiles.length + opts.rows + 1;
}

// ---------------------------------------------------------------------------

function parseArgs(argv) {
  const opts = { ...DEFAULTS, force: false, pages: null };
  const positional = [];

  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--force') opts.force = true;
    else if (a === '--dpi') opts.dpi = Number(argv[++i]);
    else if (a === '--overlap') opts.overlap = Number(argv[++i]);
    else if (a === '--grid') {
      const m = /^(\d+)x(\d+)$/.exec(argv[++i] ?? '');
      if (!m) throw new Error('--grid wants RxC, e.g. --grid 3x2');
      opts.rows = Number(m[1]);
      opts.cols = Number(m[2]);
    } else if (a === '--pages') {
      const set = new Set();
      for (const part of (argv[++i] ?? '').split(',')) {
        const range = /^(\d+)-(\d+)$/.exec(part.trim());
        if (range) for (let p = Number(range[1]); p <= Number(range[2]); p++) set.add(p);
        else if (part.trim()) set.add(Number(part.trim()));
      }
      opts.pages = set;
    } else if (a.startsWith('--')) throw new Error(`unknown option ${a}`);
    else positional.push(a);
  }

  if (opts.overlap < 0 || opts.overlap >= 1) throw new Error('--overlap wants 0 ≤ o < 1');
  if (!Number.isFinite(opts.dpi) || opts.dpi < 72) throw new Error('--dpi wants a number ≥ 72');
  return { opts, positional };
}

async function main() {
  const { opts, positional } = parseArgs(process.argv.slice(2));
  const [cote, batchArg] = positional;

  if (!cote || !batchArg) {
    process.stderr.write(
      'Usage: npm run tiles -- <folder> <batch> [--pages 164-169] [--dpi 700]\n' +
        '                       [--grid 3x2] [--overlap 0.15] [--force]\n\n' +
        'Writes archives/tiles/<folder>/p<page>/ — the sheet, the tiles,\n' +
        'the left margin upright and turned, and tiles.json with the\n' +
        'rectangles for re-cropping a doubtful word tighter.\n',
    );
    process.exit(1);
  }

  const batch = Number(batchArg);
  const pdf = resolve(BATCHES, cote, `batch-${String(batch).padStart(2, '0')}.pdf`);
  if (!(await exists(pdf))) {
    throw new Error(
      `${pdf.replace(ROOT + '/', '')} is not mirrored.\n` +
        `  npm run archive -- ${cote} --batches ${batch}`,
    );
  }

  await requireTools();
  await mkdir(TILES, { recursive: true });

  const { stdout } = await exec('pdfinfo', [pdf]);
  const count = Number(/^Pages:\s+(\d+)$/m.exec(stdout)?.[1] ?? 0);
  const first = (batch - 1) * BATCH_SIZE + 1;

  process.stdout.write(
    `folder ${cote}, batch ${batch} — pages ${first}–${first + count - 1}, ` +
      `${opts.rows}×${opts.cols} at ${opts.dpi} dpi\n`,
  );

  let written = 0;
  for (let i = 0; i < count; i++) {
    const page = first + i;
    if (opts.pages && !opts.pages.has(page)) continue;

    const dir = resolve(TILES, cote, `p${page}`);
    if (!opts.force && (await exists(resolve(dir, 'tiles.json')))) {
      process.stdout.write(`  page ${page}: already tiled\n`);
      continue;
    }

    try {
      const n = await tilePage({ pdf, pdfPage: i + 1, page, dir, opts });
      written += n;
      process.stdout.write(`  page ${page}: ${n} images\n`);
    } catch (e) {
      process.stderr.write(`  ⚠ page ${page}: ${e.message}\n`);
    }
  }

  process.stdout.write(`${written} images → ${resolve(TILES, cote).replace(ROOT + '/', '')}/\n`);
}

main().catch((e) => {
  process.stderr.write(`${e.message}\n`);
  process.exit(1);
});
