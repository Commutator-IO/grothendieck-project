#!/usr/bin/env node
/**
 * The three checks a batch has to pass, as code rather than as habit.
 *
 *   npm run verify                  every transcript
 *   npm run verify -- 115           one folder
 *   npm run verify -- 115 1         one batch
 *   npm run verify -- 115 --json    the same result, for a program to read
 *
 * The transcription skill has always ended with three mechanical checks, and
 * each of them caught a real defect on a real batch. They were instructions to
 * a person: run the renderer, look for red source in the reading view, look
 * for a line running past the right margin in the PDF. A person doing this
 * once per batch is fine. Issue #2 asks for the same passes run headlessly,
 * and "look at it" is not something a loop can do — so the three become this
 * script, whose exit code is the gate and whose `--json` is what a failed
 * check hands back to the model that has to fix it.
 *
 * ## The three
 *
 * **1. It renders.** `scripts/render.mjs` covers a deliberately restricted
 * subset of LaTeX and raises on anything outside it. Running it *is* the
 * check — with one adjustment: the renderer reports a broken transcript as a
 * warning and carries on, so that one bad file does not cost the site its
 * other sixty reading views. Here that warning is the failure.
 *
 * **2. Every formula typesets.** The skill's wording is that the reading view
 * must contain zero `katex-error` nodes *in a browser* — and the reason for
 * the italics is that the string cannot be grepped out of the HTML, because
 * KaTeX runs on the client and the node only exists after it has failed. What
 * this script does instead is neither a grep nor a browser: it takes every
 * fragment the browser will hand to KaTeX — the delimited mathematics in the
 * prose, the `data-tex` of each diagram node, the label of each arrow — and
 * typesets it here, with `throwOnError: true` and the same `TR_MACROS` the
 * page uses, imported from the renderer so there is one definition and not
 * two. What throws here is exactly what renders red there. It skips the tags
 * `renderMathInElement` skips, which is why the LaTeX source folded under each
 * diagram is not checked twice and not reported as a failure.
 *
 * **3. No overfull box.** `scripts/pdf.mjs` compiles with `--keep-logs`, and
 * an `Overfull \hbox` in the log is a line running past the right margin. In a
 * transcription that is not a cosmetic defect: the overflow is content, and it
 * is content that is invisible in the artifact people download. Underfull
 * boxes are not reported — they are slack, not loss.
 *
 * ## What it does not check
 *
 * **Whether the reading is right.** Nothing here compares a word against the
 * page. A transcription can pass all three checks and be a fluent invention,
 * which is the one failure mode this edition has no mechanical defence
 * against; that is what the human comparison beside the facsimile is for, and
 * this script is not a substitute for it. It says the file is well-formed.
 */

import { execFile } from 'node:child_process';
import { readdir, readFile } from 'node:fs/promises';
import { promisify } from 'node:util';
import { resolve, basename } from 'node:path';
import katex from 'katex';
import { TR_MACROS } from './render.mjs';

const exec = promisify(execFile);

const ROOT = resolve(import.meta.dirname, '..');
const SOURCE = resolve(ROOT, 'transcripts');
const VIEWS = resolve(ROOT, 'public', 'transcripts');
const LOGS = resolve(ROOT, 'archives', 'latex');

const args = process.argv.slice(2);
const json = args.includes('--json');
const positional = args.filter((a) => !a.startsWith('--'));
const [folder, batch] = positional;

/** `115` + `1` → the files of batch 1; `115` alone → all of folder 115's. */
function wanted(name) {
  if (!batch) return true;
  const n = String(batch).padStart(2, '0');
  return name.startsWith(`batch-${n}.`);
}

/**
 * The tags `renderMathInElement` leaves alone by default. `pre` is the one
 * that matters here: the LaTeX source of every diagram is folded into one,
 * and it is source on display, not mathematics to typeset.
 */
const IGNORED = ['script', 'noscript', 'style', 'textarea', 'pre', 'code', 'option'];

const ENTITIES = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'", '#39': "'" };
const decode = (s) =>
  s.replace(/&(amp|lt|gt|quot|apos|#39);/g, (_, e) => ENTITIES[e]).replace(/&#(\d+);/g, (_, d) => String.fromCharCode(+d));

/**
 * Every fragment the browser will hand to KaTeX, in the order it will hand
 * them over. Attributes are read off the markup before the tags are stripped,
 * because that is where the diagrams keep their mathematics.
 */
function fragments(html) {
  const out = [];

  for (const m of html.matchAll(/data-tex="([^"]*)"/g)) {
    const tex = decode(m[1]);
    if (tex.trim()) out.push({ tex, display: false, where: 'diagram node' });
  }

  for (const m of html.matchAll(/data-arrows="([^"]*)"/g)) {
    let arrows;
    try {
      arrows = JSON.parse(decode(m[1]));
    } catch {
      out.push({ tex: m[1].slice(0, 60), display: false, where: 'diagram arrows (unparseable JSON)', broken: true });
      continue;
    }
    for (const a of arrows) if (a.label?.trim()) out.push({ tex: a.label, display: false, where: 'arrow label' });
  }

  let text = html;
  for (const tag of IGNORED) text = text.replace(new RegExp(`<${tag}\\b[^>]*>[\\s\\S]*?</${tag}>`, 'gi'), ' ');
  text = decode(text.replace(/<[^>]*>/g, ' '));

  for (const m of text.matchAll(/\\\[([\s\S]*?)\\\]/g)) out.push({ tex: m[1], display: true, where: 'display maths' });
  for (const m of text.matchAll(/\\\(([\s\S]*?)\\\)/g)) out.push({ tex: m[1], display: false, where: 'inline maths' });

  return out;
}

const short = (s) => {
  const one = s.replace(/\s+/g, ' ').trim();
  return one.length > 70 ? `${one.slice(0, 67)}…` : one;
};

/* --------------------------------------------------------------- the gates */

const report = { render: null, katex: [], overfull: [], unlogged: [], logged: 0, checked: [] };

/**
 * 1. It renders.
 *
 * The renderer raises per file and carries on, so that one broken transcript
 * does not cost the site its other sixty reading views. That is right for the
 * renderer and wrong for a gate: what it prints as a warning is exactly the
 * failure this check exists to catch, so a `⚠` line counts as a failure here
 * even though the process exited zero.
 */
try {
  const { stderr } = await exec('node', [resolve(ROOT, 'scripts', 'render.mjs'), ...(folder ? [folder] : [])], {
    maxBuffer: 32 * 1024 * 1024,
  });
  const warnings = stderr
    .split('\n')
    .filter((l) => l.includes('⚠'))
    .filter((l) => !folder || l.includes(`${folder}/`))
    .filter((l) => !batch || wanted(l.split('/').pop()?.trim() ?? ''));
  report.render = warnings.length ? { ok: false, message: warnings.join('\n') } : { ok: true };
} catch (e) {
  report.render = { ok: false, message: (e.stderr || e.stdout || String(e)).trim() };
}

/** 2. Every formula typesets, with the page's own macros. */
let views = [];
try {
  const dirs = (await readdir(VIEWS, { withFileTypes: true })).filter((d) => d.isDirectory()).map((d) => d.name);
  for (const dir of folder ? dirs.filter((d) => d === folder) : dirs) {
    for (const file of (await readdir(resolve(VIEWS, dir))).filter((f) => f.endsWith('.html') && wanted(f))) {
      views.push([dir, file]);
    }
  }
} catch {
  /* Nothing rendered yet; gate 1 will have said so. */
}

const warn = console.warn;
console.warn = () => {};

for (const [dir, file] of views) {
  const html = await readFile(resolve(VIEWS, dir, file), 'utf8');
  report.checked.push(`${dir}/${file}`);
  for (const f of fragments(html)) {
    if (f.broken) {
      report.katex.push({ file: `${dir}/${file}`, where: f.where, tex: f.tex, message: 'malformed attribute' });
      continue;
    }
    try {
      /*
       * A fresh copy of the macros per call: KaTeX writes into the table it is
       * given. And its strict-mode warnings are swallowed — `«` outside a
       * `\text{}`, `\sout` reaching into maths — because the browser only
       * warns about those too and renders the formula anyway. What this gate
       * is for is the failure that produces a red `katex-error` node, and that
       * is what `throwOnError` raises on.
       */
      katex.renderToString(f.tex, { throwOnError: true, displayMode: f.display, macros: { ...TR_MACROS } });
    } catch (e) {
      report.katex.push({ file: `${dir}/${file}`, where: f.where, tex: short(f.tex), message: e.message.replace(/\s+/g, ' ') });
    }
  }
}

console.warn = warn;

/** 3. No overfull box — the engine's own log is the evidence. */
let engine = true;
try {
  await exec('which', ['tectonic']);
} catch {
  try {
    await exec('which', ['xelatex']);
  } catch {
    engine = false;
  }
}

if (engine) {
  /*
   * One folder at a time, compiling and then reading its logs before moving
   * on — because `scripts/pdf.mjs` writes every document's log into one flat
   * work directory keyed by basename, and `batch-01.fr.log` is a name twenty
   * folders share. Compiling everything first and reading afterwards
   * therefore checks folder 115's margins against whichever folder happened
   * to compile last, which is how this check first reported a clean corpus
   * over six overfull boxes it had already found once.
   */
  let dirs = [];
  try {
    dirs = (await readdir(SOURCE, { withFileTypes: true })).filter((d) => d.isDirectory()).map((d) => d.name);
  } catch {
    /* No transcripts; nothing to check. */
  }

  for (const dir of folder ? dirs.filter((d) => d === folder) : dirs) {
    const names = (await readdir(resolve(SOURCE, dir)))
      .filter((f) => f.endsWith('.tex') && wanted(f))
      .map((f) => basename(f, '.tex'));
    if (!names.length) continue;

    try {
      /*
       * `--force` because a skipped compile leaves no log, and no log is not
       * a clean margin; `--keep` because the work directory, logs and all, is
       * otherwise swept the moment the compile finishes.
       */
      await exec('node', [resolve(ROOT, 'scripts', 'pdf.mjs'), dir, '--force', '--keep'], {
        maxBuffer: 32 * 1024 * 1024,
      });
    } catch (e) {
      report.overfull.push({
        file: dir,
        message: `compilation failed: ${(e.stderr || String(e)).trim().split('\n').slice(-4).join(' ')}`,
      });
    }

    let logs = [];
    try {
      logs = (await readdir(LOGS)).filter((f) => f.endsWith('.log'));
    } catch {
      /* No log directory: nothing compiled, and the failure above says why. */
    }

    for (const name of names) {
      if (!logs.includes(`${name}.log`)) {
        report.unlogged.push(`${dir}/${name}.tex`);
        continue;
      }
      report.logged += 1;
      const log = await readFile(resolve(LOGS, `${name}.log`), 'utf8');
      /* The engine reports the badness and the source line; both are useful. */
      for (const m of log.matchAll(/Overfull \\hbox \(([\d.]+)pt too wide\)[^\n]*?(?:at lines? (\d+[^\n]*))?\n/g)) {
        report.overfull.push({ file: `${dir}/${name}.tex`, overflow: `${m[1]}pt`, at: m[2] ?? 'unknown line' });
      }
    }
  }
}

/* -------------------------------------------------------------- the answer */

const failures =
  (report.render.ok ? 0 : 1) + report.katex.length + report.overfull.length;

if (json) {
  console.log(JSON.stringify({ ok: failures === 0, ...report }, null, 1));
  process.exit(failures ? 1 : 0);
}

const scope = folder ? (batch ? `${folder} batch ${batch}` : `folder ${folder}`) : 'every transcript';
console.log(`\nVerifying ${scope} — ${report.checked.length} reading views.\n`);

if (report.render.ok) {
  console.log('  ✓ renders — the LaTeX stayed inside the subset');
} else {
  console.log('  ✗ render failed:');
  console.log(report.render.message.split('\n').map((l) => `      ${l}`).join('\n'));
}

if (!report.katex.length) {
  console.log('  ✓ every formula typesets — no katex-error node will appear');
} else {
  console.log(`  ✗ ${report.katex.length} formula(e) will render as red source:`);
  for (const k of report.katex) console.log(`      ${k.file} · ${k.where}\n        ${k.tex}\n        ${k.message}`);
}

if (!engine) {
  console.log('  — overfull boxes not checked: no Unicode TeX engine (install tectonic)');
} else if (!report.overfull.length) {
  console.log(`  ✓ no overfull box — nothing runs past the right margin (${report.logged} document(s))`);
} else {
  console.log(`  ✗ ${report.overfull.length} overfull box(es) — content is hidden in the PDF:`);
  for (const o of report.overfull) console.log(`      ${o.file} ${o.at ?? ''} ${o.overflow ?? ''} ${o.message ?? ''}`.trimEnd());
}

if (report.unlogged.length) {
  console.log(`  ! ${report.unlogged.length} document(s) have no compiler log, so their margins were not checked:`);
  for (const f of report.unlogged) console.log(`      ${f}`);
}

console.log();
process.exit(failures ? 1 : 0);
