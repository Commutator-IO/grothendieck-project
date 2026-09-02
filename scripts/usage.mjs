#!/usr/bin/env node
/**
 * What a pass actually cost, read off the sessions that produced the editions.
 *
 *   npm run usage                 every pass that wrote a transcription
 *   npm run usage -- 29           one folder
 *   npm run usage -- --all        the passes that wrote nothing, too
 *   npm run usage -- --json       the same numbers, machine-readable
 *
 * Issue #2 opens by conceding that its cost table is *declared, not metered* —
 * "~175k tokens per batch", from two batches, with the input/output split
 * estimated rather than measured. This script is the answer to that, and the
 * answer is that the declaration was low by more than an order of magnitude.
 * The estimate counted the material a pass reads. What is billed is the
 * material a pass reads *times the number of turns it stays in context*, and a
 * transcription runs to two or three hundred turns.
 *
 * ## Where the numbers come from
 *
 * Claude Code writes every session to `~/.claude/projects/<cwd-slug>/*.jsonl`,
 * one line per event, and each assistant message carries the `usage` block the
 * API returned: uncached input, cache writes (split by TTL), cache reads, and
 * output. Nothing here is modelled or inferred — it is the meter, read back.
 *
 * Two mechanical points, both of which change the totals if you get them wrong:
 *
 * — **The same assistant message appears on several lines** as its content
 *   blocks stream in, with the usage repeated verbatim on each. Dedupe by
 *   `message.id` or you count a pass three or four times over.
 * — **Cache writes are not one price.** A 5-minute entry costs 1.25× base
 *   input, a 1-hour entry 2×; `usage.cache_creation` breaks the total down by
 *   TTL and this script prices each half separately. Reads are 0.1×.
 *
 * ## What a "pass" is here
 *
 * A human prompt and everything the model did until the next human prompt —
 * `origin.kind === 'human'` marks the boundary, and subagent turns inside the
 * pass are counted, because they are billed. A pass is credited to the files
 * it wrote under `transcripts/`. That is the honest unit: it charges a batch
 * for the whole loop that produced it, tiles and re-reads and failed renders
 * included, rather than for the tokens of the finished `.tex`.
 *
 * ## What it does not measure, and cannot
 *
 * — **It is not an invoice.** These sessions were billed to a Claude Code
 *   subscription, not to the API. What is priced here is what the same
 *   traffic would cost at list price on the API, which is the number issue #2
 *   is actually asking for — what the headless pipeline would spend.
 * — **A pass that did two things is charged to both.** Several early sessions
 *   transcribed a batch and worked on the site in the same breath; their
 *   per-batch figure is an upper bound. `--single` keeps only the passes that
 *   wrote exactly one edition file, which is the figure to quote.
 * — **It says nothing about quality.** A cheap pass and a careful pass are
 *   indistinguishable here. That comparison is the second task in issue #2 and
 *   this script is not it.
 * — **The corpus is what is on this machine.** Sessions are local files; a
 *   pass run elsewhere is simply absent, and the pass count says how many were
 *   found rather than how many exist.
 */

import { createReadStream } from 'node:fs';
import { readdir } from 'node:fs/promises';
import { createInterface } from 'node:readline';
import { homedir } from 'node:os';
import { resolve, join } from 'node:path';

const ROOT = resolve(import.meta.dirname, '..');

/**
 * List price per million tokens, from the pricing page. Cache multipliers are
 * the same for every model: a write costs 1.25× base input at the 5-minute
 * TTL and 2× at the one-hour TTL, a read 0.1×.
 */
const PRICE = {
  'claude-fable-5': { in: 10, out: 50 },
  'claude-opus-5': { in: 5, out: 25 },
  'claude-opus-4-8': { in: 5, out: 25 },
  'claude-sonnet-5': { in: 2, out: 10 },
  'claude-haiku-4-5': { in: 1, out: 5 },
};
const CACHE_5M = 1.25;
const CACHE_1H = 2;
const CACHE_READ = 0.1;

const args = process.argv.slice(2);
const flag = (name) => args.includes(`--${name}`);
const folders = args.filter((a) => !a.startsWith('--'));

/** `/Users/x/y` → `-Users-x-y`, which is how Claude Code names the log directory. */
const slug = ROOT.replace(/[/.]/g, '-');
const LOGS = join(homedir(), '.claude', 'projects', slug);

/** Cost of one usage block, in dollars, at list price. */
function cost(model, u) {
  const p = PRICE[model];
  if (!p) return 0;
  const creation = u.cache_creation ?? {};
  const write5m = creation.ephemeral_5m_input_tokens ?? 0;
  const write1h = creation.ephemeral_1h_input_tokens ?? 0;
  /* Older lines carry the total without the TTL split; price those at 5m. */
  const untyped = Math.max(0, (u.cache_creation_input_tokens ?? 0) - write5m - write1h);
  return (
    ((u.input_tokens ?? 0) * p.in +
      (write5m + untyped) * p.in * CACHE_5M +
      write1h * p.in * CACHE_1H +
      (u.cache_read_input_tokens ?? 0) * p.in * CACHE_READ +
      (u.output_tokens ?? 0) * p.out) /
    1e6
  );
}

/*
 * Most passes ran on Opus 5, a few on Fable 5, one on Sonnet 5. `cost` is what
 * the pass actually was; `as` reprices the identical token traffic on each of
 * the two models the transcription skill permits, which is the comparison the
 * pipeline decision needs and which the mixed history cannot give directly.
 */
const empty = () => ({
  in: 0, write: 0, read: 0, out: 0, cost: 0, turns: 0, models: new Set(),
  as: { 'claude-fable-5': 0, 'claude-opus-5': 0 },
});

function add(t, model, u) {
  for (const m of Object.keys(t.as)) t.as[m] += cost(m, u);
  t.in += u.input_tokens ?? 0;
  t.write += u.cache_creation_input_tokens ?? 0;
  t.read += u.cache_read_input_tokens ?? 0;
  t.out += u.output_tokens ?? 0;
  t.cost += cost(model, u);
  t.turns += 1;
  if (PRICE[model]) t.models.add(model);
}

/** The first line of a prompt, with the slash-command wrapper unpicked. */
function label(text) {
  if (!text) return '';
  const cmd = text.match(/<command-message>([^<]*)<\/command-message>/);
  const arg = text.match(/<command-args>([^<]*)<\/command-args>/);
  if (cmd) return `/${cmd[1].trim()}${arg ? ` ${arg[1].trim()}` : ''}`;
  return text.replace(/<[^>]*>/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 60);
}

/** `transcripts/115/batch-01.fr.tex` → what edition of what batch that is. */
function edition(path) {
  const m = path.match(/transcripts\/([^/]+)\/(?:batch-(\d+)|[^/]+)\.(fr|modern|en|summary)\.tex$/);
  if (!m) return null;
  return { folder: m[1], batch: m[2] ?? '—', edition: m[3] };
}

const passes = [];

for (const file of (await readdir(LOGS)).filter((f) => f.endsWith('.jsonl')).sort()) {
  const seen = new Set();
  let pass = null;
  const close = () => {
    if (pass && pass.turns.turns) passes.push(pass);
    pass = null;
  };

  const rl = createInterface({
    input: createReadStream(join(LOGS, file)),
    crlfDelay: Infinity,
  });

  for await (const line of rl) {
    let o;
    try {
      o = JSON.parse(line);
    } catch {
      continue;
    }

    if (o.type === 'user' && o.origin?.kind === 'human') {
      close();
      const c = o.message?.content;
      const text = typeof c === 'string' ? c : (c ?? []).find((b) => b.type === 'text')?.text;
      pass = {
        session: file.slice(0, 8),
        started: o.timestamp,
        prompt: label(text),
        wrote: new Set(),
        turns: empty(),
      };
      continue;
    }

    if (o.type !== 'assistant' || !pass) continue;
    const m = o.message ?? {};

    for (const b of m.content ?? []) {
      if (b.type !== 'tool_use') continue;
      if (!['Write', 'Edit', 'NotebookEdit'].includes(b.name)) continue;
      const e = edition(b.input?.file_path ?? '');
      if (e) pass.wrote.add(`${e.folder}\t${e.batch}\t${e.edition}`);
    }

    if (m.id && seen.has(m.id)) continue;
    if (m.id) seen.add(m.id);
    if (m.usage) add(pass.turns, m.model, m.usage);
  }
  close();
}

/*
 * A session that was resumed is written out again under a new id, so the same
 * pass turns up twice — same human prompt, same timestamp, same usage. Keep
 * the longer copy of each and drop the rest, or the early folders are billed
 * twice.
 */
const unique = new Map();
for (const p of passes) {
  const key = `${p.started}\t${p.prompt}`;
  const seen = unique.get(key);
  if (!seen || seen.turns.turns < p.turns.turns) unique.set(key, p);
}

/* ------------------------------------------------------------------ report */

const wrote = [...unique.values()].filter((p) => p.wrote.size);
const kept = folders.length
  ? wrote.filter((p) => [...p.wrote].some((w) => folders.includes(w.split('\t')[0])))
  : wrote;

const M = (n) => (n / 1e6).toFixed(2).padStart(7);
const $ = (n) => `$${n.toFixed(2)}`;

if (flag('json')) {
  console.log(
    JSON.stringify(
      (flag('all') ? [...unique.values()] : kept).map((p) => ({
        ...p,
        wrote: [...p.wrote].map((w) => w.split('\t')),
        turns: { ...p.turns, models: [...p.turns.models] },
      })),
      null,
      1,
    ),
  );
  process.exit(0);
}

console.log(`\n${LOGS}`);
console.log(
  `${passes.length} passes across ${(await readdir(LOGS)).filter((f) => f.endsWith('.jsonl')).length} sessions; ${wrote.length} wrote an edition file.\n`,
);

console.log('  pass      date        model        in   write    read     out    cost   wrote');
console.log('  ' + '─'.repeat(95));
for (const p of kept.sort((a, b) => a.started.localeCompare(b.started))) {
  const models = [...p.turns.models].map((m) => m.replace('claude-', '')).join('+') || '—';
  const w = [...p.wrote]
    .map((x) => {
      const [f, b, e] = x.split('\t');
      return `${f}/${b === '—' ? '' : `${b} `}${e}`;
    })
    .join(', ');
  console.log(
    `  ${p.session}  ${p.started.slice(0, 10)}  ${models.padEnd(9)}` +
      ` ${M(p.turns.in)} ${M(p.turns.write)} ${M(p.turns.read)} ${M(p.turns.out)}` +
      ` ${$(p.turns.cost).padStart(8)}   ${w}`,
  );
}

/** The figure worth quoting: passes that wrote exactly one edition file. */
function summarise(name, list) {
  if (!list.length) return;
  const costs = list.map((p) => p.turns.cost).sort((a, b) => a - b);
  const mid = costs[Math.floor(costs.length / 2)];
  const mean = costs.reduce((s, c) => s + c, 0) / costs.length;
  const tok = list.reduce(
    (s, p) => ({
      in: s.in + p.turns.in + p.turns.write + p.turns.read,
      out: s.out + p.turns.out,
      turns: s.turns + p.turns.turns,
    }),
    { in: 0, out: 0, turns: 0 },
  );
  const per = (m) => list.reduce((s, p) => s + p.turns.as[m], 0) / list.length;
  console.log(
    `\n  ${name} (n=${list.length})\n` +
      `    median ${$(mid)}   mean ${$(mean)}   range ${$(costs[0])}–${$(costs.at(-1))}\n` +
      `    ${(tok.in / list.length / 1e6).toFixed(1)}M input + ${Math.round(tok.out / list.length / 1e3)}k output per pass,` +
      ` over ${Math.round(tok.turns / list.length)} turns\n` +
      `    the same traffic repriced: ${$(per('claude-opus-5'))} on Opus 5, ${$(per('claude-fable-5'))} on Fable 5`,
  );
  return { mean, opus: per('claude-opus-5'), fable: per('claude-fable-5') };
}

const single = kept.filter((p) => p.wrote.size === 1);
const one = (e) => single.filter((p) => [...p.wrote][0].endsWith(`\t${e}`));

console.log('\n  ' + '─'.repeat(95));
const fr = summarise('Transcription, one batch, nothing else written', one('fr'));
const modern = summarise('Modernised reading, one folder, nothing else written', one('modern'));

/*
 * Transcription is per batch of twenty pages; the modernised reading is per
 * folder, since it reads typed LaTeX and has no twenty-page ceiling. Scaling
 * both by the batch count, as issue #2's table did, overcharges the reading by
 * the ratio of batches to folders — an order of magnitude on the long folders.
 */
if (fr) {
  console.log('\n  At those rates, and assuming a headless pass costs what an interactive one costs:');
  for (const [what, batches, cotes] of [
    ['the five notebooks', 483, 80],
    ['the whole open-access fonds', 884, 178],
  ]) {
    for (const m of ['opus', 'fable']) {
      const total = fr[m] * batches + (modern?.[m] ?? 0) * cotes;
      console.log(
        `    ${(m === 'opus' ? what : '').padEnd(28)} ${String(batches).padStart(3)} batches, ${String(cotes).padStart(3)} folders` +
          `  on ${m === 'opus' ? 'Opus 5 ' : 'Fable 5'}   ${$(fr[m] * batches).padStart(11)} transcription` +
          (modern ? ` + ${$(modern[m] * cotes).padStart(10)} modernisation = ${$(total).padStart(11)}` : ''),
      );
    }
  }
}
console.log();
