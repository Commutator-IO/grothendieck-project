#!/usr/bin/env node
/**
 * Runs a pass without a human in front of it — the same skills, the same loop.
 *
 *   npm run headless -- transcribe 115 1        one batch
 *   npm run headless -- modernize 115           one folder
 *   npm run headless -- transcribe 29 9 --model claude-fable-5
 *   npm run headless -- transcribe 115 1 --dry  what would be sent, and nothing else
 *   npm run headless -- smoke                   one turn, to prove the chain works
 *
 * Issue #2 proposed two ways to do this: call the Messages API and rebuild the
 * agent loop around it, or hand the work to Managed Agents. Both start by
 * conceding that the skills are *prose instructions for an agent, not
 * prompts*, and then reimplement the agent — the file tools, the crop tool,
 * the turn loop — so that the prose has something to be true of.
 *
 * This takes the third way, which is the one the requirement actually asks
 * for: **it is Claude Code, as a library.** The Claude Agent SDK ships the
 * harness — the loop, Read/Write/Edit/Bash/Glob/Grep, the Skill tool — and
 * discovers `.claude/skills/` from the filesystem exactly as the CLI does. So
 * `/transcribe-grothendieck 115 1` here dispatches the identical `SKILL.md`
 * that a person dispatches by typing the same thing, reads the same
 * `references/hand.md`, shells out to the same `npm run tiles`. There is no
 * second copy of the method to keep in step with the first, which matters more
 * here than the code saved: a headless edition produced by a paraphrase of the
 * skill would not be the same edition, and nothing in the file would say so.
 *
 * What this file adds to the SDK is only what a missing human was doing:
 *
 * — **A guard, because nothing will be asked.** The session runs under
 *   `bypassPermissions`, since a headless run has nobody to answer a prompt,
 *   and a `PreToolUse` hook refuses the handful of commands that should never
 *   be reached for unsupervised. `git commit` and `git push` are among them,
 *   for the reason the issue gives: a failed check must come back into the
 *   loop and not go quietly into a commit.
 * — **The gates, wired to the loop.** `npm run verify` is run after the pass;
 *   if it fails, its JSON report is handed back into the *same session* and
 *   the pass is asked to fix what it broke, up to `--rounds` times. The exit
 *   code is the last verdict.
 * — **A meter.** Every round's `modelUsage` is recorded to
 *   `archives/usage/`, in the shape `npm run usage` reports for the
 *   interactive passes, so that the two are comparable. That comparison is the
 *   whole point of the first headless run: the interactive figures spend 69%
 *   of their cost on cache writes, much of it plausibly the one-hour cache
 *   expiring in the gaps where a person was thinking. A loop that does not
 *   stop should not pay that, and this is where it will show.
 *
 * ## Paying for it
 *
 * The SDK spawns Claude Code, which resolves credentials the way the CLI does:
 * `ANTHROPIC_API_KEY` from the environment, otherwise the login this machine
 * holds. So there are two ways to run a pass, and the difference is who is
 * billed rather than what happens:
 *
 * — **A Claude subscription** — `claude auth login`, or `claude setup-token`
 *   for a long-lived one to put in CI. The pass then draws on the same quota
 *   an interactive pass draws on, and no API invoice is raised. This is how to
 *   try it without opening a billing account, and it is what every batch in
 *   this repository was produced under. (Anthropic's SDK terms cover using
 *   your own subscription for your own work; they do not permit shipping a
 *   *product* to other people on subscription auth.)
 * — **An API key** — what an unattended run wants, because a subscription
 *   login expires and it expires mid-pass rather than before it.
 *
 * Either way, start with `--smoke`: one turn, a few hundred tokens, and it
 * proves the whole chain — credentials, skill discovery, the result shape the
 * meter reads — before a hundred-turn pass discovers a problem three hours in.
 *
 * ## What it does not settle
 *
 * **Whether the reading is any good.** The gates prove the file is
 * well-formed, never that a word matches the page. Issue #2's second task is
 * to diff a headless pass against a transcription a person has checked, and
 * this script is the thing to be diffed, not the diff. Until that comparison
 * is made, treat what comes out as a draft nobody has read — which is what its
 * own header comment will say.
 */

import { query } from '@anthropic-ai/claude-agent-sdk';
import { mkdir, readdir, writeFile } from 'node:fs/promises';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { resolve } from 'node:path';

const exec = promisify(execFile);
const ROOT = resolve(import.meta.dirname, '..');

/** The two steps the issue is about, and the skill each dispatches. */
const STEPS = {
  transcribe: { skill: 'transcribe-grothendieck', unit: 'batch' },
  modernize: { skill: 'modernize-grothendieck', unit: 'folder' },
  tag: { skill: 'tag-grothendieck', unit: 'folder' },
  findings: { skill: 'find-novelty', unit: 'folder' },
};

const argv = process.argv.slice(2);

/** The flags that take a value, so their value is not read as a positional. */
const VALUED = ['model', 'rounds', 'turns', 'budget'];

const values = {};
const positional = [];
for (let i = 0; i < argv.length; i += 1) {
  const a = argv[i];
  if (!a.startsWith('--')) {
    positional.push(a);
  } else if (VALUED.includes(a.slice(2))) {
    values[a.slice(2)] = argv[i + 1];
    i += 1;
  } else {
    values[a.slice(2)] = true;
  }
}

const flag = (name, fallback) => values[name] ?? fallback;
const has = (name) => values[name] === true;

const [step, folder, batch] = positional;

/**
 * `--smoke`, or `smoke` as the step: one turn, no tools, nothing written.
 *
 * A transcription is thirty-one million input tokens over a hundred-odd
 * turns. Finding out at turn 3 that the login expired, or that no skill was
 * discovered because the working directory was wrong, is worth a few hundred
 * tokens to learn first — and it is the check to run in CI, where what wants
 * proving is that the pipeline still authenticates, not that it can read
 * Grothendieck's hand.
 */
const smoke = has('smoke') || step === 'smoke';

if (!smoke && (!STEPS[step] || !folder)) {
  console.error(
    'Usage: npm run headless -- <transcribe|modernize|tag|findings> <folder> [batch]\n' +
      '       npm run headless -- smoke   one turn, to prove credentials and skill discovery\n' +
      '       --model <id>    claude-opus-5 (default) or claude-fable-5; nothing else\n' +
      '       --rounds <n>    verification rounds before giving up (default 3)\n' +
      '       --turns <n>     hard ceiling on agentic turns (default 400)\n' +
      '       --budget <usd>  stop the pass if it costs more than this\n' +
      '       --dry           print the prompt and the options, run nothing',
  );
  process.exit(2);
}

/**
 * Only the two models the transcription skill permits. The skill checks this
 * itself and refuses to read a page under anything else — this is the same
 * refusal one step earlier, so that a mistyped flag costs nothing rather than
 * a session's startup. Provenance is the reason in both places: a reading
 * whose model was an accident is a reading nobody can weigh later.
 */
const PERMITTED = ['claude-opus-5', 'claude-fable-5'];
const model = flag('model', 'claude-opus-5');
if (!PERMITTED.includes(model)) {
  console.error(`Refusing to run on ${model}. The editions are produced on ${PERMITTED.join(' or ')}, and on nothing else.`);
  process.exit(2);
}

const rounds = Number(flag('rounds', 3));
const maxTurns = smoke ? 1 : Number(flag('turns', 400));
const budget = values.budget ? Number(values.budget) : undefined;

const { skill, unit } = smoke ? { skill: null, unit: null } : STEPS[step];
if (!smoke && unit === 'batch' && !batch) {
  console.error(`/${skill} works one batch at a time — give the batch number.`);
  process.exit(2);
}

const prompt = smoke
  ? 'Reply with the single word OK. Do not use any tool.'
  : `/${skill} ${unit === 'batch' ? `${folder} ${batch}` : folder}`;

/* ------------------------------------------------------------- the session */

/** Whatever is on disk, so a new skill is available here the day it is added. */
const skills = (await readdir(resolve(ROOT, '.claude', 'skills'), { withFileTypes: true }))
  .filter((d) => d.isDirectory())
  .map((d) => d.name);

/**
 * The commands a pass must not reach for with nobody watching.
 *
 * `git commit` and `git push` are the two that matter, and they are refused
 * for the reason issue #2 gives: the point of wiring the gates into the loop
 * is that a failure comes back to be fixed rather than going quietly into the
 * history. What the pass produces is left in the working tree for a person to
 * read beside the facsimile and commit, or not.
 *
 * The rest are ordinary destruction. `npm run archive` and `npm run tiles`
 * write under `archives/`, and a pass legitimately clears its own tiles there;
 * anything reaching outside it is refused.
 */
const FORBIDDEN = [
  [/\bgit\s+(commit|push|tag\b)/, 'a headless pass leaves its work in the tree; a person commits it'],
  [/\bgit\s+(reset\s+--hard|clean\s+-[a-z]*f)/, 'that discards work the pass cannot get back'],
  [/\bgh\s+(issue|pr|release|api)\b/, 'nothing is posted to GitHub from an unattended pass'],
  [/\brm\s+-[a-z]*r[a-z]*f?\s+(?!.*archives\/)/, 'recursive delete outside archives/'],
  [/\bnpm\s+publish\b/, 'nothing is published from a pass'],
];

const guard = async (input) => {
  if (input.tool_name !== 'Bash') return { continue: true };
  const command = String(input.tool_input?.command ?? '');
  for (const [pattern, why] of FORBIDDEN) {
    if (pattern.test(command)) {
      return {
        continue: true,
        hookSpecificOutput: {
          hookEventName: 'PreToolUse',
          permissionDecision: 'deny',
          permissionDecisionReason: `Refused by the headless guard: ${why}.`,
        },
      };
    }
  }
  return { continue: true };
};

const options = {
  cwd: ROOT,
  model,
  /*
   * `project` and not `user`: the editions are produced by the skills in this
   * repository, at the revision this repository is at. A personal skill on
   * whatever machine happens to run the pass has no business in the loop.
   */
  settingSources: ['project'],
  skills,
  allowedTools: ['Read', 'Write', 'Edit', 'Bash', 'Glob', 'Grep', 'Skill', 'TodoWrite'],
  /*
   * There is nobody to ask. The guard hook above is what stands in for the
   * question, and it answers only about the handful of commands where the
   * answer would always have been no.
   */
  permissionMode: 'bypassPermissions',
  maxTurns,
  ...(budget ? { maxBudgetUsd: budget } : {}),
  hooks: { PreToolUse: [{ hooks: [guard] }] },
};

if (has('dry')) {
  console.log(`prompt: ${prompt}\n`);
  console.log(JSON.stringify({ ...options, hooks: '<guard>' }, null, 1));
  process.exit(0);
}

/* ----------------------------------------------------------------- the run */

const meter = { step: smoke ? 'smoke' : step, folder: smoke ? null : folder, batch: batch ?? null, model, started: new Date().toISOString(), rounds: [] };

/**
 * The credentials the child process will look for.
 *
 * The SDK spawns Claude Code, which authenticates the same way the CLI does:
 * an API key from the environment, or the OAuth session a `claude` login left
 * on this machine. A pipeline meant to run unattended wants the key — an OAuth
 * session expires, and it expires in the middle of a pass rather than before
 * it, which is the expensive place for it to happen.
 */
function authAdvice(message) {
  if (!/authenticat|OAuth|credential|401/i.test(message)) return null;
  if (process.env.ANTHROPIC_API_KEY) {
    return 'The pass could not authenticate. ANTHROPIC_API_KEY is set, so the key itself is\nbeing refused — check that it is current.\n';
  }
  return (
    'The pass could not authenticate: no ANTHROPIC_API_KEY, and no usable login.\n\n' +
    '  Two ways to pay for a pass, and they differ only in who is billed.\n\n' +
    '  On a Claude subscription — no API invoice, drawing on the same quota an\n' +
    '  interactive pass draws on, which is what every batch here was produced under:\n\n' +
    '      claude auth login          # then run this again\n' +
    '      claude setup-token         # a long-lived token instead, for CI\n\n' +
    '  On the API, which is what an unattended run wants — a subscription login\n' +
    '  expires, and it expires mid-pass rather than before it:\n\n' +
    '      export ANTHROPIC_API_KEY=...\n\n' +
    '  Either way, run `npm run headless -- smoke` first: one turn, a few hundred\n' +
    '  tokens, and it says whether the chain works before a long pass finds out.\n'
  );
}

async function pass(text, resume) {
  const round = { prompt: text, resumed: resume ?? null, tools: {}, modelUsage: {}, costUSD: 0, turns: 0 };
  let sessionId = resume;

  try {
  for await (const message of query({ prompt: text, options: { ...options, ...(resume ? { resume } : {}) } })) {
    if (message.type === 'system' && message.subtype === 'init') {
      sessionId = message.session_id;
      /* Say what loaded, once: a pass that silently found no skill would
       * otherwise transcribe from the model's own idea of what to do. */
      if (!resume) console.log(`  session ${sessionId}\n  skills: ${(message.skills ?? []).join(', ') || '(none found — check .claude/skills/)'}\n`);
    }

    if (message.type === 'assistant') {
      for (const b of message.message?.content ?? []) {
        if (b.type !== 'tool_use') continue;
        round.tools[b.name] = (round.tools[b.name] ?? 0) + 1;
        const detail =
          b.name === 'Bash' ? String(b.input?.command ?? '').slice(0, 70)
          : b.name === 'Skill' ? String(b.input?.skill ?? '')
          : String(b.input?.file_path ?? b.input?.pattern ?? '').replace(`${ROOT}/`, '');
        console.log(`  · ${b.name} ${detail}`);
      }
    }

    if (message.type === 'result') {
      round.subtype = message.subtype;
      round.turns = message.num_turns ?? 0;
      round.costUSD = message.total_cost_usd ?? 0;
      round.modelUsage = message.modelUsage ?? {};
      round.session = message.session_id ?? sessionId;
      round.text = message.subtype === 'success' ? message.result : undefined;
      round.error = message.subtype === 'success' ? undefined : message.subtype;
    }
  }
  } catch (e) {
    /*
     * The SDK throws the child's last error result, and for an auth failure
     * that arrives wrapped in a stack trace through minified code — pages of
     * it, with the one useful sentence in the middle. Say the sentence.
     */
    const advice = authAdvice(e.message ?? '');
    if (advice) {
      console.error(`\n${advice}`);
      process.exit(3);
    }
    round.error = String(e.message ?? e).split('\n')[0];
    console.error(`\n  the pass ended in an error: ${round.error}\n`);
  }

  meter.rounds.push(round);
  return round;
}

/** The gates, as `npm run verify` reports them. */
async function verify() {
  const args = [resolve(ROOT, 'scripts', 'verify.mjs'), folder, ...(batch ? [String(batch)] : []), '--json'];
  try {
    const { stdout } = await exec('node', args, { maxBuffer: 64 * 1024 * 1024 });
    return JSON.parse(stdout);
  } catch (e) {
    /* verify exits non-zero when a gate fails, and prints the report anyway. */
    try {
      return JSON.parse(e.stdout);
    } catch {
      return { ok: false, render: { ok: false, message: (e.stderr || String(e)).trim() }, katex: [], overfull: [] };
    }
  }
}

console.log(
  smoke
    ? `\nsmoke test  ·  ${model}  ·  one turn, no tools, nothing written\n`
    : `\n${prompt}  ·  ${model}  ·  up to ${maxTurns} turns, ${rounds} verification round(s)\n`,
);

let round = await pass(prompt);

/* A smoke test writes nothing, so there is nothing for the gates to check. */
let report = smoke ? { ok: !round.error } : await verify();

for (let n = 1; n <= rounds && !report.ok && !smoke; n += 1) {
  console.log(`\n  gates failed — round ${n} of ${rounds}, handed back into the same session\n`);
  const complaint =
    'The verification gates failed on what you just wrote. Fix the transcription — the ' +
    '.tex is the source of record, so correct it there and never the derived HTML or PDF — ' +
    'and do not resolve an uncertainty to make a gate pass: an illegible word stays \\ill{}. ' +
    'Re-run `npm run verify -- ' + folder + (batch ? ` ${batch}` : '') + '` when you are done.\n\n' +
    JSON.stringify({ render: report.render, katex: report.katex, overfull: report.overfull }, null, 1);

  round = await pass(complaint, round.session);
  report = await verify();
}

/* --------------------------------------------------------------- the meter */

const total = { costUSD: 0, turns: 0, tokens: { input: 0, output: 0, cacheRead: 0, cacheWrite: 0 } };
for (const r of meter.rounds) {
  total.turns += r.turns;
  /* total_cost_usd is cumulative within a session, so the rounds that resumed
   * one already contain the earlier round's spend; the per-model figures are
   * summed instead, which are per query() call. */
  for (const u of Object.values(r.modelUsage)) {
    total.costUSD += u.costUSD ?? 0;
    total.tokens.input += u.inputTokens ?? 0;
    total.tokens.output += u.outputTokens ?? 0;
    total.tokens.cacheRead += u.cacheReadInputTokens ?? 0;
    total.tokens.cacheWrite += u.cacheCreationInputTokens ?? 0;
  }
}
meter.total = total;
meter.ok = report.ok;
meter.finished = new Date().toISOString();

await mkdir(resolve(ROOT, 'archives', 'usage'), { recursive: true });
const slug = smoke
  ? `smoke-${model}`
  : `${step}-${folder}${batch ? `-batch-${String(batch).padStart(2, '0')}` : ''}-${model}`;
const meterPath = resolve(ROOT, 'archives', 'usage', `${slug}.json`);
await writeFile(meterPath, JSON.stringify(meter, null, 1), 'utf8');

const M = (n) => `${(n / 1e6).toFixed(2)}M`;

if (smoke) {
  console.log(
    `\n  ${report.ok ? '✓' : '✗'} the chain works: credentials accepted, skills discovered, ` +
      `the result carried usage the meter could read.\n` +
      `  ${(total.tokens.output / 1e3).toFixed(1)}k output, estimated $${total.costUSD.toFixed(4)}\n` +
      `  meter → ${meterPath.replace(`${ROOT}/`, '')}\n\n` +
      `  Now try a real pass. The cheapest is a tagging run — it rewrites one \\keywords\n` +
      `  line, so it exercises the same loop in a handful of turns rather than a hundred:\n\n` +
      `      npm run headless -- tag 115\n`,
  );
  process.exit(report.ok ? 0 : 1);
}

console.log(
  `\n  ${report.ok ? '✓ gates pass' : '✗ gates still failing'} after ${meter.rounds.length} round(s), ${total.turns} turns\n` +
    `  ${M(total.tokens.cacheWrite)} cache writes · ${M(total.tokens.cacheRead)} cache reads · ` +
    `${(total.tokens.output / 1e3).toFixed(0)}k output\n` +
    `  estimated $${total.costUSD.toFixed(2)} — against a median of $62 for an interactive pass (npm run usage)\n` +
    `  meter → ${meterPath.replace(`${ROOT}/`, '')}\n`,
);

if (!report.ok) {
  console.log('  The file is in the tree and is not committed. Read it beside the facsimile before you do.\n');
}
process.exit(report.ok ? 0 : 1);
