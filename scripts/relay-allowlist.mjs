#!/usr/bin/env node
/**
 * Writes `relay/allowed.json` — the exact set of third-party files the relay
 * may fetch, derived from `editions.json`.
 *
 *   npm run relay:allowlist          rewrite it
 *   npm run relay:allowlist -- --check   fail if it is out of date
 *
 * ## Why a generated allowlist rather than a host pattern
 *
 * The facsimile relay answers one route, `/source/<shelfmark>.pdf`, against one
 * hardcoded upstream. Community editions cannot work that way: they live on
 * several hosts, under paths nobody controls. The obvious shortcut — allow any
 * `.pdf` under two hostnames — turns the relay into an open proxy for two
 * university web servers, which is exactly the thing its own comments say it
 * must not become.
 *
 * So the allowlist is the finite set of URLs the site actually offers, checked
 * in and diffable. A file that is not in `editions.json` cannot be fetched
 * through the relay, and adding one is a reviewable change rather than a
 * pattern quietly matching more than it did last week.
 *
 * ## The slug
 *
 * The route needs a short opaque key rather than the URL, so that nothing in a
 * path can steer a request. The PDF's own basename serves: it is short, stable
 * and already unique across the corpus. Collisions would silently make two
 * documents into one, so this throws on them rather than picking a winner.
 */

import { readFile, writeFile } from 'node:fs/promises';
import { resolve } from 'node:path';

const ROOT = resolve(import.meta.dirname, '..');
const OUT = resolve(ROOT, 'relay/allowed.json');

const editions = JSON.parse(await readFile(resolve(ROOT, 'src/content/editions.json'), 'utf8'));

/**
 * Every community document, not only the ones that need relaying today.
 *
 * `framable` is a fact about a remote server on the day it was measured, and
 * servers change: if a host dropped `X-Frame-Options` tomorrow, or added one,
 * the fix should be one flag in `editions.json` and not a regeneration of this
 * file plus a redeploy of the relay. The relay serving a
 * route nobody asks for costs nothing; a route missing when the client starts
 * asking for it costs a blank pane.
 */
const allowed = {};
for (const e of editions) {
  for (const d of e.documents ?? []) {
    const slug = d.url.split('/').pop().replace(/\.pdf$/i, '');
    if (!/^[\w.-]+$/.test(slug)) throw new Error(`Slug unusable in a URL path: ${slug}`);
    if (allowed[slug] && allowed[slug] !== d.url) {
      throw new Error(
        `Two documents share the slug "${slug}":\n  ${allowed[slug]}\n  ${d.url}\n` +
          'Relaying them would serve one under the other\'s name.',
      );
    }
    allowed[slug] = d.url;
  }
}

const sorted = Object.fromEntries(Object.entries(allowed).sort(([a], [b]) => a.localeCompare(b)));
const body = `${JSON.stringify(sorted, null, 2)}\n`;

if (process.argv.includes('--check')) {
  const current = await readFile(OUT, 'utf8').catch(() => '');
  if (current !== body) {
    process.stderr.write(
      'relay/allowed.json is out of date with editions.json — run: npm run relay:allowlist\n',
    );
    process.exit(1);
  }
  process.stdout.write(`relay/allowed.json is up to date (${Object.keys(sorted).length} files)\n`);
  process.exit(0);
}

await writeFile(OUT, body, 'utf8');
process.stdout.write(
  `relay/allowed.json — ${Object.keys(sorted).length} files, ` +
    `${new Set(Object.values(sorted).map((u) => new URL(u).hostname)).size} hosts\n`,
);
