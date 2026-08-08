#!/usr/bin/env node
/**
 * The facsimile relay: Montpellier's own PDFs, re-served over a valid
 * certificate and framable by the site.
 *
 * This is the same twenty lines the Vite dev middleware runs, packaged to be
 * deployed. It exists because of three facts about
 * `grothendieck.umontpellier.fr`, all measured rather than assumed:
 *
 * — `X-Frame-Options: SAMEORIGIN` — no other origin may embed its files, so a
 *   probe iframe receives no document at all.
 * — Its certificate expired on 10 December 2025, so the load fails TLS
 *   verification, and the click-through warning does not render in a frame.
 * — No CORS headers, so a cross-origin `fetch` is barred too.
 *
 * All three bind the *browser* against the remote origin, and none applies to
 * a request made server-side.
 *
 * ## Why Node
 *
 * Skipping verification of the expired certificate requires
 * `rejectUnauthorized`, which Node has and edge or serverless V8 runtimes do
 * not — there, `fetch()` throws and no configuration helps. That one line
 * below decides the hosting choice for this whole file.
 *
 * The upside is that it needs no DNS arrangement whatsoever: deploy this
 * anywhere, take the hostname the platform gives you — it already has a valid
 * certificate — and point the site at it. The relay does not have to live on
 * a domain of ours, because `frame-ancestors` decides who may frame a
 * document, not what the origin is called.
 *
 * ## What it does not do
 *
 * It stores nothing and copies nothing. Bytes pass straight through, `Range`
 * included — which is what makes a 204 MB volume usable: opening page 400
 * fetches a few hundred kilobytes, not the volume.
 *
 * It is deliberately not a general proxy: only `GET`/`HEAD`, only
 * `/source/<shelfmark>.pdf`, and `ALLOWED_ORIGINS` decides who may frame it.
 * A relay that forwarded anything to anywhere would be someone else's problem
 * within a week.
 *
 *   PORT=8787 ALLOWED_ORIGINS=https://grothendieck.commutator.io node server.mjs
 */

import { createServer } from 'node:http';
import { request as httpsRequest } from 'node:https';

const PORT = Number(process.env.PORT ?? 8787);
const UPSTREAM = 'https://grothendieck.umontpellier.fr/';

/**
 * Who may embed the relay's responses.
 *
 * This is the difference between relaying a request a reader's own browser
 * would have made, and standing up a public mirror of someone else's archive.
 * The first is reasonable; the second is not ours to do.
 */
const ALLOWED_ORIGINS = (process.env.ALLOWED_ORIGINS ?? 'https://grothendieck.commutator.io')
  .split(',')
  .map((s) => s.trim())
  .filter(Boolean);

/** Only a shelfmark, and only as `<id>.pdf` — never a path, never another host. */
const PATH = /^\/source\/([\w-]+)\.pdf$/;

/** How the relay identifies itself to Montpellier. See the request below. */
const RELAY_UA =
  'grothendieck.commutator.io facsimile relay (+https://grothendieck.commutator.io/method/)';

const server = createServer((req, res) => {
  const url = new URL(req.url ?? '/', 'http://localhost');

  if (url.pathname === '/health') {
    res.writeHead(200, { 'Content-Type': 'text/plain' });
    return res.end('ok\n');
  }

  const m = PATH.exec(decodeURIComponent(url.pathname));
  if (!m) {
    res.writeHead(404, { 'Content-Type': 'text/plain' });
    return res.end('Not found\n');
  }

  if (req.method !== 'GET' && req.method !== 'HEAD') {
    res.writeHead(405, { Allow: 'GET, HEAD', 'Content-Type': 'text/plain' });
    return res.end('Method not allowed\n');
  }

  const target = `${UPSTREAM}${m[1]}.pdf`;

  /**
   * `rejectUnauthorized: false` for this upstream and this upstream only.
   *
   * The certificate is genuinely the University of Montpellier's, issued by
   * GEANT; it is its end date that has passed, not its identity. Setting it
   * per request rather than through `NODE_TLS_REJECT_UNAUTHORIZED` keeps the
   * exception to the one connection that needs it.
   */
  const upstream = httpsRequest(
    target,
    {
      method: req.method,
      rejectUnauthorized: false,
      /**
       * Nothing identifying the *reader* travels onward — no cookies, no
       * referer, and the reader's own user agent is dropped. Only the range
       * they asked for.
       *
       * But the relay names *itself*. Without this, Montpellier's logs show
       * requests with no user agent at all, which is what a scraper looks
       * like — the worst possible impression for something whose whole
       * defence is that it stores nothing and would rather not exist. An
       * archivist reading those logs can now see what the traffic is and
       * where to complain, and the URL leads to the page explaining why a
       * relay is needed and what would let us delete it.
       */
      headers: {
        'User-Agent': RELAY_UA,
        ...(req.headers.range ? { Range: req.headers.range } : {}),
      },
    },
    (up) => {
      const headers = {
        'Content-Type': 'application/pdf',
        'Accept-Ranges': 'bytes',
        // A digitised folder does not change. Long caching is what keeps a
        // reader paging through a scan from re-fetching the same ranges.
        'Cache-Control': 'public, max-age=86400',
        // Montpellier's own X-Frame-Options is deliberately not forwarded —
        // removing it is the entire purpose — but it is replaced rather than
        // dropped, so the file is framable by this site and nobody else.
        'Content-Security-Policy': `frame-ancestors ${ALLOWED_ORIGINS.join(' ')}`,
      };
      for (const h of ['content-length', 'content-range', 'etag', 'last-modified']) {
        if (up.headers[h]) headers[h] = up.headers[h];
      }
      const origin = req.headers.origin;
      if (origin && ALLOWED_ORIGINS.includes(origin)) {
        headers['Access-Control-Allow-Origin'] = origin;
      }

      res.writeHead(up.statusCode ?? 502, headers);
      up.pipe(res);
    },
  );

  // Montpellier down, or no network: say so plainly rather than hanging.
  upstream.on('error', (e) => {
    res.writeHead(502, { 'Content-Type': 'text/plain; charset=utf-8' });
    res.end(`Could not reach ${target}\n${e.message}\n`);
  });
  upstream.end();
});

server.listen(PORT, '0.0.0.0', () => {
  process.stdout.write(
    `Facsimile relay on :${PORT}\n  upstream  ${UPSTREAM}\n` +
      `  framable by  ${ALLOWED_ORIGINS.join(', ')}\n`,
  );
});
