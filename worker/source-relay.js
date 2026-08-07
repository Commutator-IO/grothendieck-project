/**
 * The production relay: what the Vite middleware does locally, on the edge.
 *
 * The reading view is two panes side by side, and that is not decoration — a
 * transcription one has to check in another tab is a transcription one stops
 * checking. So the facsimile has to render *in* the page, which means it has
 * to be served from the site's own origin. Montpellier will not allow that
 * directly:
 *
 * — `X-Frame-Options: SAMEORIGIN` forbids any other origin from framing it.
 * — Its certificate expired on 10 December 2025.
 *
 * Both are enforced by the browser against the remote origin, so a relay
 * settles both: the browser sees only this origin, framing a document with a
 * valid certificate.
 *
 * ## Why it fetches through a second hostname
 *
 * A Worker cannot skip TLS verification — there is no `rejectUnauthorized` in
 * the Workers runtime, and fetching `grothendieck.umontpellier.fr` directly
 * fails the handshake on the expired certificate. Plain HTTP is no way round
 * it either: the host answers `301` to HTTPS.
 *
 * Cloudflare's *proxy*, however, does not validate origin certificates in
 * SSL/TLS mode **Full** (as opposed to Full strict). So the file is fetched
 * through a proxied hostname of ours pointed at Montpellier, which terminates
 * with our certificate and accepts theirs. Two hops, one of which exists
 * solely because of a lapsed date.
 *
 * See the README for the two dashboard steps this expects. If they are not in
 * place, this Worker returns 502 and the pane says so — it does not fall back
 * to opening a tab.
 *
 * ## What it does not do
 *
 * It does not cache the fonds into R2, and does not copy it anywhere. Bytes
 * pass through, `Range` included — which is what makes a 204 MB volume usable:
 * a viewer opening leaf 400 fetches a few hundred kilobytes, not the volume.
 * Nothing here redistributes the archive; it relays a request the reader's own
 * browser would have made if it had been allowed to.
 */

/** Only a shelfmark, and only as `<id>.pdf` — never a path, never another host. */
const PATH = /^\/source\/([\w-]+)\.pdf$/;

export default {
  async fetch(request, env) {
    const url = new URL(request.url);
    const m = PATH.exec(url.pathname);
    if (!m) return new Response('Not found', { status: 404 });

    // Only reads. A relay that forwarded POST would be a relay someone else
    // could use for something other than reading an archive.
    if (request.method !== 'GET' && request.method !== 'HEAD') {
      return new Response('Method not allowed', { status: 405, headers: { Allow: 'GET, HEAD' } });
    }

    const origin = env.SOURCE_ORIGIN ?? 'https://montpellier.commutator.io';
    const target = `${origin}/${m[1]}.pdf`;

    let upstream;
    try {
      upstream = await fetch(target, {
        method: request.method,
        // The viewer's range request is forwarded verbatim; everything else is
        // dropped, so nothing of the reader travels to the upstream.
        headers: request.headers.get('Range') ? { Range: request.headers.get('Range') } : {},
        // A digitised folder does not change. Long edge caching is what keeps
        // a reader paging through a scan from re-fetching the same ranges.
        cf: { cacheEverything: true, cacheTtl: 86400 },
      });
    } catch (e) {
      return new Response(
        `Could not reach ${target}\n${e.message}\n\n` +
          'The relay hostname is probably not set up — see the README.\n',
        { status: 502, headers: { 'Content-Type': 'text/plain; charset=utf-8' } },
      );
    }

    // The response is rebuilt rather than forwarded: `X-Frame-Options` is
    // exactly what has to go, and passing it through would defeat the entire
    // purpose of the relay.
    const headers = new Headers();
    headers.set('Content-Type', 'application/pdf');
    headers.set('Accept-Ranges', 'bytes');
    for (const h of ['content-length', 'content-range', 'etag', 'last-modified']) {
      const v = upstream.headers.get(h);
      if (v) headers.set(h, v);
    }
    headers.set('Cache-Control', 'public, max-age=86400');
    // Framed only by this site. Stripping Montpellier's header does not mean
    // handing the file to everyone: the relay exists for this reading view.
    headers.set('X-Frame-Options', 'SAMEORIGIN');

    return new Response(upstream.body, { status: upstream.status, headers });
  },
};
