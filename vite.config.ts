import { defineConfig, type Plugin } from 'vite'
import { request } from 'node:https'
import { resolve } from 'node:path'
import react from '@vitejs/plugin-react'
import tailwindcss from '@tailwindcss/vite'

/**
 * Streams Montpellier's own PDFs through this origin, so the pane can show
 * the original files.
 *
 * The pane cannot point at `grothendieck.umontpellier.fr` directly, and not
 * for want of trying. Two blockers, both measured:
 *
 * — The server sends `X-Frame-Options: SAMEORIGIN`. No other origin may embed
 *   it, so a probe iframe receives no document at all. This one is decisive on
 *   its own and would outlive every other fix.
 * — Its certificate expired on 10 December 2025, so the load fails TLS
 *   verification, and the click-through warning does not render in a frame.
 *
 * A cross-origin `fetch` is no way round it either: there are no CORS headers.
 * Both restrictions, though, are enforced by the *browser* against the remote
 * origin. A request made server-side is subject to neither — so this
 * middleware fetches the file and re-serves it from localhost, where the frame
 * is same-origin and the certificate is not in question. Nothing is stored:
 * the bytes pass straight through.
 *
 * **Range requests are what make this usable rather than a curiosity.**
 * Montpellier honours them (verified: `206` with a correct `Content-Range`),
 * so forwarding the browser's `Range` header means a viewer opening page 400
 * of the 204 MB Long March fetches the few hundred kilobytes it needs, not the
 * whole volume. Swallowing the header and streaming from byte zero would make
 * every page turn a full download.
 */
function montpellierSource(): Plugin {
  const UPSTREAM = 'https://grothendieck.umontpellier.fr/'

  const serve = (req: any, res: any, next: () => void) => {
    const m = /^\/source\/([\w-]+)\.pdf$/.exec(decodeURIComponent((req.url ?? '').split('?')[0]))
    if (!m) return next()

    // Only a shelfmark, and only ever as `<id>.pdf`. The pattern excludes
    // slashes and dots, so no request can be steered off this host or up the
    // path — this middleware must not become an open proxy.
    const url = `${UPSTREAM}${m[1]}.pdf`

    /**
     * `https.request` rather than `fetch`, for two reasons that both bite.
     *
     * `fetch` ignores a `node:https` agent outright — Node's implementation is
     * undici, which wants a `dispatcher`, and silently dropping the option
     * leaves the expired certificate rejected and every request failing with a
     * bare "fetch failed". And `rejectUnauthorized` belongs here, per request,
     * rather than in `NODE_TLS_REJECT_UNAUTHORIZED`, which is a process-wide
     * switch that would disable verification for everything else the dev
     * server ever does.
     *
     * The certificate is genuinely the University of Montpellier's, issued by
     * GEANT. It is its end date that has passed, not its identity.
     */
    const upstream = request(
      url,
      {
        rejectUnauthorized: false,
        headers: req.headers.range ? { Range: req.headers.range } : {},
      },
      (r) => {
        res.statusCode = r.statusCode ?? 502
        res.setHeader('Content-Type', 'application/pdf')
        res.setHeader('Accept-Ranges', 'bytes')
        for (const h of ['content-length', 'content-range']) {
          if (r.headers[h]) res.setHeader(h, r.headers[h] as string)
        }
        // A folder never changes once digitised, and a viewer seeking through
        // a 200 MB scan asks for a great many ranges.
        res.setHeader('Cache-Control', 'public, max-age=86400')
        r.pipe(res)
      },
    )

    // Montpellier down, or no network: say so plainly rather than hanging.
    upstream.on('error', (e: Error) => {
      res.statusCode = 502
      res.setHeader('Content-Type', 'text/plain; charset=utf-8')
      res.end(`Could not reach ${url}\n${e.message}\n`)
    })
    upstream.end()
  }

  return {
    name: 'montpellier-source',
    configureServer: (s) => void s.middlewares.use(serve),
    // `vite preview` serves `dist/`, which has no proxy of its own — without
    // this, checking a production build would show no facsimiles at all.
    configurePreviewServer: (s) => void s.middlewares.use(serve),
  }
}

export default defineConfig({
  plugins: [react(), tailwindcss(), montpellierSource()],
  // GitHub Pages serves a project site under /<repo>/; the deploy workflow
  // would fill BASE_PATH in that case. Here the site is published on the
  // custom domain grothendieck.commutator.io, so the root is correct.
  base: process.env.BASE_PATH ?? '/',
  build: {
    rollupOptions: {
      // One HTML entry per tab. Hosting is static: /motifs/ is served from its
      // own index.html, with no client-side router and no redirect trick. A URL
      // opened on one batch still works in six months, which matters when a
      // transcription stretches over months.
      input: {
        main: resolve(import.meta.dirname, 'index.html'),
        topos: resolve(import.meta.dirname, 'topos/index.html'),
        motifs: resolve(import.meta.dirname, 'motifs/index.html'),
        longueMarche: resolve(import.meta.dirname, 'longue-marche/index.html'),
        tardifs: resolve(import.meta.dirname, 'tardifs/index.html'),
        archive: resolve(import.meta.dirname, 'archive/index.html'),
        method: resolve(import.meta.dirname, 'method/index.html'),
      },
    },
  },
  server: {
    port: process.env.PORT ? Number(process.env.PORT) : 5173,
  },
})
