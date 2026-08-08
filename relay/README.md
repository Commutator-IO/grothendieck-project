# The facsimile relay

Montpellier's own PDFs, re-served over a valid certificate so the site can
show them beside the transcription.

## Why this exists

Three facts about `grothendieck.umontpellier.fr`, all measured:

- **`X-Frame-Options: SAMEORIGIN`** — no other origin may embed its files. A
  probe iframe receives no document at all.
- **Certificate expired 10 December 2025** — the load fails TLS verification,
  and the click-through warning does not render inside a frame.
- **No CORS headers** — a cross-origin `fetch` is barred too.

All three are enforced by the *browser* against the remote origin. None applies
to a request made server-side. So a relay settles all three at once: the
browser sees one origin, with a valid certificate, that permits framing.

## Why not a Cloudflare Worker, and why no DNS change

A Worker **cannot** skip TLS verification — there is no `rejectUnauthorized` in
that runtime, and its `fetch()` throws on the expired certificate. The usual
way round is Cloudflare's *proxy* in SSL/TLS mode Full, which tolerates a bad
origin certificate — but that needs the zone on Cloudflare, and `commutator.io`
is on Google Cloud DNS (Squarespace).

It is worth being clear why no DNS record can substitute. **DNS points at
addresses; it does not terminate TLS.** A CNAME from `commutator.io` to
Montpellier would send the browser straight there, to a certificate that is now
both expired *and* issued for the wrong hostname — strictly worse.

Node has `rejectUnauthorized`, so this needs no DNS arrangement whatsoever:
deploy it anywhere, take the hostname the platform gives you — it already has a
valid certificate — and point the site at it. Cross-origin is fine, because
`frame-ancestors` is what decides who may frame a document, and the relay sets
it.

## Deploying

One file, no dependencies, nothing stored. Any container host works.

### fly.io

```bash
cd relay
fly launch --no-deploy --name grothendieck-relay
fly deploy
```

Scales to zero between readers; a suspended machine resumes in under a second.

### Anywhere else

Render, Railway, a VPS — point them at the `Dockerfile`, or just run it:

```bash
PORT=8080 ALLOWED_ORIGINS=https://grothendieck.commutator.io node server.mjs
```

## Pointing the site at it

Set a repository variable **`RELAY_URL`** (Settings → Secrets and variables →
Actions → Variables) to the relay's origin, e.g. `https://grothendieck-relay.fly.dev`.
The deploy workflow passes it to the build as `VITE_RELAY`. Nothing else changes;
local `npm run dev` keeps using its own middleware and ignores the variable.

Left unset, the built site simply has no relay and every batch shows the "not
answering" panel — the correct state for a deployment without one, not a
failure.

## What it deliberately does not do

It **stores nothing and copies nothing**. Bytes pass straight through, `Range`
included — which is what makes a 204 MB volume usable: opening page 400 fetches
a few hundred kilobytes, not the volume.

It is **not a general proxy**: only `GET`/`HEAD`, only
`/source/<shelfmark>.pdf`, and `ALLOWED_ORIGINS` decides who may frame the
result. Nothing identifying the reader — cookies, user agent, referer — is
forwarded to Montpellier.

That last restriction is the one worth keeping. Relaying a request a reader's
own browser would have made is one thing; standing up a public mirror of
someone else's archive is another, and is not ours to do.

## Checking it

```bash
curl -s http://localhost:8080/health
curl -sD- -o /dev/null -r 0-99 http://localhost:8080/source/115.pdf
```

The second should give `206`, a `Content-Range`, and a `Content-Security-Policy`
naming your site. Verified byte-identical to the source on the first 4 KB of
folder 115.
