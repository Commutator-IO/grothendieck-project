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

**That last point is worth stating plainly, because it is easy to lose:** the
relay does not need to live on `commutator.io`, or on any domain of ours. A
bare `…onrender.com` hostname works exactly as well as `facsimile.commutator.io`
would. Nothing about the pane cares what the origin is called — only that its
certificate is valid and that it permits this site to frame it.

## Deploying

One file, no dependencies, nothing stored. Any container host works. The
requirement is narrow and rules out most of the cheap options: **a real Node
process**, because `rejectUnauthorized` is what gets past the expired
certificate. Cloudflare Workers, Deno Deploy and every other V8/edge runtime
fail on that one point, not on effort.

### Render — where it actually runs

**Deployed:** `grothendieck-relay`, free plan, Frankfurt —
`https://grothendieck-relay.onrender.com`
([dashboard](https://dashboard.render.com/web/srv-d9ri0iv10e5c7384nnfg)).

Free, no DNS of ours involved, and the hostname it hands back already has a
valid certificate — the only property the browser insists on. The cost is a
cold start: the service sleeps after 15 minutes idle and takes about a minute
to wake. The pane handles that by design, showing the "not answering" panel
with a *Try again* button, so the failure is visible and self-correcting rather
than silent.

#### How it was created

From the CLI (`brew install render`, then `render login`). Note the
`--repo` flag with no GitHub App installed: the repository is public, so Render
clones it by URL. The trade-off is that pushes do not trigger a deploy
automatically — see *Redeploying* below, which is a single command.

```bash
render workspace set "Michel's workspace" --confirm

render services create \
  --name grothendieck-relay \
  --type web_service \
  --runtime docker \
  --repo https://github.com/Commutator-IO/grothendieck-project \
  --branch main \
  --root-directory relay \
  --plan free \
  --region frankfurt \
  --health-check-path /health \
  --env-var PORT=8080 \
  --env-var ALLOWED_ORIGINS=https://grothendieck.commutator.io \
  --confirm --output json
```

`render.yaml` in this directory carries the same configuration as a blueprint,
for anyone who prefers **New → Blueprint** in the dashboard. That route needs
Render's GitHub App installed on the organisation; the CLI route above does
not, which is why it was used.

#### Redeploying, logs, status

```bash
render deploys create srv-d9ri0iv10e5c7384nnfg --confirm   # after changing server.mjs
render logs --resources srv-d9ri0iv10e5c7384nnfg --tail
render services --output text --confirm
```

### When the free plan ends

It will, eventually. Heroku withdrew its free dynos in 2022 and others have
followed since; assuming Render is permanent would be the one mistake worth
avoiding here. So the question is not *if* but *what breaks when it does* —
and the answer is deliberately: very little.

**Nothing runs out on its own.** The free plan gives 750 instance-hours a
month against a month's 730, so one service can stay up continuously; the cap
only bites if several free services share the workspace. Bandwidth is 100 GB a
month, and range requests mean a reader consumes a few hundred kilobytes per
page rather than a whole volume — the whole open fonds is about 28 GB, so
ordinary reading is nowhere near it.

**The failure is visible, not silent.** If the relay stops answering — plan
withdrawn, quota exhausted, host down — `useFacsimileProxy()` gets no answer
and the pane shows the "not answering" panel with a *Try again* button and a
link to the tracking issue. The transcription, the diagrams and the downloads
all keep working, and the pane header's **Source ↗** still opens the folder at
Montpellier. The site degrades to what it was before the relay existed.

**Moving hosts is one variable.** Nothing in the codebase knows where the relay
lives: `facsimileUrl()` reads `VITE_RELAY`, which the deploy workflow fills from
the `RELAY_URL` repository variable. To move:

1. Deploy `relay/` somewhere else — it is one dependency-free file plus a
   Dockerfile, and `PORT` and `ALLOWED_ORIGINS` are the only configuration.
2. `gh variable set RELAY_URL --body https://<new-host>`
3. Re-run the Pages deploy.

No code change, no DNS change, no migration.

Where to go, if that day comes:

| Host | Cost | Note |
|---|---|---|
| **Render Starter** | $7/month | The same service with no sleep. One flag, nothing else to change. |
| **A small VPS** | ~$4/month | `node server.mjs` behind any TLS terminator. Cheapest, and the most to maintain. |
| **Any container host** | varies | The Dockerfile is the whole contract: `PORT` and `ALLOWED_ORIGINS` in, a hostname out. |

Whichever it is, the migration is the three steps above. The relay was written
to be disposable — one file, no dependencies, no state — precisely so that the
host is never a decision worth agonising over.

**How you would find out.** Nobody watches a facsimile pane. There is no
monitoring, and a reader seeing the panel is currently the alerting system.
A scheduled `curl` against `/health` that opens an issue on failure would fix
that; it does not exist yet.

### Anywhere else

Railway, a VPS, anything that runs a container — point it at the `Dockerfile`,
or just run it:

```bash
PORT=8080 ALLOWED_ORIGINS=https://grothendieck.commutator.io node server.mjs
```

## Pointing the site at it

Set a repository variable **`RELAY_URL`** (Settings → Secrets and variables →
Actions → Variables) to the relay's origin — currently
`https://grothendieck-relay.onrender.com`. The deploy workflow passes it to the
build as `VITE_RELAY`. Nothing else changes; local `npm run dev` keeps using its
own middleware and ignores the variable.

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
