import { useEffect, useState } from 'react';
import type { Edition, Manifest, TranscriptEntry } from './types.ts';

/**
 * The twenty-page batch, shared by the reading panes and by the skill.
 *
 * Twenty is not a round number picked for tidiness. It is about as much as a
 * model holds in one pass before the tail of the output degrades, and about as
 * much as a person re-reads in one sitting when checking a transcription
 * against the page. So the same division serves both ends: what the right pane
 * shows is the very file handed to the transcriber — not an extract, not a
 * re-render.
 */
export const BATCH_SIZE = 20;

export const batchCount = (pages: number) => Math.max(1, Math.ceil(pages / BATCH_SIZE));

/** The archive pages a batch covers, numbered as the inventory numbers them. */
export function batchRange(k: number, pages: number): { first: number; last: number } {
  return { first: (k - 1) * BATCH_SIZE + 1, last: Math.min(k * BATCH_SIZE, pages) };
}

export const batchId = (cote: string, batch: number) => `${cote}#${batch}`;

export const batchName = (k: number) => `batch-${String(k).padStart(2, '0')}`;

/**
 * The folder's own PDF, as Montpellier serves it, streamed through this origin.
 *
 * Not a local copy and not a cut-down extract: the same file, byte for byte,
 * fetched on demand. Montpellier honours range requests and the proxy forwards
 * them, so opening page 400 of a 204 MB volume costs a few hundred kilobytes
 * rather than the volume.
 *
 * It has to pass through this origin because the browser will not frame
 * Montpellier directly — `X-Frame-Options: SAMEORIGIN`, plus a certificate
 * that expired on 10 December 2025. Both are enforced by the browser against
 * the remote origin, and neither applies to a request made server-side.
 */
export const facsimileUrl = (cote: string) => `${RELAY}/source/${cote}.pdf`;

/**
 * Where the relay lives.
 *
 * Empty in development, where the Vite middleware answers `/source/*` on this
 * same origin. In production it is the deployed relay's absolute URL, supplied
 * at build time as `VITE_RELAY` — a static host has no middleware, and the
 * facsimile has to come from somewhere that terminates TLS on Montpellier's
 * behalf.
 *
 * Cross-origin is fine here, and is why no DNS arrangement is needed: the
 * relay sends `frame-ancestors` naming this site, which is what governs
 * whether a document may be framed. The relay's own certificate is valid,
 * which is the only other thing the browser insists on.
 */
const RELAY = (import.meta.env.VITE_RELAY ?? '').replace(/\/$/, '');

/**
 * The PDF page showing a given archive page.
 *
 * Montpellier prefixes every folder with a generated cover sheet — title,
 * shelfmark, dating — which is not a page of Grothendieck's. The inventory
 * counts pages without it ("Cote n° 26, 10 pages"); the file counts with it.
 * One is therefore always one more than the other, and this is the only place
 * that knows it.
 */
export const pdfIndexOf = (page: number) => page + 1;

export const transcriptUrl = (cote: string, k: number, edition: Edition, ext: string) =>
  `/transcripts/${cote}/${batchName(k)}.${edition}.${ext}`;

/**
 * The same, for an edition whose unit is the folder rather than the batch.
 *
 * `folder.modern.tex` covers a shelfmark entire. It was once written as
 * `batch-01.modern.tex`, which was the wrong name for it in a way that showed:
 * a reading of all 54 pages of folder 161-3 was reported as "1/3 modernised",
 * and its Modernised toggle was dead on the two batches it also covered.
 */
export const folderTranscriptUrl = (cote: string, edition: Edition, ext: string) =>
  `/transcripts/${cote}/folder.${edition}.${ext}`;

/** The folder-wide artifacts, if this shelfmark has any. */
export const folderEntry = (m: Manifest | null, cote: string): TranscriptEntry | undefined =>
  m?.folders?.[cote];

/** Whether a given edition of a batch is served by the folder-wide file. */
export function servedByFolder(
  m: Manifest | null,
  cote: string,
  edition: Edition,
  ext: 'html' | 'tex' | 'pdf',
): boolean {
  return (folderEntry(m, cote)?.[ext] ?? []).includes(edition);
}

/**
 * Where a batch's edition actually lives.
 *
 * The folder-wide file wins when it exists, because it is the one that covers
 * the pages in view; the per-batch file is the fallback. Every link to a
 * reading view or a download goes through here, so the two namings cannot
 * drift apart.
 */
export function editionUrl(
  m: Manifest | null,
  cote: string,
  k: number,
  edition: Edition,
  ext: 'html' | 'tex' | 'pdf',
): string {
  return servedByFolder(m, cote, edition, ext)
    ? folderTranscriptUrl(cote, edition, ext)
    : transcriptUrl(cote, k, edition, ext);
}

/**
 * Every edition available for a batch, counting the folder-wide ones.
 *
 * A batch of folder 161-3 has its own `fr` transcription and no `modern` file
 * of its own; the folder's reading supplies that. Merging the two is what lets
 * the toggle be live on all three batches.
 */
export function availableFor(
  m: Manifest | null,
  cote: string,
  k: number,
): TranscriptEntry {
  const own = transcript(m, cote, k);
  const whole = folderEntry(m, cote);
  if (!whole) return own;
  const merge = (a: Edition[], b: Edition[]) => [...new Set([...a, ...b])];
  return {
    html: merge(own.html, whole.html),
    tex: merge(own.tex, whole.tex),
    pdf: merge(own.pdf, whole.pdf),
  };
}

/** The original PDF at Montpellier — offered as a fallback, never in a frame. */
export const sourceUrl = (cote: string) => `https://grothendieck.umontpellier.fr/${cote}.pdf`;

/**
 * What is actually present locally.
 *
 * The site ships without a single byte of the fonds: the four books would come
 * to several gigabytes. The manifest, written by `npm run archive`, says which
 * batches exist; the rest render with the command that produces them rather
 * than with a dead link. A missing manifest is not an error — it is the state
 * of a freshly cloned repository.
 */
export function useManifest(): Manifest | null {
  const [m, setM] = useState<Manifest | null>(null);
  useEffect(() => {
    let alive = true;
    fetch('/manifest.json')
      .then((r) => (r.ok ? r.json() : null))
      .then((j) => alive && setM(j))
      .catch(() => {
        // Nothing mirrored yet: the site still works, as an inventory.
      });
    return () => {
      alive = false;
    };
  }, []);
  return m;
}

/** Whether the pane may mount a frame against the relay yet. */
export type RelayState = 'waking' | 'ready' | 'absent';

/**
 * Whether this deployment can serve facsimiles — and, by the same request,
 * what wakes the relay.
 *
 * In development the relay is a dev-server middleware; in production it is a
 * separate service, which may or may not be reachable. Rather than guess from
 * the hostname — which would be wrong the moment the deployment changes — one
 * cheap request settles it, and the pane says plainly which situation the
 * reader is in.
 *
 * That request is also the head start. A deployed relay spins down when idle
 * and pays a 30-50s cold start on the next call, so something has to knock
 * before a reader picks a folder. This hook runs when the notebook page
 * mounts — while its inventory is still being read — which is early enough,
 * and it is the only page a facsimile can be opened from.
 *
 * There was a second, dedicated knock on `/health` from every page's header.
 * It is gone — one request, on the one page a facsimile can be opened from.
 */

export function useFacsimileProxy(): RelayState {
  const [state, setState] = useState<RelayState>('waking');
  useEffect(() => {
    let alive = true;
    let timer: ReturnType<typeof setTimeout>;
    let tries = 0;

    /**
     * Answering is not the test — answering *as the relay* is.
     *
     * An instance asleep on a free tier does not refuse the connection: its
     * host accepts it and serves a start-up page, with a perfectly good status
     * and `text/html`. Read as "up", that page is what the pane would then
     * frame. Both routes below therefore check what came back, not merely that
     * something did, and `no-store` keeps a cached answer from reporting a
     * sleeping instance as awake.
     */
    let blocked = false;
    const probe = async () => {
      // `/health` first: the relay answers it alone, with nothing asked of
      // Montpellier, so an arrival on this page costs them nothing.
      if (!blocked) {
        try {
          const r = await fetch(`${RELAY}/health`, { cache: 'no-store' });
          if (r.ok && (r.headers.get('content-type') ?? '').startsWith('text/plain')) {
            if (alive) setState('ready');
            return;
          }
        } catch {
          /**
           * Content blockers cancel this one outright
           * (`ERR_BLOCKED_BY_CLIENT`) — a third-party call to a route named
           * "health" is a plausible telemetry beacon, and no amount of
           * innocence at our end changes how it reads. Noted once, so the
           * fallback below carries the rest of the round rather than adding a
           * refused request to the console every five seconds.
           */
          blocked = true;
        }
      }

      try {
        // The fallback costs Montpellier one byte — a range request rather
        // than the 35 MB folder — and it is unmistakably a fetch of content,
        // which is what gets it past the blockers that stop /health.
        const r = await fetch(`${RELAY}/source/26.pdf`, {
          headers: { Range: 'bytes=0-0' },
          cache: 'no-store',
        });
        if (r.ok && r.headers.get('content-type') === 'application/pdf') {
          if (alive) setState('ready');
          return;
        }
      } catch {
        // Unreachable this time round, which a waking host also looks like.
      }

      if (!alive) return;
      if (++tries >= 12) return setState('absent');
      timer = setTimeout(probe, 5000);
    };

    probe();
    return () => {
      alive = false;
      clearTimeout(timer);
    };
  }, []);
  return state;
}

export function transcript(m: Manifest | null, cote: string, k: number) {
  return m?.transcripts?.[batchId(cote, k)] ?? { html: [], tex: [], pdf: [] };
}

/** What exists for a batch, as the state model consumes it. */
export function evidence(m: Manifest | null, cote: string, k: number) {
  // The folder-wide reading counts for every batch it covers. Reading only the
  // batch's own row is what made a fully modernised folder report "1/3".
  const html = availableFor(m, cote, k).html;
  return { transcribed: html.includes('fr'), modernised: html.includes('modern') };
}

/**
 * How far the folder's transcription has got.
 *
 * This exists because the two editions have different units. A transcription
 * is per batch, so "is it there" is a question about the batch in front of
 * you. The modernised reading takes the folder whole — its argument runs
 * across the batch boundaries — so "can it be made yet" is never a question
 * about one batch, and answering it from the batch in view would tell a reader
 * looking at batch 1 that everything is ready when batch 3 is what is holding
 * it up.
 */
export function folderTranscription(m: Manifest | null, cote: string, pages: number) {
  const total = batchCount(pages);
  const missing: number[] = [];
  for (let k = 1; k <= total; k++) if (!evidence(m, cote, k).transcribed) missing.push(k);
  return { total, missing, done: total - missing.length, complete: missing.length === 0 };
}

/** What was claimed for a batch in `transcripts/status.json`. */
export function declared(m: Manifest | null, cote: string, k: number) {
  return m?.declared?.[batchId(cote, k)];
}

/**
 * The folder's tags — the modern English vocabulary its modernised readings
 * filed themselves under, via their `\keywords{}` lines. Empty until
 * something of the folder has been modernised, which is the point.
 */
export function folderTags(m: Manifest | null, cote: string): string[] {
  return m?.tags?.[cote] ?? [];
}
