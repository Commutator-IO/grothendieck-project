import { useEffect, useState } from 'react';
import type { Edition, Manifest } from './types.ts';

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

/**
 * Whether this deployment can serve facsimiles at all.
 *
 * In development the relay is a dev-server middleware; in production it is a
 * separate service, which may or may not be reachable. Rather than guess from
 * the hostname — which would be wrong the moment the deployment changes — one
 * cheap request settles it, and the pane says plainly which situation the
 * reader is in.
 */
/**
 * Wakes the relay before a reader has asked for a facsimile at all.
 *
 * The deployed relay spins down after inactivity, and the next request pays a
 * 30-50s cold start — during which its host answers with its own loading
 * page instead of proxying through. The facsimile pane loads the PDF in an
 * `<iframe>`, so that loading page renders inside the pane rather than
 * failing quietly, which is worse than the delay itself.
 *
 * `Header` calls this once, from every page, since any of them may lead to a
 * batch being opened. It is a fire-and-forget hit on `/health` — cheapest
 * route the relay has, no request to Montpellier behind it — not the
 * availability probe `useFacsimileProxy` already makes, which stays where it
 * is because it also gates the pane's UI and belongs to the page that shows
 * it. This one only buys the relay a head start; nothing reads its result.
 */
export function warmRelay() {
  if (!RELAY) return; // dev: the Vite middleware needs no waking
  // `no-cors`: nothing here reads the answer, and /health sends no CORS
  // headers, so a plain fetch would log a policy error on every page load —
  // noise that reads like a fault. An opaque response is exactly enough: the
  // request still reaches the host, which is the whole point.
  fetch(`${RELAY}/health`, { mode: 'no-cors' }).catch(() => {
    // Nothing to do here: a reader who goes on to open a batch gets the real
    // state from useFacsimileProxy.
  });
}

/** Whether the pane may mount a frame against the relay yet. */
export type RelayState = 'waking' | 'ready' | 'absent';

export function useFacsimileProxy(): RelayState {
  const [state, setState] = useState<RelayState>('waking');
  useEffect(() => {
    let alive = true;
    let timer: ReturnType<typeof setTimeout>;
    let tries = 0;

    /**
     * Answering is not the test — answering *with a PDF* is.
     *
     * A relay asleep on a free tier does not refuse the connection: its host
     * accepts it and serves its own start-up page, with a perfectly good
     * status and `text/html`. Read as "up", that page is what the pane would
     * then frame. So the probe keeps asking until the bytes are a PDF, and
     * only gives up after the cold start has had longer than it takes.
     */
    const probe = async () => {
      try {
        // A one-byte range: enough to prove the proxy answers, without pulling
        // a 35 MB folder just to find out.
        const r = await fetch(`${RELAY}/source/26.pdf`, { headers: { Range: 'bytes=0-0' } });
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
  const html = transcript(m, cote, k).html;
  return { transcribed: html.includes('fr'), modernised: html.includes('modern') };
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
