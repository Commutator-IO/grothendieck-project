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
export function useFacsimileProxy(): boolean | null {
  const [ok, setOk] = useState<boolean | null>(null);
  useEffect(() => {
    let alive = true;
    // A one-byte range: enough to prove the proxy answers, without pulling a
    // 35 MB folder just to find out.
    fetch(`${RELAY}/source/26.pdf`, { headers: { Range: 'bytes=0-0' } })
      .then((r) => alive && setOk(r.ok && r.headers.get('content-type') === 'application/pdf'))
      .catch(() => alive && setOk(false));
    return () => {
      alive = false;
    };
  }, []);
  return ok;
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
