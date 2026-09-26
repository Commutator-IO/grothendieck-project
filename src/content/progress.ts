import handRaw from './hand.json';
import { UNEDITED } from './books.ts';
import { batchCount } from '../lib/batches.ts';

/**
 * Where the transcription stands, for the pages that say it without loading
 * the manifest: counted from src/content/hand.json (the batches that exist)
 * against the batches of the folders nobody else has edited — the same
 * denominator as the front page's « Where the work stands ».
 */
const HAND = handRaw as unknown as { folders: { id: string; batches: number }[] };
const done = new Map(HAND.folders.map((f) => [f.id, f.batches]));

const total = UNEDITED.reduce((a, c) => a + batchCount(c.pages), 0);
const transcribed = UNEDITED.reduce((a, c) => a + (done.get(c.id) ?? 0), 0);

export default {
  total,
  transcribed,
  share: `${((100 * transcribed) / total).toFixed(1)}%`,
  folders: HAND.folders.length,
};
