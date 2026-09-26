/**
 * The inventory's datings, read as ranges without losing what kind of date
 * each end is.
 *
 * The archivists write « 1965-[vers 1971] »: a start read on the page, an end
 * worked out and approximate. Collapsing that to 1965–1971 would throw away
 * the one distinction the Timeline exists to show, so each end keeps whether
 * it was bracketed (deduced, not read) and its qualifier — « vers » (about),
 * « à partir de » and « après » (from, with no end given), « avant » (before,
 * with no start given), « années » (the decade or decades).
 */
export type Qualifier = 'vers' | 'from' | 'after' | 'before' | 'decades' | null;

export interface End {
  year: number;
  /** Inside the archivists' square brackets: a date they deduced. */
  inferred: boolean;
  qualifier: Qualifier;
}

export interface Dating {
  raw: string;
  /** Null when the start is open — « [avant 1970] ». */
  start: End | null;
  /** Null when the end is open — « [à partir de 1982] ». */
  end: End | null;
}

const QUAL: Record<string, Qualifier> = {
  vers: 'vers',
  'à partir de': 'from',
  après: 'after',
  avant: 'before',
  années: 'decades',
};

/** Parse one dating; null for « s.d. » or anything without a year. */
export function parseDating(raw: string): Dating | null {
  const ends: End[] = [];
  let depth = 0;
  let q: Qualifier = null;
  for (const m of raw.matchAll(/(\[)|(\])|(vers|à partir de|après|avant|années)|(\d{4})|(-)/g)) {
    if (m[1]) depth++;
    else if (m[2]) depth = Math.max(0, depth - 1);
    else if (m[3]) q = QUAL[m[3]];
    else if (m[4]) {
      ends.push({ year: Number(m[4]), inferred: depth > 0, qualifier: q });
      // « années 1960-1970 » and « à partir de 1964-vers 1970 »: a qualifier
      // governs the year it precedes, except « années », which spans both.
      if (q !== 'decades') q = null;
    }
  }
  if (!ends.length) return null;
  const first = ends[0];
  const last = ends[ends.length - 1];
  if (ends.length === 1) {
    if (first.qualifier === 'from' || first.qualifier === 'after') return { raw, start: first, end: null };
    if (first.qualifier === 'before') return { raw, start: null, end: first };
    return { raw, start: first, end: first };
  }
  // « [à partir de 1962- à partir de 1971] »: the second « from » still has
  // no end; the range is at least 1962–1971 and open after.
  return { raw, start: first, end: last.qualifier === 'from' ? { ...last } : last };
}

/** Whether the end of a dating is open (no year given after its last one). */
export const openEnd = (d: Dating) => d.end === null || d.end.qualifier === 'from' || d.end.qualifier === 'after';
export const openStart = (d: Dating) => d.start === null;
