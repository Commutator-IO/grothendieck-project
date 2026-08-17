import { useMemo, useState } from 'react';
import { BY_ID, COTES, GROUPS } from '../content/catalogue.ts';
import { batchCount } from '../lib/batches.ts';
import type { Cote } from '../lib/types.ts';

/** Status of a folder in one word, which is what the mosaic colours. */
type FolderState = 'here' | 'community' | 'untouched';

const folderState = (transcribedHere: boolean, hasEdition: boolean): FolderState =>
  transcribedHere ? 'here' : hasEdition ? 'community' : 'untouched';

/**
 * The fonds by area, as a wall of blocks.
 *
 * The folder list below answers "what is in the fonds"; it cannot answer "where
 * is the work", because 178 rows of equal height flatten a range that runs from
 * two pages to 695. A treemap restores the proportion, and the proportion is
 * the whole point: the thirteen folders transcribed so far are 263 pages of
 * 16,074, and no table makes that as plain as one block against the wall.
 *
 * Mondrian rather than a plain treemap because the grammar fits what is being
 * said. Flat blocks of one colour each, separated by heavy black rules, no
 * gradients and no shading: a folder is transcribed or it is not, and there is
 * nothing continuous to express. Blocks within blocks carry the one structure
 * there is — the inventory's groups — rather than a second quantity.
 *
 * Colours are the site's, not Mondrian's primaries: blue already means "ours"
 * and green "someone else's" on the rows below, and breaking that to reach for
 * a red would cost more than the pastiche is worth.
 */

interface Cell {
  cote: Cote;
  state: FolderState;
  batches: number;
  x: number;
  y: number;
  w: number;
  h: number;
}

const FILL: Record<FolderState, string> = {
  here: 'var(--color-brand-500)',
  community: 'var(--color-relu-500)',
  untouched: 'var(--color-ink-100)',
};

/** Ink that survives on each fill — the untouched blocks are nearly white. */
const INK: Record<FolderState, string> = {
  here: '#ffffff',
  community: '#ffffff',
  untouched: 'var(--color-ink-600)',
};

const LABEL: Record<FolderState, string> = {
  here: 'transcribed here',
  community: 'edited by the community',
  untouched: 'untouched',
};

/** Canvas height, in the same units as the width of 100. */
const CANVAS_H = 74;

/**
 * Squarified treemap (Bruls, Huizing, van Wijk).
 *
 * Chosen over a slice-and-dice layout because the blocks have to be readable,
 * not merely correct: slice-and-dice gives the 695-page folder a ribbon two
 * pixels wide, and a block nobody can point at conveys nothing. Aspect ratios
 * here stay close to 1, which is also what makes the wall look like a wall.
 */
function squarify(values: number[], width: number, height: number) {
  const total = values.reduce((s, v) => s + v, 0);
  const scaled = values.map((v) => (v / total) * width * height);
  const out: { x: number; y: number; w: number; h: number }[] = Array.from({
    length: values.length,
  });

  let i = 0;
  let x = 0;
  let y = 0;
  let w = width;
  let h = height;

  while (i < scaled.length) {
    const short = Math.min(w, h);
    const row: number[] = [];
    let rowSum = 0;

    // Grow the row while the worst aspect ratio in it keeps improving.
    const worst = (sum: number, extra: number) => {
      const side = sum / short;
      const all = [...row, extra];
      return Math.max(...all.map((v) => Math.max(v / side / side, (side * side) / v)));
    };

    let j = i;
    while (j < scaled.length) {
      const v = scaled[j];
      if (row.length > 0 && worst(rowSum + v, v) > worst(rowSum, row[row.length - 1])) break;
      row.push(v);
      rowSum += v;
      j += 1;
    }

    const side = rowSum / short;
    let offset = 0;
    for (let k = 0; k < row.length; k += 1) {
      const len = row[k] / side;
      out[i + k] =
        w >= h
          ? { x, y: y + offset, w: side, h: len }
          : { x: x + offset, y, w: len, h: side };
      offset += len;
    }

    if (w >= h) {
      x += side;
      w -= side;
    } else {
      y += side;
      h -= side;
    }
    i = j;
  }

  return out;
}

export function FondsMosaic({
  transcribedHere,
  hasEdition,
  onOpen,
}: {
  transcribedHere: (id: string) => boolean;
  hasEdition: (id: string) => boolean;
  onOpen: (id: string) => void;
}) {
  const [hover, setHover] = useState<Cell | null>(null);

  /**
   * The whole fonds, nested: a box per inventory group, its folders inside.
   *
   * One flat treemap of 178 folders answered "where are the pages" and nothing
   * else — the archivists' own grouping, which is the only structure this fonds
   * actually has, was invisible in it. Two levels put it back: the outer boxes
   * are the twenty-two groups, sized by their total, and each folder sits
   * inside the group it belongs to. Every folder is drawn, not the largest
   * sixty, because a group missing half its folders would misreport the one
   * thing the nesting is for.
   *
   * Blocks within blocks is also the composition this figure was reaching for
   * in the first place, rather than a grid of equals.
   */
  const groups = useMemo(() => {
    const sized = GROUPS.map((g) => {
      const cotes = g.cotes.map((id) => BY_ID.get(id)).filter((c): c is Cote => Boolean(c));
      return { g, cotes, pages: cotes.reduce((s, c) => s + c.pages, 0) };
    })
      .filter((x) => x.pages > 0)
      .sort((a, b) => b.pages - a.pages);

    const outer = squarify(
      sized.map((x) => x.pages),
      100,
      CANVAS_H,
    );

    return sized.map((x, i) => {
      const box = outer[i];
      // A strip at the top of the box carries the group's name, and the folders
      // are inset below it. Both are in canvas units, so a small group loses
      // proportionally less of itself than a fixed pixel inset would take.
      const pad = 0.35;
      const strip = Math.min(1.9, box.h * 0.22);
      const inner = {
        x: box.x + pad,
        y: box.y + strip,
        w: Math.max(box.w - pad * 2, 0.01),
        h: Math.max(box.h - strip - pad, 0.01),
      };
      const ordered = [...x.cotes].sort((a, b) => b.pages - a.pages);
      const boxes = squarify(
        ordered.map((c) => c.pages),
        inner.w,
        inner.h,
      );
      const cells: Cell[] = ordered.map((c, k) => {
        return {
          cote: c,
          state: folderState(transcribedHere(c.id), hasEdition(c.id)),
          batches: batchCount(c.pages),
          x: inner.x + boxes[k].x,
          y: inner.y + boxes[k].y,
          w: boxes[k].w,
          h: boxes[k].h,
        };
      });
      return { ...x, box, strip, cells };
    });
  }, [transcribedHere, hasEdition]);

  const cells = groups.flatMap((g) => g.cells);
  const allPages = COTES.reduce((s, c) => s + c.pages, 0);

  return (
    <section className="mt-8">
      <h2 className="titre text-[19px] text-ink-900">Where the work is</h2>
      <p className="mt-2 max-w-[52em] text-[13px] leading-relaxed text-ink-600">
        All {cells.length} folders, {allPages.toLocaleString()} pages, each block sized by its page
        count and nested inside the inventory group it belongs to — the archivists' own division,
        which is the only structure this fonds has. Colour is what has been done to a folder, not
        what is in it.
      </p>

      {/* Only the states actually on this wall. A key for a colour that never
          appears sends the eye hunting for it. */}
      <ul className="mt-3 flex flex-wrap items-center gap-x-5 gap-y-1.5 text-[12px] text-ink-500">
        {(['here', 'community', 'untouched'] as FolderState[])
          .filter((s) => cells.some((c) => c.state === s))
          .map((s) => (
            <li key={s} className="flex items-center gap-1.5">
              <span
                aria-hidden="true"
                className="inline-block h-3.5 w-6 border border-ink-900"
                style={{ background: FILL[s] }}
              />
              {LABEL[s]}
            </li>
          ))}
      </ul>

      {/* The black ground is the rules: every block is inset, so what shows
          between them is this, not a border drawn four times over. The group
          boxes are the same idea one level up — they are the gaps their folders
          do not fill. */}
      <div
        className="relative mt-3 w-full overflow-hidden rounded-[var(--radius-card)] bg-ink-900"
        style={{ aspectRatio: `100 / ${CANVAS_H}` }}
        onMouseLeave={() => setHover(null)}
      >
        {groups.map(({ g, box, strip, pages }) => (
          <div
            key={g.id}
            className="pointer-events-none absolute overflow-hidden"
            style={{
              left: `${box.x}%`,
              top: `${(box.y / CANVAS_H) * 100}%`,
              width: `${box.w}%`,
              height: `${(box.h / CANVAS_H) * 100}%`,
              padding: '2px',
            }}
          >
            <span className="block h-full w-full rounded-[2px] border border-ink-700 bg-ink-800/60">
              {/* The group's name, where the strip is tall enough to hold it.
                  A label clipped to three characters names nothing. */}
              {box.w > 11 && strip > 1.3 && (
                <span
                  className="tabular block truncate px-1 pt-[2px] text-[9px] font-semibold uppercase tracking-wide text-ink-300"
                  title={g.title}
                >
                  {g.title}
                  <span className="ml-1 font-normal normal-case tracking-normal text-ink-400">
                    {pages.toLocaleString()}p
                  </span>
                </span>
              )}
            </span>
          </div>
        ))}

        {cells.map((c) => {
          const big = c.w > 6 && c.h > 5;
          return (
            <button
              key={c.cote.id}
              type="button"
              onClick={() => onOpen(c.cote.id)}
              onMouseEnter={() => setHover(c)}
              onFocus={() => setHover(c)}
              title={`n° ${c.cote.id} — ${c.cote.title}`}
              className="absolute overflow-hidden text-left transition-[filter] hover:brightness-110 focus:z-10 focus:outline-2 focus:outline-offset-[-3px] focus:outline-white"
              style={{
                left: `${c.x}%`,
                top: `${(c.y / CANVAS_H) * 100}%`,
                width: `${c.w}%`,
                height: `${(c.h / CANVAS_H) * 100}%`,
                padding: '1px',
              }}
            >
              <span className="relative block h-full w-full" style={{ background: FILL[c.state] }}>
                {big && (
                  <span
                    className="tabular absolute bottom-[2px] left-1 text-[9px] font-semibold leading-none"
                    style={{ color: INK[c.state] }}
                  >
                    {c.cote.id}
                  </span>
                )}
              </span>
            </button>
          );
        })}
      </div>

      {/* One line under the wall rather than a floating tooltip: a tooltip that
          covers its neighbours defeats a figure whose whole subject is
          comparison. Reserved height, so nothing reflows on hover. */}
      <div className="mt-2 min-h-[3.2em] text-[12.5px] leading-relaxed text-ink-600">
        {hover ? (
          <p>
            <span className="tabular font-semibold text-ink-900">n° {hover.cote.id}</span> ·{' '}
            {hover.cote.title}
            <br />
            <span className="tabular">
              {hover.cote.pages} pages · {hover.batches} {hover.batches === 1 ? 'batch' : 'batches'}
            </span>
          </p>
        ) : (
          <p className="text-ink-400">
            Hover a block for its folder, or a group's name for its full title. Nothing is left out:
            all {COTES.length} folders are here, in the {groups.length} groups the inventory
            records.
          </p>
        )}
      </div>

    </section>
  );
}
