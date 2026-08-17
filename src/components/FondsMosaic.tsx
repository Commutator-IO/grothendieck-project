import { useMemo, useState } from 'react';
import { COTES } from '../content/catalogue.ts';
import { batchCount } from '../lib/batches.ts';
import { PRIORITY, folderState, predictYield } from '../lib/yield.ts';
import type { FolderState } from '../lib/yield.ts';
import type { Cote, Manifest } from '../lib/types.ts';

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
 * nothing continuous to express. The one continuous quantity — how much of a
 * folder is likely to be readable at all — is drawn as a block inside the
 * block, which is the composition's own idiom rather than an imposition on it.
 *
 * Colours are the site's, not Mondrian's primaries: blue already means "ours"
 * and green "someone else's" on the rows below, and breaking that to reach for
 * a red would cost more than the pastiche is worth.
 */

interface Cell {
  cote: Cote;
  state: FolderState;
  /** Transcribable share, measured where a transcription exists. */
  rate: number;
  measured: boolean;
  reason: string;
  batches: number;
  x: number;
  y: number;
  w: number;
  h: number;
}

const FILL: Record<FolderState, string> = {
  here: 'var(--color-brand-500)',
  community: 'var(--color-relu-500)',
  priority: 'var(--color-encours-500)',
  untouched: 'var(--color-ink-100)',
};

/** Ink that survives on each fill — the untouched blocks are nearly white. */
const INK: Record<FolderState, string> = {
  here: '#ffffff',
  community: '#ffffff',
  priority: '#3a2a02',
  untouched: 'var(--color-ink-600)',
};

const LABEL: Record<FolderState, string> = {
  here: 'transcribed here',
  community: 'edited by the community',
  priority: 'worth opening next',
  untouched: 'untouched',
};

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
  manifest,
  transcribedHere,
  hasEdition,
  onOpen,
}: {
  manifest: Manifest | null;
  transcribedHere: (id: string) => boolean;
  hasEdition: (id: string) => boolean;
  onOpen: (id: string) => void;
}) {
  const [hover, setHover] = useState<Cell | null>(null);
  const [showYield, setShowYield] = useState(true);

  /**
   * The sixty largest folders, which are 74% of the fonds by page.
   *
   * Not all 178: below about sixty pages the blocks stop carrying a legible
   * shelfmark, and a wall of unlabelled slivers would be decoration. What is
   * dropped is stated under the figure rather than left to be discovered.
   */
  const cells = useMemo<Cell[]>(() => {
    const top = [...COTES].sort((a, b) => b.pages - a.pages).slice(0, 60);
    const boxes = squarify(
      top.map((c) => c.pages),
      100,
      62,
    );
    return top.map((c, i) => {
      const y = predictYield(c, manifest);
      return {
        cote: c,
        state: folderState(c, transcribedHere(c.id), hasEdition(c.id)),
        rate: y.rate,
        measured: y.basis === 'measured',
        reason: y.reason,
        batches: batchCount(c.pages),
        ...boxes[i],
      };
    });
  }, [manifest, transcribedHere, hasEdition]);

  const shownPages = cells.reduce((s, c) => s + c.cote.pages, 0);
  const allPages = COTES.reduce((s, c) => s + c.pages, 0);

  /**
   * The one-pass folders that are still untranscribed — the list #12 works
   * through. Drawn separately because they cannot be seen on the wall above:
   * the smallest of them is 2 pages against a 695-page neighbour, which is a
   * block a third of a pixel wide.
   */
  const small = useMemo<Cell[]>(() => {
    const ones = COTES.filter(
      (c) => batchCount(c.pages) === 1 && !transcribedHere(c.id),
    ).sort((a, b) => b.pages - a.pages);
    const boxes = squarify(
      ones.map((c) => c.pages),
      100,
      26,
    );
    return ones.map((c, i) => {
      const y = predictYield(c, manifest);
      return {
        cote: c,
        state: folderState(c, false, hasEdition(c.id)),
        rate: y.rate,
        measured: y.basis === 'measured',
        reason: y.reason,
        batches: 1,
        ...boxes[i],
      };
    });
  }, [manifest, transcribedHere, hasEdition]);

  /** The candidates, in the order the two issues put them. */
  const candidates = useMemo(
    () =>
      Object.keys(PRIORITY)
        .map((id) => COTES.find((c) => c.id === id))
        .filter((c): c is Cote => Boolean(c))
        .sort((a, b) => a.pages - b.pages),
    [],
  );

  return (
    <section className="mt-8">
      <div className="flex flex-wrap items-baseline justify-between gap-3">
        <h2 className="titre text-[19px] text-ink-900">Where the work is</h2>
        <button
          type="button"
          onClick={() => setShowYield((v) => !v)}
          className="rounded-md border border-ink-200 bg-white px-2.5 py-1 text-[12px] text-ink-600 transition hover:border-brand-400 hover:text-brand-700"
        >
          {showYield ? 'Hide the unreadable share' : 'Show the unreadable share'}
        </button>
      </div>
      <p className="mt-2 max-w-[52em] text-[13px] leading-relaxed text-ink-600">
        The {cells.length} largest folders, each block sized by its page count — {shownPages.toLocaleString()}{' '}
        of the fonds' {allPages.toLocaleString()} pages. Colour is what has been done to a folder, not
        what is in it.
        {showYield && (
          <>
            {' '}
            The pale band across the top of each block is the share of its pages that is expected to
            carry no mathematics — administrative versos, blanks, returned typescript — and so will
            never be transcribed. Measured where a transcription exists, estimated everywhere else.
          </>
        )}
      </p>

      {/* Only the states actually on this wall. A key for a colour that never
          appears sends the eye hunting for it. */}
      <ul className="mt-3 flex flex-wrap items-center gap-x-5 gap-y-1.5 text-[12px] text-ink-500">
        {(['here', 'community', 'priority', 'untouched'] as FolderState[])
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

      {/* The black ground is the rules: every block is inset by a pixel and a
          half, so what shows between them is this, not a border drawn four
          times over. */}
      <div
        className="relative mt-3 w-full overflow-hidden rounded-[var(--radius-card)] bg-ink-900"
        style={{ aspectRatio: '100 / 62' }}
        onMouseLeave={() => setHover(null)}
      >
        {cells.map((c) => {
          const big = c.w > 7 && c.h > 6;
          return (
            <button
              key={c.cote.id}
              type="button"
              onClick={() => onOpen(c.cote.id)}
              onMouseEnter={() => setHover(c)}
              onFocus={() => setHover(c)}
              title={`n° ${c.cote.id} — ${c.cote.title}`}
              className="absolute overflow-hidden text-left transition-[filter] hover:brightness-105 focus:z-10 focus:outline-2 focus:outline-offset-[-3px] focus:outline-white"
              style={{
                left: `${c.x}%`,
                top: `${(c.y / 62) * 100}%`,
                width: `${c.w}%`,
                height: `${(c.h / 62) * 100}%`,
                padding: '1.5px',
              }}
            >
              <span className="relative block h-full w-full" style={{ background: FILL[c.state] }}>
                {/* The block within the block: pages the folder is not expected
                    to yield. Drawn from the top so the coloured remainder still
                    sits on the baseline of the wall and stays comparable across
                    neighbours. */}
                {showYield && c.rate < 0.999 && (
                  <span
                    aria-hidden="true"
                    className="absolute inset-x-0 top-0 block"
                    style={{
                      height: `${(1 - c.rate) * 100}%`,
                      background: 'var(--color-ink-50)',
                      borderBottom: c.measured ? '1.5px solid #131210' : '1.5px dashed #575348',
                    }}
                  />
                )}
                {big && (
                  <span
                    className="tabular absolute bottom-1 left-1.5 text-[10px] font-semibold leading-none"
                    style={{ color: INK[c.state] }}
                  >
                    {c.cote.id}
                    <span className="ml-1 font-normal opacity-70">{c.cote.pages}p</span>
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
              {hover.cote.pages} pages · {hover.batches} {hover.batches === 1 ? 'pass' : 'passes'} ·{' '}
              {Math.round(hover.rate * 100)}% expected to carry mathematics
            </span>{' '}
            <span className="text-ink-500">
              ({hover.measured ? 'measured' : 'estimated'}: {hover.reason})
            </span>
            {PRIORITY[hover.cote.id] && (
              <>
                <br />
                <span className="text-encours-700">{PRIORITY[hover.cote.id]}</span>
              </>
            )}
          </p>
        ) : (
          <p className="text-ink-400">
            Hover a block for its folder. Below sixty pages a folder is not drawn here — {COTES.length - cells.length}{' '}
            of the 178 are left out, {(allPages - shownPages).toLocaleString()} pages between them.
          </p>
        )}
      </div>

      {/* The candidates get their own wall, at their own scale. On the wall
          above, drawn against a 695-page folder, every one of them would be a
          sliver: the point of a second figure is that the small end has a
          shape too, and it is where the only finishable work is. Same rules,
          same colours, a hundredth of the area. */}
      <h3 className="titre mt-8 text-[16px] text-ink-900">What one pass could finish</h3>
      <p className="mt-1.5 max-w-[52em] text-[13px] leading-relaxed text-ink-600">
        The other end of the fonds, at its own scale — every untranscribed folder that fits in a
        single twenty-page pass. Together they are {small.reduce((s, c) => s + c.cote.pages, 0)}{' '}
        pages, {((small.reduce((s, c) => s + c.cote.pages, 0) / allPages) * 100).toFixed(1)}% of the
        fonds; the wall above is the same figure drawn at a hundred times the area. Gold marks the
        thirteen that move a group furthest.
      </p>

      <div
        className="relative mt-3 w-full overflow-hidden rounded-[var(--radius-card)] bg-ink-900"
        style={{ aspectRatio: '100 / 26' }}
        onMouseLeave={() => setHover(null)}
      >
        {small.map((c) => (
          <button
            key={c.cote.id}
            type="button"
            onClick={() => onOpen(c.cote.id)}
            onMouseEnter={() => setHover(c)}
            onFocus={() => setHover(c)}
            title={`n° ${c.cote.id} — ${c.cote.title}`}
            className="absolute overflow-hidden text-left transition-[filter] hover:brightness-105 focus:z-10 focus:outline-2 focus:outline-offset-[-3px] focus:outline-white"
            style={{
              left: `${c.x}%`,
              top: `${(c.y / 26) * 100}%`,
              width: `${c.w}%`,
              height: `${(c.h / 26) * 100}%`,
              padding: '1.5px',
            }}
          >
            <span className="relative block h-full w-full" style={{ background: FILL[c.state] }}>
              {showYield && c.rate < 0.999 && (
                <span
                  aria-hidden="true"
                  className="absolute inset-x-0 top-0 block"
                  style={{
                    height: `${(1 - c.rate) * 100}%`,
                    background: 'var(--color-ink-50)',
                    borderBottom: c.measured ? '1.5px solid #131210' : '1.5px dashed #575348',
                  }}
                />
              )}
              {c.w > 6 && (
                <span
                  className="tabular absolute bottom-1 left-1.5 text-[10px] font-semibold leading-none"
                  style={{ color: INK[c.state] }}
                >
                  {c.cote.id}
                  <span className="ml-1 font-normal opacity-70">{c.cote.pages}p</span>
                </span>
              )}
            </span>
          </button>
        ))}
      </div>

      <h3 className="titre mt-7 text-[16px] text-ink-900">Worth opening next</h3>
      <p className="mt-1.5 max-w-[52em] text-[13px] leading-relaxed text-ink-600">
        Thirteen folders that each finish in a single pass, and that between them move three groups
        a long way. None of them closes a group — every group in the fonds still holds a folder of
        two passes or more — and none is chosen for what it might contain, which is exactly what
        nobody knows before reading it.
      </p>
      <ul className="mt-3 grid gap-1.5 sm:grid-cols-2 lg:grid-cols-3">
        {candidates.map((c) => {
          const y = predictYield(c, manifest);
          return (
            <li key={c.id}>
              <button
                type="button"
                onClick={() => onOpen(c.id)}
                className="flex w-full items-stretch gap-2 rounded-md border border-ink-900 bg-white text-left transition hover:border-brand-500"
              >
                <span
                  aria-hidden="true"
                  className="w-2 shrink-0"
                  style={{ background: FILL.priority }}
                />
                <span className="min-w-0 flex-1 py-1.5 pr-2">
                  <span className="tabular text-[12px] font-semibold text-ink-800">
                    n° {c.id} · {c.pages}p
                  </span>
                  <span className="ml-1.5 text-[11.5px] text-ink-500">
                    ≈{y.pages} readable
                  </span>
                  <span className="block truncate text-[12.5px] text-ink-700">{c.title}</span>
                  <span className="block text-[11.5px] text-encours-700">{PRIORITY[c.id]}</span>
                </span>
              </button>
            </li>
          );
        })}
      </ul>
      <p className="mt-2.5 max-w-[52em] text-[12px] leading-relaxed text-ink-400">
        Ratios come from the thirteen folders transcribed so far, where 231 of 263 inventory pages
        carried mathematics. Nine of those were ten pages or fewer and all ran to 100%; the five
        longer ones averaged 83%. Everything drawn for an unopened folder rests on those five
        observations and on its inventory title, and inventory titles have already been wrong twice
        here — « Divers » and « Documents isolés » both turned out to be mathematics.
      </p>
    </section>
  );
}
