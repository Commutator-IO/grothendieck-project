import { useEffect, useState } from 'react';
import { BY_ID } from '../content/catalogue.ts';

/**
 * A folder's place in time, and a control to move through it.
 *
 * The maps are laid out once, with a fixed seed, so a node never moves; what
 * the scrubber changes is which folders are counted. A folder counts from the
 * year of its dating's midpoint — the same midpoint `npm run fonds-maps` uses
 * for the colour by dating — which is a tendency and not a date: the inventory
 * mostly infers its datings, and a range of 1958–1973 puts the folder at 1965.5.
 * Undated folders (« s.d. ») have no place on the axis; they appear only when
 * the scrubber is set to « all ».
 */
export function folderYear(id: string): number | null {
  const ys = [...(BY_ID.get(id)?.date ?? '').matchAll(/\b(19\d\d)\b/g)].map((m) => Number(m[1]));
  return ys.length ? (Math.min(...ys) + Math.max(...ys)) / 2 : null;
}

const Y0 = 1949;
const Y1 = 1991;

/** null means « all », undated folders included. */
export type Moment = number | null;

export const shownAt = (t: Moment) => (id: string) => {
  if (t === null) return true;
  const y = folderYear(id);
  return y !== null && y <= t + 0.5;
};

export function useMoment(): [Moment, (t: Moment) => void] {
  return useState<Moment>(null);
}

export function TimeScrubber({
  value,
  onChange,
  counted,
  total,
  noun,
}: {
  value: Moment;
  onChange: (t: Moment) => void;
  counted: number;
  total: number;
  noun: string;
}) {
  const [playing, setPlaying] = useState(false);

  useEffect(() => {
    if (!playing) return;
    const id = setInterval(() => {
      onChange(((cur: Moment) => (cur === null || cur >= Y1 ? Y0 : cur + 1))(value));
    }, 450);
    return () => clearInterval(id);
  }, [playing, value, onChange]);
  useEffect(() => {
    if (playing && value === Y1) setPlaying(false);
  }, [playing, value]);

  return (
    <div className="mt-3 flex flex-wrap items-center gap-x-3 gap-y-2 text-[12px]">
      <span className="text-ink-400">Time</span>
      <button
        type="button"
        onClick={() => {
          if (!playing && (value === null || value >= Y1)) onChange(Y0);
          setPlaying(!playing);
        }}
        aria-pressed={playing}
        className="rounded-full bg-ink-100 px-2.5 py-1 text-ink-700 hover:bg-ink-200"
      >
        {playing ? 'Pause' : 'Play'}
      </button>
      <input
        type="range"
        min={Y0}
        max={Y1}
        step={1}
        value={value ?? Y1}
        onChange={(e) => {
          setPlaying(false);
          onChange(Number(e.target.value));
        }}
        aria-label="Show the folders dated up to this year"
        className="w-48 accent-[#38539d] sm:w-64"
      />
      <span className="tabular w-10 font-semibold text-ink-900">{value ?? 'all'}</span>
      <button
        type="button"
        onClick={() => {
          setPlaying(false);
          onChange(null);
        }}
        aria-pressed={value === null}
        className={`rounded-full px-2.5 py-1 ${value === null ? 'bg-ink-800 text-white' : 'bg-ink-100 text-ink-600 hover:bg-ink-200'}`}
      >
        all
      </button>
      <span className="tabular text-ink-500">
        {counted} of {total} {noun}
        {value !== null && ' · by the midpoint of the inventory’s dating; undated folders only under « all »'}
      </span>
    </div>
  );
}
