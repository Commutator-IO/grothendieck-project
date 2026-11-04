import { memo, useEffect, useLayoutEffect, useMemo, useRef, useState } from 'react';
import katex from 'katex';
import 'katex/dist/katex.min.css';

/**
 * A reconstructed blackboard beside a Buffalo recording: what Grothendieck
 * probably wrote, rebuilt from the recording's automatic captions, item by
 * item, each at the second it is spoken. Items appear as the video reaches
 * them, as chalk on a board; a click takes the video back to that moment.
 *
 * The boards are written in the git-ignored transcripts-buffalo/ and published
 * to public/buffalo-boards/ by `npm run buffalo-boards`.
 */

export interface BoardItem {
  t: number;
  kind: 'h' | 'p' | 'm' | 'cd';
  text: string;
  uncertain?: boolean;
}
export interface Board {
  video: string;
  start: number;
  end: number;
  session: string;
  tape: string;
  pass: string;
  items: BoardItem[];
}

const tex = (s: string, display: boolean) => katex.renderToString(s, { displayMode: display, throwOnError: false });
// Inline $…$ in prose; the rest is our own HTML (<b>, <i>), written with the board.
const prose = (s: string) => s.split(/(\$[^$]+\$)/).map((p) => (p.startsWith('$') ? tex(p.slice(1, -1), false) : p)).join('');

/**
 * The ghost of earlier chalk: broad, faint sweeps where a brush went over the slate, and the prints of
 * chalky fingers along its edges.
 *
 * He works two boards in turn, so every other panel is the same physical board. The marks come from the
 * board, not from the panel: all the panels of one board carry the same bands and the same prints, and
 * each time the board is wiped again a new layer, a little shifted, lands on top of the earlier ones.
 */
const mulberry = (seed: number) => {
  let a = Math.imul(seed + 1, 2654435761) >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
};
const MAX_LAYERS = 5;

const Smears = memo(function Smears({ board, layers }: { board: 0 | 1; layers: number }) {
  const { strokes, prints } = useMemo(() => {
    // The geometry of the board: the same for every layer of it.
    const rnd = mulberry(board * 101 + 7);
    const bands = Array.from({ length: 3 }, () => ({
      gy: 50 + rnd() * 190,
      gx: 15 + rnd() * 230,
      passes: 2 + Math.floor(rnd() * 2),
      pass: Array.from({ length: 3 }, () => ({ dx: (rnd() - 0.3) * 50, dy: 11 + rnd() * 9, len: 230 + rnd() * 190, rise: 6 + rnd() * 20, sag: 4 + rnd() * 12, w: 13 + rnd() * 14, o: 0.03 + rnd() * 0.035 })),
    }));
    const marks = Array.from({ length: 6 }, (_, k) => ({ x: k < 3 ? 3 + rnd() * 5 : 592 + rnd() * 5, y: 40 + rnd() * 220, rx: 4 + rnd() * 5, ry: 14 + rnd() * 22, o: 0.05 + rnd() * 0.05 }));
    const strokes: { d: string; w: number; o: number }[] = [];
    const prints: typeof marks = [];
    const n = Math.min(layers, MAX_LAYERS);
    // The layers pile up, but the total is held down so that old boards stay discreet.
    const gain = n > 1 ? 1.5 / (n + 0.5) : 1;
    for (let l = 0; l < n; l++) {
      const j = mulberry(board * 1009 + l * 31 + 3); // each wipe lands a little off the last
      for (const b of bands)
        for (let k = 0; k < b.passes; k++) {
          const q = b.pass[k];
          const x0 = b.gx + q.dx + (j() - 0.5) * 28;
          const y0 = b.gy + k * q.dy + (j() - 0.5) * 14;
          const len = q.len + (j() - 0.5) * 60;
          strokes.push({ d: `M${x0} ${y0} Q${x0 + len * 0.55} ${y0 - q.rise * 0.4 + q.sag} ${x0 + len} ${y0 - q.rise}`, w: q.w, o: q.o * gain });
        }
      for (const m of marks) prints.push({ ...m, o: m.o * gain, x: m.x + (j() - 0.5) * 3, y: m.y + (j() - 0.5) * 16 });
    }
    return { strokes, prints };
  }, [board, layers]);
  return (
    <svg
      aria-hidden="true"
      viewBox="0 0 600 300"
      preserveAspectRatio="none"
      style={{ position: 'absolute', inset: 0, width: '100%', height: '100%', pointerEvents: 'none' }}
    >
      {/* Soft edges without a blur filter, which is costly on ten panels: three strokes, wide and faint to narrow. */}
      <g fill="none" stroke="#f4f4ee" strokeLinecap="round">
        {strokes.flatMap((k, i) => [
          <path key={`${i}a`} d={k.d} strokeWidth={k.w * 1.5} strokeOpacity={k.o * 0.35} />,
          <path key={`${i}b`} d={k.d} strokeWidth={k.w} strokeOpacity={k.o * 0.5} />,
          <path key={`${i}c`} d={k.d} strokeWidth={k.w * 0.55} strokeOpacity={k.o * 0.6} />,
        ])}
      </g>
      <g fill="#f4f4ee">
        {prints.map((m, i) => (
          <ellipse key={i} cx={m.x} cy={m.y} rx={m.rx} ry={m.ry} fillOpacity={m.o} />
        ))}
      </g>
    </svg>
  );
});

/**
 * The board is a stack of sliding panels of one fixed height, as in the amphitheatres of the IHP:
 * slate panels between aluminium rails, a chalk ledge below. Items are laid out panel by panel, a
 * new panel starting when the next item would not fit, and the scroll snaps from one panel to the
 * next, so a turn of the wheel moves one board and never races through several.
 */
const PAD_Y = 32; // py-4, top and bottom of a panel
/*
 * The panels are shorter than the board's window, so the foot of the previous panel stays in view
 * above the current one. Their size follows what the recordings say of Grothendieck's board at
 * Buffalo: he writes « on the other part of the blackboard » after about a dozen of our items and
 * erases after thirty-five to forty, in two or three parts, so about a dozen items a panel.
 */
const PEEK = 0.28;
const MAX_ITEMS = 12;

export function Blackboard({ board, now, onSeek }: { board: Board; now: number; onSeek: (t: number) => void }) {
  const html = useMemo(
    () => board.items.map((i) => (i.kind === 'm' || i.kind === 'cd' ? tex(i.text, true) : prose(i.text))),
    [board],
  );
  const shown = board.items.filter((i) => i.t <= now).length;
  const pane = useRef<HTMLDivElement>(null);
  const items = useRef<(HTMLButtonElement | null)[]>([]);
  // The panel height is the visible height of the board, measured.
  const [ph, setPh] = useState(0);
  // Where each panel after the first begins, as an index into the items.
  const [breaks, setBreaks] = useState<number[]>([]);
  const [at, setAt] = useState(0);

  useLayoutEffect(() => {
    const el = pane.current;
    if (!el) return;
    const ro = new ResizeObserver(() => setPh(el.clientHeight));
    ro.observe(el);
    return () => ro.disconnect();
  }, []);

  // No horizontal scrolling: a line of chalk wider than the board (a long display formula) is
  // written smaller until it fits, as one would on a real board.
  useLayoutEffect(() => {
    const fit = () => {
      const lines = [...(pane.current?.querySelectorAll<HTMLElement>('.chalk') ?? [])];
      // One pass to reset, one to measure, one to write: interleaving them forces a layout per line.
      lines.forEach((b) => (b.style.fontSize = ''));
      const sizes = lines.map((b) => {
        const w = b.clientWidth;
        const need = Math.max(b.scrollWidth, ...[...b.querySelectorAll<HTMLElement>('.katex-display > .katex')].map((k) => k.scrollWidth));
        return need > w + 1 ? (parseFloat(getComputedStyle(b).fontSize) * w) / need : 0;
      });
      lines.forEach((b, i) => {
        if (sizes[i]) b.style.fontSize = `${sizes[i]}px`;
      });
    };
    fit();
    const ro = new ResizeObserver(fit);
    if (pane.current) ro.observe(pane.current);
    return () => ro.disconnect();
  }, [shown, html, breaks]);

  // Fill the panels in order; a heading is never left alone at the foot of a panel.
  const peek = Math.round(ph * PEEK);
  const panelH = ph - peek;
  useLayoutEffect(() => {
    if (!ph) return;
    const room = panelH - PAD_Y;
    const size = (k: number) => {
      const el = items.current[k];
      if (!el) return { h: 0, m: 0 };
      return { h: el.offsetHeight, m: k === 0 ? 0 : board.items[k].kind === 'h' ? 16 : 6 };
    };
    // A sentence is never cut between two panels: a display is kept with the line that introduces
    // it, and the words that finish the sentence after it (« commutes. ») stay with the display.
    const glued = (k: number) => {
      if (k === 0) return false;
      const a = board.items[k - 1];
      const b = board.items[k];
      const display = (i: BoardItem) => i.kind === 'm' || i.kind === 'cd';
      if (b.kind === 'p' && display(a) && /^[a-z]/.test(b.text.trimStart())) return true;
      return display(b) && a.kind === 'p' && !/[.?!]\s*$/.test(a.text);
    };
    const out: number[] = [];
    let used = 0;
    let count = 0;
    for (let k = 0; k < shown; k++) {
      const { h, m } = size(k);
      // The whole run of glued items that follows k, to be placed together.
      let run = h;
      let n = 1;
      for (let j = k + 1; j < shown && glued(j); j++) {
        run += size(j).m + size(j).h;
        n++;
      }
      let need = used ? m + run : run;
      if (board.items[k].kind === 'h' && k + n < shown) need += size(k + n).m + size(k + n).h;
      if (used && (used + need > room || count + n > MAX_ITEMS)) {
        out.push(k);
        used = run;
        count = n;
      } else {
        used += used ? m + run : run;
        count += n;
      }
      k += n - 1;
    }
    setBreaks((b) => (b.length === out.length && b.every((x, i) => x === out[i]) ? b : out));
  }, [shown, html, ph, panelH, board.items]);

  // Keep the latest chalk in view: the last panel, smoothly for one new item, at once after a jump.
  const before = useRef(0);
  useEffect(() => {
    const el = pane.current;
    if (el) el.scrollTo({ top: el.scrollHeight, behavior: shown - before.current === 1 ? 'smooth' : 'auto' });
    before.current = shown;
    setAt(Number.MAX_SAFE_INTEGER); // the last panel; clamped below
  }, [shown, breaks.length]);

  const starts = [0, ...breaks.filter((b) => b < shown)];
  const panels = starts.map((a, i) => [a, i + 1 < starts.length ? starts[i + 1] : shown] as const);

  return (
    <div className="blackboard flex h-full flex-col overflow-hidden rounded-md border-[3px] border-[#3b3f43] bg-[#2a2e31] shadow-[0_2px_10px_rgb(0_0_0/.25)]">
      <div
        ref={pane}
        onScroll={(e) => panelH > 0 && setAt(Math.round((e.currentTarget.scrollTop + peek) / panelH))}
        style={{ scrollPaddingTop: peek }}
        className="board-scroll flex-1 snap-y snap-mandatory overflow-y-auto overflow-x-hidden"
      >
        {/* The lecture opens on a clean board: an empty panel above, the one he writes on below, both in view. */}
        <section aria-hidden="true" style={{ minHeight: panelH || undefined }} className="slate relative snap-start snap-always">
          <Smears board={1} layers={1} />
        </section>
        {panels.map(([a, b], n) => (
          <section
            key={n}
            style={{ minHeight: panelH || undefined }}
            className="slate rail relative snap-start snap-always px-5 py-4"
          >
            <Smears board={(n % 2) as 0 | 1} layers={n % 2 === 0 ? n / 2 + 1 : (n + 3) / 2} />
            {board.items.slice(a, b).map((i, j) => {
              const k = a + j;
              return (
                <button
                  key={k}
                  ref={(el) => {
                    items.current[k] = el;
                  }}
                  type="button"
                  onClick={() => onSeek(i.t)}
                  title={`${Math.floor(i.t / 60)}:${String(i.t % 60).padStart(2, '0')}${i.uncertain ? ' · uncertain' : ''}`}
                  className={`chalk block w-full text-left transition-opacity hover:opacity-100 ${k === shown - 1 ? 'opacity-100' : 'opacity-85'} ${
                    i.kind === 'h' ? 'mt-4 text-[26px] underline decoration-1 underline-offset-4' : 'mt-1.5 text-[20px] leading-snug'
                  } ${j === 0 ? '!mt-0' : ''} ${i.uncertain ? 'text-[#e9d9a8]' : 'text-[#eceee9]'}`}
                  dangerouslySetInnerHTML={{ __html: html[k] + (i.uncertain ? ' <span class="text-[15px]">?</span>' : '') }}
                />
              );
            })}
            {shown === 0 && <p className="chalk text-[20px] text-[#8d9294]">The board fills as the lecture goes on.</p>}
          </section>
        ))}
      </div>
      <Ledge panel={Math.max(1, Math.min(at, panels.length))} of={panels.length} />
    </div>
  );
}

/** The chalk ledge, seen slightly from above, with a few sticks on it; and which panel is in view. */
function Ledge({ panel, of }: { panel: number; of: number }) {
  return (
    <div className="relative h-[26px] shrink-0 select-none" aria-hidden={of <= 1}>
      <div className="absolute inset-x-0 top-0 h-[17px] origin-bottom bg-gradient-to-b from-[#9fa09c] to-[#cfcec7] [transform:perspective(220px)_rotateX(38deg)]" />
      <div className="absolute inset-x-0 bottom-0 h-[9px] bg-gradient-to-b from-[#e2e1db] to-[#8f8e88]" />
      <span className="absolute bottom-[11px] left-[14%] h-[6px] w-[34px] -rotate-3 rounded-full bg-gradient-to-b from-white to-[#d8d6cf] shadow-[0_2px_2px_rgb(0_0_0/.45)]" />
      <span className="absolute bottom-[12px] left-[20%] h-[6px] w-[18px] rotate-12 rounded-full bg-gradient-to-b from-[#fff3b0] to-[#e3cf6e] shadow-[0_2px_2px_rgb(0_0_0/.45)]" />
      <span className="absolute bottom-[11px] left-[63%] h-[6px] w-[26px] rotate-2 rounded-full bg-gradient-to-b from-[#ffe0e8] to-[#e3a6b6] shadow-[0_2px_2px_rgb(0_0_0/.45)]" />
      <span className="absolute bottom-[10px] left-[30%] h-[2px] w-[40px] rounded-full bg-white/40 blur-[1px]" />
      {/* Dust and the prints of chalky fingers along the ledge. */}
      <span className="absolute bottom-[8px] left-[44%] h-[3px] w-[26px] rounded-full bg-white/50 blur-[1.5px]" />
      <span className="absolute bottom-[11px] left-[8%] h-[2px] w-[14px] rounded-full bg-white/60 blur-[1px]" />
      <span className="absolute bottom-[2px] left-[52%] h-[4px] w-[10px] rounded-full bg-white/35 blur-[1.5px]" />
      <span className="absolute bottom-[3px] left-[80%] h-[3px] w-[16px] rounded-full bg-white/30 blur-[1.5px]" />
      {of > 1 && (
        <span className="tabular absolute bottom-[1px] right-2 text-[9.5px] font-medium text-[#3f413e]">
          board {panel} / {of}
        </span>
      )}
    </div>
  );
}
