import { useEffect, useLayoutEffect, useMemo, useRef, useState } from 'react';
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
    const fit = () =>
      pane.current?.querySelectorAll<HTMLElement>('.chalk').forEach((b) => {
        b.style.fontSize = '';
        const w = b.clientWidth;
        const need = Math.max(b.scrollWidth, ...[...b.querySelectorAll<HTMLElement>('.katex-display > .katex')].map((k) => k.scrollWidth));
        if (need > w + 1) b.style.fontSize = `${(parseFloat(getComputedStyle(b).fontSize) * w) / need}px`;
      });
    fit();
    const ro = new ResizeObserver(fit);
    if (pane.current) ro.observe(pane.current);
    return () => ro.disconnect();
  }, [shown, html]);

  // Fill the panels in order; a heading is never left alone at the foot of a panel.
  const peek = Math.round(ph * PEEK);
  const panelH = ph - peek;
  useLayoutEffect(() => {
    if (!ph) return;
    const room = panelH - PAD_Y;
    const size = (k: number) => {
      const el = items.current[k];
      if (!el) return { h: 0, m: 0 };
      return { h: el.offsetHeight, m: k === 0 ? 0 : parseFloat(getComputedStyle(el).marginTop) || 0 };
    };
    const out: number[] = [];
    let used = 0;
    let count = 0;
    for (let k = 0; k < shown; k++) {
      const { h, m } = size(k);
      let need = used ? m + h : h;
      if (board.items[k].kind === 'h' && k + 1 < shown) need += size(k + 1).m + size(k + 1).h;
      if (used && (used + need > room || count >= MAX_ITEMS)) {
        out.push(k);
        used = h;
        count = 1;
      } else {
        used += used ? m + h : h;
        count++;
      }
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
        {panels.map(([a, b], n) => (
          <section
            key={n}
            style={{ minHeight: panelH || undefined }}
            className={`slate relative snap-start snap-always px-5 py-4 ${n ? 'rail' : ''}`}
          >
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
      <Ledge panel={Math.min(at, panels.length - 1) + 1} of={panels.length} />
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
