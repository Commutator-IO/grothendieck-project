import { useEffect, useMemo, useRef } from 'react';
import katex from 'katex';
import 'katex/dist/katex.min.css';

/**
 * A reconstructed blackboard beside a Buffalo recording: what Grothendieck
 * probably wrote, rebuilt from the recording's automatic captions, item by
 * item, each at the second it is spoken. Items appear as the video reaches
 * them, as chalk on a board; a click takes the video back to that moment.
 *
 * The boards live in the git-ignored transcripts-buffalo/ and are shown only
 * in builds made with RENDER_BUFFALO (and in the dev server) — a reading of the
 * lectures is not published while the rights question is open (#31).
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

export function Blackboard({ board, now, onSeek }: { board: Board; now: number; onSeek: (t: number) => void }) {
  const html = useMemo(
    () => board.items.map((i) => (i.kind === 'm' || i.kind === 'cd' ? tex(i.text, true) : prose(i.text))),
    [board],
  );
  const shown = board.items.filter((i) => i.t <= now).length;
  // Keep the latest chalk in view by scrolling the board itself, never the page.
  // Smoothly for one new item, at once after a jump in the video.
  const pane = useRef<HTMLDivElement>(null);
  const before = useRef(0);
  useEffect(() => {
    const el = pane.current;
    if (el) el.scrollTo({ top: el.scrollHeight, behavior: shown - before.current === 1 ? 'smooth' : 'auto' });
    before.current = shown;
  }, [shown]);

  return (
    <div className="blackboard flex h-full flex-col rounded-xl border-[6px] border-[#5b4632] bg-[#1b1d1c] shadow-inner">
      <div ref={pane} className="flex-1 overflow-y-auto px-5 py-4">
        {board.items.slice(0, shown).map((i, k) => (
          <button
            key={k}
            type="button"
            onClick={() => onSeek(i.t)}
            title={`${Math.floor(i.t / 60)}:${String(i.t % 60).padStart(2, '0')}${i.uncertain ? ' · uncertain' : ''}`}
            className={`chalk block w-full text-left transition-opacity hover:opacity-100 ${k === shown - 1 ? 'opacity-100' : 'opacity-85'} ${
              i.kind === 'h' ? 'mt-4 text-[26px] underline decoration-1 underline-offset-4 first:mt-0' : 'mt-1.5 text-[20px] leading-snug'
            } ${i.uncertain ? 'text-[#e9d9a8]' : 'text-[#f1efe6]'}`}
            dangerouslySetInnerHTML={{ __html: html[k] + (i.uncertain ? ' <span class="text-[15px]">?</span>' : '') }}
          />
        ))}
        {shown === 0 && <p className="chalk text-[20px] text-[#8b8f8a]">The board fills as the lecture goes on.</p>}
      </div>
      <p className="border-t border-[#3a3d3b] px-5 py-2 text-[11.5px] leading-snug text-[#9a9e99]">
        Reconstructed from the recording's automatic captions, not from the board itself: wording, layout and notation
        are ours; yellow items are less certain. {board.pass}
      </p>
    </div>
  );
}
