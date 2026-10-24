import { useEffect, useRef } from 'react';
import { attachNotes, openComment } from '../lib/notes.ts';
import type { CommentContext } from '../lib/report.ts';

/**
 * The React side of src/lib/notes.ts: a page marks each commentable entry
 * with `data-comment` (its location, as JSON), and a selection inside one is
 * commented on with that location. Each entry also gets a « Comment » button,
 * which is the keyboard's way in and needs no selection at all.
 */
export const commentData = (ctx: CommentContext) => ({ 'data-comment': JSON.stringify(ctx) });

function contextOf(range: Range): CommentContext | null {
  const n = range.startContainer;
  const el = (n.nodeType === 1 ? (n as Element) : n.parentElement)?.closest('[data-comment]');
  if (!el) return null;
  try {
    return JSON.parse(el.getAttribute('data-comment') as string) as CommentContext;
  } catch {
    return null;
  }
}

/** Makes the element under the returned ref commentable by selection. */
export function useComments<T extends Element>(scope: string, title: string) {
  const ref = useRef<T>(null);
  useEffect(() => {
    if (!ref.current) return;
    return attachNotes({ root: ref.current, scope, title, contextOf });
  }, [scope, title]);
  return ref;
}

export function CommentButton({
  scope,
  ctx,
  text,
  className = '',
}: {
  scope: string;
  ctx: CommentContext;
  /** What the comment is about, quoted at the head of the panel and (cut short) in the issue. */
  text: string;
  className?: string;
}) {
  return (
    <button
      type="button"
      data-notes-skip
      onClick={() => openComment(scope, { start: -1, text, ctx })}
      title="Comment on this entry: keep a note in this browser or open a prefilled GitHub issue"
      className={`inline-flex select-none items-center gap-1 rounded-md px-1.5 py-0.5 text-[11px] font-medium text-ink-400 transition hover:bg-ink-50 hover:text-brand-700 focus-visible:outline-2 focus-visible:outline-brand-400 ${className}`}
    >
      <svg viewBox="0 0 16 16" className="h-3 w-3" aria-hidden="true" fill="none">
        <path
          d="M3 3.5h10a1 1 0 0 1 1 1v6a1 1 0 0 1-1 1H7l-3 2.5v-2.5H3a1 1 0 0 1-1-1v-6a1 1 0 0 1 1-1Z"
          stroke="currentColor"
          strokeWidth="1.3"
          strokeLinejoin="round"
        />
      </svg>
      Comment
    </button>
  );
}
