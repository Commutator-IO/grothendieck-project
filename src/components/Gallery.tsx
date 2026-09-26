import { useEffect, useMemo, useState } from 'react';

/**
 * A gallery of one kind of mathematical drawing — the diagrams, the formulas —
 * as the transcriptions set them: a list of folders beside a frame that shows
 * one folder's carousel (public/transcripts/<kind>/<folder>.html), or the
 * carousel of the richest across the fonds (richest.html), which is where the
 * page opens.
 */
export interface GalleryFolder {
  id: string;
  title: string;
  date: string;
  n: number;
  /** Per hundred pages transcribed, for the « densest » order. */
  density: number;
}

const GREEN = '#128557';
const RICHEST = 'richest';
const shortTitle = (t: string) => t.replace(/\s*:\s*notes manuscrites.*$/i, '').replace(/\s*:.*$/, '');

export function Gallery({
  kind,
  folders,
  noun,
  richestLabel,
  richestHelp,
}: {
  kind: 'diagrams' | 'formulas';
  folders: GalleryFolder[];
  noun: [string, string];
  richestLabel: string;
  richestHelp: string;
}) {
  const [sel, setSel] = useState<{ id: string; at?: number }>(() => {
    const [id, at] = location.hash.slice(1).split('/');
    return id === RICHEST || folders.some((x) => x.id === id) ? { id, at: at ? Number(at) : undefined } : { id: RICHEST };
  });
  const [order, setOrder] = useState<'count' | 'density' | 'shelfmark'>('count');

  useEffect(() => {
    history.replaceState(null, '', `#${sel.id}${sel.at ? `/${sel.at}` : ''}`);
  }, [sel]);
  useEffect(() => {
    const go = () => {
      const [id, at] = location.hash.slice(1).split('/');
      if (id === RICHEST || folders.some((x) => x.id === id)) setSel({ id, at: at ? Number(at) : undefined });
    };
    addEventListener('hashchange', go);
    return () => removeEventListener('hashchange', go);
  }, [folders]);

  const list = useMemo(() => {
    const l = [...folders];
    if (order === 'count') l.sort((a, b) => b.n - a.n);
    if (order === 'density') l.sort((a, b) => b.density - a.density);
    return l;
  }, [order, folders]);
  const max = Math.max(...folders.map((f) => (order === 'density' ? f.density : f.n)));
  const folder = folders.find((f) => f.id === sel.id);
  const src = `/transcripts/${kind}/${sel.id}.html${sel.at ? `#d${sel.at}` : ''}`;

  return (
    <div className="mt-8 grid gap-6 lg:grid-cols-[18rem_1fr]">
      <aside>
        <button
          type="button"
          onClick={() => setSel({ id: RICHEST })}
          aria-pressed={sel.id === RICHEST}
          className={`w-full rounded-lg border px-3 py-2 text-left text-[13px] ${
            sel.id === RICHEST ? 'border-ink-900 bg-ink-900 text-white' : 'border-ink-200 text-ink-800 hover:bg-ink-50'
          }`}
        >
          <span className="font-semibold">{richestLabel}</span>
          <span className={`block text-[11.5px] ${sel.id === RICHEST ? 'text-ink-200' : 'text-ink-500'}`}>{richestHelp}</span>
        </button>
        <div className="mt-4 flex flex-wrap items-center gap-1.5 text-[12px]">
          <span className="text-ink-400">By folder</span>
          {(
            [
              ['count', 'most'],
              ['density', 'densest'],
              ['shelfmark', 'shelfmark'],
            ] as const
          ).map(([k, label]) => (
            <button
              key={k}
              type="button"
              onClick={() => setOrder(k)}
              aria-pressed={order === k}
              className={`rounded-full border px-2.5 py-0.5 ${
                order === k ? 'border-ink-900 bg-ink-900 text-white' : 'border-ink-200 text-ink-600 hover:bg-ink-100'
              }`}
            >
              {label}
            </button>
          ))}
        </div>
        <ul className="mt-3 max-h-[32rem] space-y-0.5 overflow-y-auto pr-1 text-[12.5px]">
          {list.map((f) => {
            const v = order === 'density' ? f.density : f.n;
            return (
              <li key={f.id}>
                <button
                  type="button"
                  onClick={() => setSel({ id: f.id })}
                  aria-pressed={f.id === sel.id}
                  title={f.title}
                  className={`flex w-full items-center gap-2 rounded px-1.5 py-1 text-left ${f.id === sel.id ? 'bg-ink-100' : 'hover:bg-ink-50'}`}
                >
                  <span className="tabular w-11 shrink-0 font-semibold text-ink-900">{f.id}</span>
                  <span className="h-1.5 flex-1 rounded-full bg-ink-100">
                    <span className="block h-1.5 rounded-full" style={{ width: `${(100 * v) / max}%`, background: GREEN }} />
                  </span>
                  <span className="tabular w-10 shrink-0 text-right text-ink-500">{order === 'density' ? v.toFixed(0) : v}</span>
                </button>
              </li>
            );
          })}
        </ul>
        <p className="mt-2 text-[11.5px] leading-snug text-ink-400">
          {order === 'density' ? `${noun[1]} per hundred pages transcribed.` : `${noun[1]} in the folder.`}
        </p>
      </aside>

      <section className="min-w-0">
        <div className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
          <h2 className="text-[15px] font-semibold text-ink-900">
            {folder ? (
              <>
                n° {folder.id} <span className="font-normal text-ink-600">{shortTitle(folder.title)}</span>
              </>
            ) : (
              richestLabel
            )}
          </h2>
          {folder && (
            <span className="tabular text-[12.5px] text-ink-400">
              {folder.n} {folder.n > 1 ? noun[1].toLowerCase() : noun[0]} · {folder.date || 's.d.'}
            </span>
          )}
          <a href={src} target="_blank" rel="noreferrer" className="ml-auto text-[12.5px] text-brand-600 hover:text-brand-700">
            open on its own ↗
          </a>
        </div>
        <iframe
          key={src}
          src={src}
          title={`${noun[1]} — ${folder ? `folder ${folder.id}` : richestLabel}`}
          className="mt-3 h-[36rem] w-full rounded-[var(--radius-card)] border border-ink-200 bg-white"
        />
        <p className="mt-2 text-[12px] text-ink-400">‹ › or the arrow keys, once the frame has the focus, turn the slides.</p>
      </section>
    </div>
  );
}
