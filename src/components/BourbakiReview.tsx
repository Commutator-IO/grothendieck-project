import { useEffect, useState } from 'react';

/**
 * Checks of the local Bourbaki transcriptions (#50), for the dev server only. The questions live in
 * public/transcripts-bourbaki/review.json, which .gitignore keeps out of the repository with the
 * transcriptions themselves; the built site has neither, so this tab is not offered there. Each check
 * opens the AHP's facsimile at its page beside the rendered transcription. Answers stay in this browser.
 */

type Mark = 'yes' | 'no' | 'unsure';
interface Ans {
  mark?: Mark;
  note?: string;
}
type Store = Record<string, Ans>;
interface Check {
  id: string;
  page: number;
  batch: number;
  /** For a recording: the second of the video to listen from. */
  t?: number;
  q: string;
}
interface Doc {
  id: string;
  title: string;
  /** A YouTube id, for the Buffalo recordings: the check is heard, not read on a facsimile. */
  video?: string;
  /** For a Quillen notebook: the folder of its rendered transcriptions, and their language. */
  base?: string;
  lang?: string;
  pdf: string;
  item: string;
  checks: Check[];
}
interface Review {
  built: string;
  docs: Doc[];
}

const KEY = 'gn-review:bourbaki-50';
const MARKS: [Mark, string][] = [
  ['yes', 'Yes'],
  ['no', 'No'],
  ['unsure', 'Unsure'],
];

function load(): Store {
  try {
    const v = JSON.parse(localStorage.getItem(KEY) || '{}');
    return v && typeof v === 'object' ? v : {};
  } catch {
    return {};
  }
}
function save(s: Store) {
  try {
    localStorage.setItem(KEY, JSON.stringify(s));
  } catch {
    /* private mode: the answers live as long as the tab */
  }
}

const one = (s?: string) => (s ?? '').trim().replace(/\s*\n\s*/g, ' ');
// Bourbaki rédactions by default; a Quillen notebook names its own folder and language.
const html = (d: Doc, c: Check) =>
  `/${d.base ?? 'transcripts-bourbaki'}/${d.base ? d.id.replace(/^quillen-/, '') : d.id}/batch-${String(c.batch).padStart(2, '0')}.${d.lang ?? 'fr'}.html`;

function markdown(r: Review, s: Store): string {
  const out = ['Answers from the local Bourbaki review (#50); readings only, nothing quoted beyond a few words.', ''];
  for (const d of r.docs) {
    const rows = d.checks.filter((c) => s[c.id]?.mark || one(s[c.id]?.note));
    if (!rows.length) continue;
    out.push(`### ${d.title}`);
    for (const c of rows) {
      const a = s[c.id];
      const name = MARKS.find(([m]) => m === a.mark)?.[1] ?? 'No answer';
      const at = c.t !== undefined ? `${Math.floor(c.t / 60)}:${String(c.t % 60).padStart(2, '0')}` : `p. ${c.page}`;
      out.push(`- **${name}** — ${at}, ${c.id}${one(a.note) ? `: ${one(a.note)}` : ''}`);
    }
    out.push('');
  }
  return out.join('\n');
}

export function BourbakiReview() {
  const [r, setR] = useState<Review | null>(null);
  const [err, setErr] = useState(false);
  const [s, setS] = useState<Store>(load);
  const [docId, setDocId] = useState<string>('');
  const [checkId, setCheckId] = useState<string>('');
  const [copied, setCopied] = useState(false);

  useEffect(() => {
    // no-store: the file is edited between sessions, and a cached copy would show answered checks again.
    fetch('/transcripts-bourbaki/review.json', { cache: 'no-store' })
      .then((res) => (res.ok ? res.json() : Promise.reject(new Error(String(res.status)))))
      .then((j: Review) => {
        setR(j);
        setDocId(j.docs[0]?.id ?? '');
        setCheckId(j.docs[0]?.checks[0]?.id ?? '');
      })
      .catch(() => setErr(true));
  }, []);

  if (err)
    return (
      <p className="mt-6 text-[14px] text-ink-600">
        No local review file (public/transcripts-bourbaki/review.json). The Bourbaki checks exist only on a machine that holds the
        transcriptions.
      </p>
    );
  if (!r) return <p className="mt-6 text-[14px] text-ink-500">Loading…</p>;
  if (!r.docs.length) return <p className="mt-6 text-[14px] text-ink-600">No checks left: every doubtful reading has been answered.</p>;

  const doc = r.docs.find((d) => d.id === docId) ?? r.docs[0];
  const check = doc.checks.find((c) => c.id === checkId) ?? doc.checks[0];
  const set = (id: string, patch: Partial<Ans>) => {
    const next = { ...s, [id]: { ...s[id], ...patch } };
    setS(next);
    save(next);
  };
  const total = r.docs.reduce((n, d) => n + d.checks.length, 0);
  const answered = r.docs.reduce((n, d) => n + d.checks.filter((c) => s[c.id]?.mark).length, 0);
  const copy = async () => {
    try {
      await navigator.clipboard.writeText(markdown(r, s));
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    } catch {
      /* no clipboard permission */
    }
  };
  const btn = (on: boolean) =>
    `rounded-md border px-2.5 py-1 text-[12.5px] font-medium transition ${
      on ? 'border-brand-700 bg-brand-700 text-white' : 'border-ink-300 bg-white text-ink-800 hover:border-brand-500'
    }`;

  return (
    <div className="mt-6">
      <p className="max-w-[48em] text-[14px] leading-relaxed text-ink-700">
        The doubtful readings of the local Bourbaki transcriptions (first passes, {r.built}). Each check shows the AHP facsimile at its page
        and the rendered transcription; answer, add a word if needed, then copy the answers into the chat. This tab exists only on the dev
        server.
      </p>
      <div className="mt-3 flex flex-wrap items-center gap-2 text-[13px]">
        <span className="text-ink-500">
          {answered} of {total} answered
        </span>
        <button type="button" className={btn(false)} onClick={copy}>
          {copied ? 'Copied' : 'Copy all answers as Markdown'}
        </button>
      </div>

      <div className="mt-4 grid gap-4 xl:grid-cols-[18rem_minmax(0,1fr)]">
        <nav aria-label="Rédactions" className="grid content-start gap-3">
          {r.docs.map((d) => (
            <div key={d.id}>
              <button
                type="button"
                className={`text-left text-[13px] font-semibold ${d.id === doc.id ? 'text-brand-700' : 'text-ink-800'}`}
                onClick={() => {
                  setDocId(d.id);
                  setCheckId(d.checks[0].id);
                }}
              >
                {d.title}
              </button>
              {d.id === doc.id && (
                <ol className="mt-1 grid gap-0.5 pl-3">
                  {d.checks.map((c) => (
                    <li key={c.id}>
                      <button
                        type="button"
                        onClick={() => setCheckId(c.id)}
                        className={`text-left text-[12.5px] ${c.id === check.id ? 'font-semibold text-ink-900' : 'text-ink-600'}`}
                      >
                        {s[c.id]?.mark ? '✓ ' : '· '}
                        {c.t !== undefined ? `${Math.floor(c.t / 60)}:${String(c.t % 60).padStart(2, '0')}` : `p. ${c.page}`} —{' '}
                        {c.id.split('-').slice(1).join('-')}
                      </button>
                    </li>
                  ))}
                </ol>
              )}
            </div>
          ))}
        </nav>

        <section>
          <p className="text-[15px] leading-relaxed text-ink-900">
            <span className="font-semibold">
              {doc.video && check.t !== undefined
                ? `${Math.floor(check.t / 60)}:${String(check.t % 60).padStart(2, '0')}`
                : `p. ${check.page}`}
              .
            </span>{' '}
            {check.q}
          </p>
          <div className="mt-2 flex flex-wrap gap-2">
            {MARKS.map(([m, label]) => (
              <button key={m} type="button" className={btn(s[check.id]?.mark === m)} onClick={() => set(check.id, { mark: m })}>
                {label}
              </button>
            ))}
          </div>
          <textarea
            className="mt-2 w-full rounded-md border border-ink-300 p-2 text-[13px]"
            rows={2}
            placeholder="What you read (a few words)"
            value={s[check.id]?.note ?? ''}
            onChange={(e) => set(check.id, { note: e.target.value })}
          />
          {doc.video ? (
            <>
              <p className="mt-1 text-[12px] text-ink-500">
                <a
                  className="text-brand-700 underline"
                  href={`https://www.youtube.com/watch?v=${doc.video}&t=${check.t ?? 0}s`}
                  target="_blank"
                  rel="noreferrer"
                >
                  Listen from {Math.floor((check.t ?? 0) / 60)}:{String((check.t ?? 0) % 60).padStart(2, '0')} on YouTube
                </a>{' '}
                · the transcript is in transcripts-buffalo/ (local); start a few seconds early.
              </p>
              <iframe
                key={`v-${doc.id}-${check.t}`}
                title="Recording"
                src={`https://www.youtube.com/embed/${doc.video}?start=${Math.max(0, (check.t ?? 0) - 5)}`}
                allow="encrypted-media; picture-in-picture"
                className="mt-3 aspect-video w-full max-w-3xl rounded-md border border-ink-200"
              />
            </>
          ) : (
            <>
              <p className="mt-1 text-[12px] text-ink-500">
                <a className="text-brand-700 underline" href={`${doc.pdf}#page=${check.page}`} target="_blank" rel="noreferrer">
                  Facsimile, p. {check.page}
                </a>{' '}
                ·{' '}
                <a className="text-brand-700 underline" href={doc.item} target="_blank" rel="noreferrer">
                  AHP notice
                </a>{' '}
                ·{' '}
                <a className="text-brand-700 underline" href={html(doc, check)} target="_blank" rel="noreferrer">
                  Transcription, batch {check.batch}
                </a>
              </p>
              <p className="mt-1 text-[12px] text-ink-500">
                p. {check.page} is the PDF page, the number the archive pencils top right. Some viewers ignore the page in the link and open
                at p. 1, which shows the start of the rédaction: go to p. {check.page} by hand.
              </p>
              <div className="mt-3 grid gap-3 2xl:grid-cols-2">
                <iframe
                  key={`f-${doc.id}-${check.page}`}
                  title="Facsimile"
                  src={`${doc.pdf}#page=${check.page}`}
                  className="h-[80vh] w-full rounded-md border border-ink-200 bg-white"
                />
                <iframe
                  key={`t-${doc.id}-${check.batch}`}
                  title="Transcription"
                  src={html(doc, check)}
                  className="h-[80vh] w-full rounded-md border border-ink-200 bg-white"
                />
              </div>
            </>
          )}
        </section>
      </div>
    </div>
  );
}
