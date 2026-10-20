import { useCallback, useEffect, useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import { FacsimilePane, type OpenBatch } from './components/FacsimilePane.tsx';
import { BY_ID } from './content/catalogue.ts';
import QUEUE from './content/review-queue.json';
import { batchRange, pdfIndexOf, sourceUrl, useFacsimileProxy } from './lib/batches.ts';
import {
  answerIssues,
  answersMarkdown,
  isMaths,
  loadAnswers,
  saveAnswers,
  VERDICT_NAME,
  type Answer,
  type ReviewItem,
  type ReviewKind,
  type Snippet,
  type Verdict,
} from './lib/review.ts';

/**
 * Whether this build may show transcription text — the same switch as the
 * reading views (#31). The deploy sets it from the repository variable
 * RENDER_TRANSCRIPTS; unset, as in development, it is on.
 *
 * The snippets sit in their own file and are imported only behind this
 * constant, which Vite replaces at build time: with the switch off the import
 * is dead code and the file is not in the bundle at all.
 */
const SHOW_READINGS = import.meta.env.VITE_RENDER_TRANSCRIPTS !== 'false';

const ITEMS = QUEUE.items as ReviewItem[];

const KIND_NAME: Record<ReviewKind, string> = {
  ill: 'Unread word',
  uncertain: 'Doubtful reading',
  add: 'His insertion?',
  supplied: 'Our supply?',
  date: 'Date on a leaf',
  letter: 'Letter',
  argument: 'Edition’s argument',
  reference: 'Reference',
};

function useSnippets(): Record<string, Snippet> | null {
  const [s, setS] = useState<Record<string, Snippet> | null>(null);
  useEffect(() => {
    if (!SHOW_READINGS) return;
    let alive = true;
    import('./content/review-snippets.json').then((m) => alive && setS(m.default as Record<string, Snippet>));
    return () => {
      alive = false;
    };
  }, []);
  return s;
}

const idFromHash = () => {
  const h = decodeURIComponent(location.hash.slice(1));
  return ITEMS.some((i) => i.id === h) ? h : null;
};

export function ReviewPage() {
  const snippets = useSnippets();
  const relay = useFacsimileProxy();
  const [answers, setAnswers] = useState<Record<string, Answer>>(loadAnswers);
  const [kind, setKind] = useState<ReviewKind | 'all'>('all');
  const [id, setId] = useState<string>(() => idFromHash() ?? ITEMS.find((i) => !loadAnswers()[i.id])?.id ?? ITEMS[0].id);
  const [pane, setPane] = useState(true);
  const [paneBatch, setPaneBatch] = useState<number | null>(null);
  const [copied, setCopied] = useState(false);

  const shown = useMemo(() => (kind === 'all' ? ITEMS : ITEMS.filter((i) => i.kind === kind)), [kind]);
  const item = ITEMS.find((i) => i.id === id) ?? ITEMS[0];
  const index = shown.findIndex((i) => i.id === item.id);
  const answer = answers[item.id];

  const go = useCallback((next: string) => {
    setId(next);
    setPaneBatch(null);
    history.replaceState(null, '', `#${next}`);
  }, []);
  useEffect(() => {
    const onHash = () => {
      const h = idFromHash();
      if (h) go(h);
    };
    addEventListener('hashchange', onHash);
    return () => removeEventListener('hashchange', onHash);
  }, [go]);

  const step = (d: number) => {
    const list = shown.length ? shown : ITEMS;
    const i = list.findIndex((x) => x.id === item.id);
    go(list[(i + d + list.length) % list.length].id);
  };

  const record = (verdict: Verdict, extra: Partial<Answer> = {}, advance = true) => {
    const next = { ...answers, [item.id]: { ...answers[item.id], verdict, ...extra, date: new Date().toISOString() } };
    if (verdict !== 'other') delete next[item.id].reading;
    setAnswers(next);
    saveAnswers(next);
    if (advance) {
      const list = shown.length ? shown : ITEMS;
      const i = list.findIndex((x) => x.id === item.id);
      const after = [...list.slice(i + 1), ...list.slice(0, i)].find((x) => !next[x.id]);
      if (after) go(after.id);
    }
  };

  const clearOne = () => {
    const next = { ...answers };
    delete next[item.id];
    setAnswers(next);
    saveAnswers(next);
  };

  const sendable = useMemo(
    () =>
      ITEMS.filter((i) => answers[i.id] && answers[i.id].verdict !== 'skip').map(
        (i) => [i, answers[i.id]] as [ReviewItem, Answer],
      ),
    [answers],
  );
  const issues = useMemo(() => answerIssues(sendable), [sendable]);

  // A browser lets one click open one window: several parts are offered as links.
  const [parts, setParts] = useState(false);
  const send = () => {
    if (issues.length === 1) window.open(issues[0].url, '_blank', 'noopener');
    else setParts(true);
  };
  const copy = async () => {
    try {
      await navigator.clipboard.writeText(answersMarkdown(sendable));
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    } catch {
      /* no clipboard permission: the text stays selectable below */
    }
  };

  const cote = BY_ID.get(item.cote);
  const pages = cote?.pages ?? (item.page ?? 20);
  const batch = paneBatch ?? item.batch;
  const facsimile: OpenBatch = {
    cote: item.cote,
    title: cote?.title ?? `Folder ${item.cote}`,
    date: cote?.date ?? '',
    batch,
    pages,
    page: paneBatch ? batchRange(paneBatch, pages).first : (item.page ?? undefined),
    wholeFolder: !paneBatch,
    relay,
  };
  const done = ITEMS.filter((i) => answers[i.id]).length;

  return (
    <>
      <div className={`transition-[padding] duration-150 ${pane ? 'lg:pr-[var(--pane,0px)]' : ''}`}>
        <Header path="/review/" />
        <main className="mx-auto max-w-6xl px-4 py-8 sm:px-5">
          <header className="max-w-[48em]">
            <h1 className="titre text-[30px] leading-tight text-ink-900">Review against the facsimile</h1>
            <p className="mt-2 text-[14.5px] leading-relaxed text-ink-700">
              The open checks of{' '}
              <a className="text-brand-700 underline" href="https://github.com/Commutator-IO/grothendieck-project/issues/35">
                issue #35
              </a>{' '}
              that need a reader of French handwriting, not of the mathematics: one spot of a page at a time, with
              Montpellier’s facsimile beside it. Your answers stay in this browser until you send them as a prefilled
              GitHub issue.
            </p>
            <p className="mt-2 text-[13px] text-ink-500">
              {done} of {ITEMS.length} answered · built from #35 on {QUEUE.built}
            </p>
          </header>

          <div className="mt-6 grid gap-6 2xl:grid-cols-[14rem_minmax(0,1fr)]">
            <nav aria-label="Checks" className="order-2 2xl:order-1">
              <label className="block text-[11px] font-semibold uppercase tracking-wider text-ink-400" htmlFor="kind">
                Show
              </label>
              <select
                id="kind"
                value={kind}
                onChange={(e) => setKind(e.target.value as ReviewKind | 'all')}
                className="mt-1 w-full rounded-md border border-ink-200 bg-white px-2 py-1.5 text-[13px]"
              >
                <option value="all">All checks ({ITEMS.length})</option>
                {(Object.keys(KIND_NAME) as ReviewKind[]).map((k) => {
                  const n = ITEMS.filter((i) => i.kind === k).length;
                  return n ? (
                    <option key={k} value={k}>
                      {KIND_NAME[k]} ({n})
                    </option>
                  ) : null;
                })}
              </select>
              <ol className="mt-2 max-h-[40vh] overflow-y-auto 2xl:max-h-[70vh] rounded-md border border-ink-200 text-[12.5px]">
                {shown.map((i) => {
                  const a = answers[i.id];
                  return (
                    <li key={i.id}>
                      <button
                        type="button"
                        onClick={() => go(i.id)}
                        aria-current={i.id === item.id ? 'true' : undefined}
                        className={`flex w-full items-center gap-2 px-2 py-1.5 text-left hover:bg-ink-50 ${
                          i.id === item.id ? 'bg-ink-100 font-semibold' : ''
                        }`}
                      >
                        <span
                          aria-label={a ? VERDICT_NAME[a.verdict] : 'Not answered'}
                          className={`h-2 w-2 shrink-0 rounded-full ${
                            !a
                              ? 'border border-ink-300'
                              : a.verdict === 'right'
                                ? 'bg-emerald-500'
                                : a.verdict === 'other'
                                  ? 'bg-brand-500'
                                  : a.verdict === 'illegible'
                                    ? 'bg-amber-500'
                                    : 'bg-ink-300'
                          }`}
                        />
                        <span className="truncate">
                          {i.cote}
                          {i.page ? ` p. ${i.page}` : ''} · {KIND_NAME[i.kind]}
                        </span>
                      </button>
                    </li>
                  );
                })}
              </ol>
            </nav>

            <section className="order-1 min-w-0 2xl:order-2" aria-live="polite">
              <div className="rounded-xl border border-ink-200 bg-white p-4 sm:p-5">
                <p className="flex flex-wrap items-center gap-x-2 text-[11.5px] font-semibold uppercase tracking-wider text-ink-400">
                  <span className="rounded bg-ink-100 px-1.5 py-0.5 text-ink-600">{KIND_NAME[item.kind]}</span>
                  <span>
                    Folder {item.cote} · batch {item.batch}
                    {item.page ? ` · page ${item.page}` : ''}
                  </span>
                  <span className="ml-auto normal-case tracking-normal">
                    {index >= 0 ? index + 1 : '–'} / {shown.length}
                  </span>
                </p>
                <h2 className="mt-2 text-[17px] font-semibold leading-snug text-ink-900">{item.question}</h2>
                {cote && <p className="mt-1 text-[12.5px] text-ink-500">{cote.title}</p>}

                {SHOW_READINGS ? (
                  snippets?.[item.id] ? (
                    <Reading s={snippets[item.id]} />
                  ) : (
                    <p className="mt-3 text-[13px] italic text-ink-500">
                      {snippets ? 'No passage quoted for this check: the question says where to look.' : 'Loading the reading…'}
                    </p>
                  )
                ) : (
                  <p className="mt-3 rounded-md bg-ink-50 px-3 py-2 text-[13px] text-ink-600">
                    The transcriptions are not shown on the site at the moment, so the current reading is not quoted
                    here. The question and the facsimile are enough to answer from the page.
                  </p>
                )}
                {item.context && <p className="mt-2 text-[12.5px] text-ink-500">{item.context}</p>}

                <p className="mt-3 flex flex-wrap gap-x-4 gap-y-1 text-[13px]">
                  {SHOW_READINGS && (
                    <a className="text-brand-700 underline" href={item.link}>
                      {isMaths(item.kind) ? 'Open the modernised reading' : 'Open the reading at this page'}
                    </a>
                  )}
                  <a
                    className="text-brand-700 underline"
                    href={`${sourceUrl(item.cote)}#page=${pdfIndexOf(item.page ?? batchRange(item.batch, pages).first)}`}
                    target="_blank"
                    rel="noopener"
                  >
                    Facsimile at Montpellier ↗
                  </a>
                  {!pane && (
                    <button type="button" className="hidden text-brand-700 underline lg:inline" onClick={() => setPane(true)}>
                      Show the facsimile beside
                    </button>
                  )}
                </p>

                <Answering key={item.id} item={item} answer={answer} onRecord={record} onClear={clearOne} />

                <div className="mt-4 flex justify-between text-[13px]">
                  <button type="button" className="rounded-md px-2 py-1 text-ink-600 hover:bg-ink-50" onClick={() => step(-1)}>
                    ← Previous
                  </button>
                  <button type="button" className="rounded-md px-2 py-1 text-ink-600 hover:bg-ink-50" onClick={() => step(1)}>
                    Next →
                  </button>
                </div>
              </div>

              <div className="mt-6 rounded-xl border border-ink-200 bg-ink-50 p-4 sm:p-5">
                <h2 className="text-[15px] font-semibold text-ink-900">Send my answers</h2>
                <p className="mt-1 text-[13px] text-ink-600">
                  {sendable.length
                    ? `${sendable.length} answer${sendable.length === 1 ? '' : 's'} to send (skipped checks are left out). `
                    : 'No answers yet. '}
                  Sending opens GitHub’s new-issue form, prefilled and referencing #35; nothing is published until you
                  submit it, and it needs a GitHub account. Only your verdict, your reading (fifteen words at most) and
                  your note go into it — no transcription text.
                  {issues.length > 1 &&
                    ` The answers are too many for one link: they go in ${issues.length} issues, one per part, or copy them as Markdown into one.`}
                </p>
                <div className="mt-3 flex flex-wrap gap-2">
                  <button
                    type="button"
                    disabled={!sendable.length}
                    onClick={send}
                    className="rounded-md bg-brand-700 px-3 py-1.5 text-[13px] font-semibold text-white disabled:opacity-40"
                  >
                    Send my answers{issues.length > 1 ? ` (${issues.length} issues)` : ''}
                  </button>
                  <button
                    type="button"
                    disabled={!sendable.length}
                    onClick={copy}
                    className="rounded-md border border-ink-300 bg-white px-3 py-1.5 text-[13px] disabled:opacity-40"
                  >
                    {copied ? 'Copied' : 'Copy as Markdown'}
                  </button>
                  <button
                    type="button"
                    disabled={!done}
                    onClick={() => {
                      if (!confirm('Forget all your answers in this browser?')) return;
                      setAnswers({});
                      saveAnswers({});
                    }}
                    className="rounded-md px-3 py-1.5 text-[13px] text-ink-500 hover:bg-white disabled:opacity-40"
                  >
                    Clear my answers
                  </button>
                </div>
                {parts && issues.length > 1 && (
                  <ol className="mt-3 grid gap-1 text-[13px]">
                    {issues.map((is) => (
                      <li key={is.url}>
                        <a className="text-brand-700 underline" href={is.url} target="_blank" rel="noopener">
                          {is.title} ↗
                        </a>
                      </li>
                    ))}
                  </ol>
                )}
              </div>
            </section>
          </div>
        </main>
        <Footer />
      </div>
      {pane && <FacsimilePane open={facsimile} onClose={() => setPane(false)} onBatch={setPaneBatch} />}
    </>
  );
}

/** The current reading, the doubtful word marked. Formulas stay as TeX. */
function Reading({ s }: { s: Snippet }) {
  return (
    <blockquote className="mt-3 rounded-md border-l-4 border-brand-300 bg-ink-50 px-3 py-2 text-[15px] leading-relaxed text-ink-800">
      <Tex text={s.before} />
      {s.glueBefore ? '' : ' '}
      <mark className="rounded bg-amber-200 px-0.5 font-semibold text-ink-900">
        <Tex text={s.word} />
      </mark>
      {s.glueAfter ? '' : ' '}
      <Tex text={s.after} />
    </blockquote>
  );
}

function Tex({ text }: { text: string }) {
  return (
    <>
      {text.split(/(\$[^$]*\$)/).map((p, i) =>
        p.startsWith('$') && p.endsWith('$') && p.length > 1 ? (
          <code key={i} className="font-mono text-[13px] text-ink-700">
            {p.slice(1, -1)}
          </code>
        ) : (
          p
        ),
      )}
    </>
  );
}

function Answering({
  item,
  answer,
  onRecord,
  onClear,
}: {
  item: ReviewItem;
  answer: Answer | undefined;
  onRecord: (v: Verdict, extra?: Partial<Answer>, advance?: boolean) => void;
  onClear: () => void;
}) {
  const [other, setOther] = useState(answer?.verdict === 'other');
  const [reading, setReading] = useState(answer?.reading ?? '');
  const [note, setNote] = useState(answer?.note ?? '');
  const maths = isMaths(item.kind);
  const label: Record<Exclude<Verdict, 'skip'>, string> = maths
    ? { right: 'It checks out', other: 'It does not hold', illegible: "Can't tell" }
    : { right: VERDICT_NAME.right, other: VERDICT_NAME.other, illegible: VERDICT_NAME.illegible };
  const btn = (on: boolean) =>
    `rounded-md border px-3 py-1.5 text-[13px] font-medium transition ${
      on ? 'border-brand-700 bg-brand-700 text-white' : 'border-ink-300 bg-white text-ink-800 hover:border-brand-500'
    }`;

  return (
    <div className="mt-4 border-t border-ink-100 pt-4">
      <div className="flex flex-wrap gap-2">
        <button type="button" className={btn(answer?.verdict === 'right')} onClick={() => onRecord('right', { note })}>
          {label.right}
        </button>
        <button type="button" className={btn(other)} onClick={() => setOther(true)}>
          {label.other}
        </button>
        <button type="button" className={btn(answer?.verdict === 'illegible')} onClick={() => onRecord('illegible', { note })}>
          {label.illegible}
        </button>
        <button type="button" className={btn(answer?.verdict === 'skip')} onClick={() => onRecord('skip')}>
          Skip
        </button>
      </div>
      {other && (
        <form
          className="mt-3"
          onSubmit={(e) => {
            e.preventDefault();
            onRecord('other', { reading: reading.trim(), note });
          }}
        >
          <label className="block text-[12.5px] text-ink-600" htmlFor="reading">
            {maths ? 'What is wrong, in a few words' : 'What you read on the page (a few words)'}
          </label>
          <div className="mt-1 flex gap-2">
            <input
              id="reading"
              value={reading}
              onChange={(e) => setReading(e.target.value)}
              autoFocus
              className="min-w-0 flex-1 rounded-md border border-ink-300 px-2 py-1.5 text-[14px]"
            />
            <button type="submit" disabled={!reading.trim()} className="rounded-md bg-brand-700 px-3 py-1.5 text-[13px] font-semibold text-white disabled:opacity-40">
              Save
            </button>
          </div>
        </form>
      )}
      <label className="mt-3 block text-[12.5px] text-ink-600" htmlFor="note">
        Note (optional) — what makes you sure, or unsure
      </label>
      <textarea
        id="note"
        value={note}
        onChange={(e) => setNote(e.target.value)}
        onBlur={() => answer && note !== (answer.note ?? '') && onRecord(answer.verdict, { note }, false)}
        rows={2}
        className="mt-1 w-full rounded-md border border-ink-300 px-2 py-1.5 text-[13px]"
      />
      {answer && (
        <p className="mt-1 text-[12px] text-ink-500">
          Your answer: {maths && answer.verdict !== 'skip' ? label[answer.verdict] : VERDICT_NAME[answer.verdict]}
          {answer.reading ? ` — « ${answer.reading} »` : ''}.{' '}
          <button type="button" className="underline" onClick={onClear}>
            Clear
          </button>
        </p>
      )}
    </div>
  );
}
