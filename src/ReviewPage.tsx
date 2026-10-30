import { useCallback, useEffect, useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import { BnfReview } from './components/BnfReview.tsx';
import { BourbakiReview } from './components/BourbakiReview.tsx';
import { FacsimilePane, type OpenBatch } from './components/FacsimilePane.tsx';
import BNF from './content/review-bnf.json';
import { BY_ID } from './content/catalogue.ts';
import QUEUE from './content/review-queue.json';
import { batchRange, pdfIndexOf, sourceUrl, useFacsimileProxy } from './lib/batches.ts';
import {
  answerIssues,
  answerName,
  answersMarkdown,
  isMaths,
  loadAnswers,
  saveAnswers,
  type Answer,
  type Choice,
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

// Readers of the hand first, then the questions for mathematicians.
const ITEMS = [...(QUEUE.items as ReviewItem[])].sort((a, b) => Number(isMaths(a.kind)) - Number(isMaths(b.kind)));
const AUDIENCE = { readers: 'Reading the hand', maths: 'For mathematicians' } as const;
type Filter = ReviewKind | 'all' | keyof typeof AUDIENCE;
const audienceOf = (k: ReviewKind): keyof typeof AUDIENCE => (isMaths(k) ? 'maths' : 'readers');
/** Answered here, with anything but « Skip »: such items leave the list unless « Show answered » is on. */
const isAnswered = (a: Answer | undefined) => !!a && a.verdict !== 'skip';
const ORDER = new Map(ITEMS.map((i, n) => [i.id, n]));

const KIND_NAME: Record<ReviewKind, string> = {
  ill: 'Unread word',
  uncertain: 'Doubtful reading',
  add: 'His insertion?',
  supplied: 'Our supply?',
  date: 'Date on a leaf',
  letter: 'Letter',
  argument: 'Edition’s argument',
  reference: 'Reference',
  hypothesis: 'Hypothesis behind a counterexample',
  imprecise: 'Statement too imprecise to fix',
  unproved: 'Stated without proof?',
  paper: 'Printed side of reused paper',
  quoted: 'Words quoted outside the edition',
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
  const [kind, setKind] = useState<Filter>('all');
  const [id, setId] = useState<string>(() => idFromHash() ?? ITEMS.find((i) => !loadAnswers()[i.id])?.id ?? ITEMS[0].id);
  const [pane, setPane] = useState(true);
  const [paneBatch, setPaneBatch] = useState<number | null>(null);
  const [copied, setCopied] = useState(false);
  const [showAnswered, setShowAnswered] = useState(false);
  // Two sets of questions: the Montpellier checks of #35, and the BnF visit (#37), which has no facsimile online.
  // A third, the Bourbaki transcriptions (#50), on the dev server only: their questions sit in an ignored file.
  const [source, setSource] = useState<'montpellier' | 'bnf' | 'bourbaki'>(() =>
    location.hash.startsWith('#bnf') ? 'bnf' : import.meta.env.DEV && location.hash.startsWith('#bourbaki') ? 'bourbaki' : 'montpellier',
  );

  // The items listed: answered ones (not skipped) are hidden unless asked for, so the list is what is left to do.
  const listed = useMemo(
    () => (showAnswered ? ITEMS : ITEMS.filter((i) => !isAnswered(answers[i.id]))),
    [answers, showAnswered],
  );
  const inKind = useCallback(
    (i: ReviewItem) => kind === 'all' || (kind in AUDIENCE ? audienceOf(i.kind) === kind : i.kind === kind),
    [kind],
  );
  const shown = useMemo(() => listed.filter(inKind), [listed, inKind]);
  const answeredHere = ITEMS.filter((i) => inKind(i) && isAnswered(answers[i.id])).length;
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

  // Previous / Next walk the list as shown; from an item no longer in it (just answered), the nearest neighbour.
  const step = (d: number) => {
    if (!shown.length) return;
    const i = shown.findIndex((x) => x.id === item.id);
    if (i >= 0) return go(shown[(i + d + shown.length) % shown.length].id);
    const at = ORDER.get(item.id) ?? 0;
    const next = d > 0 ? (shown.find((x) => ORDER.get(x.id)! > at) ?? shown[0]) : ([...shown].reverse().find((x) => ORDER.get(x.id)! < at) ?? shown[shown.length - 1]);
    go(next.id);
  };

  const record = (verdict: Verdict, extra: Partial<Answer> = {}, advance = true) => {
    // A new answer replaces the old one whole (its choice, its reading), keeping only the note.
    const next = { ...answers, [item.id]: { note: answers[item.id]?.note, ...extra, verdict, date: new Date().toISOString() } };
    setAnswers(next);
    saveAnswers(next);
    if (advance) {
      // The next item with no answer at all, in the order of the list and after this one.
      const at = ORDER.get(item.id) ?? 0;
      const list = ITEMS.filter((x) => x.id !== item.id && inKind(x) && !next[x.id]);
      const after = list.find((x) => ORDER.get(x.id)! > at) ?? list[0];
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
    // Sent answers stay hidden from the list; they leave the queue for good once applied (review-answered.json).
    setShowAnswered(false);
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
      <div className={`transition-[padding] duration-150 ${pane && source === 'montpellier' ? 'lg:pr-[var(--pane,0px)]' : ''}`}>
        <Header path="/review/" />
        <main className="mx-auto max-w-6xl px-4 py-8 sm:px-5">
          <header className="max-w-[48em]">
            <h1 className="titre text-[30px] leading-tight text-ink-900">Review against the facsimile</h1>
            <p className="mt-2 text-[14.5px] leading-relaxed text-ink-700">
              The open checks of{' '}
              <a className="text-brand-700 underline" href="https://github.com/Commutator-IO/grothendieck-project/issues/35">
                issue #35
              </a>{' '}
              that need a reader of French handwriting. Each is one spot of a page, shown beside Montpellier’s
              facsimile, with a plain question and its answers as buttons. A few, under « For mathematicians », ask
              instead whether an argument or a reference of the edition holds. Your answers stay in this browser until
              you send them as a prefilled GitHub issue.
            </p>
            <p className="mt-2 text-[13px] text-ink-500">
              {done} of {ITEMS.length} answered · built from #35 on {QUEUE.built}
            </p>
          </header>

          <div role="tablist" aria-label="Questions" className="mt-5 flex gap-1 border-b border-ink-200">
            {(
              [
                ['montpellier', `Montpellier fonds (${listed.length})`],
                ['bnf', `BnF visit, NAF 29093 (${BNF.boxes.reduce((n, b) => n + b.items.length, 0)})`],
                ...(import.meta.env.DEV ? ([['bourbaki', 'Local: Bourbaki, Buffalo, Quillen']] as const) : []),
              ] as const
            ).map(([k, label]) => (
              <button
                key={k}
                role="tab"
                type="button"
                aria-selected={source === k}
                onClick={() => {
                  setSource(k);
                  history.replaceState(null, '', k === 'montpellier' ? `#${item.id}` : `#${k}`);
                }}
                className={`-mb-px border-b-2 px-3 py-2 text-[14px] ${
                  source === k ? 'border-brand-700 font-semibold text-ink-900' : 'border-transparent text-ink-500 hover:text-ink-800'
                }`}
              >
                {label}
              </button>
            ))}
          </div>

          {source === 'bnf' && <BnfReview />}
          {import.meta.env.DEV && source === 'bourbaki' && <BourbakiReview />}
          <div hidden={source !== 'montpellier'} className="mt-6 grid gap-6 2xl:grid-cols-[14rem_minmax(0,1fr)]">
            <nav aria-label="Checks" className="order-2 2xl:order-1">
              <label className="block text-[11px] font-semibold uppercase tracking-wider text-ink-400" htmlFor="kind">
                Show
              </label>
              <select
                id="kind"
                value={kind}
                onChange={(e) => setKind(e.target.value as Filter)}
                className="mt-1 w-full rounded-md border border-ink-200 bg-white px-2 py-1.5 text-[13px]"
              >
                <option value="all">All checks ({listed.length})</option>
                {(Object.keys(AUDIENCE) as (keyof typeof AUDIENCE)[]).map((au) => (
                  <optgroup key={au} label={AUDIENCE[au]}>
                    <option value={au}>
                      All: {AUDIENCE[au].toLowerCase()} ({listed.filter((i) => audienceOf(i.kind) === au).length})
                    </option>
                    {(Object.keys(KIND_NAME) as ReviewKind[])
                      .filter((k) => audienceOf(k) === au)
                      .map((k) => {
                        const n = listed.filter((i) => i.kind === k).length;
                        return ITEMS.some((i) => i.kind === k) ? (
                          <option key={k} value={k}>
                            {KIND_NAME[k]} ({n})
                          </option>
                        ) : null;
                      })}
                  </optgroup>
                ))}
              </select>
              <label className="mt-2 flex items-center gap-2 text-[12.5px] text-ink-600">
                <input
                  type="checkbox"
                  checked={showAnswered}
                  onChange={(e) => setShowAnswered(e.target.checked)}
                  className="h-4 w-4 accent-brand-700"
                />
                Show answered ({answeredHere})
              </label>
              {!shown.length && (
                <p className="mt-2 rounded-md border border-ink-200 px-2 py-2 text-[12.5px] text-ink-500">
                  {answeredHere ? 'Every check in this view is answered.' : 'No checks in this view.'}
                </p>
              )}
              <ol hidden={!shown.length} className="mt-2 max-h-[40vh] overflow-y-auto 2xl:max-h-[70vh] rounded-md border border-ink-200 text-[12.5px]">
                {shown.map((i, n) => {
                  const a = answers[i.id];
                  const au = audienceOf(i.kind);
                  const head = n === 0 ? shown.some((x) => audienceOf(x.kind) !== au) : audienceOf(shown[n - 1].kind) !== au;
                  return (
                    <li key={i.id}>
                      {head && (
                        <p className="sticky top-0 border-b border-ink-200 bg-ink-50 px-2 py-1 text-[11px] font-semibold uppercase tracking-wider text-ink-500">
                          {AUDIENCE[au]}
                        </p>
                      )}
                      <button
                        type="button"
                        onClick={() => go(i.id)}
                        aria-current={i.id === item.id ? 'true' : undefined}
                        className={`flex w-full items-center gap-2 px-2 py-1.5 text-left hover:bg-ink-50 ${
                          i.id === item.id ? 'bg-ink-100 font-semibold' : ''
                        }`}
                      >
                        <span
                          aria-label={a ? answerName(i, a) : 'Not answered'}
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
                  {isMaths(item.kind) && (
                    <span className="rounded bg-brand-700 px-1.5 py-0.5 text-white">{AUDIENCE.maths}</span>
                  )}
                  <span className="rounded bg-ink-100 px-1.5 py-0.5 text-ink-600">{KIND_NAME[item.kind]}</span>
                  <span>
                    Folder {item.cote} · batch {item.batch}
                    {item.page ? ` · page ${item.page}` : ''}
                  </span>
                  <span className="ml-auto normal-case tracking-normal">
                    {index >= 0 ? index + 1 : '–'} / {shown.length}
                  </span>
                </p>
                <h2 className="mt-2 text-[17px] font-semibold leading-snug text-ink-900">{item.prompt}</h2>
                {cote && <p className="mt-1 text-[12.5px] text-ink-500">{cote.title}</p>}

                {item.entry && <Entry rows={item.entry} />}
                {item.claim && (
                  <blockquote className="mt-3 rounded-md border-l-4 border-brand-300 bg-ink-50 px-3 py-2 text-[14.5px] leading-relaxed text-ink-800">
                    <span className="block text-[11px] font-semibold uppercase tracking-wider text-ink-400">
                      {item.kind === 'reference' ? 'The references' : item.kind === 'hypothesis' ? 'The statement as read' : 'The edition’s claim'}
                    </span>
                    {item.claim}
                  </blockquote>
                )}
                {SHOW_READINGS && snippets?.[item.id] && <Reading s={snippets[item.id]} />}
                {!SHOW_READINGS && ['ill', 'uncertain', 'add', 'supplied'].includes(item.kind) && (
                  <p className="mt-3 rounded-md bg-ink-50 px-3 py-2 text-[13px] text-ink-600">
                    The transcriptions are not shown on the site at the moment, so the passage is not quoted here.
                  </p>
                )}
                <p className="mt-3 text-[13.5px] text-ink-700">
                  <span className="font-semibold text-ink-900">Where to look: </span>
                  {item.hint}
                </p>
                <details className="mt-2 text-[12.5px] text-ink-500">
                  <summary className="cursor-pointer select-none">Details</summary>
                  <p className="mt-1">
                    From #35, « {item.section} »{item.details ? ':' : '.'}
                  </p>
                  {item.details && <p className="mt-1 text-ink-600">{item.details}</p>}
                  {item.context && <p className="mt-1">{item.context}</p>}
                </details>

                <p className="mt-3 flex flex-wrap gap-x-4 gap-y-1 text-[13px]">
                  {SHOW_READINGS && (
                    <a className="text-brand-700 underline" href={item.link}>
                      {isMaths(item.kind) && item.kind !== 'hypothesis' ? 'Open the modernised reading' : 'Open the reading at this page'}
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
                  submit it, and it needs a GitHub account. The issue carries only your verdict, your reading (fifteen
                  words at most) and your note, and no transcription text.
                  {issues.length > 1 &&
                    ` There are too many answers for one link, so they go in ${issues.length} issues, one per part; you can also copy them as Markdown into a single issue.`}
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
      {pane && source === 'montpellier' && <FacsimilePane open={facsimile} onClose={() => setPane(false)} onBatch={setPaneBatch} />}
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

/** A letter's register entry, the reading to check. */
function Entry({ rows }: { rows: [string, string][] }) {
  return (
    <dl className="mt-3 grid grid-cols-[6.5rem_minmax(0,1fr)] gap-x-3 gap-y-1 rounded-md border-l-4 border-brand-300 bg-ink-50 px-3 py-2 text-[13.5px]">
      {rows.map(([k, v]) => (
        <div key={k} className="contents">
          <dt className="text-ink-500">{k}</dt>
          <dd className="text-ink-800">{v}</dd>
        </div>
      ))}
    </dl>
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
  // An answer saved before the choices has a verdict only: it lights the first button of that verdict.
  const isChosen = (c: Choice) =>
    !!answer && (answer.choice ? answer.choice === c.value : item.choices.find((x) => x.verdict === answer.verdict) === c);
  const [asking, setAsking] = useState<Choice | null>(() => item.choices.find((c) => c.ask && isChosen(c)) ?? null);
  const [reading, setReading] = useState(answer?.reading ?? '');
  const [note, setNote] = useState(answer?.note ?? '');
  const cantTell = !item.choices.some((c) => c.verdict === 'illegible');
  const btn = (on: boolean) =>
    `rounded-md border px-3 py-1.5 text-[13px] font-medium transition ${
      on ? 'border-brand-700 bg-brand-700 text-white' : 'border-ink-300 bg-white text-ink-800 hover:border-brand-500'
    }`;

  return (
    <div className="mt-4 border-t border-ink-100 pt-4">
      <div className="flex flex-wrap gap-2">
        {item.choices.map((c) => (
          <button
            key={c.value}
            type="button"
            className={btn(asking ? asking === c : isChosen(c))}
            onClick={() => {
              if (c.ask) setAsking(c);
              else {
                setAsking(null);
                onRecord(c.verdict, { choice: c.value, note });
              }
            }}
          >
            {c.value}
          </button>
        ))}
        {cantTell && (
          <button
            type="button"
            className={btn(!asking && answer?.verdict === 'illegible')}
            onClick={() => {
              setAsking(null);
              onRecord('illegible', { note });
            }}
          >
            Can’t tell
          </button>
        )}
        <button
          type="button"
          className={btn(!asking && answer?.verdict === 'skip')}
          onClick={() => {
            setAsking(null);
            onRecord('skip', { note });
          }}
        >
          Skip
        </button>
      </div>
      {asking && (
        <form
          className="mt-3"
          onSubmit={(e) => {
            e.preventDefault();
            onRecord(asking.verdict, { choice: asking.value, reading: reading.trim(), note });
          }}
        >
          <label className="block text-[12.5px] text-ink-600" htmlFor="reading">
            {asking.ask} (fifteen words at most)
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
        Note (optional): what makes you sure or unsure
      </label>
      <textarea
        id="note"
        value={note}
        onChange={(e) => setNote(e.target.value)}
        onBlur={() => answer && note !== (answer.note ?? '') && onRecord(answer.verdict, { ...answer, note }, false)}
        rows={2}
        className="mt-1 w-full rounded-md border border-ink-300 px-2 py-1.5 text-[13px]"
      />
      {answer && (
        <p className="mt-1 text-[12px] text-ink-500">
          Your answer: {answerName(item, answer)}
          {answer.reading ? `, « ${answer.reading} »` : ''}.{' '}
          <button type="button" className="underline" onClick={onClear}>
            Clear
          </button>
        </p>
      )}
    </div>
  );
}
