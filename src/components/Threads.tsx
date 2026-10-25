import { useEffect } from 'react';
import { BY_ID } from '../content/catalogue.ts';
import datedRaw from '../content/dated-leaves.json';
import proposedRaw from '../content/proposed-datings.json';
import { FINDINGS } from '../content/findings.ts';
import { LINKS, THREADS } from '../content/threads.ts';
import type { Finding, FindingLink, LinkBasis, LinkKind, Thread } from '../lib/types.ts';
import { notation } from '../lib/notation.tsx';

/**
 * Threads: ordered lines of thought across folders, and the typed links that
 * join findings outside them. The data is src/content/threads.ts; the dates are
 * read here, at render time, from the inventory, the dates written on the
 * leaves and the project's proposed datings, so a corrected dating corrects
 * every thread. A thread's order is that of the question, not a chronology.
 */

const FIND = new Map(FINDINGS.map((n) => [n.id, n]));

const STATUS_DOT: Record<Finding['status'], string> = {
  unsearched: 'bg-ink-300',
  candidate: 'bg-brand-500',
  matched: 'bg-white ring-2 ring-ink-400',
  refuted: 'bg-alerte-500',
  confirmed: 'bg-relu-500',
};
const STATUS_WORD: Record<Finding['status'], string> = {
  unsearched: 'not looked up',
  candidate: 'candidate',
  matched: 'in the literature',
  refuted: 'refuted',
  confirmed: 'checked by a person',
};

const BASIS: Record<LinkBasis, { label: string; help: string; className: string }> = {
  'cross-reference': {
    label: 'cross-reference',
    help: 'A modernised reading names the other folder itself.',
    className: 'border border-brand-300 bg-brand-50 text-brand-700',
  },
  'same-object': {
    label: 'same object',
    help: 'The same notation, statement or pages.',
    className: 'border border-ink-300 bg-ink-100 text-ink-600',
  },
  date: {
    label: 'dates',
    help: 'Dates written on the leaves place the two pieces.',
    className: 'border border-ink-300 bg-ink-100 text-ink-600',
  },
  edition: {
    label: "edition's inference",
    help: "Rests on our reading alone (« rapprochement de l'édition »).",
    className: 'border border-dashed border-alerte-500 bg-white text-alerte-700',
  },
};

/** « A kind B », read forwards from A and backwards from B. */
const KIND_OUT: Record<LinkKind, string> = {
  continues: 'continues',
  uses: 'uses',
  generalises: 'generalises',
  corrects: 'corrects',
  'same-question': 'asks the same question as',
};
const KIND_IN: Record<LinkKind, string> = {
  continues: 'continued by',
  uses: 'used by',
  generalises: 'generalised by',
  corrects: 'corrected by',
  'same-question': 'asks the same question as',
};

/** The claim cut at a word, for a link or a frieze step. */
export function shorten(s: string, max = 96): string {
  if (s.length <= max) return s;
  const cut = s.slice(0, max);
  const sp = cut.lastIndexOf(' ');
  return `${cut.slice(0, sp > 40 ? sp : max).replace(/[\s,;:(]+$/, '')}…`;
}

/* ---- dates, read at render time ---------------------------------------- */

const years = (s: string | null | undefined) =>
  (s?.match(/\b(1[89]\d\d)\b/g) ?? []).map(Number);

type Dated = { folder: string; iso?: string; kind?: string };
const leafYears = new Map<string, number[]>();
for (const r of (datedRaw as { records: Dated[] }).records) {
  // « paper » records date a Bourbaki rédaction written on the back of, not the leaf.
  if (r.kind === 'paper') continue;
  const y = years(r.iso);
  if (y.length) leafYears.set(r.folder, [...(leafYears.get(r.folder) ?? []), ...y]);
}
type Proposed = { folder: string; from: string | null; to: string | null };
const proposedYears = new Map<string, number[]>();
for (const r of (proposedRaw as { records: Proposed[] }).records)
  proposedYears.set(r.folder, [...years(r.from), ...years(r.to)]);

/** The years a folder is dated to: inventory, leaves and proposed dating together. */
function folderYears(cote: string): number[] {
  return [
    ...years(BY_ID.get(cote)?.date),
    ...(leafYears.get(cote) ?? []),
    ...(proposedYears.get(cote) ?? []),
  ];
}

function rangeOf(t: Thread): string | null {
  const ys = t.steps.flatMap((s) => {
    const f = FIND.get(s.id);
    return f ? folderYears(f.cote) : [];
  });
  if (!ys.length) return null;
  const a = Math.min(...ys);
  const b = Math.max(...ys);
  return a === b ? `${a}` : `${a}–${b}`;
}

/* ---- indexes ------------------------------------------------------------ */

/** For each finding, its neighbours in each thread containing it. */
const IN_THREADS = new Map<string, { thread: Thread; prev?: string; next?: string }[]>();
for (const t of THREADS)
  t.steps.forEach((s, i) => {
    const list = IN_THREADS.get(s.id) ?? [];
    list.push({ thread: t, prev: t.steps[i - 1]?.id, next: t.steps[i + 1]?.id });
    IN_THREADS.set(s.id, list);
  });

/** For each finding, its typed links in both directions. */
const LINKED = new Map<string, { link: FindingLink; other: string; out: boolean }[]>();
for (const l of LINKS) {
  LINKED.set(l.from, [...(LINKED.get(l.from) ?? []), { link: l, other: l.to, out: true }]);
  LINKED.set(l.to, [...(LINKED.get(l.to) ?? []), { link: l, other: l.from, out: false }]);
}

/* ---- pieces ------------------------------------------------------------- */

function BasisLabel({ basis, where }: { basis: LinkBasis; where?: string }) {
  const b = BASIS[basis];
  return (
    <span
      title={where ? `${b.help} ${where}` : b.help}
      className={`inline-block rounded-full px-2 py-0.5 text-[10px] font-semibold uppercase tracking-wide ${b.className}`}
    >
      {b.label}
    </span>
  );
}

function FindingLinkText({ id }: { id: string }) {
  const f = FIND.get(id);
  if (!f) return null;
  return (
    <a
      href={`#${id}`}
      title={f.claim}
      className="text-brand-700 underline decoration-brand-200 underline-offset-2 hover:decoration-brand-600"
    >
      <span className="tabular font-semibold">n° {f.cote}</span> {notation(shorten(f.claim, 80))}
    </a>
  );
}

/**
 * The foot of a finding card: where the finding sits in its threads (the step
 * before and the step after, with the thread's title), and its typed links in
 * both directions. Renders nothing for the findings that are in neither.
 */
export function SeeAlso({ id }: { id: string }) {
  const threads = IN_THREADS.get(id) ?? [];
  const links = LINKED.get(id) ?? [];
  if (!threads.length && !links.length) return null;
  return (
    <div className="mt-3 border-t border-ink-100 pt-3 text-[12.5px] leading-relaxed text-ink-600">
      <h4 className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">See also</h4>
      <ul className="mt-1.5 space-y-1.5">
        {threads.map(({ thread, prev, next }) => (
          <li key={thread.id} className="max-w-[48em]">
            In the thread{' '}
            <a
              href={`#thread-${thread.id}`}
              className="font-semibold text-ink-800 underline decoration-ink-300 underline-offset-2 hover:text-brand-700"
            >
              {thread.title}
            </a>
            :
            <ul className="mt-0.5 space-y-0.5 pl-3">
              {prev && (
                <li>
                  <span className="text-ink-500">previous: </span>
                  <FindingLinkText id={prev} />
                </li>
              )}
              {next && (
                <li>
                  <span className="text-ink-500">next: </span>
                  <FindingLinkText id={next} />
                </li>
              )}
            </ul>
          </li>
        ))}
        {links.map(({ link, other, out }) => (
          <li key={`${link.from}>${link.to}`} className="max-w-[48em]">
            <span className="text-ink-500">{out ? KIND_OUT[link.kind] : KIND_IN[link.kind]}: </span>
            <FindingLinkText id={other} />{' '}
            <BasisLabel basis={link.basis} where={link.where} />
            <span className="block pl-3 text-ink-500">{link.note}</span>
          </li>
        ))}
      </ul>
    </div>
  );
}

function ThreadBlock({ t }: { t: Thread }) {
  const range = rangeOf(t);
  const n = t.steps.length;
  return (
    <li id={`thread-${t.id}`} className="card scroll-mt-16">
      <details className="group/thread">
        <summary className="flex cursor-pointer list-none flex-wrap items-baseline gap-x-3 gap-y-1 px-5 py-3.5 marker:content-none">
          <span aria-hidden="true" className="inline-block text-ink-400 transition-transform group-open/thread:rotate-90">
            ▸
          </span>
          <span className="text-[15px] font-semibold leading-snug text-ink-900">{t.title}</span>
          <span className="tabular text-[12px] text-ink-500">{n} findings</span>
          {range && (
            <span
              className="tabular text-[12px] text-ink-400"
              title="Years from the inventory, the dates on the leaves and the proposed datings of the folders in the thread"
            >
              {range}
            </span>
          )}
          {t.codicological && (
            <span className="text-[10px] uppercase tracking-wide text-ink-400">about the object</span>
          )}
        </summary>
        <div className="px-5 pb-5">
          <p className="max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">{t.intro}</p>
          <ol className="mt-4">
            {t.steps.map((s, i) => {
              const f = FIND.get(s.id);
              if (!f) return null;
              const last = i === t.steps.length - 1;
              const next = t.steps[i + 1]?.from;
              const dashed = next?.basis === 'edition';
              return (
                <li key={s.id} className="relative pl-7">
                  {/* The rail: solid where the next step rests on the page or the dates,
                      dashed where it rests on the edition's reading alone. */}
                  {!last && (
                    <span
                      aria-hidden="true"
                      className={`absolute bottom-0 left-[6px] top-3 w-0 border-l-2 ${
                        dashed ? 'border-dashed border-alerte-500/60' : 'border-ink-300'
                      }`}
                    />
                  )}
                  <span
                    aria-hidden="true"
                    title={STATUS_WORD[f.status]}
                    className={`absolute left-0 top-[7px] h-3.5 w-3.5 rounded-full ${STATUS_DOT[f.status]}`}
                  />
                  <p className="text-[13.5px] leading-snug">
                    <span className="mr-1.5 tabular text-[11px] font-bold text-ink-400">{i + 1}.</span>
                    <a
                      href={`#${f.id}`}
                      className="text-brand-700 underline decoration-brand-200 underline-offset-2 hover:decoration-brand-600"
                    >
                      {notation(shorten(f.claim, 130))}
                    </a>
                  </p>
                  <p className="mt-0.5 text-[11.5px] text-ink-500">
                    <span className="tabular">
                      n° {f.cote}, pp. {f.pages}
                    </span>
                    {BY_ID.get(f.cote)?.date && (
                      <span className="tabular"> · inv. {BY_ID.get(f.cote)?.date}</span>
                    )}{' '}
                    · {STATUS_WORD[f.status]}
                  </p>
                  {next && (
                    <div className="my-2.5 max-w-[44em] pb-2 text-[12.5px] leading-relaxed text-ink-600">
                      <BasisLabel basis={next.basis} where={next.where} />{' '}
                      <span>{next.sentence}</span>
                    </div>
                  )}
                  {last && <div className="pb-1" />}
                </li>
              );
            })}
          </ol>
        </div>
      </details>
    </li>
  );
}

export function ThreadsSection() {
  // A link to a thread (from a card's « See also », or pasted) opens it.
  useEffect(() => {
    const go = () => {
      const el = document.getElementById(decodeURIComponent(location.hash.slice(1)));
      if (!el?.id.startsWith('thread-')) return;
      el.querySelector('details')?.setAttribute('open', '');
      requestAnimationFrame(() => el.scrollIntoView({ block: 'start' }));
    };
    go();
    window.addEventListener('hashchange', go);
    return () => window.removeEventListener('hashchange', go);
  }, []);
  return (
    <section id="threads" className="mt-10 scroll-mt-16">
      <h2 className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
        Threads — {THREADS.length}
      </h2>
      <div className="mt-2 max-w-[44em] space-y-2 text-[14px] leading-relaxed text-ink-600">
        <p>
          A thread follows one object or one question across folders, step by step, in the
          order of the question. It is not a chronology: most leaves are undated, and
          nothing here says who did what first. Each step links to its finding card; between
          two steps, a sentence says what recurs and a label says what that rests on.
        </p>
        <p>
          A link records recurrence and continuation, never influence or priority. Those
          marked <BasisLabel basis="edition" /> (dashed in the frieze) rest on our reading
          alone; the others rest on a cross-reference in a modernised reading, on the same
          notation or pages, or on dates written on the leaves. Findings not in a thread may
          still carry typed links, shown in the « See also » line of their card.
        </p>
      </div>
      <ul className="mt-4 space-y-2">
        {THREADS.map((t) => (
          <ThreadBlock key={t.id} t={t} />
        ))}
      </ul>
    </section>
  );
}
