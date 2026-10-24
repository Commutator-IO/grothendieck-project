import { useState } from 'react';
import { FINDINGS } from '../content/findings.ts';
import type { Finding } from '../lib/types.ts';

/**
 * Where the mathematical findings stand, as two part-to-whole bars: every row
 * by outcome, then the open rows by what his own leaves do with them. Counts
 * are read from `FINDINGS` at render time, so the figure cannot drift from the
 * list below it. Colours are the six categorical slots of the fonds maps (the
 * people network's, checked there) and one brand ramp, light to dark, for the
 * ordinal second bar; every segment is also named in the legend and the table.
 */

interface Part {
  key: string;
  label: string;
  note: string;
  fill: string;
  rows: Finding[];
}

const math = () => FINDINGS.filter((n) => n.kind === 'mathematical');
const isOpen = (n: Finding) => !n.lean && (n.status === 'candidate' || n.status === 'unsearched');

function outcomeParts(): Part[] {
  const rows = math();
  const open = rows.filter(isOpen);
  const reach = (r: Finding['reach'] | 'other') =>
    open.filter((n) => (r === 'other' ? !n.reach || ['imprecise', 'doubtful', 'open-problem'].includes(n.reach) : n.reach === r));
  return [
    { key: 'lean', label: 'Proved in Lean', note: 'the statement holds as the reading gives it, or more generally, or is corrected by the proof', fill: '#128557', rows: rows.filter((n) => n.lean) },
    { key: 'matched', label: 'Found later in the literature', note: 'searched and found in print: kept as a killed candidate', fill: '#38539d', rows: rows.filter((n) => !n.lean && n.status === 'matched') },
    { key: 'refuted', label: 'Shown false as stated', note: 'a counterexample or a contradiction', fill: '#d55181', rows: rows.filter((n) => !n.lean && n.status === 'refuted') },
    { key: 'reachable', label: 'Open, within reach of Lean', note: 'mathlib has the theory the statement needs', fill: '#c9900c', rows: reach('reachable') },
    { key: 'beyond', label: 'Open, beyond mathlib today', note: 'needs a theory mathlib does not have (schemes, étale cohomology, topoi, stacks…): provable in principle, not now', fill: '#4a3aa7', rows: reach('beyond') },
    { key: 'other', label: 'Open, statement not settled', note: 'to be made precise, doubtful as read, or an open problem', fill: '#eb6834', rows: reach('other') },
  ];
}

function pageParts(): Part[] {
  const open = math().filter(isOpen);
  const by = (p: Finding['onPage']) => open.filter((n) => n.onPage === p);
  return [
    { key: 'proved', label: 'Proved on his leaves', note: 'a complete argument on the page', fill: '#283a68', rows: by('proved') },
    { key: 'partial', label: 'Partly proved by him', note: 'a sketch, an argument with gaps, or a special case', fill: '#4a6bbd', rows: by('partial') },
    { key: 'stated', label: 'Stated without proof', note: 'his conjecture or question', fill: '#97afe1', rows: by('stated') },
    { key: 'unread', label: 'Not yet judged', note: 'no reading of the page recorded for this row', fill: '#cbc5b5', rows: open.filter((n) => !n.onPage) },
  ].filter((p) => p.key !== 'unread' || p.rows.length > 0);
}

function Bar({ title, parts }: { title: string; parts: Part[] }) {
  const [hover, setHover] = useState<string | null>(null);
  const total = parts.reduce((s, p) => s + p.rows.length, 0);
  const pct = (k: number) => (total ? Math.round((100 * k) / total) : 0);
  const shown = parts.filter((p) => p.rows.length > 0);
  const active = shown.find((p) => p.key === hover);
  return (
    <figure className="mt-5">
      <figcaption className="text-[13px] font-semibold text-ink-800">
        {title} <span className="font-normal text-ink-500">({total})</span>
      </figcaption>
      <div className="relative mt-2">
        <div className="flex h-7 w-full gap-[2px]" role="img" aria-label={`${title}: ${shown.map((p) => `${p.label} ${p.rows.length}`).join(', ')}`}>
          {shown.map((p, i) => (
            <div
              key={p.key}
              onMouseEnter={() => setHover(p.key)}
              onMouseLeave={() => setHover(null)}
              onFocus={() => setHover(p.key)}
              onBlur={() => setHover(null)}
              tabIndex={0}
              style={{ flexGrow: p.rows.length, flexBasis: 0, background: p.fill, opacity: hover && hover !== p.key ? 0.45 : 1 }}
              className={`min-w-[3px] cursor-default outline-none ${i === 0 ? 'rounded-l-[4px]' : ''} ${i === shown.length - 1 ? 'rounded-r-[4px]' : ''}`}
            />
          ))}
        </div>
        {active && (
          <div className="pointer-events-none absolute left-0 top-9 z-10 max-w-[30em] rounded-md border border-ink-200 bg-white px-3 py-2 text-[12.5px] leading-snug text-ink-700 shadow-sm">
            <span className="font-semibold text-ink-900">{active.label}</span> — {active.rows.length} rows ({pct(active.rows.length)} %)
            <br />
            <span className="text-ink-500">{active.note}</span>
          </div>
        )}
      </div>
      <ul className="mt-3 grid gap-x-6 gap-y-1 text-[12.5px] text-ink-600 sm:grid-cols-2">
        {shown.map((p) => (
          <li key={p.key} className="flex items-baseline gap-2" onMouseEnter={() => setHover(p.key)} onMouseLeave={() => setHover(null)}>
            <span className="inline-block h-2.5 w-2.5 shrink-0 translate-y-[1px] rounded-[2px]" style={{ background: p.fill }} />
            <span>
              <span className="text-ink-800">{p.label}</span> · {p.rows.length} ({pct(p.rows.length)} %)
            </span>
          </li>
        ))}
      </ul>
    </figure>
  );
}

export function FindingsChart() {
  const outcome = outcomeParts();
  const onPage = pageParts();
  const beyond = outcome.find((p) => p.key === 'beyond')!.rows;
  const theories = new Map<string, number>();
  for (const n of beyond) theories.set(n.theory ?? 'unspecified', (theories.get(n.theory ?? 'unspecified') ?? 0) + 1);
  return (
    <section id="where-they-stand" className="mt-10 scroll-mt-16">
      <h2 className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">Where the mathematical findings stand</h2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        Each mathematical row counted once. « Beyond mathlib » is not « unprovable »: those statements
        need a theory the library does not yet have, and could be proved once it does. Whether a row
        is within reach, and what his leaves do with it, are the edition's judgements, made on the
        reading and the finding, not checked by a person.
      </p>
      <Bar title="All mathematical rows, by outcome" parts={outcome} />
      <Bar title="Open rows, by what his own leaves do" parts={onPage} />
      <details className="mt-4 text-[12.5px] text-ink-600">
        <summary className="cursor-pointer text-ink-500 hover:text-brand-700">The figures as a table</summary>
        <table className="mt-2 w-full max-w-[40em] border-collapse">
          <tbody>
            {[...outcome, ...onPage].map((p) => (
              <tr key={`${p.key}`} className="border-t border-ink-100">
                <td className="py-1 pr-3 text-ink-800">{p.label}</td>
                <td className="py-1 pr-3 text-right tabular-nums">{p.rows.length}</td>
                <td className="py-1 text-ink-500">{p.note}</td>
              </tr>
            ))}
            {[...theories].sort((a, b) => b[1] - a[1]).map(([t, k]) => (
              <tr key={t} className="border-t border-ink-100">
                <td className="py-1 pr-3 pl-4 text-ink-700">beyond mathlib: {t}</td>
                <td className="py-1 pr-3 text-right tabular-nums">{k}</td>
                <td />
              </tr>
            ))}
          </tbody>
        </table>
      </details>
    </section>
  );
}
