import { useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import { BY_ID } from './content/catalogue.ts';
import lettersRaw from './content/letters.json';

/**
 * The correspondence the folders hold, as a register.
 *
 * Not the letters: a line per letter — who, when, where it is in the fonds,
 * how the transcription gives it — so a reader can find one without the site
 * circulating what it should not. Third-party letters may not be circulated
 * without permission, and those already in print stay condensed; the register
 * says which is which rather than deciding it again here.
 */

interface Letter {
  folder: string;
  batch: number;
  pages: string;
  date: string | null;
  iso: string | null;
  dating: 'written' | 'inferred' | 'none';
  direction: 'from' | 'to' | 'other';
  correspondent: string | null;
  correspondentNote: string | null;
  place: string | null;
  form: string;
  language: string;
  treatment: 'full' | 'summarised' | 'named';
  summary: string;
  where: string;
}
const RAW = (lettersRaw as unknown as { built: string; records: Letter[] });
const RECORDS = RAW.records;

// One letter to three people is three records; the counts of letters use the
// physical letter, keyed by where it sits.
const letterKey = (l: Letter) => `${l.folder}#${l.pages}`;
const LETTERS = [...new Map(RECORDS.map((l) => [letterKey(l), l])).values()];

const DIR: Record<Letter['direction'], { label: string; colour: string }> = {
  from: { label: 'from him', colour: '#38539d' },
  to: { label: 'to him', colour: '#c9900c' },
  other: { label: 'between others, or unclear', colour: 'var(--color-ink-300)' },
};
const TREAT: Record<Letter['treatment'], string> = {
  full: 'transcribed',
  summarised: 'summarised',
  named: 'named only',
};
const LANG: Record<string, string> = { fr: 'French', en: 'English', de: 'German' };
const who = (l: Letter) => l.correspondent ?? l.correspondentNote ?? 'unidentified';
const shortTitle = (id: string) =>
  (BY_ID.get(id)?.title ?? '').replace(/\s*:\s*notes manuscrites.*$/i, '').replace(/\s*:.*$/, '');

function H2({ id, children }: { id: string; children: React.ReactNode }) {
  return (
    <h2 id={id} className="scroll-mt-16 text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
      {children}
    </h2>
  );
}

function Kpi({ value, label, help }: { value: string | number; label: string; help?: string }) {
  return (
    <div className="card px-4 py-3">
      <p className="tabular text-[24px] font-semibold leading-tight text-ink-900">{value}</p>
      <p className="mt-0.5 text-[12.5px] text-ink-600">{label}</p>
      {help && <p className="mt-1 text-[11.5px] leading-snug text-ink-400">{help}</p>}
    </div>
  );
}

function Legend() {
  return (
    <ul className="mt-3 flex flex-wrap items-center gap-x-5 gap-y-1 text-[12px] text-ink-500">
      {(Object.keys(DIR) as Letter['direction'][]).map((d) => (
        <li key={d} className="flex items-center gap-1.5">
          <span className="inline-block h-2.5 w-2.5 rounded-sm" style={{ background: DIR[d].colour }} /> {DIR[d].label}
        </li>
      ))}
    </ul>
  );
}

/** Letters per year, stacked by direction, over the years the register spans. */
function ByYear() {
  const dated = RECORDS.filter((l) => l.iso);
  const ys = dated.map((l) => Number((l.iso as string).slice(0, 4)));
  const y0 = Math.min(...ys) - 1;
  const y1 = Math.max(...ys) + 1;
  const years = Array.from({ length: y1 - y0 + 1 }, (_, i) => y0 + i);
  const stack = years.map((y) => {
    const here = LETTERS.filter((l) => l.iso && Number(l.iso.slice(0, 4)) === y);
    return (Object.keys(DIR) as Letter['direction'][]).map((d) => ({ d, n: here.filter((l) => l.direction === d).length }));
  });
  const max = Math.max(1, ...stack.map((s) => s.reduce((a, b) => a + b.n, 0)));
  const W = 900;
  const H = 200;
  const L = 30;
  const B = 26;
  const bw = (W - L - 10) / years.length;
  const y = (v: number) => ((H - B - 10) * v) / max;
  const [sel, setSel] = useState<number | null>(null);
  const undated = LETTERS.filter((l) => !l.iso).length;

  return (
    <section className="mt-12">
      <H2 id="by-year">Letters by year</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        Each letter counted once, by the year written on it (or, for one, by the transcriber's
        dating). {undated} letters carry no date and are not drawn.
      </p>
      <Legend />
      <div className="mt-2 overflow-x-auto" onMouseLeave={() => setSel(null)}>
        <svg viewBox={`0 0 ${W} ${H}`} className="w-full min-w-[560px] rounded-[var(--radius-card)] border border-ink-200 bg-white" role="img" aria-label="Letters per year by direction">
          {Array.from({ length: max + 1 }, (_, i) => i).filter((i) => i % Math.max(1, Math.ceil(max / 4)) === 0).map((i) => (
            <g key={i}>
              <line x1={L} x2={W - 10} y1={H - B - y(i)} y2={H - B - y(i)} stroke="var(--color-ink-200)" />
              <text x={L - 6} y={H - B - y(i) + 4} textAnchor="end" className="tabular" style={{ fontSize: 11, fill: 'var(--color-ink-400)' }}>
                {i}
              </text>
            </g>
          ))}
          {stack.map((s, i) => {
            let acc = 0;
            return (
              <g key={years[i]} onMouseEnter={() => setSel(years[i])} opacity={sel === null || sel === years[i] ? 1 : 0.35}>
                <rect x={L + i * bw} y={0} width={bw} height={H - B} fill="#fff" fillOpacity={0} />
                {s.map(({ d, n }) => {
                  if (!n) return null;
                  const h = y(n);
                  const r = <rect key={d} x={L + i * bw + 2} y={H - B - acc - h} width={bw - 4} height={Math.max(0, h - 2)} rx={2} fill={DIR[d].colour} />;
                  acc += h;
                  return r;
                })}
                {(years[i] % 5 === 0 || years.length < 16) && (
                  <text x={L + i * bw + bw / 2} y={H - 8} textAnchor="middle" className="tabular" style={{ fontSize: 11, fill: 'var(--color-ink-400)' }}>
                    {years[i]}
                  </text>
                )}
              </g>
            );
          })}
        </svg>
      </div>
      <div className="mt-2 min-h-[3em] text-[12.5px] leading-relaxed text-ink-600">
        {sel !== null ? (
          <ul>
            {LETTERS.filter((l) => l.iso?.startsWith(String(sel))).map((l) => (
              <li key={letterKey(l)}>
                <span className="tabular text-ink-900">{l.date}</span> · {DIR[l.direction].label}
                {l.direction !== 'other' && `, ${l.direction === 'from' ? 'to' : 'from'} ${who(l)}`} ·{' '}
                <a href={`/archive/#${l.folder}/${l.batch}`} className="tabular font-semibold text-ink-900 hover:text-brand-700">
                  n° {l.folder}
                </a>
              </li>
            ))}
            {!LETTERS.some((l) => l.iso?.startsWith(String(sel))) && <li className="text-ink-400">{sel}: none.</li>}
          </ul>
        ) : (
          <p className="text-ink-400">Hover a year for its letters.</p>
        )}
      </div>
    </section>
  );
}

/** Correspondents, each a bar split by direction. */
function Correspondents({ onPick, picked }: { onPick: (c: string | null) => void; picked: string | null }) {
  const rows = useMemo(() => {
    const m = new Map<string, Record<Letter['direction'], number>>();
    for (const l of RECORDS) {
      const k = l.correspondent ?? 'Not named here';
      const e = m.get(k) ?? { from: 0, to: 0, other: 0 };
      e[l.direction]++;
      m.set(k, e);
    }
    return [...m]
      .map(([name, c]) => ({ name, c, n: c.from + c.to + c.other }))
      .sort((a, b) => (a.name === 'Not named here' ? 1 : 0) - (b.name === 'Not named here' ? 1 : 0) || b.n - a.n || a.name.localeCompare(b.name));
  }, []);
  const max = Math.max(...rows.map((r) => r.n));
  return (
    <section className="mt-12">
      <H2 id="correspondents">Correspondents</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        A letter to three people counts for each. People who are not public figures are not named:
        they are counted together at the foot. Choose a name to filter the register below.
      </p>
      <Legend />
      <ul className="mt-3 grid gap-x-8 gap-y-1 text-[12.5px] sm:grid-cols-2">
        {rows.map((r) => (
          <li key={r.name}>
            <button
              type="button"
              onClick={() => onPick(picked === r.name ? null : r.name)}
              aria-pressed={picked === r.name}
              className={`flex w-full items-center gap-2 rounded px-1 py-0.5 text-left ${picked === r.name ? 'bg-ink-100' : 'hover:bg-ink-50'}`}
            >
              <span className={`w-40 shrink-0 truncate ${r.name === 'Not named here' ? 'italic text-ink-500' : 'text-ink-900'}`}>{r.name}</span>
              <span className="flex h-2.5 flex-1 gap-px">
                {(Object.keys(DIR) as Letter['direction'][]).map((d) =>
                  r.c[d] ? <span key={d} className="h-2.5 rounded-sm" style={{ width: `${(100 * r.c[d]) / max}%`, background: DIR[d].colour }} /> : null,
                )}
              </span>
              <span className="tabular w-6 shrink-0 text-right text-ink-500">{r.n}</span>
            </button>
          </li>
        ))}
      </ul>
    </section>
  );
}

function Register({ picked }: { picked: string | null }) {
  const rows = picked
    ? RECORDS.filter((l) => (l.correspondent ?? 'Not named here') === picked)
    : LETTERS;
  return (
    <section className="mt-12">
      <H2 id="register">The register</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        {picked ? (
          <>
            {rows.length} {rows.length === 1 ? 'letter' : 'letters'} with {picked}.{' '}
          </>
        ) : (
          <>Every letter once, in shelfmark order. </>
        )}
        The date is as the letter writes it; « how given » says whether the transcription gives its
        text, a summary, or only notes that it is there.
      </p>
      <div className="mt-3 overflow-x-auto rounded-[var(--radius-card)] border border-ink-200 bg-white">
        <table className="w-full min-w-[760px] text-[12.5px]">
          <thead className="text-left text-[11px] uppercase tracking-wide text-ink-400">
            <tr className="border-b border-ink-200">
              <th className="px-3 py-2 font-semibold">Where</th>
              <th className="px-2 py-2 font-semibold">Date</th>
              <th className="px-2 py-2 font-semibold">Who</th>
              <th className="px-2 py-2 font-semibold">How given</th>
              <th className="px-2 py-2 font-semibold">What</th>
            </tr>
          </thead>
          <tbody>
            {rows.map((l, i) => {
              const others = RECORDS.filter((r) => letterKey(r) === letterKey(l)).map(who);
              return (
                <tr key={i} className="border-b border-ink-100 align-top last:border-0">
                  <td className="whitespace-nowrap px-3 py-2">
                    <a href={`/archive/#${l.folder}/${l.batch}`} className="tabular font-semibold text-ink-900 hover:text-brand-700" title={BY_ID.get(l.folder)?.title}>
                      n° {l.folder}
                    </a>
                    <span className="tabular text-ink-400"> p. {l.pages}</span>
                    <br />
                    <span className="text-[11.5px] text-ink-400">{shortTitle(l.folder).slice(0, 24)}</span>
                  </td>
                  <td className="px-2 py-2 text-ink-700">
                    {l.date ?? <span className="text-ink-400">{l.dating === 'inferred' ? `[${l.iso}]` : 's.d.'}</span>}
                  </td>
                  <td className="px-2 py-2 text-ink-700">
                    <span className="inline-block h-2 w-2 rounded-sm align-middle" style={{ background: DIR[l.direction].colour }} />{' '}
                    {l.direction === 'from' ? 'to ' : l.direction === 'to' ? 'from ' : ''}
                    {(picked ? [who(l)] : others).join(', ')}
                  </td>
                  <td className="whitespace-nowrap px-2 py-2 text-ink-500">
                    {TREAT[l.treatment]}
                    <br />
                    <span className="text-[11.5px] text-ink-400">
                      {l.form}, {LANG[l.language] ?? l.language}
                    </span>
                  </td>
                  <td className="px-2 py-2 text-ink-600">{l.summary}</td>
                </tr>
              );
            })}
          </tbody>
        </table>
      </div>
    </section>
  );
}

export function LettersPage() {
  const [picked, setPicked] = useState<string | null>(null);
  const named = new Set(RECORDS.map((l) => l.correspondent).filter(Boolean)).size;
  const dated = LETTERS.filter((l) => l.dating === 'written').length;
  const from = LETTERS.filter((l) => l.direction === 'from').length;
  const to = LETTERS.filter((l) => l.direction === 'to').length;
  const ys = LETTERS.filter((l) => l.iso).map((l) => Number((l.iso as string).slice(0, 4)));

  return (
    <>
      <Header path="/letters/" />

      <main className="mx-auto max-w-5xl px-5 py-12">
        <header className="max-w-[44em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.14em] text-ink-400">Letters</p>
          <h1 className="titre mt-2 text-[30px] leading-tight text-ink-900">
            The correspondence in the folders
          </h1>
          <p className="mt-4 text-[15.5px] leading-relaxed text-ink-600">
            The fonds is working notes, not a correspondence, but letters turn up in it: carbons of
            his, answers filed with the mathematics they answer, drafts broken off. This is a register
            of those the transcriptions have found so far — where each one is, when, with whom, and
            how the site gives it.
          </p>
        </header>

        <div className="mt-6 max-w-[44em] rounded-[var(--radius-card)] border border-encours-200 bg-encours-50 px-4 py-3 text-[13px] leading-relaxed text-ink-700">
          <strong className="font-semibold">A register, not the letters.</strong> Letters from others
          may not be circulated without permission, and those already published — the
          Grothendieck–Serre correspondence — stay condensed. People who are not public figures are
          not named. The count grows only as folders are read: {ys.length ? `${Math.min(...ys)}–${Math.max(...ys)}` : ''} is
          the span found so far, not the span of his correspondence.
        </div>

        <div className="mt-6 grid grid-cols-2 gap-3 sm:grid-cols-4">
          <Kpi value={LETTERS.length} label="letters found" help={`in ${new Set(LETTERS.map((l) => l.folder)).size} folders`} />
          <Kpi value={dated} label="dated on the letter" />
          <Kpi value={`${from} · ${to}`} label="from him · to him" help={`${LETTERS.length - from - to} between others or unclear`} />
          <Kpi value={named} label="named correspondents" />
        </div>

        <ByYear />
        <Correspondents onPick={setPicked} picked={picked} />
        <Register picked={picked} />

        <p className="mt-12 max-w-[44em] text-[12px] leading-relaxed text-ink-400">
          src/content/letters.json, built on {RAW.built} by reading the transcriptions' headers and
          pages; every record carries the file and line it rests on. Letters only referred to — « ma
          lettre à Verdier » — are left out unless the folder holds them.
        </p>
      </main>

      <Footer />
    </>
  );
}
