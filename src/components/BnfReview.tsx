import { useState } from 'react';
import BNF from '../content/review-bnf.json';

/**
 * The questions for the BnF visit (#37), box by box, apart from the
 * Montpellier checks of #35: no facsimile online, no transcription, only
 * what a box shows. Answers stay in this browser until copied or sent.
 */

type Mark = 'yes' | 'no' | 'partly' | 'unseen';
interface Ans {
  mark?: Mark;
  where?: string;
  note?: string;
}
type Store = Record<string, Ans>;

const KEY = 'gn-review:bnf-37';
const REPO = 'https://github.com/Commutator-IO/grothendieck-project';
const SITE = 'https://grothendieck.commutator.io';
const MARKS: [Mark, string][] = [
  ['yes', 'Yes'],
  ['partly', 'Partly'],
  ['no', 'No'],
  ['unseen', 'Not reached'],
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

type Box = (typeof BNF.boxes)[number];
// Boxes whose review is finished carry `done` (the date) and leave the tab; « Copy all answers »
// still exports what was entered for them.
const BOXES: Box[] = BNF.boxes.filter((b) => !('done' in b));
const plain = (s: string) => s.replace(/«\s*/g, '"').replace(/\s*»/g, '"');
const one = (s?: string) => (s ?? '').trim().replace(/\s*\n\s*/g, ' ');

function boxMarkdown(b: Box, s: Store): string {
  const out = [`### Box (${b.box}) — ${plain(b.title)}`, `Question: ${plain(b.question)}`, ''];
  for (const it of b.items) {
    const a = s[it.id];
    if (!a?.mark && !one(a?.where) && !one(a?.note)) continue;
    const name = MARKS.find(([m]) => m === a.mark)?.[1] ?? 'No answer';
    let l = `- **${name}** — ${plain(it.text)}`;
    if (one(a.where)) l += ` (ff. ${one(a.where)})`;
    if (one(a.note)) l += `: ${one(a.note)}`;
    out.push(l);
  }
  for (const g of BNF.grid) {
    const v = one(s[`${b.id}:${g.id}`]?.note);
    if (v) out.push(`- ${g.label}: ${v}`);
  }
  return out.join('\n');
}

function allMarkdown(s: Store): string {
  const parts = [`Answers from the BnF visit page (${SITE}/review/#bnf), NAF 29093, for #37.`, ''];
  for (const b of BNF.boxes) if (answeredIn(b, s)) parts.push(boxMarkdown(b, s), '');
  const dens = BNF.density.map((d) => [d.label, one(s[d.id]?.note)]).filter(([, v]) => v);
  if (dens.length) parts.push('### Density of the writing', ...dens.map(([k, v]) => `- ${k}: ${v}`), '');
  return parts.join('\n');
}

const answeredIn = (b: Box, s: Store) =>
  b.items.some((it) => s[it.id]?.mark || one(s[it.id]?.note)) || BNF.grid.some((g) => one(s[`${b.id}:${g.id}`]?.note));

export function BnfReview() {
  const [s, setS] = useState<Store>(load);
  const [boxId, setBoxId] = useState<string>(() => {
    const h = decodeURIComponent(location.hash.slice(1));
    return BOXES.find((b) => h === `bnf-${b.id}`)?.id ?? BOXES[0].id;
  });
  const [copied, setCopied] = useState(false);
  const box = BOXES.find((b) => b.id === boxId) ?? BOXES[0];

  const set = (id: string, patch: Partial<Ans>) => {
    const next = { ...s, [id]: { ...s[id], ...patch } };
    setS(next);
    save(next);
  };
  const pick = (id: string) => {
    setBoxId(id);
    history.replaceState(null, '', `#bnf-${id}`);
  };
  const done = (b: Box) => b.items.filter((it) => s[it.id]?.mark).length;
  const copy = async () => {
    try {
      await navigator.clipboard.writeText(allMarkdown(s));
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    } catch {
      /* no clipboard permission */
    }
  };
  const issueUrl = (b: Box) => {
    const title = `[BnF #37] Box (${b.box}): ${b.title}`;
    const body = `Answers from ${SITE}/review/#bnf-${b.id}, for #37. They describe the box; nothing is quoted.\n\n${boxMarkdown(b, s)}`;
    return `${REPO}/issues/new?title=${encodeURIComponent(title)}&body=${encodeURIComponent(body.slice(0, 7000))}`;
  };
  const btn = (on: boolean) =>
    `rounded-md border px-2.5 py-1 text-[12.5px] font-medium transition ${
      on ? 'border-brand-700 bg-brand-700 text-white' : 'border-ink-300 bg-white text-ink-800 hover:border-brand-500'
    }`;

  return (
    <div className="mt-6">
      <p className="max-w-[48em] text-[14px] leading-relaxed text-ink-700">
        The questions of the visit sheet (
        <a className="text-brand-700 underline" href={`${REPO}/blob/main/docs/bnf/fiche.pdf`}>
          docs/bnf/fiche.pdf
        </a>
        ), one box at a time, in the order the boxes are asked for. For each, say whether the box shows it, and give the
        leaves if you can. Notes describe what you see; copy nothing out. Answers stay in this browser.
      </p>

      <details className="mt-4 rounded-md border border-ink-200 bg-white px-3 py-2 text-[13px] text-ink-700" open>
        <summary className="cursor-pointer font-semibold text-ink-900">Sessions to come, by pochette</summary>
        <ol className="mt-2 grid gap-1">
          {BNF.sessions.map((se) => (
            <li key={se.n}>
              <span className="font-semibold">Session {se.n}</span> · {se.theme}: {se.ask.join(' · ')}
            </li>
          ))}
        </ol>
        <p className="mt-1 text-[12px] text-ink-500">
          If only whole boxes can be served, ask for them in this order and go straight to the pochettes named.
        </p>
      </details>

      <div role="tablist" aria-label="Boxes" className="mt-4 flex flex-wrap gap-1.5">
        {BOXES.map((b) => (
          <button
            key={b.id}
            role="tab"
            type="button"
            aria-selected={b.id === box.id}
            onClick={() => pick(b.id)}
            className={`rounded-md border px-2.5 py-1 text-[13px] ${
              b.id === box.id
                ? 'border-brand-700 bg-brand-50 font-semibold text-brand-800'
                : 'border-ink-200 bg-white text-ink-700'
            }`}
          >
            ({b.box}){' '}
            <span className="text-ink-400">
              {done(b)}/{b.items.length}
            </span>
          </button>
        ))}
        <button
          role="tab"
          type="button"
          aria-selected={boxId === 'density'}
          onClick={() => pick('density')}
          className={`rounded-md border px-2.5 py-1 text-[13px] ${
            boxId === 'density'
              ? 'border-brand-700 bg-brand-50 font-semibold text-brand-800'
              : 'border-ink-200 bg-white text-ink-700'
          }`}
        >
          Density
        </button>
      </div>

      {boxId === 'density' ? (
        <section className="mt-4 rounded-xl border border-ink-200 bg-white p-4 sm:p-5">
          <h2 className="text-[17px] font-semibold text-ink-900">Density of the writing</h2>
          <p className="mt-1 text-[13px] text-ink-600">
            The timeline assumes 250 words a page for these fair copies, against 140 for the Montpellier notes. Count
            one full page of each.
          </p>
          <div className="mt-3 grid gap-3">
            {BNF.density.map((d) => (
              <label
                key={d.id}
                className="grid gap-1 text-[13px] text-ink-700 sm:grid-cols-[minmax(0,1fr)_8rem] sm:items-center"
              >
                {d.label}
                <input
                  inputMode="numeric"
                  value={s[d.id]?.note ?? ''}
                  onChange={(e) => set(d.id, { note: e.target.value })}
                  className="rounded-md border border-ink-300 px-2 py-1.5 text-[14px]"
                />
              </label>
            ))}
          </div>
        </section>
      ) : (
        <section className="mt-4 rounded-xl border border-ink-200 bg-white p-4 sm:p-5">
          <p className="text-[11.5px] font-semibold uppercase tracking-wider text-ink-400">
            NAF 29093 ({box.box}){box.folios ? ` · ${box.folios} leaves` : ''}
          </p>
          <h2 className="mt-1 text-[18px] font-semibold leading-snug text-ink-900">{box.title}</h2>
          <p className="mt-2 text-[14px] leading-relaxed text-ink-800">{box.question}</p>
          {box.seen && <p className="mt-1 text-[12.5px] text-ink-500">{box.seen}</p>}
          <ul className="mt-3 grid gap-1 rounded-md bg-ink-50 px-3 py-2 text-[12.5px] text-ink-700">
            {box.pochettes.map((pc) => (
              <li key={pc.n}>
                <span className="font-semibold text-ink-900">Pochette {pc.n}</span>: {pc.label}
              </li>
            ))}
            <li>
              <a className="text-brand-700 underline" href={box.notice} target="_blank" rel="noopener">
                BnF notice of box ({box.box}) ↗
              </a>
            </li>
          </ul>

          <ol className="mt-4 grid gap-3">
            {box.items.map((it, n) => {
              const a = s[it.id] ?? {};
              return (
                <li key={it.id} className="rounded-lg border border-ink-100 p-3">
                  <p className="text-[14px] text-ink-900">
                    <span className="mr-1 text-ink-400">{n + 1}.</span>
                    {it.text}
                  </p>
                  {'at' in it && it.at && <p className="mt-0.5 text-[12px] text-ink-500">Where: {it.at}</p>}
                  <div className="mt-2 flex flex-wrap items-center gap-1.5">
                    {MARKS.map(([m, label]) => (
                      <button
                        key={m}
                        type="button"
                        className={btn(a.mark === m)}
                        onClick={() => set(it.id, { mark: a.mark === m ? undefined : m })}
                      >
                        {label}
                      </button>
                    ))}
                    <input
                      aria-label="Leaves"
                      placeholder="ff."
                      value={a.where ?? ''}
                      onChange={(e) => set(it.id, { where: e.target.value })}
                      className="ml-1 w-24 rounded-md border border-ink-300 px-2 py-1 text-[13px]"
                    />
                  </div>
                  <input
                    aria-label="Note"
                    placeholder="What the box shows (optional)"
                    value={a.note ?? ''}
                    onChange={(e) => set(it.id, { note: e.target.value })}
                    className="mt-2 w-full rounded-md border border-ink-300 px-2 py-1.5 text-[13px]"
                  />
                </li>
              );
            })}
          </ol>

          <h3 className="mt-5 text-[13px] font-semibold text-ink-900">The box as a whole</h3>
          <div className="mt-2 grid gap-2 sm:grid-cols-2">
            {BNF.grid.map((g) => (
              <label key={g.id} className="grid gap-1 text-[12.5px] text-ink-600">
                {g.label}
                <input
                  value={s[`${box.id}:${g.id}`]?.note ?? ''}
                  onChange={(e) => set(`${box.id}:${g.id}`, { note: e.target.value })}
                  className="rounded-md border border-ink-300 px-2 py-1.5 text-[13px] text-ink-900"
                />
              </label>
            ))}
          </div>

          <p className="mt-4 flex flex-wrap gap-3 text-[13px]">
            <a
              className={`text-brand-700 underline ${answeredIn(box, s) ? '' : 'pointer-events-none opacity-40'}`}
              href={issueUrl(box)}
              target="_blank"
              rel="noopener"
            >
              Send box ({box.box}) as a GitHub issue ↗
            </a>
          </p>
        </section>
      )}

      <div className="mt-6 flex flex-wrap gap-2">
        <button
          type="button"
          onClick={copy}
          className="rounded-md bg-brand-700 px-3 py-1.5 text-[13px] font-semibold text-white"
        >
          {copied ? 'Copied' : 'Copy all answers as Markdown'}
        </button>
        <button
          type="button"
          onClick={() => {
            if (!confirm('Forget all your BnF answers in this browser?')) return;
            setS({});
            save({});
          }}
          className="rounded-md px-3 py-1.5 text-[13px] text-ink-500 hover:bg-ink-50"
        >
          Clear
        </button>
      </div>
      <p className="mt-2 text-[12.5px] text-ink-500">
        The Markdown can go straight to Claude or into an issue. A GitHub issue is public: keep notes to what a box
        contains.
      </p>
    </div>
  );
}
