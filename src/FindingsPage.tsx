import { Footer, Header } from './components/Frame.tsx';
import { FINDINGS } from './content/findings.ts';
import { BY_ID } from './content/catalogue.ts';
import type { Finding } from './lib/types.ts';

/**
 * What the readings turned up that the inventory does not record.
 *
 * The page is a list of claims with a status attached, and the status is the
 * point. A page of findings without one would be a page of assertions, and
 * assertions about what other mathematicians did not do are the one thing this
 * project is in no position to make: the literature can be searched but never
 * exhausted, and almost nothing in the fonds is dated, so precedence is not
 * available to us about anyone.
 *
 * Hence two decisions that shape the layout. The status is a badge on every
 * row, never a footnote — a reader must not be able to take a candidate for a
 * result by skimming. And `matched` rows, the ones that turned out to be in
 * the books, stay on the page under their own heading rather than being
 * deleted: they are the evidence the list is pruned rather than grown, and
 * they save the next reader the search.
 */

const STATUS: Record<
  Finding['status'],
  { label: string; help: string; className: string }
> = {
  unsearched: {
    label: 'not looked up',
    help: 'Nobody has searched the literature for this yet. It is a question, not a finding.',
    className: 'bg-ink-100 text-ink-600',
  },
  candidate: {
    label: 'candidate',
    help: 'Searched in the sources listed and not found there. Still provisional: the literature can never be exhausted.',
    className: 'bg-brand-100 text-brand-700',
  },
  matched: {
    label: 'in the literature',
    help: 'Looked up and found. Kept on the page so nobody searches for it twice.',
    className: 'bg-ink-100 text-ink-500',
  },
  confirmed: {
    label: 'checked by a person',
    help: 'A human reader has verified this. No machine pass may set this status.',
    className: 'bg-emerald-100 text-emerald-800',
  },
};

const KIND: Record<Finding['kind'], string> = {
  mathematical: 'about the literature',
  codicological: 'about the object',
};

function Row({ n }: { n: Finding }) {
  const s = STATUS[n.status];
  const cote = BY_ID.get(n.cote);
  return (
    <li className="card p-5">
      <div className="flex flex-wrap items-baseline gap-x-3 gap-y-1.5">
        <span className="tabular text-[12.5px] font-semibold text-ink-800">
          Cote n° {n.cote}
        </span>
        <span className="tabular text-[12.5px] text-ink-500">pages {n.pages}</span>
        <span
          title={s.help}
          className={`rounded-full px-2 py-0.5 text-[10px] font-bold uppercase tracking-wide ${s.className}`}
        >
          {s.label}
        </span>
        <span className="text-[10px] uppercase tracking-wide text-ink-400">{KIND[n.kind]}</span>
      </div>

      <p className="mt-2.5 text-[15px] leading-relaxed text-ink-900">{n.claim}</p>

      <dl className="mt-3 grid gap-2 text-[13px] leading-relaxed sm:grid-cols-[8.5rem_1fr]">
        <dt className="text-ink-400">What it rests on</dt>
        <dd className="text-ink-700">{n.basis}</dd>

        {/* Printed even when null. A reader has to be able to tell "the page
            carries this alone" from "nobody said", and an absent row says the
            second while meaning the first. */}
        <dt className="text-ink-400">Ours, not his</dt>
        <dd className={n.ours ? 'text-ink-700' : 'text-ink-400'}>
          {n.ours ?? 'Nothing — the page carries the statement alone.'}
        </dd>

        <dt className="text-ink-400">Searched</dt>
        <dd className={n.literature.length ? 'text-ink-700' : 'text-ink-400'}>
          {n.literature.length ? (
            <ul className="space-y-0.5">
              {n.literature.map((l) => (
                <li key={l}>{l}</li>
              ))}
            </ul>
          ) : (
            'Nothing yet.'
          )}
        </dd>

        <dt className="text-ink-400">What would settle it</dt>
        <dd className="text-ink-700">{n.settle}</dd>
      </dl>

      {cote && (
        <p className="mt-3 text-[12px] text-ink-400">
          {cote.title} · {cote.date}
        </p>
      )}
    </li>
  );
}

export function FindingsPage() {
  const open = FINDINGS.filter((n) => n.status !== 'matched');
  const closed = FINDINGS.filter((n) => n.status === 'matched');

  return (
    <>
      <Header path="/findings/" />

      <main className="mx-auto max-w-4xl px-5 py-12">
        <header className="max-w-[46em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.14em] text-ink-400">
            Findings from the readings
          </p>
          <h1 className="titre mt-2 text-[30px] leading-tight text-ink-900">
            What these folders hold that the inventory does not say
          </h1>
          <p className="mt-4 text-[15px] leading-relaxed text-ink-600">
            Reading a folder end to end turns things up: a leaf bound backwards, two
            manuscripts interleaved, a theorem proved under a hypothesis weaker than the
            one in the books. This page lists them, and lists what each one still needs
            before anyone should believe it.
          </p>
          <p className="mt-3 text-[15px] leading-relaxed text-ink-600">
            Nothing here claims priority. A claim that something is <em>new</em> is a
            claim about the literature, and the literature can be searched but never
            exhausted; a claim that something came <em>first</em> needs a date, and these
            folders are undated — the inventory's «&nbsp;vers 1963-1973&nbsp;» is an
            archivist's guess from a verso. So each row says what was searched, what the
            edition supplied rather than the page, and what would settle it.
          </p>
        </header>

        <section className="mt-10">
          <h2 className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
            Open — {open.length}
          </h2>
          <ul className="mt-3 space-y-3">
            {open.map((n) => (
              <Row key={n.id} n={n} />
            ))}
          </ul>
        </section>

        {closed.length > 0 && (
          <section className="mt-10">
            <h2 className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
              Looked up and found — {closed.length}
            </h2>
            <p className="mt-2 max-w-[46em] text-[13.5px] leading-relaxed text-ink-500">
              Candidates that turned out to be in the literature. They stay here on
              purpose: a killed candidate saves the next reader the search, and a list
              that only ever grows is not being checked.
            </p>
            <ul className="mt-3 space-y-3">
              {closed.map((n) => (
                <Row key={n.id} n={n} />
              ))}
            </ul>
          </section>
        )}

        <section className="mt-12 max-w-[46em] text-[13.5px] leading-relaxed text-ink-500">
          <h2 className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
            How this list is made
          </h2>
          <p className="mt-2">
            By <code className="rounded bg-ink-100 px-1 py-0.5 text-[12px]">/find-novelty</code>,
            a skill that reads a folder's transcriptions and its modernised reading and
            proposes candidates — never the facsimile, which is the transcription's job.
            It is written around refusing to overclaim: it may not assert priority, it
            must name the sources it searched, and it must separate what the page carries
            from what the edition supplied. It may not mark anything{' '}
            <em>checked by a person</em>; only a person may.
          </p>
          <p className="mt-2">
            None of these has been reviewed by a mathematician. If one of them is wrong —
            and the mathematical ones are the likeliest things on this site to be wrong —
            the fastest way to say so is an issue against the folder.
          </p>
        </section>
      </main>

      <Footer />
    </>
  );
}
