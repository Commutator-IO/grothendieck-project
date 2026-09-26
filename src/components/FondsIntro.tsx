import { EDITED_COTES, TOTAL_PAGES, UNEDITED } from '../content/books.ts';
import { COTES } from '../content/catalogue.ts';
import { availableFor, batchCount } from '../lib/batches.ts';
import type { Manifest } from '../lib/types.ts';

/**
 * What this fonds is, who made the documents, and where the work stands —
 * the opening of the site's front page, which is the whole fonds.
 *
 * It used to open a front page of its own that led to the notebooks; the
 * site now reads the whole fonds, so the introduction stands above the
 * inventory it introduces, and the notebooks have a page of their own.
 */
export function FondsIntro({ manifest }: { manifest: Manifest | null }) {

  /**
   * What exists, counted from the manifest rather than declared.
   *
   * The front page should not have to be edited when a batch is finished, and
   * a figure kept by hand is a figure that goes stale. These come from the
   * files on the deployed site, so they are true by construction — and when
   * they are zero, the honest thing is what the page then says.
   */
  // `availableFor`, not `transcript`: the modernised reading is one file for
  // the whole folder, so it appears in the folder's own row rather than in any
  // batch's. Counting batch rows alone reported zero modernised batches while
  // three folders had been read end to end.
  //
  // Counted over UNEDITED, not over the whole fonds: 24 folders are already
  // transcribed by mathematicians, and re-doing them would be waste rather
  // than progress, so they are not work outstanding and do not belong in the
  // denominator. What that costs in honesty is paid back below, where the
  // figure against all 884 batches is given beside it.
  const batches = UNEDITED.flatMap((c) =>
    Array.from({ length: batchCount(c.pages) }, (_, i) => availableFor(manifest, c.id, i + 1)),
  );
  const done = {
    total: batches.length,
    transcribed: batches.filter((b) => b.html.includes('fr')).length,
    modernised: batches.filter((b) => b.html.includes('modern')).length,
  };
  const setAside = {
    folders: EDITED_COTES.length,
    pages: EDITED_COTES.reduce((s, c) => s + c.pages, 0),
    batches: EDITED_COTES.reduce((s, c) => s + batchCount(c.pages), 0),
  };

  return (
    <>
        <header className="max-w-[46em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.11em] text-brand-600">
            Fonds Alexandre Grothendieck · University of Montpellier
          </p>
          <h1 className="titre mt-2 text-[40px] leading-[1.1] text-ink-900">
            The mathematics Grothendieck wrote and never published
          </h1>
          <p className="mt-4 text-[17px] leading-relaxed text-ink-700">
            The digitised fonds holds 178 openly accessible folders, 1949 to 1991: sixteen
            thousand pages of working notes, in his own hand. This site gives the full inventory,
            and puts the transcription beside the facsimile so that every reading can be checked
            against the page it came from.
          </p>
        </header>

        <div className="tabular mt-8 flex flex-wrap gap-x-8 gap-y-2 text-[14px] text-ink-600">
          <Figure value={COTES.length} label="folders in open access" />
          <Figure value={TOTAL_PAGES} label="digitised pages" />
          <Figure value={1991 - 1949} label="years covered" />
        </div>

        <Disclaimer />

        <Progress done={done} setAside={setAside} />
    </>
  );
}

/**
 * Who made these documents, said plainly and early.
 *
 * High on the page rather than in a footer, because it changes how everything
 * below it should be read. Someone who takes a transcription for a scholarly
 * edition will cite it as one, and the way to prevent that is not a
 * disclaimer nobody scrolls to — it is a sentence before the material.
 *
 * It says the model and the year because provenance is the point: in five
 * years the interesting question about these files will be what produced them,
 * and a page that only says "AI" will not answer it.
 */
function Disclaimer() {
  return (
    <section className="mt-8 max-w-[52em] rounded-[var(--radius-card)] border border-encours-200 bg-encours-50 px-5 py-4">
      <p className="text-[11px] font-bold uppercase tracking-[0.1em] text-encours-700">
        How these documents were made
      </p>
      <p className="mt-2 text-[13.5px] leading-relaxed text-ink-700">
        The transcriptions and modernised readings on this site were produced in 2026 by{' '}
        <strong className="font-semibold text-ink-900">Claude Opus 5</strong> and{' '}
        <strong className="font-semibold text-ink-900">Claude Opus 5.5</strong>, and for part of
        them by <strong className="font-semibold text-ink-900">Claude Fable 5</strong> and{' '}
        <strong className="font-semibold text-ink-900">Claude Fable 5.1</strong>, which are no
        longer used for new passes — a folder at a time, the transcriptions twenty pages at a
        time. Which model made which file is not a
        detail we keep a tally of here — <strong className="font-semibold text-ink-900">each
        file records the model and the date of its pass in its own header, and that header is
        the authority</strong>, not this sentence. A disputed reading years from now needs to
        know what produced it, and the file is the only place that cannot drift.
      </p>
      <p className="mt-2 text-[13.5px] leading-relaxed text-ink-700">
        <strong className="font-semibold text-ink-900">None of it is a scholarly edition, and
        none of it has been verified by a person</strong> unless the batch says so. A machine pass
        over seventy-year-old handwriting produces a reading — checkable against the facsimile on
        the same screen, which is its whole value and its whole claim. Where an established
        edition exists, it is marked in{' '}
        <a
          href="#folders"
          className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
        >
          the list of folders below
        </a>{' '}
        and should be used instead of anything here.
      </p>
    </section>
  );
}

/**
 * Where the work stands, in two numbers and a bar.
 *
 * Deliberately unflattering, and the denominator is where that is decided.
 * It counts the folders nobody has edited — the work this project is for —
 * rather than the whole fonds, because a folder Maltsiniotis has transcribed
 * is not work outstanding. But narrowing a denominator flatters a ratio for
 * free, so the figure against the whole fonds is printed beside it and the
 * pages set aside are named. Ten thousand pages against a handful transcribed
 * is still the true ratio, and a bar that rounded it up to a visible sliver
 * would be the first dishonest thing on the page.
 */
function Progress({
  done,
  setAside,
}: {
  done: { total: number; transcribed: number; modernised: number };
  setAside: { folders: number; pages: number; batches: number };
}) {
  const pct = (n: number) => (n / done.total) * 100;
  const whole = done.total + setAside.batches;
  const asWords =
    done.transcribed === 0
      ? 'none yet'
      : `${((done.transcribed / done.total) * 100).toFixed(1)}% of it`;

  return (
    <section className="card mt-10 max-w-[52em] px-5 py-4">
      <div className="flex flex-wrap items-baseline gap-x-4 gap-y-1">
        <h2 className="titre text-[17px] text-ink-900">Where the work stands</h2>
        <p className="tabular ml-auto text-[12.5px] text-ink-500">
          {done.total.toLocaleString('en-GB')} batches of 20 pages · {asWords}
        </p>
      </div>

      <p className="mt-1 text-[12.5px] leading-relaxed text-ink-500">
        Counted against what nobody has edited, not against the whole fonds.
      </p>

      <div className="tabular mt-3 flex flex-wrap gap-x-7 gap-y-2 text-[13.5px] text-ink-600">
        <span>
          <strong className="titre text-[22px] text-relu-600">{done.transcribed}</strong>{' '}
          transcribed
        </span>
        <span>
          <strong className="titre text-[22px] text-brand-600">{done.modernised}</strong>{' '}
          modernised
        </span>
      </div>

      {/* One bar, two segments: modernised is a subset of transcribed, so it
          sits inside rather than beside it. */}
      <div className="mt-3 flex h-2 overflow-hidden rounded-full bg-ink-200">
        <span className="bg-brand-500" style={{ width: `${pct(done.modernised)}%` }} />
        <span
          className="bg-relu-500"
          style={{ width: `${pct(done.transcribed - done.modernised)}%` }}
        />
      </div>

      {/* The concession, in full, immediately under the bar. Whoever reads the
          percentage must be able to reach the unflattering one without leaving
          the paragraph. */}
      <p className="mt-3 text-[12.5px] leading-relaxed text-ink-500">
        <strong className="font-semibold text-ink-700">
          {setAside.batches} batches are set aside as already edited
        </strong>{' '}
        — {setAside.pages.toLocaleString('en-GB')} pages in {setAside.folders} folders, among them
        the Dérivateurs, the Long March, Pursuing Stacks and Esquisse d'un programme, all
        transcribed by mathematicians. Re-doing them would be waste, not progress, so they are not
        counted as work outstanding. Against the whole fonds — all{' '}
        {whole.toLocaleString('en-GB')} batches — the figure above would be{' '}
        {((done.transcribed / whole) * 100).toFixed(1)}%.{' '}
        <a
          href="#folders"
          className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
        >
          Which folders they are
        </a>
        .
      </p>

      <p className="mt-3 text-[12.5px] leading-relaxed text-ink-500">
        Counted from the files themselves, not from a tally kept by hand. A batch counts as
        transcribed once its LaTeX exists, and as modernised once the modernised reading does —
        neither claims anyone has checked it against the pages.{' '}
        <a
          href="/method/"
          className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
        >
          Method &amp; progress
        </a>{' '}
        breaks it down per notebook, with what it costs.
      </p>
    </section>
  );
}

function Figure({ value, label }: { value: number; label: string }) {
  return (
    <span className="flex items-baseline gap-2">
      <strong className="titre text-[26px] text-ink-900">{value.toLocaleString('en-GB')}</strong>
      <span className="text-ink-500">{label}</span>
    </span>
  );
}
