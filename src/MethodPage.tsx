import { useEffect, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import { BOOKS, cotesOf } from './content/books.ts';
import { BATCH_SIZE, batchCount, batchRange, useManifest } from './lib/batches.ts';
import { STATES, readProgress, stateOf, type Progress, type State } from './lib/progress.ts';

/**
 * Method, and where the transcription stands.
 *
 * Two things on one page, on purpose. A progress table without a method is a
 * scoreboard: it says how much has been done and nothing about whether it is
 * worth anything. A method without a progress table is a promise. Together
 * they are checkable — which is the only claim this project can honestly make
 * about a body of work no one will read end to end.
 */
export function MethodPage() {
  const manifest = useManifest();
  const [progress, setProgress] = useState<Progress>({});
  useEffect(() => setProgress(readProgress()), []);

  return (
    <>
      <Header path="/method/" />

      <main className="mx-auto max-w-6xl px-5 py-10">
        <header className="max-w-[46em]">
          <h1 className="titre text-[34px] leading-tight text-ink-900">Method &amp; progress</h1>
          <p className="mt-3 text-[15.5px] leading-relaxed text-ink-700">
            How these leaves are turned into LaTeX, what the process refuses to do, and how far it
            has got. The refusals matter more than the method: a transcription that silently
            guesses is worse than no transcription, because nothing on the page tells you which
            words were read and which were invented.
          </p>
        </header>

        <Progress4 progress={progress} manifest={manifest} />

        <div className="mt-14 grid gap-x-10 gap-y-8 md:grid-cols-2">
          <div className="prose-fonds">
            <h2 className="titre text-[22px] text-ink-900">How Grothendieck wrote</h2>
            <p className="mt-3">
              Everything downstream follows from this, so it is worth stating plainly. These are
              not fair copies. They are working notes, written for one reader, and the archive's
              own description of the fonds names the traits that make them hard:
            </p>
            <h3>Versos carry other people's paper</h3>
            <p>
              He wrote on the back of whatever was to hand — letters from the university
              administration, offprints, Bourbaki seminar notes, typescripts his secretary had
              returned. The digitisation kept the versos, and they are frequently unrelated to the
              recto. They were also scanned in whatever orientation preserved the physical
              object, so an unrelated verso often appears upside down.
            </p>
            <h3>Two numbering systems, sometimes three</h3>
            <p>
              Grothendieck paginated some drafts himself — the Long March runs 1 to 787 across
              four boxes. The archivists then numbered every leaf in pencil, bottom left. The PDF
              adds a third count of its own, one page ahead of the archive's because of the
              generated cover sheet. This site counts in archive leaves throughout, and the
              transcription records the author's own page number wherever it is visible.
            </p>
            <h3>Neutral sheets are part of the record</h3>
            <p>
              Where staples or paper clips once held a bundle together, the archivists inserted a
              blank separator and scanned it. A blank page in the facsimile is therefore
              information about the original grouping, not an artefact to be dropped.
            </p>
            <h3>Dates are mostly inferred</h3>
            <p>
              Outside correspondence, almost nothing is dated. The ranges in the inventory come
              from versos: a letter of 1980 on the back places the folder at 1980 or later. The
              late notebooks are the exception, and the reason they are worth starting with —{' '}
              <em>Vers une géométrie des formes</em> dates nearly every chapter to the day.
            </p>
          </div>

          <div className="prose-fonds">
            <h2 className="titre text-[22px] text-ink-900">How transcription proceeds</h2>
            <p className="mt-3">
              One batch of {BATCH_SIZE} leaves per pass, always from the local facsimile file and
              never from a re-render of it. The batch is the unit end to end: the file shown in
              the pane is the file read, and the LaTeX it produces covers those leaves and no
              others.
            </p>
            <h3>Three editions, one source</h3>
            <p>
              Each batch yields a French transcription — Grothendieck wrote in French, and the
              transcription stays in his language, his notation and his paragraphing — then an
              English translation of it, then a summary that restates the argument for a reader at
              undergraduate level. The translation and the summary are derived from the
              transcription, never from the leaf directly: two independent readings of the same
              handwriting would diverge, and nothing would say which was right.
            </p>
            <h3>Uncertainty is marked, not resolved</h3>
            <p>
              An unreadable word is <code>\ill&#123;&#125;</code>, a doubtful reading is{' '}
              <code>\uncertain&#123;…&#125;</code>, an editorial addition is bracketed. The rule
              is that a reader must be able to reconstruct which characters were on the page. A
              transcription that smooths over a gap has destroyed the only thing it was for.
            </p>
            <h3>Every leaf is anchored</h3>
            <p>
              The LaTeX marks each source leaf with <code>\leaf&#123;47&#125;</code>. That is what
              lets the reading view turn the facsimile as you scroll, and what lets a
              disagreement about a formula be settled by looking at one specific leaf rather than
              at a folder of six hundred.
            </p>
            <h3>Mathematics before prose</h3>
            <p>
              Where the two compete — a diagram crammed into a margin, a formula overwritten three
              times — the mathematics is transcribed and the surrounding prose is summarised, with
              the omission marked. The reverse is easy to produce and worthless.
            </p>
          </div>
        </div>

        <section className="mt-14 max-w-[52em]">
          <h2 className="titre text-[22px] text-ink-900">What this site does not claim</h2>
          <ul className="prose-fonds mt-3">
            <li>
              <strong>The progress table is a declaration, not an observation.</strong> Marks live
              in your browser and are set by hand. The site does not verify that a{' '}
              <code>.tex</code> file exists, still less that it is any good. It counts what you
              have told it.
            </li>
            <li>
              <strong>Two of the four notebooks are our groupings.</strong> “Cahier de Topos” and
              “Cahiers tardifs” do not exist in the inventory; each says so at the head of its
              page. “Cahier de Motifs” and “La Longue Marche” reproduce inventory groups exactly.
            </li>
            <li>
              <strong>No transcription is authoritative.</strong> A machine pass over
              seventy-year-old handwriting produces a reading, checkable against the facsimile on
              the same screen. That is its whole value; it is not an edition.
            </li>
            <li>
              <strong>About 10,000 leaves of the fonds are not here at all.</strong> Third-party
              correspondence cannot be circulated without permission, and the non-mathematical
              papers — the 1978 trial plea, the reflections — are under 5% of the fonds and not in
              open access.
            </li>
          </ul>
        </section>
      </main>

      <Footer />
    </>
  );
}

/** Progress across the four notebooks, batch by batch. */
function Progress4({
  progress,
  manifest,
}: {
  progress: Progress;
  manifest: ReturnType<typeof useManifest>;
}) {
  return (
    <section className="mt-10">
      <h2 className="titre text-[22px] text-ink-900">Where it stands</h2>
      <p className="mt-2 max-w-[46em] text-[13.5px] leading-relaxed text-ink-600">
        One bar per notebook. The grey portion is untouched, and the coloured portions are the
        states you have marked on the notebook pages.
      </p>

      <ul className="mt-6 space-y-5">
        {BOOKS.map((b) => {
          const cotes = cotesOf(b);
          const batches = cotes.flatMap((c) =>
            Array.from({ length: batchCount(c.pages) }, (_, i) => {
              const { first, last } = batchRange(i + 1, c.pages);
              return { cote: c.id, batch: i + 1, pages: last - first + 1 };
            }),
          );
          const counts: Record<State, number> = {
            todo: 0,
            running: 0,
            drafted: 0,
            checked: 0,
            skipped: 0,
          };
          for (const x of batches) counts[stateOf(progress, x.cote, x.batch)] += 1;
          const mirrored = batches.filter((x) =>
            manifest?.facsimiles?.[x.cote]?.batches.includes(x.batch),
          ).length;

          return (
            <li key={b.key} className="card px-5 py-4">
              <div className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
                <h3 className="titre text-[17px] text-ink-900">
                  <a href={b.path} className="hover:text-brand-700">
                    {b.title}
                  </a>
                </h3>
                <p className="tabular ml-auto text-[12.5px] text-ink-500">
                  {batches.length} batches · {mirrored} mirrored ·{' '}
                  <strong className="font-semibold text-relu-600">{counts.checked}</strong> checked
                </p>
              </div>

              <div className="mt-2.5 flex h-2.5 overflow-hidden rounded-full bg-ink-200">
                {(['checked', 'drafted', 'running', 'skipped'] as State[]).map((s) =>
                  counts[s] ? (
                    <span
                      key={s}
                      className={BAR_COLOURS[s]}
                      style={{ width: `${(counts[s] / batches.length) * 100}%` }}
                      title={`${counts[s]} ${s}`}
                    />
                  ) : null,
                )}
              </div>
            </li>
          );
        })}
      </ul>

      <ul className="mt-5 flex flex-wrap gap-x-5 gap-y-1.5 text-[12px] text-ink-500">
        {STATES.map((s) => (
          <li key={s.key} className="flex items-center gap-1.5" title={s.help}>
            <span className={`h-2.5 w-2.5 rounded-sm ${BAR_COLOURS[s.key]}`} />
            {s.label}
          </li>
        ))}
      </ul>
    </section>
  );
}

const BAR_COLOURS: Record<State, string> = {
  todo: 'bg-ink-200',
  running: 'bg-encours-500',
  drafted: 'bg-brand-500',
  checked: 'bg-relu-500',
  skipped: 'bg-alerte-200',
};
