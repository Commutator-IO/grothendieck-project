import { Footer, Header } from './components/Frame.tsx';
import { BOOKS, TOTAL_PAGES, cotesOf, pagesOf } from './content/books.ts';
import { COTES } from './content/catalogue.ts';
import { batchCount, transcript, useManifest } from './lib/batches.ts';

/**
 * The front page: what this fonds is, and where to open it.
 *
 * The Montpellier inventory is complete and rigorous, and quite unreadable for
 * anyone who wants to *read*: 178 folders filed by accession number, each
 * titled with whatever Grothendieck had pencilled on the cover. This site does
 * not claim to replace it — it offers five ways in, and says each time where
 * the division comes from.
 */
export function HomePage() {
  const manifest = useManifest();

  /**
   * What exists, counted from the manifest rather than declared.
   *
   * The front page should not have to be edited when a batch is finished, and
   * a figure kept by hand is a figure that goes stale. These come from the
   * files on the deployed site, so they are true by construction — and when
   * they are zero, the honest thing is what the page then says.
   */
  const batches = COTES.flatMap((c) =>
    Array.from({ length: batchCount(c.pages) }, (_, i) => transcript(manifest, c.id, i + 1)),
  );
  const done = {
    total: batches.length,
    transcribed: batches.filter((b) => b.html.includes('fr')).length,
    modernised: batches.filter((b) => b.html.includes('modern')).length,
  };

  return (
    <>
      <Header path="/" />

      <main className="mx-auto max-w-6xl px-5 py-12">
        <header className="max-w-[46em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.11em] text-brand-600">
            Fonds Alexandre Grothendieck · University of Montpellier
          </p>
          <h1 className="titre mt-2 text-[40px] leading-[1.1] text-ink-900">
            The mathematics Grothendieck wrote and never published
          </h1>
          <p className="mt-4 text-[17px] leading-relaxed text-ink-700">
            The digitised fonds holds 178 openly accessible folders, 1949 to 1991: sixteen
            thousand leaves of working notes, in his own hand. This site gives the full inventory,
            and puts the transcription beside the facsimile so that every reading can be checked
            against the leaf it came from.
          </p>
        </header>

        <div className="tabular mt-8 flex flex-wrap gap-x-8 gap-y-2 text-[14px] text-ink-600">
          <Figure value={COTES.length} label="folders in open access" />
          <Figure value={TOTAL_PAGES} label="digitised leaves" />
          <Figure value={1991 - 1949} label="years covered" />
        </div>

        <Disclaimer />

        <Progress done={done} />

        <section className="mt-12">
          <h2 className="titre text-[24px] text-ink-900">Five notebooks to begin with</h2>
          <p className="mt-2 max-w-[46em] text-[14px] leading-relaxed text-ink-600">
            Two reproduce an inventory group as it stands; three are groupings of our own, and
            say so at the head of the page. The distinction is not fussiness: citing “the Cahier
            de Topos” does not commit you to the same thing as citing folder 19.
          </p>

          <ul className="mt-6 grid gap-4 md:grid-cols-2">
            {BOOKS.map((b) => {
              const cotes = cotesOf(b);
              return (
                <li key={b.key} className="card flex flex-col p-5">
                  <div className="flex items-baseline gap-2">
                    <h3 className="titre text-[20px] text-ink-900">
                      <a href={b.path} className="hover:text-brand-700">
                        {b.title}
                      </a>
                    </h3>
                    <span
                      className={`rounded-full px-2 py-0.5 text-[10px] font-semibold uppercase tracking-wide ${
                        b.inventoryGroup
                          ? 'bg-brand-100 text-brand-700'
                          : 'bg-encours-100 text-encours-700'
                      }`}
                    >
                      {b.inventoryGroup ? 'inventory' : 'editorial'}
                    </span>
                  </div>
                  <p className="mt-1 text-[12px] font-medium uppercase tracking-wide text-ink-400">
                    {b.period}
                  </p>
                  <p className="mt-2.5 flex-1 text-[14px] leading-relaxed text-ink-600">
                    {b.subtitle}
                  </p>
                  <p className="tabular mt-4 flex flex-wrap gap-x-4 text-[12.5px] text-ink-500">
                    <span>{cotes.length} folders</span>
                    <span>{pagesOf(b).toLocaleString('en-GB')} leaves</span>
                  </p>
                  <a
                    href={b.path}
                    className="mt-4 inline-block self-start rounded-lg bg-brand-600 px-3.5 py-1.5 text-[13px] font-medium text-white transition hover:bg-brand-700"
                  >
                    Open the notebook
                  </a>
                </li>
              );
            })}
          </ul>
        </section>

        <section className="mt-14 grid gap-6 md:grid-cols-2 lg:grid-cols-3">
          <div className="prose-fonds">
            <h2 className="titre text-[22px] text-ink-900">What these leaves are</h2>
            <p className="mt-3">
              <strong>Working notes</strong>, not finished texts. Grothendieck wrote for himself,
              day by day, taking the same chapter up four times over — the four “moutures” of{' '}
              <em>Analysis situs</em>, in June 1986, sit in one folder and read in sequence.
            </p>
            <p>
              He reused his <strong>versos</strong>: administrative letters, Bourbaki seminar
              notes, his secretary's drafts. The digitisation kept them, deliberately. Every other
              verso has nothing to do with its recto, and may appear upside down.
            </p>
            <p>
              The titles are his, pencilled on the folder; those <strong>in brackets</strong> were
              proposed by the archivists. The dates, correspondence aside, are nearly all
              inferred — from a dated verso, a numbered Bourbaki talk, an institute letterhead.
            </p>
          </div>

          <div className="prose-fonds">
            <h2 className="titre text-[22px] text-ink-900">What is being made of them</h2>
            <p className="mt-3">
              Each batch of leaves yields two documents, both in French. The{' '}
              <strong>transcription</strong> is the leaves as written — his notation, his
              paragraphing, and a critical apparatus that keeps what was read apart from what was
              guessed. An illegible word stays illegible; nothing is smoothed over.
            </p>
            <p>
              The <strong>modernised reading</strong> is the same mathematics in current notation
              and current names, opening with a summary that orients someone who has not met the
              subject. It is the one document allowed to depart from the leaf, and is held to
              being correct as it stands: where the manuscript is loose it says what is true, and
              a footnote says what the leaf has.
            </p>
            <p>
              Both are LaTeX, and both open in the browser — source and compiled PDF alike.
              Whatever is transcribed is marked in the folder lists, so it is visible at a glance
              what has been done and what has not.
            </p>
          </div>

          <div className="prose-fonds">
            <h2 className="titre text-[22px] text-ink-900">Why the scans pass through here</h2>
            <p className="mt-3">
              The facsimile is Montpellier's own file, fetched as you read it — nothing is copied
              or redistributed. It cannot be framed straight from their server, though, and for
              two reasons your browser enforces: they send{' '}
              <code>X-Frame-Options: SAMEORIGIN</code>, which forbids any other site from
              embedding them, and their certificate expired on 10 December 2025.
            </p>
            <p>
              Both restrictions apply to the browser, not to a server. So a relay on this origin
              requests the file and passes the bytes straight through — range requests included,
              which is what lets you open leaf 400 of a 204 MB volume without waiting for the
              volume.
            </p>
            <p>
              The result is the thing worth having: the transcription and the handwriting on one
              screen, side by side, with no second tab to lose your place in.
            </p>
          </div>
        </section>

        <section className="card mt-12 max-w-[52em] px-5 py-4">
          <p className="text-[13.5px] leading-relaxed text-ink-600">
            Nothing here is an edition. A machine pass over seventy-year-old handwriting
            produces a reading, checkable against the facsimile on the same screen — that is its
            whole value and its whole claim. Where a scholarly edition already exists, the{' '}
            <a
              href="/archive/"
              className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
            >
              archive page
            </a>{' '}
            marks the folder and links to it; use that instead.
          </p>
          <p className="mt-3 text-[13.5px] leading-relaxed text-ink-600">
            The whole fonds — all 178 folders, in Grothendieck's own filing order — is on{' '}
            <a
              href="/archive/"
              className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
            >
              the archive page
            </a>
            . The{' '}
            <a
              href="/method/"
              className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
            >
              method page
            </a>{' '}
            says how transcription proceeds, what it refuses to do, and where it stands.
          </p>
        </section>
      </main>

      <Footer />
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
        The transcriptions and modernised readings on this site were produced by{' '}
        <strong className="font-semibold text-ink-900">Claude Fable 5</strong>, in 2026, one
        twenty-leaf batch at a time. Each file records the model and the date of its pass in its
        own header.
      </p>
      <p className="mt-2 text-[13.5px] leading-relaxed text-ink-700">
        <strong className="font-semibold text-ink-900">None of it is a scholarly edition, and
        none of it has been verified by a person</strong> unless the batch says so. A machine pass
        over seventy-year-old handwriting produces a reading — checkable against the facsimile on
        the same screen, which is its whole value and its whole claim. Where an established
        edition exists, it is marked on{' '}
        <a
          href="/archive/"
          className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
        >
          the archive page
        </a>{' '}
        and should be used instead of anything here.
      </p>
    </section>
  );
}

/**
 * Where the work stands, in two numbers and a bar.
 *
 * Deliberately unflattering. Sixteen thousand leaves against a handful
 * transcribed is the true ratio, and a progress bar that rounds it up to a
 * visible sliver would be the first dishonest thing on the page. The figures
 * are given plainly, and the fraction of the whole is spelled out in words
 * beside them.
 */
function Progress({
  done,
}: {
  done: { total: number; transcribed: number; modernised: number };
}) {
  const pct = (n: number) => (n / done.total) * 100;
  const asWords =
    done.transcribed === 0
      ? 'none yet'
      : `${((done.transcribed / done.total) * 100).toFixed(1)}% of the fonds`;

  return (
    <section className="card mt-10 max-w-[52em] px-5 py-4">
      <div className="flex flex-wrap items-baseline gap-x-4 gap-y-1">
        <h2 className="titre text-[17px] text-ink-900">Where the work stands</h2>
        <p className="tabular ml-auto text-[12.5px] text-ink-500">
          {done.total.toLocaleString('en-GB')} batches of 20 leaves · {asWords}
        </p>
      </div>

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

      <p className="mt-3 text-[12.5px] leading-relaxed text-ink-500">
        Counted from the files themselves, not from a tally kept by hand. A batch counts as
        transcribed once its LaTeX exists, and as modernised once the modernised reading does —
        neither claims anyone has checked it against the leaves.{' '}
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
