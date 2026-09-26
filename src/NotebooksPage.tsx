import { Footer, Header } from './components/Frame.tsx';
import { BOOKS, cotesOf, pagesOf } from './content/books.ts';

/**
 * The five notebooks, as a way in.
 *
 * The site's front page used to be this; it now opens on the whole fonds,
 * and the notebooks — two inventory groups and three groupings of our own —
 * are one side of the header's switch, with this page as their landing.
 */
export function NotebooksPage() {
  return (
    <>
      <Header path="/notebooks/" />

      <main className="mx-auto max-w-6xl px-5 py-12">
        <header className="max-w-[46em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.11em] text-brand-600">
            Notebooks
          </p>
          <h1 className="titre mt-2 text-[34px] leading-[1.1] text-ink-900">
            Five ways into the fonds
          </h1>
        </header>


        <section className="mt-4">
          <h2 className="sr-only">Five notebooks to begin with</h2>
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
                    <span>{pagesOf(b).toLocaleString('en-GB')} pages</span>
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
            <h2 className="titre text-[22px] text-ink-900">What these pages are</h2>
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
              Every folder yields two documents per batch of pages, both in French. The{' '}
              <strong>transcription</strong> is the pages as written — his notation, his
              paragraphing, and a critical apparatus that keeps what was read apart from what was
              guessed. An illegible word stays illegible; nothing is smoothed over. It is made
              twenty pages at a time, which is as far as one pass of reading handwriting carries.
            </p>
            <p>
              The <strong>modernised reading</strong> is the same mathematics in current notation
              and current names, opening with a summary that orients someone who has not met the
              subject. It is the one document allowed to depart from the page, and is held to
              being correct as it stands: where the manuscript is loose it says what is true, and
              a footnote says what the page has. It is made only once the whole folder has been
              transcribed, and in a single pass over all of it: its job is to make an argument
              run continuously, and Grothendieck's arguments do not stop where the batches do.
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
              which is what lets you open page 400 of a 204 MB volume without waiting for the
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
            whole value and its whole claim. Where a scholarly edition already exists,{' '}
            <a
              href="/#folders"
              className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
            >
              the whole fonds
            </a>{' '}
            marks the folder and links to it; use that instead.
          </p>
          <p className="mt-3 text-[13.5px] leading-relaxed text-ink-600">
            The whole fonds — all 178 folders, in Grothendieck's own filing order — is on{' '}
            <a
              href="/"
              className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
            >
              the front page
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
