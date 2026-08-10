import { H2, H3, LI, P, useHashTarget } from './components/Anchors.tsx';
import { Footer, Header } from './components/Frame.tsx';
import { BOOKS, cotesOf } from './content/books.ts';
import { COTES } from './content/catalogue.ts';
import {
  BATCH_SIZE,
  batchCount,
  batchRange,
  declared,
  evidence,
  useManifest,
} from './lib/batches.ts';
import { STATES, shownState, type State } from './lib/progress.ts';

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
  useHashTarget();

  return (
    <>
      <Header path="/method/" />

      <main className="mx-auto max-w-6xl px-5 py-10">
        <header className="max-w-[46em]">
          <h1 className="titre text-[34px] leading-tight text-ink-900">Method &amp; progress</h1>
          <P id="intro" className="mt-3 text-[15.5px] leading-relaxed text-ink-700">
            How these pages are turned into LaTeX, what the process refuses to do, and how far it
            has got. The refusals matter more than the method: a transcription that silently
            guesses is worse than no transcription, because nothing on the page tells you which
            words were read and which were invented.
          </P>
          <p className="mt-2 text-[12.5px] text-ink-400">
            Every paragraph below has its own address: hover one and the mark in the margin copies
            a link straight to it.
          </p>
        </header>

        <StatusSequence />

        <Progress4 manifest={manifest} />

        <div className="mt-14 grid gap-x-10 gap-y-8 md:grid-cols-2">
          <div className="prose-fonds">
            <H2 id="how-he-wrote">How Grothendieck wrote</H2>
            <P id="how-he-wrote-working-notes" className="mt-3">
              Everything downstream follows from this, so it is worth stating plainly. These are
              not fair copies. They are working notes, written for one reader, and the archive's
              own description of the fonds names the traits that make them hard:
            </P>
            <H3 id="versos">Versos carry other people's paper</H3>
            <P id="versos-unrelated">
              He wrote on the back of whatever was to hand — letters from the university
              administration, offprints, Bourbaki seminar notes, typescripts his secretary had
              returned. The digitisation kept the versos, and they are frequently unrelated to the
              recto. They were also scanned in whatever orientation preserved the physical
              object, so an unrelated verso often appears upside down.
            </P>
            <H3 id="numbering">Two numbering systems, sometimes three</H3>
            <P id="numbering-archive-pages">
              Grothendieck paginated some drafts himself — the Long March runs 1 to 787 across
              four boxes. The archivists then numbered every page in pencil, bottom left. The PDF
              adds a third count of its own, one page ahead of the archive's because of the
              generated cover sheet. This site counts in archive pages throughout, and the
              transcription records the author's own page number wherever it is visible.
            </P>
            <H3 id="neutral-sheets">Neutral sheets are part of the record</H3>
            <P id="neutral-sheets-not-artefacts">
              Where staples or paper clips once held a bundle together, the archivists inserted a
              blank separator and scanned it. A blank page in the facsimile is therefore
              information about the original grouping, not an artefact to be dropped.
            </P>
            <H3 id="dating">Dates are mostly inferred</H3>
            <P id="dating-from-versos">
              Outside correspondence, almost nothing is dated. The ranges in the inventory come
              from versos: a letter of 1980 on the back places the folder at 1980 or later. The
              late notebooks are the exception, and the reason they are worth starting with —{' '}
              <em>Vers une géométrie des formes</em> dates nearly every chapter to the day.
            </P>
          </div>

          <div className="prose-fonds">
            <H2 id="how-it-proceeds">How transcription proceeds</H2>
            <P id="the-batch-is-the-unit" className="mt-3">
              One batch of {BATCH_SIZE} pages per pass, always from the local facsimile file and
              never from a re-render of it. The batch is the unit end to end: the file shown in
              the pane is the file read, and the LaTeX it produces covers those pages and no
              others.
            </P>
            <H3 id="microbatches">Microbatches, and why twenty</H3>
            <P id="why-twenty">
              Each pass runs on <strong>Fable 5</strong>, in a fresh context, on one batch and
              never two. The limit is not arbitrary: past roughly twenty handwritten pages the
              quality of machine reading degrades towards the end of the pass, and nothing in the
              output signals where it began to slip. A transcription whose weakening point is
              unknown cannot be used at all — so the batch is sized to keep page 18 read as
              carefully as page 2, and each file records in its header which model produced it
              and when.
            </P>
            <H3 id="two-editions">Two editions, one source</H3>
            <P id="two-editions-both-french">
              Each batch yields a <strong>transcription</strong> — Grothendieck wrote in French,
              and it stays in his language, his notation and his paragraphing — and then a{' '}
              <strong>modernised reading</strong>, the same mathematics in current notation,
              opening with a summary for someone who has not met the subject. Both in
              French: the notions were thought in that language, and an English translation was
              one more artifact to keep in step for no gain the other two did not give.
            </P>
            <P id="modern-reads-the-transcription">
              The modernised reading works from the transcription, never from the page directly.
              Two independent readings of the same handwriting would diverge, and nothing would
              say which was right.
            </P>
            <P id="modern-correct-as-it-stands">
              The modernised reading is the one that is allowed to depart from the page, and it is
              held to a different standard: <strong>correct as it stands</strong>. Where the
              manuscript is loose or elliptical it states what is true and footnotes what the page
              has. It carries no brackets and no page markers — it groups by argument rather than
              by sheet — so the facsimile stays put while it is open. Everything the apparatus
              carried is in its footnotes instead.
            </P>
            <H3 id="uncertainty">Uncertainty is marked, not resolved</H3>
            <P id="uncertainty-reconstructible">
              An unreadable word is <code>\ill&#123;&#125;</code>, a doubtful reading is{' '}
              <code>\uncertain&#123;…&#125;</code>, an editorial addition is bracketed. The rule
              is that a reader must be able to reconstruct which characters were on the page. A
              transcription that smooths over a gap has destroyed the only thing it was for.
            </P>
            <H3 id="page-anchors">Every page is anchored</H3>
            <P id="page-anchors-turn-the-facsimile">
              The LaTeX marks each source page with <code>\page&#123;47&#125;</code>. That is what
              lets the reading view turn the facsimile as you scroll, and what lets a
              disagreement about a formula be settled by looking at one specific page rather than
              at a folder of six hundred.
            </P>
            <H3 id="mathematics-first">Mathematics before prose</H3>
            <P id="mathematics-first-prose-summarised">
              Where the two compete — a diagram crammed into a margin, a formula overwritten three
              times — the mathematics is transcribed and the surrounding prose is summarised, with
              the omission marked. The reverse is easy to produce and worthless.
            </P>
          </div>
        </div>

        <Pipeline />

        <CostAndHorizon />

        <Contributors />

        <section className="mt-14 max-w-[52em]">
          <H2 id="not-claimed">What this site does not claim</H2>
          <ul className="prose-fonds mt-3">
            <LI id="not-claimed-observed-vs-declared">
              <strong>Most of the progress table is observed; the last step is claimed.</strong>{' '}
              Which files exist is a fact, read from the manifest: a transcribed batch shows as{' '}
              <em>drafted</em>, and one that also has a modernised reading shows as{' '}
              <em>AI-reviewed</em> — the modernisation pass reads the transcription critically and,
              held to being correct as it stands, catches things. It caught four on folder 115.
              That is a review, and calling it one is accurate. It is not a <em>human</em> review,
              which is why <em>checked</em> is separate, stays a declaration kept in your browser,
              and means only what you meant by it. The site never claims a transcript is any good;
              only that it exists, and that a second pass has been over it.
            </LI>
            <LI id="not-claimed-our-groupings">
              <strong>Two of the four notebooks are our groupings.</strong> “Cahier de Topos” and
              “Cahiers tardifs” do not exist in the inventory; each says so at the head of its
              page. “Cahier de Motifs” and “La Longue Marche” reproduce inventory groups exactly.
            </LI>
            <LI id="not-claimed-authoritative">
              <strong>No transcription is authoritative.</strong> A machine pass over
              seventy-year-old handwriting produces a reading, checkable against the facsimile on
              the same screen. That is its whole value; it is not an edition.
            </LI>
            <LI id="not-claimed-whole-fonds">
              <strong>About 10,000 pages of the fonds are not here at all.</strong> Third-party
              correspondence cannot be circulated without permission, and the non-mathematical
              papers — the 1978 trial plea, the reflections — are under 5% of the fonds and not in
              open access.
            </LI>
          </ul>
        </section>
      </main>

      <Footer />
    </>
  );
}

/** Progress across the four notebooks, batch by batch. */
function Progress4({ manifest }: { manifest: ReturnType<typeof useManifest> }) {
  return (
    <section className="mt-10">
      <H2 id="where-it-stands">Where it stands</H2>
      <P id="where-it-stands-bars" className="mt-2 max-w-[46em] text-[13.5px] leading-relaxed text-ink-600">
        One bar per notebook. The grey portion is untouched, and the coloured portions are the
        states you have marked on the notebook pages.
      </P>

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
            reviewed: 0,
            checked: 0,
            skipped: 0,
          };
          for (const x of batches) {
            counts[
              shownState(declared(manifest, x.cote, x.batch), evidence(manifest, x.cote, x.batch))
            ] += 1;
          }
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
                {(['checked', 'reviewed', 'drafted', 'running', 'skipped'] as State[]).map((s) =>
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
  drafted: 'bg-brand-300',
  reviewed: 'bg-brand-600',
  checked: 'bg-relu-500',
  skipped: 'bg-alerte-200',
};

/**
 * The people who did the transcription work.
 *
 * Named here rather than in a footnote, because the scale of what they did by
 * hand is the single most important piece of context for anything this site
 * produces. Matthias Künzer typed two thousand pages of the Dérivateurs into
 * LaTeX. A machine pass over the same folder would take an afternoon and be
 * worth less. Knowing that before starting is what stops this project from
 * duplicating decades of scholarship and calling it progress.
 *
 * The list is partial and says so. Attribution in this field is genuinely
 * hard: the CSG credits many transcriptions to "Mateo Carmona et al.", and the
 * et al. are not named anywhere we can reach.
 */
const CONTRIBUTORS: { name: string; url?: string; work: string }[] = [
  {
    name: 'Jean Malgoire',
    work:
      'Grothendieck\u2019s former student at Montpellier, and the reason any of this exists: ' +
      'the archives were given to him personally, he kept them at home until 2010, and he ' +
      'deposited them at the university. He edited the first thirty-seven sections of the Long ' +
      'March in 1995, co-edited the D\u00e9rivateurs and the Motifs transcription, and worked ' +
      'beside the archivists during the 2015 cataloguing \u2014 deciphering the handwriting and ' +
      'identifying the themes that the inventory\u2019s groups now record.',
  },
  {
    name: 'Georges Maltsiniotis',
    url: 'https://webusers.imj-prg.fr/~georges.maltsiniotis/groth.html',
    work:
      'Editor of Pursuing Stacks \u2014 volume I published by the Soci\u00e9t\u00e9 ' +
      'math\u00e9matique de France as Documents math\u00e9matiques 20 \u2014 and co-editor of ' +
      'the D\u00e9rivateurs. His pages at the IMJ-PRG are where the homotopy-theoretic ' +
      'manuscripts have been made available for two decades, together with the scholarly work ' +
      '(Ast\u00e9risque 301, and Cisinski\u2019s 308) that made them legible as mathematics ' +
      'rather than as documents.',
  },
  {
    name: 'Matthias Künzer',
    work:
      'Transcribed the D\u00e9rivateurs into LaTeX \u2014 roughly two thousand manuscript pages, ' +
      'the fullest transcription of any single folder in the fonds \u2014 and edited the ' +
      'Grothendieck\u2013Brown correspondence. If one wants a sense of what this work costs when ' +
      'done properly, it is this.',
  },
  {
    name: 'Leila Schneps and Pierre Lochak',
    url: 'https://webusers.imj-prg.fr/~leila.schneps/grothendieckcircle/',
    work:
      'The Grothendieck Circle: they edited Esquisse d\u2019un Programme with an English ' +
      'translation in Geometric Galois Actions I (LMS Lecture Notes 242, 1997), and assembled ' +
      'the collection of scanned and typed unpublished texts that was, for years, the only way ' +
      'to read most of this material at all.',
  },
  {
    name: 'Mateo Carmona',
    url: 'https://csg.igrothendieck.org/transcriptions/',
    work:
      'Coordinator of the Centre for Grothendieckian Studies at the Istituto Grothendieck since ' +
      '2023, and the driving force behind its transcription programme \u2014 some thirty texts ' +
      'and forty letters, from the Vietnam lecture notes to the regular polyhedra. Much of it is ' +
      'credited to \u201cMateo Carmona et al.\u201d, and the collaborators are not named where ' +
      'we can see them.',
  },
  {
    name: 'Hélène Rodriguez, Frédéric Troilo and Sophie Dikoff',
    work:
      'Not transcribers but the condition of transcription. In six months of 2015\u201316 they ' +
      'catalogued the whole fonds, kept Grothendieck\u2019s own folder titles, proposed the ' +
      'bracketed ones where he left none, dated folders from their versos, and numbered every ' +
      'page in pencil. Every shelfmark and every date on this site is theirs.',
  },
];

function Contributors() {
  return (
    <section className="mt-14 max-w-[52em]">
      <H2 id="before-us">Who did this work before us</H2>
      <P id="before-us-use-theirs" className="prose-fonds mt-3">
        Large parts of the fonds have already been transcribed by hand, over decades, by people
        who knew the mathematics. Where their edition exists it is better than anything produced
        here and should be used instead — the{' '}
        <a
          href="/archive/"
          className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
        >
          archive page
        </a>{' '}
        marks which folders those are. This site is for the rest.
      </P>

      <ul className="mt-6 space-y-4">
        {CONTRIBUTORS.map((c) => (
          <li key={c.name} className="card px-5 py-4">
            <h3 className="text-[15px] font-semibold text-ink-900">
              {c.url ? (
                <a
                  href={c.url}
                  target="_blank"
                  rel="noopener noreferrer"
                  className="underline decoration-ink-300 underline-offset-2 hover:text-brand-700 hover:decoration-brand-400"
                >
                  {c.name} ↗
                </a>
              ) : (
                c.name
              )}
            </h3>
            <p className="mt-1.5 text-[13.5px] leading-relaxed text-ink-600">{c.work}</p>
          </li>
        ))}
      </ul>

      <P id="before-us-incomplete" className="mt-5 text-[12.5px] leading-relaxed text-ink-400">
        Incomplete, and certainly unfair to people whose names are not published alongside the
        work they did. Corrections are welcome.
      </P>
    </section>
  );
}

/**
 * What one batch costs, measured, and what the whole job would cost, derived.
 *
 * Every number here traces to the one batch actually completed — folder 115,
 * 14 pages, transcribed with Fable 5 on 8 August 2026 — and says so. The site
 * cannot measure tokens or hours itself; these are declared figures from the
 * pilot, and the honest way to present a sample of one is as a sample of one:
 * the per-batch constants sit in this object so the next completed batch can
 * correct them in one place.
 */
const PILOT = {
  /** Batches completed so far, by hand-count. */
  batchesDone: 2,
  /** The two steps cost very differently, and the split is the useful fact:
      transcription reads page images — the whole batch at full page scale,
      then dozens of high-resolution crops for the hard hands — while the
      modernised reading works from the transcription's text alone. Figures
      are per batch, averaged over the two batches done (folder 115 ran
      lighter, folder 161-1 — nineteen dense pages — about twice as heavy). */
  transcribe: { hoursPerBatch: 0.8, tokensPerBatchK: 145 },
  modernize: { hoursPerBatch: 0.3, tokensPerBatchK: 30 },
  /** Sum of the two steps — the scope table below multiplies this. */
  hoursPerBatch: 1.1,
  tokensPerBatchK: 175,
  /** Dense continuous prose (the Long March) will run slower and heavier
      than folder 115's formula-dominated pages; the range reflects that. */
  spread: 1.6,
};

function CostAndHorizon() {
  const bookBatches = BOOKS.reduce(
    (s, b) => s + cotesOf(b).reduce((x, c) => x + batchCount(c.pages), 0),
    0,
  );
  // The whole open-access fonds, not only the notebooks.
  const allBatches = COTES.reduce((s, c) => s + batchCount(c.pages), 0);

  const hoursDone = PILOT.batchesDone * PILOT.hoursPerBatch;
  const tokensDoneK = PILOT.batchesDone * PILOT.tokensPerBatchK;

  const est = (batches: number) => ({
    hoursLow: Math.round(batches * PILOT.hoursPerBatch),
    hoursHigh: Math.round(batches * PILOT.hoursPerBatch * PILOT.spread),
    tokensLowM: (batches * PILOT.tokensPerBatchK) / 1000,
    tokensHighM: (batches * PILOT.tokensPerBatchK * PILOT.spread) / 1000,
  });
  const books = est(bookBatches);
  const fonds = est(allBatches);
  const fmtM = (m: number) => `${m >= 10 ? Math.round(m) : m.toFixed(1)} M`;

  return (
    <section className="mt-14 max-w-[52em]">
      <H2 id="cost">Cost, and the horizon</H2>
      <P id="cost-measured" className="prose-fonds mt-3">
        Two batches have been completed, both with Fable 5 on 8 August 2026: folder 115,
        fourteen pages, and folder 161-1, nineteen. Together they cost about{' '}
        <strong>{hoursDone.toFixed(1)} h</strong> of wall-clock and roughly{' '}
        <strong>{tokensDoneK}k tokens</strong> in and out. The two steps are not comparable,
        and the split is the useful number: transcription carries almost all of it, because
        it reads page images — the batch at full page scale, then dozens of high-resolution
        crops to settle a word — while the modernised reading works from the transcription's
        text and costs a fraction as much. The second batch ran about twice the first:
        nineteen dense pages against fourteen, and far more close-up reading. Everything
        below multiplies a per-batch average of two measurements, which is barely better than
        a sample of one; treat the ranges as a first anchor, to be corrected by the next
        batches.
      </P>

      <div className="mt-5 overflow-x-auto">
        <table className="w-full border-collapse text-[13px]">
          <thead>
            <tr className="border-b border-ink-200 text-left text-[11px] font-bold uppercase tracking-wide text-ink-400">
              <th className="py-2 pr-4">Scope</th>
              <th className="py-2 pr-4">Batches</th>
              <th className="py-2 pr-4">Hours</th>
              <th className="py-2">Tokens</th>
            </tr>
          </thead>
          <tbody className="tabular text-ink-700">
            {/* The two skills, priced apart, then their sum: per batch, so
                the rows below — which are multiples of that sum — can be read
                straight off them. */}
            <tr className="border-b border-ink-100">
              <td className="py-2 pr-4 font-medium text-ink-900">
                <code className="text-[12px]">/transcribe</code>, per batch
              </td>
              <td className="py-2 pr-4 text-ink-400">1</td>
              <td className="py-2 pr-4">{PILOT.transcribe.hoursPerBatch} h</td>
              <td className="py-2">{PILOT.transcribe.tokensPerBatchK}k</td>
            </tr>
            <tr className="border-b border-ink-100">
              <td className="py-2 pr-4 font-medium text-ink-900">
                <code className="text-[12px]">/modernize</code>, per batch
              </td>
              <td className="py-2 pr-4 text-ink-400">1</td>
              <td className="py-2 pr-4">{PILOT.modernize.hoursPerBatch} h</td>
              <td className="py-2">{PILOT.modernize.tokensPerBatchK}k</td>
            </tr>
            <tr className="border-b border-ink-200">
              <td className="py-2 pr-4 font-medium text-ink-900">Done so far, both steps</td>
              <td className="py-2 pr-4">{PILOT.batchesDone}</td>
              <td className="py-2 pr-4">{hoursDone.toFixed(1)} h</td>
              <td className="py-2">{tokensDoneK}k</td>
            </tr>
            <tr className="border-b border-ink-100">
              <td className="py-2 pr-4 font-medium text-ink-900">The five notebooks</td>
              <td className="py-2 pr-4">{bookBatches}</td>
              <td className="py-2 pr-4">
                {books.hoursLow}–{books.hoursHigh} h
              </td>
              <td className="py-2">
                {fmtM(books.tokensLowM)}–{fmtM(books.tokensHighM)}
              </td>
            </tr>
            <tr>
              <td className="py-2 pr-4 font-medium text-ink-900">Whole open-access fonds</td>
              <td className="py-2 pr-4">{allBatches}</td>
              <td className="py-2 pr-4">
                {fonds.hoursLow}–{fonds.hoursHigh} h
              </td>
              <td className="py-2">
                {fmtM(fonds.tokensLowM)}–{fmtM(fonds.tokensHighM)}
              </td>
            </tr>
          </tbody>
        </table>
      </div>

      <P id="cost-caveats" className="mt-4 text-[12.5px] leading-relaxed text-ink-500">
        The upper bounds assume dense continuous prose — the Long March, not folder 115's
        formula-dominated pages. Hours are machine-pass wall-clock only: the human
        page-by-page check that turns <em>Drafted</em> into <em>Checked</em> is not in the
        table, and it is the slower half of the work. Folders already edited by the community
        (marked on the archive page) should be subtracted from any plan rather than
        re-transcribed.
      </P>
    </section>
  );
}

/**
 * The pipeline, drawn.
 *
 * Two skills, two artifacts, and a human step that is not automated — said in
 * prose three times over on this page, and still easier to take in at a glance.
 * Drawn rather than described because the one thing a reader keeps needing is
 * the *order*: which document derives from which, and at what point a claim
 * stops being observable.
 *
 * Inline SVG, in the site's own palette, with the text as real text so it can
 * be selected and read aloud. No external library: a dependency to draw four
 * boxes would cost more than it saves.
 */
function Pipeline() {
  const box = 'fill-white stroke-[#e4e0d5]';
  return (
    <section className="mt-12 max-w-[52em]">
      <H2 id="pipeline">The pipeline</H2>
      <P id="pipeline-two-skills" className="prose-fonds mt-3">
        Two skills, run in order, on one batch of twenty pages at a time. The modernised
        reading closes its résumé with a <code className="text-[13px]">\keywords{'{}'}</code>{' '}
        line — English search terms — which the manifest extracts as the folder's tags. The
        last step is the one no file can vouch for.
      </P>

      <div className="card mt-5 overflow-x-auto px-4 py-5">
        <svg
          viewBox="0 0 980 300"
          className="w-full min-w-[680px]"
          role="img"
          aria-label="Pipeline: the facsimile is transcribed by transcribe-grothendieck into the transcription, which modernize-grothendieck turns into the modernised reading; its keywords line becomes the folder's tags via the manifest; both editions render to HTML and PDF; a human check is the final, unautomated step."
          style={{ fontFamily: 'system-ui, -apple-system, sans-serif' }}
        >
          <defs>
            <marker id="pipehead" viewBox="0 0 10 10" refX="9" refY="5"
              markerWidth="6" markerHeight="6" orient="auto-start-reverse">
              <path d="M0,1 L9,5 L0,9" fill="none" stroke="#726d5f" strokeWidth="1.6" />
            </marker>
          </defs>

          {/* Source */}
          <rect x="8" y="40" width="176" height="66" rx="8" className={box} strokeWidth="1.5" />
          <text x="96" y="68" textAnchor="middle" fontSize="13" fontWeight="600" fill="#131210">
            Facsimile
          </text>
          <text x="96" y="86" textAnchor="middle" fontSize="10.5" fill="#726d5f">
            Montpellier, streamed
          </text>
          <text x="96" y="99" textAnchor="middle" fontSize="10.5" fill="#726d5f">
            never stored
          </text>

          <line x1="188" y1="73" x2="292" y2="73" stroke="#726d5f" strokeWidth="1.3"
            markerEnd="url(#pipehead)" />
          <text x="240" y="60" textAnchor="middle" fontSize="9.5" fontWeight="600" fill="#38539d">
            /transcribe
          </text>
          <text x="240" y="90" textAnchor="middle" fontSize="9" fill="#9d9787">
            20 pages/pass
          </text>

          {/* Transcription */}
          <rect x="296" y="40" width="196" height="66" rx="8" className={box} strokeWidth="1.5" />
          <text x="394" y="66" textAnchor="middle" fontSize="12" fontWeight="600" fill="#131210"
            style={{ fontFamily: 'ui-monospace, Menlo, monospace' }}>
            batch-NN.fr.tex
          </text>
          <text x="394" y="84" textAnchor="middle" fontSize="10.5" fill="#726d5f">
            the transcription — apparatus,
          </text>
          <text x="394" y="97" textAnchor="middle" fontSize="10.5" fill="#726d5f">
            page by page
          </text>

          <line x1="496" y1="73" x2="600" y2="73" stroke="#726d5f" strokeWidth="1.3"
            markerEnd="url(#pipehead)" />
          <text x="548" y="60" textAnchor="middle" fontSize="9.5" fontWeight="600" fill="#38539d">
            /modernize
          </text>
          <text x="548" y="90" textAnchor="middle" fontSize="9" fill="#9d9787">
            from the .tex
          </text>

          {/* Modernised */}
          <rect x="604" y="40" width="212" height="66" rx="8" className={box} strokeWidth="1.5" />
          <text x="710" y="66" textAnchor="middle" fontSize="12" fontWeight="600" fill="#131210"
            style={{ fontFamily: 'ui-monospace, Menlo, monospace' }}>
            batch-NN.modern.tex
          </text>
          <text x="710" y="84" textAnchor="middle" fontSize="10.5" fill="#726d5f">
            summary, then the
          </text>
          <text x="710" y="97" textAnchor="middle" fontSize="10.5" fill="#726d5f">
            mathematics modernised
          </text>

          {/* Tags, extracted — an output of the modernise step, not a file
              anyone edits: the manifest reads the \keywords line back out. */}
          <line x1="820" y1="73" x2="842" y2="73" stroke="#726d5f" strokeWidth="1.3"
            markerEnd="url(#pipehead)" />
          <rect x="846" y="40" width="126" height="66" rx="8" className={box} strokeWidth="1.5" />
          <text x="909" y="64" textAnchor="middle" fontSize="12" fontWeight="600" fill="#131210">
            folder tags
          </text>
          <text x="909" y="81" textAnchor="middle" fontSize="10" fill="#726d5f">
            <tspan style={{ fontFamily: 'ui-monospace, Menlo, monospace' }}>\keywords</tspan>
            {', read out'}
          </text>
          <text x="909" y="94" textAnchor="middle" fontSize="10" fill="#726d5f">
            by npm run manifest
          </text>

          {/* States, observed */}
          <rect x="332" y="120" width="124" height="22" rx="11" fill="#dfe6f6" />
          <text x="394" y="135" textAnchor="middle" fontSize="10" fontWeight="700" fill="#2e447f"
            letterSpacing="0.06em">
            DRAFTED
          </text>
          <rect x="648" y="120" width="124" height="22" rx="11" fill="#c1cfee" />
          <text x="710" y="135" textAnchor="middle" fontSize="10" fontWeight="700" fill="#283a68"
            letterSpacing="0.06em">
            AI-REVIEWED
          </text>

          {/* Human step, deliberately dashed */}
          <line x1="710" y1="146" x2="710" y2="186" stroke="#9d9787" strokeWidth="1.3"
            strokeDasharray="4 4" markerEnd="url(#pipehead)" />
          <rect x="604" y="190" width="212" height="52" rx="8" fill="#eefaf5"
            stroke="#a7e0c3" strokeWidth="1.5" strokeDasharray="5 4" />
          <text x="710" y="211" textAnchor="middle" fontSize="11.5" fontWeight="600" fill="#0e6b4a">
            CHECKED
          </text>
          <text x="710" y="228" textAnchor="middle" fontSize="10.5" fill="#128a5f">
            a person, page by page — declared
          </text>

          {/* Derived outputs */}
          <line x1="394" y1="146" x2="394" y2="186" stroke="#cbc5b5" strokeWidth="1.3"
            markerEnd="url(#pipehead)" />
          <rect x="8" y="190" width="484" height="52" rx="8" fill="#f8f7f3"
            stroke="#e4e0d5" strokeWidth="1.5" />
          <text x="250" y="211" textAnchor="middle" fontSize="11" fill="#413e36">
            <tspan style={{ fontFamily: 'ui-monospace, Menlo, monospace' }}>npm run render</tspan>
            {' → reading view · '}
            <tspan style={{ fontFamily: 'ui-monospace, Menlo, monospace' }}>npm run pdf</tspan>
            {' → PDF'}
          </text>
          <text x="250" y="228" textAnchor="middle" fontSize="10.5" fill="#726d5f">
            derived from either .tex, never edited, both open in the browser
          </text>

          <text x="8" y="272" fontSize="10.5" fill="#9d9787">
            Everything above the dashed line is observed from the files. Below it is a claim.
          </text>
        </svg>
      </div>
    </section>
  );
}

/**
 * The six states, in order, and where each one comes from.
 *
 * Worth a table rather than a paragraph because the useful question is not
 * "what does drafted mean" but "who says so" — and the answer differs from
 * row to row. Three are facts about files; three are somebody's word, written
 * down in the repository where a change is a diff.
 */
function StatusSequence() {
  const SOURCE: Record<State, { from: string; observed: boolean }> = {
    todo: { from: 'Neither file exists', observed: true },
    running: { from: 'transcripts/status.json', observed: false },
    drafted: { from: 'batch-NN.fr.tex exists', observed: true },
    reviewed: { from: 'batch-NN.modern.tex exists', observed: true },
    checked: { from: 'transcripts/status.json', observed: false },
    skipped: { from: 'transcripts/status.json', observed: false },
  };

  return (
    <section className="mt-12 max-w-[52em]">
      <H2 id="six-states">The six states</H2>
      <P id="six-states-in-the-repository" className="prose-fonds mt-3">
        A batch moves through these in order. Nothing here can be changed from the browser: three
        of the six are read off the files themselves, and the other three are written in{' '}
        <code>transcripts/status.json</code>, in the repository, where a change is a diff somebody
        can review. A mark kept in a visitor's browser told them something nobody else could see,
        and told them nothing from a second machine.
      </P>

      <div className="mt-5 overflow-x-auto">
        <table className="w-full border-collapse text-[13px]">
          <thead>
            <tr className="border-b border-ink-200 text-left text-[11px] font-bold uppercase tracking-wide text-ink-400">
              <th className="py-2 pr-4">State</th>
              <th className="py-2 pr-4">Means</th>
              <th className="py-2 pr-4">Comes from</th>
              <th className="py-2">Kind</th>
            </tr>
          </thead>
          <tbody className="text-ink-700">
            {STATES.map((s) => (
              <tr key={s.key} className="border-b border-ink-100 align-top">
                <td className="py-2 pr-4">
                  <span
                    className={`whitespace-nowrap rounded px-1.5 py-0.5 text-[10px] font-semibold uppercase tracking-wide ${BADGE[s.key]}`}
                  >
                    {s.label}
                  </span>
                </td>
                <td className="py-2 pr-4 text-[12.5px] leading-relaxed">{s.help}</td>
                <td className="py-2 pr-4 font-mono text-[11.5px] text-ink-500">
                  {SOURCE[s.key].from}
                </td>
                <td className="py-2 text-[12px]">
                  {SOURCE[s.key].observed ? (
                    <span className="text-relu-700">observed</span>
                  ) : (
                    <span className="text-encours-700">declared</span>
                  )}
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>

      <P id="six-states-monotonic" className="mt-4 text-[12.5px] leading-relaxed text-ink-500">
        Evidence only ever moves a batch forward. A batch marked <em>checked</em> has been through
        a comparison the manifest cannot contradict, and one marked <em>skipped</em> records a
        decision that a file appearing later does not undo. <em>Drafted</em> and <em>reviewed</em>
        {' '}are never written down at all — they are read off the files, so they cannot go stale.
      </P>

      <P id="six-states-report" className="prose-fonds mt-4">
        The step from <em>AI-reviewed</em> to <em>checked</em> is a person reading against the
        pages, and readers are how it happens. Every folder that has been transcribed carries a{' '}
        <strong className="font-semibold text-ink-800">Report</strong> button, and so does every
        open batch, beside the source links — it opens an issue on the repository with the
        shelfmark, the batch and the page on screen already filled in. A disputed reading then
        sits in public, next to the file it disputes, which is what an apparatus is for.
      </P>
    </section>
  );
}

const BADGE: Record<State, string> = {
  todo: 'bg-ink-200 text-ink-500',
  running: 'bg-encours-200 text-encours-700',
  drafted: 'bg-brand-100 text-brand-700',
  reviewed: 'bg-brand-200 text-brand-800',
  checked: 'bg-relu-200 text-relu-700',
  skipped: 'bg-alerte-100 text-alerte-700',
};
