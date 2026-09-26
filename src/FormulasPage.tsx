import { Footer, Header } from './components/Frame.tsx';
import { Gallery } from './components/Gallery.tsx';
import formulasRaw from './content/formulas.json';
import handRaw from './content/hand.json';
import progress from './content/progress.ts';

/**
 * Every displayed formula in the transcriptions, one at a time: a carousel
 * per folder and one of the richest across the fonds, written by
 * `node scripts/formulas.mjs` (public/transcripts/formulas/), set by KaTeX as
 * the reading views set them, apparatus included.
 */
const FM = formulasRaw as unknown as {
  built: string;
  total: number;
  medianSymbols: number;
  folders: { id: string; title: string; date: string; n: number; maxSymbols: number }[];
};
const PAGES = new Map((handRaw as unknown as { folders: { id: string; pages: number }[] }).folders.map((f) => [f.id, f.pages]));

export function FormulasPage() {
  const pagesRead = [...PAGES.values()].reduce((a, b) => a + b, 0);
  const richest = Math.max(...FM.folders.map((f) => f.maxSymbols));

  return (
    <>
      <Header path="/formulas/" />

      <main className="mx-auto max-w-6xl px-5 py-12">
        <header className="max-w-[46em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.14em] text-ink-400">Formulas</p>
          <h1 className="titre mt-2 text-[30px] leading-tight text-ink-900">The displayed formulas, one at a time</h1>
          <p className="mt-4 text-[15.5px] leading-relaxed text-ink-600">
            Every formula he set apart from the text — {FM.total.toLocaleString('en-GB')} of them in{' '}
            {FM.folders.length} folders — as the transcriptions give them, with what could not be read left unread: an
            illegible index stays illegible. The richest come first, then a folder at a time.
          </p>
        </header>

        <div className="mt-6 grid grid-cols-2 gap-3 sm:grid-cols-4">
          {[
            [FM.total.toLocaleString('en-GB'), 'displayed formulas'],
            [((100 * FM.total) / pagesRead).toFixed(0), 'per hundred pages read'],
            [String(FM.medianSymbols), 'distinct symbols in the median formula'],
            [String(richest), 'in the richest'],
          ].map(([v, l]) => (
            <div key={l} className="card px-4 py-3">
              <p className="tabular text-[24px] font-semibold text-ink-900">{v}</p>
              <p className="text-[12.5px] text-ink-600">{l}</p>
            </div>
          ))}
        </div>

        <Gallery
          kind="formulas"
          noun={['formula', 'Formulas']}
          richestLabel="The 200 richest"
          richestHelp="by distinct symbols first, then by size"
          folders={FM.folders.map((f) => ({
            id: f.id,
            title: f.title,
            date: f.date,
            n: f.n,
            density: (100 * f.n) / Math.max(1, PAGES.get(f.id) ?? 1),
          }))}
        />

        <section className="mt-12 max-w-[46em] text-[13px] leading-relaxed text-ink-500">
          <h2 className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">How this page is made</h2>
          <p className="mt-2">
            A formula counts here when the transcription sets it apart — <code>\[…\]</code>, <code>equation</code>,{' '}
            <code>align</code>, <code>gather</code> — and not when it runs in the text. « Richest » is a count, not a
            judgement: the distinct symbols a formula uses — a letter in a given alphabet, so that 𝒞 is not C, a named
            symbol such as ⊗ or lim, an operator — and, after that, how many it writes. It finds the formulas that
            carry the most, not the ones that matter most, which no count can find. So far {progress.transcribed} of
            the {progress.total} batches nobody else has edited are transcribed ({progress.share}); none has been
            checked against the facsimile by a person.
          </p>
          <p className="mt-2 text-[12px] text-ink-400">
            Built on {FM.built} by <code>node scripts/formulas.mjs</code>; symbols are counted by{' '}
            <code>scripts/lib/symbols.mjs</code>, the same way for the diagrams.
          </p>
        </section>
      </main>

      <Footer />
    </>
  );
}
