import { Footer, Header } from './components/Frame.tsx';
import { Gallery } from './components/Gallery.tsx';
import diagramsRaw from './content/diagrams.json';
import handRaw from './content/hand.json';
import manifestProgress from './content/progress.ts';

/**
 * Every commutative diagram in the transcriptions, one at a time.
 *
 * The diagrams are drawn by the reading views' own renderer — a grid of KaTeX
 * nodes with the arrows measured and drawn in SVG — in one carousel per folder
 * and one of the richest across the fonds, written by `node scripts/diagrams.mjs`
 * (public/transcripts/diagrams/). Each links back to its page, where it stands
 * between the lines it belongs to.
 */
interface Diagram {
  batch: number;
  page: string | null;
  nodes: number;
  arrows: number;
  rows: number;
  symbols: number;
}
interface FolderDiagrams {
  id: string;
  title: string;
  date: string;
  n: number;
  diagrams: Diagram[];
}
const DG = diagramsRaw as unknown as { built: string; total: number; folders: FolderDiagrams[] };
const PAGES = new Map((handRaw as unknown as { folders: { id: string; pages: number }[] }).folders.map((f) => [f.id, f.pages]));

export function DiagramsPage() {
  const all = DG.folders.flatMap((f) => f.diagrams);
  const pagesRead = [...PAGES.values()].reduce((a, b) => a + b, 0);
  const median = [...all].map((d) => d.nodes).sort((a, b) => a - b)[Math.floor(all.length / 2)];
  const squares = all.filter((d) => d.nodes === 4 && d.rows === 2).length;
  const p = manifestProgress;

  return (
    <>
      <Header path="/diagrams/" />

      <main className="mx-auto max-w-6xl px-5 py-12">
        <header className="max-w-[46em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.14em] text-ink-400">Diagrams</p>
          <h1 className="titre mt-2 text-[30px] leading-tight text-ink-900">The commutative diagrams, one at a time</h1>
          <p className="mt-4 text-[15.5px] leading-relaxed text-ink-600">
            Commutative diagrams are the language of this fonds. He drew them in the margins, across a page, crammed
            between two formulas; the transcriptions set each one in{' '}
            <code className="rounded bg-ink-100 px-1 text-[13px]">tikz-cd</code>. Here are all{' '}
            {DG.total.toLocaleString('en-GB')} of them from the {DG.folders.length} folders that have any — the richest
            first, then a folder at a time — each drawn larger than on its page and linked back to it.
          </p>
        </header>

        <div className="mt-6 grid grid-cols-2 gap-3 sm:grid-cols-4">
          {[
            [DG.total.toLocaleString('en-GB'), 'diagrams'],
            [((100 * DG.total) / pagesRead).toFixed(0), 'per hundred pages read'],
            [String(median), 'nodes in the median diagram'],
            [String(squares), 'squares, two by two'],
          ].map(([v, l]) => (
            <div key={l} className="card px-4 py-3">
              <p className="tabular text-[24px] font-semibold text-ink-900">{v}</p>
              <p className="text-[12.5px] text-ink-600">{l}</p>
            </div>
          ))}
        </div>

        <Gallery
          kind="diagrams"
          noun={['diagram', 'Diagrams']}
          richestLabel="The 60 richest"
          richestHelp="by nodes, arrows and twice the distinct symbols they name"
          folders={DG.folders.map((f) => ({
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
            A language model reads each folder's pages from Montpellier's facsimile, twenty at a time, and writes what
            it reads in a restricted LaTeX; a diagram becomes a <code>tikzcd</code> environment. A script gathers
            those environments, counts their nodes, arrows and distinct symbols, and draws them with the site's own
            renderer — KaTeX for the nodes, the arrows measured and drawn in SVG. So far {p.transcribed} of the{' '}
            {p.total} batches of twenty pages nobody else has edited are transcribed ({p.share}), in {p.folders}{' '}
            folders. None has been checked against the facsimile by a person: an arrow can be misread as easily as a
            word, and each diagram links to its page so that anyone can check it.
          </p>
          <p className="mt-2 text-[12px] text-ink-400">
            Built on {DG.built} by <code>node scripts/diagrams.mjs</code>. A diagram the transcriber described in a
            note rather than drew is not here.
          </p>
        </section>
      </main>

      <Footer />
    </>
  );
}
