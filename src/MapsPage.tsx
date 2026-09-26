import { useHashTarget } from './components/Anchors.tsx';
import { FoldersToPrint, LineageToFolders } from './components/ConnectionGraphs.tsx';
import { CitationMap, MathMap } from './components/FondsMaps.tsx';
import { Footer, Header } from './components/Frame.tsx';
import { PeopleNetwork } from './components/PeopleNetwork.tsx';

/**
 * The maps of the whole fonds, on one page.
 *
 * They were drawn for issue #27 and first shown under the Findings list,
 * which made them look like findings. They are not: each is a picture of
 * what the transcriptions and the published record say together, with every
 * edge resting on a file and a line, and none of them claims anything the
 * list below it does not. They cut across all the folders, so they sit on the
 * fonds side of the header, beside the inventory.
 */
const CONTENTS: { id: string; label: string; help: string }[] = [
  { id: 'folders-and-print', label: 'Folders and print', help: 'which folders a published text draws on' },
  { id: 'lineage', label: 'Lineage', help: 'his students, theirs, and who has worked on the archives' },
  { id: 'people-network', label: 'People', help: 'who is named together in the same folder' },
  { id: 'math-map', label: 'Mathematics', help: 'the subjects the folders share' },
  { id: 'citation-map', label: 'Citations', help: 'what the folders cite, as far as read' },
];

export function MapsPage() {
  useHashTarget();

  return (
    <>
      <Header path="/maps/" />

      <main className="mx-auto max-w-4xl px-5 py-12">
        <header className="max-w-[44em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.14em] text-ink-400">
            Maps of the fonds
          </p>
          <h1 className="titre mt-2 text-[30px] leading-tight text-ink-900">
            How the folders connect — to print, to people, to each other
          </h1>
          <p className="mt-4 text-[15.5px] leading-relaxed text-ink-600">
            Five pictures of the same transcriptions. Every edge rests on something one can
            open: a line of a transcript, a page of a published edition, an entry of the
            Mathematics Genealogy Project. None is a judgement of influence, and a folder not
            yet transcribed has nothing to draw, so each map is as incomplete as the reading
            and grows with it.
          </p>
        </header>

        <nav aria-label="On this page" className="mt-6">
          <ol className="grid gap-x-6 gap-y-1.5 text-[13px] sm:grid-cols-2">
            {CONTENTS.map((c, i) => (
              <li key={c.id} className="flex gap-2">
                <span className="tabular text-ink-400">{i + 1}</span>
                <span>
                  <a href={`#${c.id}`} className="font-medium text-ink-900 hover:text-brand-700">
                    {c.label}
                  </a>{' '}
                  <span className="text-ink-500">— {c.help}</span>
                </span>
              </li>
            ))}
          </ol>
        </nav>

        <FoldersToPrint />

        <LineageToFolders />

        <PeopleNetwork />

        <MathMap />

        <CitationMap />
      </main>

      <Footer />
    </>
  );
}
