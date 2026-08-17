import raw from './books.json';
import editionsRaw from './editions.json';
import { BY_ID, COTES } from './catalogue.ts';
import type {
  Book,
  BookKey,
  BookSection,
  Cote,
  EditionDocument,
  PublishedEdition,
} from '../lib/types.ts';

const EDITIONS = editionsRaw as PublishedEdition[];

/**
 * The four books, read back from the JSON the mirroring script also reads.
 *
 * Typing is applied here rather than in the JSON: this is the one place where
 * a folder cited by a book but absent from the inventory would show, and it is
 * better that it show on start-up than when a pane opens empty.
 */
export const BOOKS: Book[] = raw as Book[];

export const BY_KEY = new Map(BOOKS.map((b) => [b.key, b]));

export function book(key: BookKey): Book {
  const b = BY_KEY.get(key);
  if (!b) throw new Error(`Unknown book: ${key}`);
  return b;
}

/**
 * Folders a scholarly edition already covers, and which edition.
 *
 * Read off `editions.json`, which is the site's one record of who has edited
 * what. A folder appears here whatever the edition's kind: a published volume,
 * a community transcription and a partial edition all mean the same thing for
 * the purpose this serves — someone else has done the work, at a standard this
 * project does not claim to match.
 */
const EDITED = new Map<string, PublishedEdition>();
for (const e of EDITIONS) for (const c of e.cotes) EDITED.set(c, e);

export const editionOf = (id: string) => EDITED.get(id);

/**
 * The scholarly documents that transcribe a given folder, with their edition.
 *
 * Empty for most folders, and empty too for a folder whose edition is a
 * printed book or a page of links rather than a file — an edition without
 * `documents` is not a lesser edition, it is one whose pages this site cannot
 * put beside the facsimile. The pane distinguishes the two cases rather than
 * showing an empty frame for either.
 */
export function documentsFor(cote: string): { doc: EditionDocument; edition: PublishedEdition }[] {
  return EDITIONS.flatMap((e) =>
    (e.documents ?? []).filter((d) => d.cote === cote).map((doc) => ({ doc, edition: e })),
  );
}

/**
 * The folders no scholarly edition covers — the work this project is actually
 * for, and the honest denominator for a progress figure.
 *
 * Counting against all 178 folders measures the fonds; counting against these
 * measures the job. The two differ by 24 folders and 5,822 pages — the
 * Dérivateurs, the Long March, Pursuing Stacks, Esquisse d'un programme and a
 * handful more — which are already transcribed to a standard this project does
 * not claim to match, and which it would be waste rather than progress to do
 * again.
 *
 * Anything shown against this denominator has to show the other one too. A
 * ratio improves whenever its denominator shrinks, and a page that quietly
 * swapped 884 batches for 582 would be reporting a change in bookkeeping as
 * though it were work done.
 */
export const UNEDITED: Cote[] = COTES.filter((c) => !EDITED.has(c.id));

/** Its complement, for the sentence that has to name what was set aside. */
export const EDITED_COTES: Cote[] = COTES.filter((c) => EDITED.has(c.id));

/**
 * Folders inside a notebook that is being worked through now.
 *
 * Not a claim that any page of them is transcribed — that is read off the
 * files, and most of these have nothing yet. It is the weaker and still useful
 * fact that they are spoken for: someone is going through this notebook, and
 * the whole-fonds figure should not paint them the same colour as the hundred
 * folders nobody has opened. Driven by `inProgress` in books.json, so finishing
 * a notebook is an edit to the data.
 */
export const IN_PROGRESS: ReadonlySet<string> = new Set(
  BOOKS.filter((b) => b.inProgress).flatMap((b) => b.sections.flatMap((s) => s.cotes)),
);

/** Whether this book hides `id`, and therefore why. */
export const hiddenBy = (b: Book, id: string) => (b.excludeEdited ? EDITED.get(id) : undefined);

/**
 * A book's folders, in section order.
 *
 * Honours `excludeEdited`, so that every count drawn from this — the notebook's
 * header, its card on the home page, the method page's arithmetic — agrees with
 * what the notebook actually lists. A page claiming 2,135 pages it does not
 * show would be worse than either choice made cleanly.
 */
export function cotesOf(b: Book): Cote[] {
  return b.sections.flatMap((s) =>
    s.cotes
      .filter((id) => !hiddenBy(b, id))
      .map((id) => {
        const c = BY_ID.get(id);
        if (!c) throw new Error(`Folder ${id} cited by “${b.title}” but absent from the inventory.`);
        return c;
      }),
  );
}

/** What a book leaves out, per section, so the page can say so where it happens. */
export function excludedOf(b: Book, s: BookSection): { cote: Cote; edition: PublishedEdition }[] {
  return s.cotes.flatMap((id) => {
    const e = hiddenBy(b, id);
    const c = BY_ID.get(id);
    return e && c ? [{ cote: c, edition: e }] : [];
  });
}

export const pagesOf = (b: Book) => cotesOf(b).reduce((s, c) => s + c.pages, 0);

/** The whole fonds, for the tab that gives it as it stands. */
export const TOTAL_PAGES = COTES.reduce((s, c) => s + c.pages, 0);
