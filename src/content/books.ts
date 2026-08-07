import raw from './books.json';
import { BY_ID, COTES } from './catalogue.ts';
import type { Book, BookKey, Cote } from '../lib/types.ts';

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

/** A book's folders, in section order. */
export function cotesOf(b: Book): Cote[] {
  return b.sections.flatMap((s) =>
    s.cotes.map((id) => {
      const c = BY_ID.get(id);
      if (!c) throw new Error(`Folder ${id} cited by “${b.title}” but absent from the inventory.`);
      return c;
    }),
  );
}

export const pagesOf = (b: Book) => cotesOf(b).reduce((s, c) => s + c.pages, 0);

/** The whole fonds, for the tab that gives it as it stands. */
export const TOTAL_PAGES = COTES.reduce((s, c) => s + c.pages, 0);
