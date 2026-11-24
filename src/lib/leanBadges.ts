import { useEffect, type RefObject } from 'react';
import LEAN_PAGES from '../content/lean-pages.json';
import LITERATURE_PAGES from '../content/literature-pages.json';
import PRINT_PAGES from '../content/print-pages.json';

/**
 * Badges beside the pages of a reading that something else of the edition rests on:
 *
 *  - « ∎ Lean » and a proof card's name, opening the card's main theorem (the last it lists) in
 *    GrothendieckArchivesProofs, at its line, at the commit the links were made from
 *    (scripts/lean-lines.mjs → src/content/lean-pages.json); green when the statement holds,
 *    amber when partly proved, pink when the page is wrong;
 *  - « In print » and the first source of a finding found later in the literature, opening its
 *    card on the Findings tab (scripts/literature-pages.mjs → src/content/literature-pages.json);
 *  - « His print » and the passage of his own published texts (EGA, SGA, FGA, PTT…) that the pages
 *    draft, share statements with, or prove where the print only announces it
 *    (src/content/publications.json → src/content/print-pages.json), opening the printed text.
 *
 * The reading views are frames with their own stylesheet (ar5iv's), so a badge carries its style
 * inline and is added to the frame's document after it loads, beside the page marker
 * (`data-page`). One badge per item and document, at the first of its pages the document has: a
 * card citing pp. 9–25 is marked once, at p. 9. In the modernised reading a marker covers a range
 * of pages (« 5–8 »), and the badge goes to the narrowest range that contains the page. Several
 * items of one kind on one page make one badge, which opens their list over the text.
 */
type Card = { batch: number; page: string; name: string; verdict: string; href: string };
type Print = { id: string; page: string; name: string; refs: string[] };
const CARDS = LEAN_PAGES as unknown as Record<string, Card[]>;
const PRINTS = LITERATURE_PAGES as unknown as Record<string, Print[]>;
type Own = { page: string; name: string; kind: string; note: string; href: string };
const OWN = PRINT_PAGES as unknown as Record<string, Own[]>;

/** One thing a badge stands for, whatever its kind. */
type Item = { page: string; text: string; listText: string; title: string; href: string; colour: readonly string[] };

const runs = (page: string) =>
  page
    .split(/,\s*/)
    .map((r) => {
      const [a, b] = r.split(/[–-]/).map((x) => Number.parseInt(x, 10));
      return [a, Number.isFinite(b) ? b : a] as const;
    })
    .filter(([a]) => Number.isFinite(a));

const LEAN_COLOURS = {
  false: ['#b4235a', '#fbeaf0', '#efc2d3'],
  partly: ['#a16207', '#fdf6e7', '#f0dcae'],
  holds: ['#128557', '#eaf6ef', '#b9dfc9'],
} as const;
const PRINT_COLOUR = ['#38539d', '#eef1fa', '#c6d0ec'] as const;
const OWN_COLOUR = ['#7a4a14', '#f8f0e4', '#e2cba7'] as const;
const leanColour = (verdict: string) => (/false|refuted/.test(verdict) ? LEAN_COLOURS.false : /partly/.test(verdict) ? LEAN_COLOURS.partly : LEAN_COLOURS.holds);
const short = (s: string) => (s.length > 48 ? `${s.slice(0, 46).replace(/\s+\S*$/, '')}…` : s);

const leanItems = (cote: string): Item[] =>
  (CARDS[cote] ?? []).map((c) => ({
    page: c.page,
    text: `∎ Lean · ${short(c.name)}`,
    listText: `${short(c.name)} — ${c.verdict}`,
    title: `${c.name} (${c.verdict}; pages ${c.page}). Opens the proof in GrothendieckArchivesProofs.`,
    href: c.href,
    colour: leanColour(c.verdict),
  }));

const printItems = (cote: string): Item[] =>
  (PRINTS[cote] ?? []).map((f) => ({
    page: f.page,
    text: `In print · ${short(f.name)}`,
    listText: `${short(f.name)} — ${f.id}`,
    title: `Found later in the literature (pages ${f.page}): ${f.refs.join(' · ')}. Opens the finding.`,
    href: `/findings/#${f.id}`,
    colour: PRINT_COLOUR,
  }));

const ownItems = (cote: string): Item[] =>
  (OWN[cote] ?? []).map((o) => ({
    page: o.page,
    text: `His print · ${short(o.name)}`,
    listText: o.name,
    title: `${o.name}: these pages ${o.kind}. ${o.note} Opens the printed text.`,
    href: o.href,
    colour: OWN_COLOUR,
  }));

const pill = ([fg, bg, border]: readonly string[]) =>
  `display:inline-block;margin:0 0 0 .45em;padding:0 .45em;border:1px solid ${border};border-radius:4px;background:${bg};color:${fg};` +
  'font:600 11px/1.6 system-ui,-apple-system,sans-serif;text-decoration:none;vertical-align:.1em;white-space:nowrap;cursor:pointer';

function attach(doc: Document, groups: { items: Item[]; noun: string; mixed: (items: Item[]) => readonly string[] }[]): () => void {
  const marks = Array.from(doc.querySelectorAll<HTMLElement>('[data-page]')).map((m) => {
    const start = Number(m.dataset.page);
    const end = Number.parseInt((/[–-](\d+)/.exec(m.textContent ?? '') ?? [])[1] ?? '', 10);
    return { m, start, end: Number.isFinite(end) ? end : start };
  });
  const added: HTMLElement[] = [];
  const link = (it: Item, inList: boolean) => {
    const a = doc.createElement('a');
    a.href = it.href;
    a.target = '_blank';
    a.rel = 'noopener noreferrer';
    a.title = it.title;
    a.textContent = inList ? it.listText : it.text;
    a.setAttribute(
      'style',
      inList ? `display:block;margin:.15em 0;color:${it.colour[0]};font:500 12px/1.4 system-ui,-apple-system,sans-serif;text-decoration:none` : pill(it.colour),
    );
    return a;
  };
  for (const { items, noun, mixed } of groups) {
    // The items by the marker they go to: the narrowest that covers one of their pages (a
    // modernised reading may open on the whole folder's range before its sections narrow it).
    const at = new Map<HTMLElement, Item[]>();
    for (const it of items) {
      for (const [a, b] of runs(it.page)) {
        const m = marks.filter((k) => k.start <= b && k.end >= a).sort((x, y) => x.end - x.start - (y.end - y.start))[0]?.m;
        if (m) {
          at.set(m, [...(at.get(m) ?? []), it]);
          break;
        }
      }
    }
    for (const [m, its] of at) {
      let el: HTMLElement;
      if (its.length === 1) el = link(its[0], false);
      else {
        el = doc.createElement('details');
        el.setAttribute('style', 'display:inline-block;position:relative;vertical-align:.1em');
        const s = doc.createElement('summary');
        s.textContent = `${noun} · ${its.length}`;
        s.setAttribute('style', `${pill(mixed(its))};list-style:none`);
        el.append(s);
        // Opened over the text, not into it, so the paragraph does not reflow around the list.
        const list = doc.createElement('div');
        list.setAttribute(
          'style',
          'position:absolute;left:.45em;top:1.9em;z-index:5;min-width:22em;max-width:34em;padding:.4em .7em;border:1px solid #d9d4c7;border-radius:6px;background:#fffdf8;box-shadow:0 4px 14px rgb(19 18 16/.14)',
        );
        its.forEach((it) => list.append(link(it, true)));
        el.append(list);
      }
      el.classList.add('tr-lean');
      // After the marker and the badges already there.
      let after: Element = m;
      while (after.nextElementSibling?.classList.contains('tr-lean')) after = after.nextElementSibling;
      after.after(el);
      added.push(el);
    }
  }
  return () => added.forEach((a) => a.remove());
}

export function attachLeanBadges(doc: Document, cote: string): () => void {
  return attach(doc, [
    {
      items: leanItems(cote),
      noun: '∎ Lean · proofs',
      mixed: (its) => leanColour(its.map((i) => i.title).join(' ')),
    },
    { items: printItems(cote), noun: 'In print · findings', mixed: () => PRINT_COLOUR },
    { items: ownItems(cote), noun: 'His print · passages', mixed: () => OWN_COLOUR },
  ]);
}

const hasBadges = (cote: string) => (CARDS[cote]?.length ?? 0) + (PRINTS[cote]?.length ?? 0) + (OWN[cote]?.length ?? 0) > 0;

/** The badges on a reading frame, added when its document loads and removed with it. */
export function useLeanBadges(frame: RefObject<HTMLIFrameElement | null>, url: string, enabled: boolean, cote: string) {
  useEffect(() => {
    if (!enabled || !hasBadges(cote)) return;
    const el = frame.current;
    if (!el) return;
    let detach = () => {};
    const run = () => {
      detach();
      const doc = el.contentDocument;
      if (doc?.querySelector('[data-page]')) detach = attachLeanBadges(doc, cote);
    };
    el.addEventListener('load', run);
    if (el.contentDocument?.readyState === 'complete') run();
    return () => {
      el.removeEventListener('load', run);
      detach();
    };
  }, [frame, url, enabled, cote]);
}
