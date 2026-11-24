import LEAN_PAGES from '../content/lean-pages.json';

/**
 * A badge beside the page of a reading that a proof card cites: « ∎ Lean » and the card's name,
 * opening the card's main theorem (the last it lists) in GrothendieckArchivesProofs, at the line, at the commit
 * the links were made from (scripts/lean-lines.mjs → src/content/lean-pages.json).
 *
 * The reading views are frames with their own stylesheet (ar5iv's), so the badge carries its
 * style inline and is added to the frame's document after it loads, beside the page marker
 * (`data-page`). One badge per card and document, at the first of the card's pages the document
 * has: a card citing pp. 9–25 is marked once, at p. 9, not seventeen times. In the modernised
 * reading a marker covers a range of pages (« 5–8 »), and the badge goes to the range that
 * contains the card's page.
 */
type Card = { batch: number; page: string; name: string; verdict: string; href: string };
const CARDS = LEAN_PAGES as unknown as Record<string, Card[]>;

const runs = (page: string) =>
  page
    .split(/,\s*/)
    .map((r) => {
      const [a, b] = r.split(/[–-]/).map((x) => Number.parseInt(x, 10));
      return [a, Number.isFinite(b) ? b : a] as const;
    })
    .filter(([a]) => Number.isFinite(a));

const colour = (verdict: string) =>
  /false|refuted/.test(verdict) ? ['#b4235a', '#fbeaf0', '#efc2d3'] : /partly/.test(verdict) ? ['#a16207', '#fdf6e7', '#f0dcae'] : ['#128557', '#eaf6ef', '#b9dfc9'];

export function attachLeanBadges(doc: Document, cote: string): () => void {
  const cards = CARDS[cote];
  if (!cards?.length) return () => {};
  const marks = Array.from(doc.querySelectorAll<HTMLElement>('[data-page]')).map((m) => {
    const start = Number(m.dataset.page);
    const end = Number.parseInt((/[–-](\d+)/.exec(m.textContent ?? '') ?? [])[1] ?? '', 10);
    return { m, start, end: Number.isFinite(end) ? end : start };
  });
  // The cards by the marker they go to, in the order of the cards.
  const at = new Map<HTMLElement, Card[]>();
  for (const c of cards) {
    for (const [a, b] of runs(c.page)) {
      // The narrowest marker that covers the page: a modernised reading may open on the
      // whole folder's range (« 1–72 ») before its sections narrow it down.
      const m = marks.filter((k) => k.start <= b && k.end >= a).sort((x, y) => x.end - x.start - (y.end - y.start))[0]?.m;
      if (m) {
        at.set(m, [...(at.get(m) ?? []), c]);
        break;
      }
    }
  }
  const added: HTMLElement[] = [];
  const pill = (fg: string, bg: string, border: string) =>
    `display:inline-block;margin:0 0 0 .45em;padding:0 .45em;border:1px solid ${border};border-radius:4px;background:${bg};color:${fg};` +
    'font:600 11px/1.6 system-ui,-apple-system,sans-serif;text-decoration:none;vertical-align:.1em;white-space:nowrap;cursor:pointer';
  const link = (c: Card, inList: boolean) => {
    const [fg, bg, border] = colour(c.verdict);
    const a = doc.createElement('a');
    a.href = c.href;
    a.target = '_blank';
    a.rel = 'noopener noreferrer';
    a.title = `${c.name} (${c.verdict}; pages ${c.page}). Opens the proof in GrothendieckArchivesProofs.`;
    const name = c.name.length > 48 ? `${c.name.slice(0, 46).replace(/\s+\S*$/, '')}…` : c.name;
    a.textContent = inList ? `${name} — ${c.verdict}` : `∎ Lean · ${name}`;
    a.setAttribute(
      'style',
      inList
        ? `display:block;margin:.15em 0;color:${fg};font:500 12px/1.4 system-ui,-apple-system,sans-serif;text-decoration:none`
        : pill(fg, bg, border),
    );
    return a;
  };
  for (const [m, cs] of at) {
    let el: HTMLElement;
    if (cs.length === 1) el = link(cs[0], false);
    else {
      // Several proofs on one page: one pill that opens their list, rather than a row of pills.
      el = doc.createElement('details');
      el.setAttribute('style', 'display:inline-block;position:relative;vertical-align:.1em');
      const s = doc.createElement('summary');
      const [fg, bg, border] = colour(cs.map((c) => c.verdict).join(' '));
      s.textContent = `∎ Lean · ${cs.length} proofs`;
      s.setAttribute('style', `${pill(fg, bg, border)};list-style:none`);
      el.append(s);
      const list = doc.createElement('div');
      // Opened over the text, not into it, so the paragraph does not reflow around the list.
      list.setAttribute(
        'style',
        'position:absolute;left:.45em;top:1.9em;z-index:5;min-width:22em;max-width:34em;padding:.4em .7em;border:1px solid #d9d4c7;border-radius:6px;background:#fffdf8;box-shadow:0 4px 14px rgb(19 18 16/.14)',
      );
      cs.forEach((c) => list.append(link(c, true)));
      el.append(list);
    }
    el.classList.add('tr-lean');
    m.after(el);
    added.push(el);
  }
  return () => added.forEach((a) => a.remove());
}
