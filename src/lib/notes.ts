import { QUOTE_WORDS, commentIssueUrl, type CommentContext } from './report.ts';

/**
 * Select a passage, comment on it, keep the comment as a note or open a
 * prefilled issue. Ported from maths-articles (public/notes.js).
 *
 * The site is static: nothing leaves the browser until the reader clicks
 * « Open an issue », and then only GitHub's own form opens, prefilled, for the
 * reader to submit or not. Notes live in localStorage, one list per scope (a
 * batch's reading, the Findings page, the Timeline).
 *
 * The passage may sit in another document — the reading view is a same-origin
 * iframe grown to its content, so a panel fixed inside it would land at the
 * bottom of a frame thousands of pixels tall. The interface is therefore
 * always drawn in the top document, and only the selection and the highlight
 * belong to the root's own document.
 *
 * Highlights use the CSS Custom Highlight API, which colours text ranges
 * without touching the DOM: a passage may cross a KaTeX formula without
 * breaking it. Browsers without it keep the list of notes, without colour.
 */

export interface Note {
  id: string;
  /** Offset of the passage in the root's flattened text, to re-find it. */
  start: number;
  /** The whole selection: it stays in this browser. */
  text: string;
  /** The same passage with its formulas as TeX: what is shown and cited. */
  quote?: string;
  comment: string;
  date: string;
  ctx: CommentContext;
}

export interface NotesOptions {
  root: Element;
  scope: string;
  /** Where a selection sits, or null if it is not commentable there. */
  contextOf: (range: Range) => CommentContext | null;
  /** Name of the list in the notes panel. */
  title: string;
}

const KEY = (scope: string) => `gn-notes:${scope}`;

function load(scope: string): Note[] {
  try {
    const v = JSON.parse(localStorage.getItem(KEY(scope)) || '[]');
    return Array.isArray(v) ? v : [];
  } catch {
    return [];
  }
}

function save(scope: string, notes: Note[]) {
  try {
    if (notes.length) localStorage.setItem(KEY(scope), JSON.stringify(notes));
    else localStorage.removeItem(KEY(scope));
  } catch {
    /* private mode, storage full: the note is lost, the issue still opens */
  }
}

/* ---------- the root's text, flattened ---------- */

const SKIP = '.katex-mathml, .tr-page, .tr-demo-diag, [data-notes-skip]';

function textNodes(root: Element) {
  const doc = root.ownerDocument;
  const out: { node: Text; start: number }[] = [];
  const walker = doc.createTreeWalker(root, NodeFilter.SHOW_TEXT, {
    acceptNode: (n) =>
      !n.parentElement || n.parentElement.closest(SKIP) ? NodeFilter.FILTER_REJECT : NodeFilter.FILTER_ACCEPT,
  });
  let pos = 0;
  for (let n = walker.nextNode() as Text | null; n; n = walker.nextNode() as Text | null) {
    out.push({ node: n, start: pos });
    pos += n.data.length;
  }
  return out;
}

const flat = (nodes: { node: Text }[]) => nodes.map((x) => x.node.data).join('');

function offsetsOf(range: Range, nodes: { node: Text; start: number }[]) {
  let start = -1;
  let end = -1;
  for (const x of nodes) {
    if (!range.intersectsNode(x.node)) continue;
    const s = x.node === range.startContainer ? range.startOffset : 0;
    const e = x.node === range.endContainer ? range.endOffset : x.node.data.length;
    if (start < 0) start = x.start + s;
    end = x.start + e;
  }
  return start < 0 || end <= start ? null : { start, end };
}

function rangeAt(doc: Document, nodes: { node: Text; start: number }[], start: number, end: number) {
  const r = doc.createRange();
  let started = false;
  for (const x of nodes) {
    const len = x.node.data.length;
    if (!started && start <= x.start + len) {
      r.setStart(x.node, start - x.start);
      started = true;
    }
    if (started && end <= x.start + len) {
      r.setEnd(x.node, end - x.start);
      return r;
    }
  }
  return null;
}

/** The passage with its formulas as TeX, as a reader would quote it. */
function quoteOf(range: Range): string {
  const div = range.startContainer.ownerDocument!.createElement('div');
  div.appendChild(range.cloneContents());
  div.querySelectorAll('.katex').forEach((k) => {
    const tex = k.querySelector('annotation[encoding="application/x-tex"]');
    k.replaceWith(tex ? `$${tex.textContent!.trim()}$` : (k.textContent ?? ''));
  });
  div.querySelectorAll(SKIP).forEach((k) => k.remove());
  return (div.textContent ?? '').replace(/\s+/g, ' ').trim();
}

/** The occurrence of a note's text closest to where it was taken. */
function locate(note: Note, doc: Document, nodes: { node: Text; start: number }[], text: string) {
  const needle = note.text;
  if (!needle || note.start < 0) return null;
  let best = -1;
  for (let i = text.indexOf(needle); i >= 0; i = text.indexOf(needle, i + 1)) {
    if (best < 0 || Math.abs(i - note.start) < Math.abs(best - note.start)) best = i;
  }
  return best < 0 ? null : rangeAt(doc, nodes, best, best + needle.length);
}

/* ---------- the interface, one per top document ---------- */

interface Attached extends NotesOptions {
  paint: () => void;
}

const active: Attached[] = [];
let ui: ReturnType<typeof buildUi> | null = null;

function el<K extends keyof HTMLElementTagNameMap>(tag: K, cls?: string, text?: string) {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text != null) e.textContent = text;
  return e;
}

function button(cls: string, text: string, onClick: () => void) {
  const b = el('button', cls, text);
  b.type = 'button';
  b.onclick = onClick;
  return b;
}

const excerpt = (t: string, max: number) => {
  const s = t.replace(/\s+/g, ' ').trim();
  return s.length > max ? `${s.slice(0, max)}…` : s;
};

function buildUi() {
  const fab = button('gn-ui gn-fab', 'Comment', () => {});
  fab.hidden = true;
  fab.title = 'Comment on the selected passage — keep a note or open an issue';
  // Keep the selection when the button is pressed.
  fab.addEventListener('mousedown', (e) => e.preventDefault());

  const panel = el('div', 'gn-ui gn-panel');
  panel.hidden = true;
  panel.setAttribute('role', 'dialog');
  panel.setAttribute('aria-label', 'Comment on the passage');

  const listBtn = button('gn-ui gn-list-btn', 'Notes', () => {
    list.hidden = !list.hidden;
    if (!list.hidden) renderList();
  });
  listBtn.hidden = true;
  listBtn.setAttribute('aria-label', 'Your notes on this page');

  const list = el('div', 'gn-ui gn-list');
  list.hidden = true;
  list.setAttribute('role', 'dialog');
  list.setAttribute('aria-label', 'Your notes on this page');

  document.body.append(fab, panel, listBtn, list);
  document.addEventListener('keydown', (e) => {
    if (e.key !== 'Escape') return;
    if (!panel.hidden) closePanel();
    else if (!list.hidden) list.hidden = true;
  });
  return { fab, panel, listBtn, list };
}

function getUi() {
  if (!ui) ui = buildUi();
  return ui;
}

let returnFocus: HTMLElement | null = null;

function closePanel() {
  const { panel } = getUi();
  panel.hidden = true;
  for (const a of active) a.root.ownerDocument.defaultView?.getSelection()?.removeAllRanges();
  if (returnFocus) returnFocus.focus();
  else if (document.activeElement instanceof HTMLElement && panel.contains(document.activeElement)) document.activeElement.blur();
  returnFocus = null;
}

function paintAll() {
  for (const a of active) a.paint();
}

/** Opens the comment panel for a passage — from a selection or an entry's button. */
export function openComment(scope: string, note: Omit<Note, 'id' | 'date' | 'comment'> & Partial<Note>) {
  const { panel, fab } = getUi();
  const n: Note = { id: String(Date.now()), date: new Date().toISOString(), comment: '', ...note };
  returnFocus = document.activeElement instanceof HTMLElement && document.activeElement !== document.body
    ? document.activeElement
    : null;
  fab.hidden = true;
  panel.replaceChildren();
  panel.hidden = false;

  const where = [
    n.ctx.label,
    n.ctx.page ? `page ${n.ctx.page}` : null,
  ].filter(Boolean).join(' · ');
  const ta = el('textarea', 'gn-text');
  ta.placeholder = 'Your comment — a misreading, a doubt, a reference…';
  ta.setAttribute('aria-label', 'Your comment');
  ta.value = n.comment;
  const store = () => {
    n.comment = ta.value.trim();
    const notes = load(scope);
    const i = notes.findIndex((m) => m.id === n.id);
    if (i >= 0) notes[i] = n;
    else notes.push(n);
    save(scope, notes);
    paintAll();
    renderList();
  };
  const row = el('div', 'gn-row');
  row.append(
    button('gn-btn gn-btn-primary', 'Open an issue on GitHub', () => {
      store();
      window.open(commentIssueUrl(n.ctx, n.quote ?? n.text, n.comment), '_blank', 'noopener');
      closePanel();
    }),
    button('gn-btn', 'Keep as a note', () => {
      store();
      closePanel();
    }),
    button('gn-btn gn-btn-quiet', 'Cancel', closePanel),
  );
  panel.append(
    el('p', 'gn-where', where),
    ...(n.text ? [el('blockquote', 'gn-quote', excerpt(n.quote ?? n.text, 400))] : []),
    ta,
    row,
    el(
      'p',
      'gn-hint',
      QUOTE_WORDS[n.ctx.kind] <= 15
        ? `A note stays in this browser. The issue opens on GitHub, prefilled, and is public once you submit it: it quotes only the first ${QUOTE_WORDS[n.ctx.kind]} words of the passage, with ${n.ctx.kind === 'reading' ? 'the shelfmark, batch, edition and page' : 'where it stands'}.`
        : 'A note stays in this browser. The issue opens on GitHub, prefilled; nothing is published until you submit it.',
    ),
  );
  ta.focus();
}

function renderList() {
  const { list, listBtn } = getUi();
  const all = active.flatMap((a) => load(a.scope).map((n) => ({ n, a })));
  listBtn.hidden = !active.length;
  listBtn.textContent = all.length ? `Notes (${all.length})` : 'Notes';
  if (list.hidden) return;
  list.replaceChildren();
  const head = el('div', 'gn-list-head');
  head.append(el('strong', '', 'Your notes on this page'), button('gn-btn gn-btn-quiet', 'Close', () => {
    list.hidden = true;
    listBtn.focus();
  }));
  list.append(head);
  if (!all.length) {
    list.append(el('p', 'gn-hint', 'Select a passage, then « Comment ». Notes stay in this browser.'));
    return;
  }
  for (const { n, a } of all) {
    const item = el('div', 'gn-item');
    item.append(el('p', 'gn-where', [n.ctx.label, n.ctx.page ? `page ${n.ctx.page}` : null].filter(Boolean).join(' · ')));
    if (n.text) item.append(el('blockquote', 'gn-quote', excerpt(n.quote ?? n.text, 160)));
    if (n.comment) item.append(el('p', 'gn-comment', n.comment));
    const row = el('div', 'gn-row');
    row.append(
      button('gn-btn gn-btn-quiet', 'Go to', () => {
        const doc = a.root.ownerDocument;
        const nodes = textNodes(a.root);
        const r = locate(n, doc, nodes, flat(nodes));
        const target = r?.startContainer.parentElement ?? (n.ctx.ref ? doc.getElementById(n.ctx.ref) : null);
        const frame = doc.defaultView?.frameElement;
        if (target && frame && doc !== document) {
          const y = target.getBoundingClientRect().top + frame.getBoundingClientRect().top + window.scrollY;
          window.scrollTo({ top: y - window.innerHeight / 3, behavior: 'smooth' });
        } else target?.scrollIntoView({ block: 'center', behavior: 'smooth' });
      }),
      button('gn-btn gn-btn-quiet', 'Edit', () => {
        list.hidden = true;
        openComment(a.scope, n);
      }),
      button('gn-btn gn-btn-quiet', 'Issue', () => window.open(commentIssueUrl(n.ctx, n.quote ?? n.text, n.comment), '_blank', 'noopener')),
      button('gn-btn gn-btn-quiet', 'Delete', () => {
        save(a.scope, load(a.scope).filter((m) => m.id !== n.id));
        paintAll();
        renderList();
      }),
    );
    item.append(row);
    list.append(item);
  }
}

/**
 * Makes `root` commentable by selection. Returns the function that undoes it.
 */
export function attachNotes(opts: NotesOptions): () => void {
  const { root, scope, contextOf } = opts;
  const doc = root.ownerDocument;
  const win = doc.defaultView;
  if (!win) return () => {};
  const { fab, panel } = getUi();
  let pending: { range: Range; note: Omit<Note, 'id' | 'date' | 'comment'> } | null = null;

  const W = win as Window & typeof globalThis;
  const hasHighlight = typeof W.CSS !== 'undefined' && 'highlights' in W.CSS && typeof W.Highlight !== 'undefined';
  const paint = () => {
    if (!hasHighlight) return;
    const nodes = textNodes(root);
    const text = flat(nodes);
    const ranges = load(scope)
      .map((n) => locate(n, doc, nodes, text))
      .filter((r): r is Range => !!r);
    W.CSS.highlights.set('gn-note', new W.Highlight(...ranges));
  };

  const current = () => {
    const sel = win.getSelection();
    if (!sel || sel.isCollapsed || !sel.rangeCount) return null;
    const range = sel.getRangeAt(0);
    if (!root.contains(range.commonAncestorContainer)) return null;
    const ctx = contextOf(range);
    if (!ctx) return null;
    const nodes = textNodes(root);
    const off = offsetsOf(range, nodes);
    if (!off) return null;
    const text = flat(nodes).slice(off.start, off.end);
    if (!text.trim()) return null;
    return { range: range.cloneRange(), note: { start: off.start, text, ctx: { ...ctx }, quote: quoteOf(range) } };
  };

  const place = () => {
    const s = current();
    if (!s || !panel.hidden) {
      if (pending && !s) {
        fab.hidden = true;
        pending = null;
      }
      return;
    }
    pending = s;
    const r = s.range.getBoundingClientRect();
    const frame = win.frameElement;
    const dx = frame && doc !== document ? frame.getBoundingClientRect().left : 0;
    const dy = frame && doc !== document ? frame.getBoundingClientRect().top : 0;
    fab.hidden = false;
    fab.onclick = () => {
      if (pending) openComment(scope, pending.note);
    };
    if (window.innerWidth < 640) {
      // On a phone the system's own menu sits over the selection.
      fab.classList.add('gn-fab-bottom');
      fab.style.left = '';
      fab.style.top = '';
    } else {
      fab.classList.remove('gn-fab-bottom');
      fab.style.left = `${Math.max(8, Math.min(window.innerWidth - 120, dx + r.left + r.width / 2 - 45))}px`;
      fab.style.top = `${dy + r.bottom + window.scrollY + 8}px`;
    }
  };

  let timer: number | undefined;
  const onChange = () => {
    window.clearTimeout(timer);
    timer = window.setTimeout(place, 180);
  };
  doc.addEventListener('selectionchange', onChange);
  // Keyboard: with a passage selected, Alt+C (or the button itself) opens the panel.
  const onKey = (e: KeyboardEvent) => {
    if (e.altKey && (e.key === 'c' || e.code === 'KeyC') && pending && !fab.hidden) {
      e.preventDefault();
      fab.click();
    }
  };
  doc.addEventListener('keydown', onKey);
  if (doc !== document) document.addEventListener('keydown', onKey);

  const me: Attached = { ...opts, paint };
  active.push(me);
  // After KaTeX has typeset: the flattened text must be the one a later
  // selection will see.
  window.setTimeout(paint, 0);
  window.setTimeout(paint, 1500);
  renderList();

  return () => {
    doc.removeEventListener('selectionchange', onChange);
    doc.removeEventListener('keydown', onKey);
    if (doc !== document) document.removeEventListener('keydown', onKey);
    window.clearTimeout(timer);
    const i = active.indexOf(me);
    if (i >= 0) active.splice(i, 1);
    fab.hidden = true;
    renderList();
  };
}
