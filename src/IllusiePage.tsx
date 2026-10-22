import { lazy, Suspense, useCallback, useEffect, useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import inventoryRaw from './content/illusie.json';
import { ITEM_NOTES } from './content/illusie-highlights.ts';
import { PUBLIC_VIEWS } from './content/illusie-public.ts';
import type { IllusieView } from './components/IllusieReader.tsx';

/**
 * The Fonds Grothendieck–Illusie, as an inventory (#85).
 *
 * The IHÉS holds this fonds — Grothendieck's letters to Luc Illusie, his
 * correspondence with colleagues, notes, EGA and SGA papers — and keeps its
 * scans on a bare file server, repo-archives.ihes.fr, outside its public
 * catalogue. Until the IHÉS answers on their use, this page is metadata only:
 * the titles, dates and page counts its own item records give
 * (scripts/illusie-catalogue.mjs), each linking out to the item's directory
 * there. No scan is framed, relayed, mirrored or thumbnailed.
 *
 * The reading view — each item's transcription beside its facsimile, the
 * layout of the Montpellier folders (components/IllusieReader.tsx) — is built
 * but switched off: it is compiled in only when the build is made with
 * RENDER_ILLUSIE (repository variable, read by the deploy as
 * VITE_RENDER_ILLUSIE), and in the dev server. Off, the condition below is a
 * constant `false`, the lazy import goes with it, and the deployed page is the
 * inventory alone, without the pane or a single image address.
 */

const RENDER_ILLUSIE = import.meta.env.DEV || import.meta.env.VITE_RENDER_ILLUSIE === 'true';
const IllusieReader = lazy(() => import('./components/IllusieReader.tsx').then((m) => ({ default: m.IllusieReader })));
/** Whether an item opens in the reading view: every item with RENDER_ILLUSIE, else only the exceptions. */
const readable = (id: string) => RENDER_ILLUSIE || id in PUBLIC_VIEWS;

/** `#FG_IL_2_GIRAUD69/1/p3`: an item, a batch of twenty pages, a page. As on the fonds' pages. */
function fromHash(): { id: string; batch: number; page?: number } | null {
  const h = /^#([\w-]+)\/(\d+)(?:\/fr)?(?:\/p(\d+))?$/.exec(decodeURIComponent(location.hash));
  return h ? { id: h[1], batch: Math.max(1, Number(h[2])), page: h[3] ? Number(h[3]) : undefined } : null;
}

interface Item {
  id: string;
  series: string;
  title: string | null;
  creator: string | null;
  recipient: string | null;
  date: string | null;
  sort: string | null;
  pages: number;
  url: string;
  metadata?: false;
}
interface Inventory {
  built: string;
  source: string;
  series: { id: string; label: string }[];
  unreadable: { id: string; why: string }[];
  items: Item[];
}
const INV = inventoryRaw as unknown as Inventory;
const ITEMS = INV.items;
const PAGES = ITEMS.reduce((n, i) => n + i.pages, 0);

const fold = (s: string) => s.normalize('NFD').replace(/[̀-ͯ]/g, '').toLowerCase();
const byId = (a: Item, b: Item) => a.id.localeCompare(b.id, 'en', { numeric: true });
/** The records write names in capitals (« GROTHENDIECK »); shown in title case. */
const name = (s: string | null) =>
  s ? s.toLowerCase().replace(/(^|[\s\-'’(,;/])(\p{L})/gu, (_, p: string, c: string) => p + c.toUpperCase()) : null;

export function IllusiePage() {
  const [q, setQ] = useState('');
  const [onlyHits, setOnlyHits] = useState(false);
  const [open, setOpen] = useState(() => {
    const h = fromHash();
    return h && readable(h.id) ? h : null;
  });
  // All page addresses only in a build that shows every item; otherwise the exceptions'.
  const [views, setViews] = useState<Record<string, IllusieView>>(PUBLIC_VIEWS);
  useEffect(() => {
    if (!RENDER_ILLUSIE) return;
    void import('./content/illusie-pages.json').then((m) =>
      setViews((m.default as unknown as { views: Record<string, IllusieView> }).views),
    );
  }, []);

  useEffect(() => {
    // A series anchor (#FG_IL_3_…) is not an item: it moves the page and
    // leaves the reading view as it is.
    const onHash = () => {
      const h = fromHash();
      if (h && readable(h.id)) setOpen(h);
    };
    addEventListener('hashchange', onHash);
    return () => removeEventListener('hashchange', onHash);
  }, []);

  const goTo = useCallback((id: string, batch: number) => {
    history.replaceState(null, '', `#${id}/${batch}`);
    setOpen({ id, batch });
  }, []);
  const onPage = useCallback((page: number) => setOpen((o) => (o && o.page !== page ? { ...o, page } : o)), []);
  const close = useCallback(() => {
    history.replaceState(null, '', location.pathname);
    setOpen(null);
  }, []);
  const item = open ? ITEMS.find((i) => i.id === open.id) : undefined;

  const groups = useMemo(() => {
    const needle = fold(q.trim());
    return INV.series
      .map((s) => ({
        ...s,
        items: ITEMS.filter(
          (i) =>
            i.series === s.id &&
            (!onlyHits || ITEM_NOTES[i.id] !== undefined) &&
            (!needle || fold(`${i.id} ${i.title ?? ''} ${i.creator ?? ''} ${i.recipient ?? ''} ${i.date ?? ''}`).includes(needle)),
        ).sort(byId),
      }))
      .filter((g) => g.items.length);
  }, [q, onlyHits]);
  const shown = groups.reduce((n, g) => n + g.items.length, 0);

  return (
    <>
      {/* The content shifts rather than sliding under the facsimile pane, as on the fonds' pages. */}
      <div className={item ? 'transition-[padding] duration-150 lg:pr-[var(--pane,0px)]' : undefined}>
      <Header path="/illusie/" />
      <main className="mx-auto max-w-6xl px-5 py-12">
        <header className="max-w-[46em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.11em] text-brand-600">Illusie</p>
          <h1 className="titre mt-2 text-[34px] leading-[1.1] text-ink-900">The Fonds Grothendieck–Illusie</h1>
          <p className="mt-4 text-[15px] leading-relaxed text-ink-600">
            Papers of Grothendieck from Luc Illusie's archives, now held by the Institut des Hautes Études
            Scientifiques: letters to Illusie, letters with colleagues, mathematical notes, and papers of EGA
            and SGA. This page is their inventory, as the IHÉS's own item records describe them — title,
            date, number of pages — with each item linked to its directory on the IHÉS's server.
          </p>
          <p className="tabular mt-3 text-[14px] text-ink-700">
            {ITEMS.length} items in {INV.series.length} series, {PAGES.toLocaleString('en')} pages.
          </p>
        </header>

        <aside className="mt-6 max-w-[46em] rounded-xl border border-ink-200 bg-ink-50 px-4 py-3 text-[13px] leading-relaxed text-ink-700">
          {RENDER_ILLUSIE ? (
            <>
              The fonds is held by the IHÉS. Its scans are on the IHÉS's file server and are not reproduced
              here: the facsimile pane loads the IHÉS's page views from that server, and no image or PDF of
              them is stored on this site. The correspondence is under its authors' rights.
            </>
          ) : (
            <>
              The fonds is held by the IHÉS. Its scans are on the IHÉS's file server and are not reproduced
              here: no image, PDF or transcription of them is stored on this site, and only the letter to
              Giraud of 13 June 1969 opens with its page views, loaded from the IHÉS's server. The
              correspondence is under its authors' rights.
            </>
          )} For any use of the documents, contact the IHÉS archives,{' '}
          <a href="mailto:archives@ihes.fr" className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2">
            archives@ihes.fr
          </a>
          .
        </aside>

        {item && open && readable(item.id) && (
          <Suspense fallback={null}>
            <IllusieReader
              item={item}
              view={views[item.id]}
              batch={open.batch}
              page={open.page}
              onBatch={(b) => goTo(item.id, b)}
              onPage={onPage}
              onClose={close}
            />
          </Suspense>
        )}

        <nav className="mt-8 flex flex-wrap gap-2" aria-label="Series">
          {INV.series.map((s) => (
            <a
              key={s.id}
              href={`#${s.id}`}
              className="rounded-lg border border-ink-200 px-3 py-1 text-[12.5px] text-ink-700 hover:border-brand-500 hover:bg-brand-50"
            >
              {s.label} · {ITEMS.filter((i) => i.series === s.id).length}
            </a>
          ))}
        </nav>

        <div className="mt-4 flex flex-wrap items-center gap-2">
          <input
            type="search"
            value={q}
            onChange={(e) => setQ(e.target.value)}
            placeholder="Search titles, names, dates, shelfmarks…"
            className="w-full rounded-lg border border-ink-200 px-3 py-1.5 text-[13px] sm:w-80"
          />
          <label className="flex items-center gap-1.5 text-[12.5px] text-ink-700">
            <input type="checkbox" checked={onlyHits} onChange={(e) => setOnlyHits(e.target.checked)} />
            Only those meeting the fonds
          </label>
          <p className="tabular text-[12px] text-ink-500">{shown} shown</p>
          <p className="text-[12px] text-alerte-600">In red, the items that meet the Montpellier fonds or an open question of the edition.</p>
        </div>

        {groups.map((g) => (
          <section key={g.id} id={g.id} className="mt-10 scroll-mt-20">
            <h2 className="text-[18px] font-semibold text-ink-900">{g.label}</h2>
            <p className="tabular mt-0.5 text-[12px] text-ink-500">
              {g.items.length} items · {g.items.reduce((n, i) => n + i.pages, 0).toLocaleString('en')} pages ·{' '}
              <a href={`${INV.source}${g.id}/`} target="_blank" rel="noreferrer" className="hover:text-brand-700">
                {g.id} ↗
              </a>
            </p>
            <ul className="mt-3 grid gap-2">
              {g.items.map((i) => (
                <li key={i.id} className={`rounded-xl border bg-white px-4 py-3 ${ITEM_NOTES[i.id] ? 'border-alerte-500 ring-1 ring-alerte-500' : 'border-ink-200'}`}>
                  <div className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
                    {readable(i.id) ? (
                      <span className="min-w-0 flex-1">
                        <a
                          href={`#${i.id}/1`}
                          onClick={(e) => {
                            e.preventDefault();
                            goTo(i.id, 1);
                            scrollTo({ top: 0, behavior: 'instant' });
                          }}
                          aria-current={open?.id === i.id ? 'true' : undefined}
                          className={`text-[14px] font-medium hover:text-brand-700 ${open?.id === i.id ? 'text-brand-700' : 'text-ink-900'}`}
                        >
                          {i.title ?? <span className="italic text-ink-500">No readable record</span>}
                        </a>{' '}
                        <a href={i.url} target="_blank" rel="noreferrer" className="text-[12px] text-ink-400 hover:text-brand-700">
                          IHÉS ↗
                        </a>
                      </span>
                    ) : (
                      <a
                        href={i.url}
                        target="_blank"
                        rel="noreferrer"
                        className="min-w-0 flex-1 text-[14px] font-medium text-ink-900 hover:text-brand-700"
                      >
                        {i.title ?? <span className="italic text-ink-500">No readable record</span>}{' '}
                        <span className="text-ink-400">↗</span>
                      </a>
                    )}
                    <span className="tabular shrink-0 text-[12px] text-ink-500">{i.date ?? i.sort ?? 's.d.'}</span>
                  </div>
                  <p className="mt-1 text-[12px] text-ink-500">
                    {[
                      i.id,
                      i.creator || i.recipient
                        ? [name(i.creator), name(i.recipient)].filter(Boolean).join(' → ')
                        : null,
                      i.pages ? `${i.pages} p.` : null,
                    ]
                      .filter(Boolean)
                      .join(' · ')}
                  </p>
                  {ITEM_NOTES[i.id] && <p className="mt-1.5 text-[12.5px] leading-relaxed text-alerte-700">{ITEM_NOTES[i.id]}</p>}
                </li>
              ))}
            </ul>
          </section>
        ))}

        <p className="mt-10 text-[12px] text-ink-400">
          Fonds Grothendieck–Illusie, Institut des Hautes Études Scientifiques. Inventory read from the item
          records at {INV.source} on {INV.built}
          {INV.unreadable.length ? `; ${INV.unreadable.length} items have no readable record and are listed by shelfmark` : ''}.
        </p>
      </main>
      <Footer collection="illusie" />
      </div>
    </>
  );
}
