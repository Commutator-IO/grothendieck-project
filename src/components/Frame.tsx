import { useEffect, useState } from 'react';
import { BOOKS } from '../content/books.ts';
import { warmRelay } from '../lib/batches.ts';

/**
 * Header and footer, shared by every page.
 *
 * Hosting is static, so each tab is a real document rather than a client-side
 * route. A URL opened on one batch still works months later, which matters when
 * transcription stretches over months.
 */

const OTHER_PAGES: { path: string; label: string }[] = [
  { path: '/archive/', label: 'Whole fonds' },
  { path: '/method/', label: 'Method & progress' },
  { path: '/contribute/', label: 'Contribute' },
];

function isCurrent(path: string, here: string): boolean {
  const h = here.endsWith('/') ? here : `${here}/`;
  return path === h;
}

export function Header({ path }: { path: string }) {
  const [open, setOpen] = useState(false);

  // Every page carries this header, and any of them may lead to a batch being
  // opened — so this is the one place that reaches every reader early enough
  // to matter. See warmRelay's own comment for why.
  useEffect(() => {
    warmRelay();
  }, []);

  // Escape closes the folded-out menu. On a tablet it opens by tap rather than
  // hover, so without this there is no way out of it.
  useEffect(() => {
    if (!open) return;
    const onKey = (e: KeyboardEvent) => e.key === 'Escape' && setOpen(false);
    document.addEventListener('keydown', onKey);
    return () => document.removeEventListener('keydown', onKey);
  }, [open]);

  // The folded-out menu has room for the full titles; only the inline row is
  // short of space.
  const links = [...BOOKS.map((b) => ({ path: b.path, label: b.title })), ...OTHER_PAGES];

  return (
    <header className="sticky top-0 z-40 border-b border-ink-200 bg-white/93 backdrop-blur-md backdrop-saturate-150">
      <div className="mx-auto flex max-w-6xl items-center gap-4 px-5 py-2.5">
        <a href="/" className="flex min-w-0 items-center gap-2.5">
          <Mark />
          <span className="min-w-0 truncate text-[13px] font-semibold tracking-tight text-ink-900">
            Grothendieck Archives
          </span>
        </a>

        <nav className="ml-auto hidden items-center gap-0.5 text-[13px] text-ink-500 lg:flex">
          {BOOKS.map((b) => (
            <a
              key={b.path}
              href={b.path}
              aria-current={isCurrent(b.path, path) ? 'page' : undefined}
              className={`rounded-lg px-2.5 py-1.5 transition ${
                isCurrent(b.path, path)
                  ? 'font-semibold text-ink-900'
                  : 'hover:bg-ink-50 hover:text-brand-700'
              }`}
            >
              {b.navTitle ?? b.title}
            </a>
          ))}
          <span aria-hidden="true" className="mx-1.5 h-4 w-px bg-ink-200" />
          {OTHER_PAGES.map((p) => (
            <a
              key={p.path}
              href={p.path}
              aria-current={isCurrent(p.path, path) ? 'page' : undefined}
              className={`rounded-lg px-2.5 py-1.5 transition ${
                isCurrent(p.path, path)
                  ? 'font-semibold text-ink-900'
                  : 'hover:bg-ink-50 hover:text-brand-700'
              }`}
            >
              {p.label}
            </a>
          ))}
        </nav>

        <button
          type="button"
          onClick={() => setOpen(!open)}
          aria-expanded={open}
          className="ml-auto rounded-lg border border-ink-200 px-2.5 py-1 text-[12px] font-medium text-ink-600 lg:hidden"
        >
          {open ? 'Close' : 'Menu'}
        </button>
      </div>

      {open && (
        <nav className="border-t border-ink-200 bg-white px-5 py-2 lg:hidden">
          {links.map((p) => (
            <a
              key={p.path}
              href={p.path}
              className="block rounded-lg px-2 py-2 text-[14px] text-ink-700 hover:bg-ink-50"
            >
              {p.label}
            </a>
          ))}
        </nav>
      )}
    </header>
  );
}

/**
 * The mark: a sheet and its verso.
 *
 * The fonds turns on that duality — Grothendieck reused his versos, and the
 * digitisation kept them. It is the first thing one learns on opening a
 * folder, so it may as well be the first thing one sees.
 */
function Mark() {
  return (
    <svg viewBox="0 0 24 24" className="h-6 w-6 shrink-0 text-brand-600" aria-hidden="true" fill="none">
      <rect x="3" y="2.5" width="12" height="17" rx="1.5" className="fill-brand-100 stroke-current" strokeWidth="1.3" />
      <rect x="9" y="4.5" width="12" height="17" rx="1.5" className="fill-white stroke-current" strokeWidth="1.3" />
      <path d="M11.5 9h7M11.5 12h7M11.5 15h4.5" className="stroke-current" strokeWidth="1.1" strokeLinecap="round" opacity="0.55" />
    </svg>
  );
}

export function Footer() {
  return (
    <footer className="mt-16 border-t border-ink-200 bg-white">
      <div className="mx-auto max-w-6xl px-5 py-8 text-[12.5px] leading-relaxed text-ink-500">
        <p className="max-w-[52em]">
          Facsimiles come from the{' '}
          <strong className="font-semibold text-ink-700">Alexandre Grothendieck fonds</strong> at
          the University of Montpellier, given by Jean Malgoire and catalogued in 2015–2016 by
          Hélène Rodriguez and Frédéric Troilo under the direction of Sophie Dikoff. Of the fonds'
          some 28,000 pages, about 18,000 may be circulated: third-party correspondence cannot be,
          without permission.
        </p>
        <p className="mt-3 max-w-[52em]">
          This site neither hosts nor redistributes the fonds. It gives the inventory, and reads
          the files one has downloaded from Montpellier oneself.
        </p>
        <p className="mt-4">
          <a
            href="https://grothendieck.umontpellier.fr/"
            target="_blank"
            rel="noopener noreferrer"
            className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
          >
            grothendieck.umontpellier.fr ↗
          </a>
        </p>
      </div>
    </footer>
  );
}
