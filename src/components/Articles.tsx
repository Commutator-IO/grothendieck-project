import { H2 } from './Anchors.tsx';

/** A paper of the edition, as the Method and Built pages list it. */
export type ArticleItem = { id: string; title: string; lang: string; what: string; pdf: string; src: string; tei?: string; more?: { label: string; href: string }[] };

/** Interest of each article, from 1 to 3 stars. */
export const STARS: Record<string, 1 | 2 | 3> = {
  'reading-2': 3,
  'reading-159': 3,
  'reading-1': 3,
  'reading-126': 2,
  'reading-58': 2,
  'reading-33': 2,
  'article-effective': 3,
  'article-loday-filtration': 2,
  'article-buffalo-open': 2,
  'article-qcoh-descent': 2,
  'article-problem-three': 2,
  'article-kostant': 3,
  'article-bridges': 2,
  'article-bridges-notes': 2,
  'article-polytopes': 2,
  'article-moduli': 2,
  'article-quillen-lean': 2,
  'article-recollement': 1,
  'article-tangent': 3,
  'article-lean': 3,
  'article-problems': 3,
  'article': 2,
  'article-cicm': 2,
  'article-rhm': 2,
  'article-carbon': 1,
  'article-bigon': 2,
};

export function Articles({ id = 'articles', title = 'The articles', items }: { id?: string; title?: string; items: ArticleItem[] }) {
  const pill = 'rounded-full border border-ink-200 px-3 py-0.5 text-[12.5px] text-ink-700 transition hover:border-brand-400 hover:text-brand-700';
  return (
    <section className="mt-10">
      <H2 id={id}>{title}</H2>
      <div className="mt-4 grid gap-4 md:grid-cols-2">
        {items.map((a) => (
          <article key={a.id} id={a.id} className="card flex scroll-mt-20 flex-col px-5 py-4">
            <p className="text-[11px] font-semibold uppercase tracking-[0.08em] text-ink-400">{a.lang}</p>
            <h3 className="mt-1 text-[15px] font-semibold italic leading-snug text-ink-900">
              {a.title}
              {STARS[a.id] && (
                <span
                  className="ml-2 whitespace-nowrap not-italic tracking-[0.1em] text-amber-500"
                  title={`Interest: ${STARS[a.id]} of 3`}
                  aria-label={`Interest: ${STARS[a.id]} of 3`}
                >
                  {'★'.repeat(STARS[a.id])}
                  <span className="text-ink-200">{'★'.repeat(3 - STARS[a.id])}</span>
                </span>
              )}
            </h3>
            <p className="mt-2 flex-1 text-[13px] leading-relaxed text-ink-600">{a.what}</p>
            <p className="mt-3 flex flex-wrap items-center gap-2">
              <a href={a.pdf} className={pill}>
                PDF
              </a>
              {a.more?.map((m) => (
                <a key={m.href} href={m.href} className={pill}>
                  {m.label}
                </a>
              ))}
              {a.tei && (
                <a href={a.tei} className={pill} title="The submission file, valid against the journal's tei_jtei schema">
                  TEI
                </a>
              )}
              <code className="ml-auto text-[11px] text-ink-400">{a.src}</code>
            </p>
          </article>
        ))}
      </div>
    </section>
  );
}

