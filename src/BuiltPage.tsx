import { Articles, type ArticleItem } from './components/Articles.tsx';
import { Footer, Header } from './components/Frame.tsx';

/**
 * Built with Lean: the Lean proofs of the archives, and the papers about them.
 *
 * It follows the presentation of « Built with Stacks » (stacks.axiommath.ai/built): a picture
 * of the code as a city, what it is, how big it is and what it draws on, and its links. The
 * city and the treemap are a static page, /built/map/ (docs/archives-map), drawn from the
 * declarations of GrothendieckArchivesProofs. The Lean papers, which the Method page used to
 * list, are below.
 */
const LEAN_ARTICLES: ArticleItem[] = [
  {
    id: 'article-cicm',
    title: "Formalising a Mathematician's Working Notes: Lean Proofs from the Grothendieck Archive",
    lang: 'English',
    what: 'Prepared for the Conference on Intelligent Computer Mathematics: how statements of the readings are chosen, formalised and attributed, what the proofs found, and where the general lemmas went (Lean Pool).',
    pdf: '/article/grothendieck-cicm.pdf',
    src: 'docs/cicm/article.tex',
  },
  {
    id: 'article-lean',
    title: 'Annexe. Énoncés des lectures modernisées démontrés',
    lang: 'French',
    what: 'For each folder proved in Lean: the leaf in context, the statement as the reading has it, a proof written out for a mathematician, and what is not proved. In the chronological order of the fonds’ themes.',
    pdf: '/article/grothendieck-lean.pdf',
    more: [{ label: 'Hexagon', href: 'https://hexagonmath.org/2611.00125v1' }],
    src: 'docs/lean/article.tex',
  },
  {
    id: 'article-quillen-lean',
    title: "Daniel Quillen's Notebooks: Statements Proved in Lean",
    lang: 'English',
    what: "One hundred and twenty statements from Quillen's research notebooks (Clay Mathematics Institute), from general topology and linear algebra to representation theory, commutative algebra and theta functions, proved in Lean and written out without it. All one hundred and ten hold in the form proved; several under weaker hypotheses than the page's, one fails for p = 2, one needs 2 to be cancellable, and four come from his notes of lectures. The notebooks are in copyright: everything is stated in the paper's own words, with notebook and page.",
    pdf: '/article/quillen-lean.pdf',
    src: 'docs/quillen-lean/article.tex',
  },
];

const link = 'font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700';

export function BuiltPage() {
  return (
    <>
      <Header path="/built/" />

      <main className="mx-auto max-w-6xl px-5 py-10">
        <header className="max-w-[46em]">
          <h1 className="titre text-[34px] leading-tight text-ink-900">Built with Lean</h1>
          <p className="mt-3 text-[15.5px] leading-relaxed text-ink-700">
            Lean proofs of statements from the archives, built on Mathlib and the Stacks library.
          </p>
        </header>

        <section className="mt-8 grid items-start gap-6 border-t border-ink-200 pt-8 md:grid-cols-[minmax(0,5fr)_minmax(0,7fr)]">
          <a href="/built/map/?layout=city&links=1" aria-label="See the code as a city">
            <img
              src="/built/city.webp"
              width={1000}
              height={520}
              alt="The declarations of GrothendieckArchivesProofs as a city, with the Stacks modules they import in a grey district and a line for each import"
              className="w-full rounded-lg border border-ink-200"
            />
          </a>
          <div>
            <h2 className="titre text-[24px] leading-snug text-ink-900">Grothendieck Archives Proofs</h2>
            <p className="mt-3 text-[15.5px] leading-relaxed text-ink-800">
              The statements of the modernised readings of the Montpellier notes, and of the
              lectures Grothendieck gave at Buffalo in 1973, proved in Lean 4 against Mathlib, with
              the open problems of both stated as propositions.
            </p>
            <p className="mt-3 text-[13px] leading-relaxed text-ink-500">
              About 159,000 lines of Lean in 496 files, drawing on 172 modules of the Stacks library.
            </p>
            <p className="mt-3 flex flex-wrap gap-x-5 gap-y-1 text-[13.5px]">
              <a href="/built/map/?layout=city&links=1" className={link}>See it in the city &rarr;</a>
              <a href="/built/map/" className={link}>Browse the treemap &rarr;</a>
              <a href="/article/grothendieck-lean.pdf" className={link}>Article &#8599;</a>
              <a href="https://github.com/Commutator-IO/GrothendieckArchivesProofs" className={link}>Lean code &#8599;</a>
            </p>
          </div>
        </section>

        <Articles id="articles" title="The articles" items={LEAN_ARTICLES} />
      </main>

      <Footer />
    </>
  );
}
