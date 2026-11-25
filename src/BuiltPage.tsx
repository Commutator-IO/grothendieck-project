import { Articles, STARS, type ArticleItem } from './components/Articles.tsx';
import { H2, P } from './components/Anchors.tsx';
import { Footer, Header } from './components/Frame.tsx';
import { NUMDAM, Where, linkCls } from './components/Where.tsx';

/**
 * Built with Lean: the Lean proofs of the archives, and the papers about them.
 *
 * It follows the presentation of « Built with Stacks » (stacks.axiommath.ai/built): a picture
 * of the code as a city, what it is, how big it is and what it draws on, and its links. The
 * city and the treemap are a static page, /built/map/ (docs/archives-map), drawn from the
 * declarations of GrothendieckArchivesProofs. The papers that rest on the Lean proofs or on their statements, which the Method page used to
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
    more: [{ label: 'Hexagon', href: 'https://hexagonmath.org/pdf/2611.00125v3' }],
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
  {
    id: 'article-problems',
    title: "Open Questions from Grothendieck's Montpellier Notes: Thirteen Statements a Formalisation Could Not Reach",
    lang: 'English',
    what: 'Statements from the folders that the formalisation could not settle, each with its page, the context, what the literature search found, the ideas of proof, and what would settle it.',
    pdf: '/article/grothendieck-problems.pdf',
    more: [{ label: 'Hexagon (part II)', href: 'https://hexagonmath.org/pdf/2611.00125v3' }],
    src: 'docs/problems/article.tex',
  },
];

/** Standalone papers deposited, or being deposited, as preprints (Hexagon). */
const PREPRINTS: ArticleItem[] = [
  {
    id: 'article-kostant',
    title: "Kostant's tori in apposition: the Borel subgroups are opposite, and there is no distinguished class in type A_2l",
    lang: 'English',
    what: "Grothendieck's letter to Kostant of 22 October 1969 asks two questions on quadruples (T, B, T', B') with T, T' maximal tori in apposition. Are B and B' in general position? Yes, in every type: all |W| Borel subgroups through the centraliser of a cyclic element are opposite to B, a short consequence of Kostant (1959) and of a lemma of Bălibanu (2023), given in full and formalised in Lean 4 for the flag forms of the classical types. Is there a distinguished class, invariant under the exterior automorphisms? Not in type A_2l, where the exterior automorphism fixes no class; elsewhere a construction with the Coxeter plane gives a canonical pair of classes, exchanged by the sign of the lowest root vector, and computations list the invariant classes up to A_6 and D_5.",
    pdf: '/article/grothendieck-kostant.pdf',
    more: [
      { label: 'Hexagon', href: 'https://hexagonmath.org/2611.01016v1' },
      { label: 'Note de lecture (fr)', href: '/article/grothendieck-kostant-note-fr.pdf' },
    ],
    src: 'docs/kostant/article.tex',
  },
  {
    id: 'article-effective',
    title: "Non-effective finite equivalence relations on finite schemes over a field: Venken's example checked, and a second one",
    lang: 'English',
    what: "The problem he gave at Buffalo on 11 July 1973, first asked in FGA (1961): is every finite equivalence relation on a finite scheme over a field effective? No: Venken had answered it in 1971, in a corollary of a note on flat descent (a local Artin algebra of dimension 33). The note checks his example by machine and gives a second one, of length 15 (16 in characteristic 2) in two variables, from Raicu's relation on the plane, certified over every field.",
    pdf: '/article/grothendieck-effective.pdf',
    src: 'docs/effective/article.tex',
    more: [
      { label: 'Hexagon', href: 'https://hexagonmath.org/2611.01019v1' },
      { label: 'Note de lecture (fr)', href: '/article/grothendieck-effective-note-fr.pdf' },
    ],
  },
  {
    id: 'article-bigon',
    title: 'A bigon-free dichotomy for pseudoline arrangements, after a note of Grothendieck',
    lang: 'English',
    what: 'Folder 80: every arrangement of pseudolines without bigonal pseudolines is four lines in general position or contains II₅, II′₃,₂ or the complete quadrangle. A proof, the ordering of page 28, the near-pencils as the only arrangements avoiding the three, a counterexample to page 24 as written, an enumeration up to nine pseudolines, and the Lean proof.',
    pdf: '/article/grothendieck-bigon.pdf',
    more: [
      { label: 'Hexagon', href: 'https://hexagonmath.org/pdf/2611.00188v2' },
      { label: 'Lean', href: 'https://github.com/Commutator-IO/GrothendieckArchivesProofs' },
      { label: 'Note de lecture (fr)', href: '/article/grothendieck-bigon-note-fr.pdf' },
    ],
    src: 'docs/bigon/article.tex',
  },
  {
    id: 'article-tangent',
    title: 'The tangent line at a marked point on M₀,ₙ/𝔖ₙ₋₁, after a table of Grothendieck',
    lang: 'English',
    what: 'Folder 146: the Picard group of [M₀,ₙ/𝔖ₙ₋₁] is cyclic of order (n − 1)(n − 2), generated by the tangent line at the marked point, for every n; the table of page 70 completed. The odd case does not seem to be in print.',
    pdf: '/article/grothendieck-tangent.pdf',
    more: [
      { label: 'Hexagon', href: 'https://hexagonmath.org/pdf/2611.00189v2' },
      { label: 'Note de lecture (fr)', href: '/article/grothendieck-tangent-note-fr.pdf' },
    ],
    src: 'docs/tangent/article.tex',
  },
];

/** Single results of the edition, each written up as a standalone paper. */
const DRAFTS: ArticleItem[] = [
  {
    id: 'reading-2',
    title: 'Riemann–Roch : notes antiques (avant 1958) — lecture modernisée',
    lang: 'French',
    what: 'Modernised reading of folder 2, among those that shed the most light on chaotic notes. Forty-four pages of scattered computations, the most disordered of the early folders, read as one story: the number (−1)^{i−1}(i−1)! that the pages keep meeting, and the Riemann–Roch theorem around it. The reading is nearly three times as long as the transcription: it reconstructs what the leaves only sketch.',
    pdf: '/transcripts/2/2.modern.pdf',
    src: 'transcripts/2/2.modern.tex',
  },
  {
    id: 'reading-159',
    title: 'Connexions projectives et uniformisation — lecture modernisée',
    lang: 'French',
    what: 'Modernised reading of folder 159, among those that shed the most light on chaotic notes. Short, gappy notes rebuilt into a coherent account of projective structures on a surface and uniformisation, from charts and changes of charts up. Nearly three times the length of the transcription.',
    pdf: '/transcripts/159/159.modern.pdf',
    src: 'transcripts/159/159.modern.tex',
  },
  {
    id: 'reading-1',
    title: 'Analyse fonctionnelle (1953) — lecture modernisée',
    lang: 'French',
    what: 'Modernised reading of folder 1, among those that shed the most light on chaotic notes. The most disordered folder of the fonds (about thirty unread, doubtful or struck marks per hundred words), read as one idea: the sequence of singular values of an operator under sums and products, with 148 footnotes carrying the apparatus. Re-read against the facsimile in November 2026.',
    pdf: '/transcripts/1/1.modern.pdf',
    src: 'transcripts/1/1.modern.tex',
  },
  {
    id: 'reading-126',
    title: 'Descente fidèlement plate. Divers — lecture modernisée',
    lang: 'French',
    what: 'Modernised reading of folder 126, among those that shed the most light on chaotic notes. Scattered leaves on descent brought back to a single question, when an object built after an extension comes from one defined before it, starting from complex conjugation.',
    pdf: '/transcripts/126/126.modern.pdf',
    src: 'transcripts/126/126.modern.tex',
  },
  {
    id: 'reading-58',
    title: 'Théorie de « Lefschetz–Grauert » — lecture modernisée',
    lang: 'French',
    what: 'Modernised reading of folder 58, among those that shed the most light on chaotic notes. Sixty-six heavily corrected pages read as one question: what a hyperplane section keeps of the topology of the variety, in π₁ and Pic.',
    pdf: '/transcripts/58/58.modern.pdf',
    src: 'transcripts/58/58.modern.tex',
  },
  {
    id: 'reading-33',
    title: 'SGA 1965, brouillon — lecture modernisée',
    lang: 'French',
    what: 'Modernised reading of folder 33, among those that shed the most light on chaotic notes. A seminar draft written on the back of unrelated typescripts, a hundred and eighty pages from which the reading extracts the formalism of étale cohomology, built almost entirely though its announced pretext, L-functions, is never reached.',
    pdf: '/transcripts/33/33.modern.pdf',
    src: 'transcripts/33/33.modern.tex',
  },
  {
    id: 'article-buffalo-open',
    title: "The open problems of Grothendieck's 1973 Buffalo lectures, and what became of them",
    lang: 'English',
    what: 'The questions, conjectures and problems he states in the topos, algebraic geometry and group-scheme courses, each with its second in the recordings and its status today: most settled, several against his expectation (presheaf topoi, f^!, descent of non-quasi-compact immersions, colimits of accessible categories), one by Perrin in 1976, one independent of ZFC; algebraic theories over a fixed base still look open.',
    pdf: '/article/grothendieck-buffalo-open.pdf',
    src: 'docs/buffalo-open/article.tex',
  },
  {
    id: 'article-qcoh-descent',
    title: 'Descent of quasi-coherent sheaves along universal effective epimorphisms of schemes',
    lang: 'English',
    what: "His question at Buffalo on 11 July 1973: do quasi-coherent sheaves descend along the universal effective epimorphisms, the coverings of the canonical topology, and is pulling them back at least fully faithful? Pulling back is fully faithful along all of them, with no quasi-compactness; descent is effective along the quasi-compact ones (Mesablishvili; an independent proof here); and if some ultrafilter on the primes is generated by ℵ₁ sets, as under CH, the Stacks Project's covering of Spec ℤ carries a non-effective datum, so quasi-coherent sheaves are not a stack for the canonical topology. The ZFC case stays open.",
    pdf: '/article/grothendieck-qcoh-descent.pdf',
    src: 'docs/qcoh-descent/article.tex',
    more: [{ label: 'Note de lecture (fr)', href: '/article/grothendieck-qcoh-descent-note-fr.pdf' }],
  },
  {
    id: 'article-problem-three',
    title: "Grothendieck's « problem three »: generation under limits and algebraic theories relative to a class of limits",
    lang: 'English',
    what: "His question at Buffalo on 2 July 1973: for a class D of limits and colimits, is a theory basic over a set I exactly when I generates it under D-limits and D-colimits? Basic implies generation for every D; basic is equivalent to generation plus algebraicity over some base; the two coincide for small D and for Grothendieck topoi. For all small limits the converse fails: {2} generates Set in two steps, checked in Lean, but Set is not algebraic, and an example of Adámek and Rosický shows that the number of steps is unbounded in general. Finite limits with all colimits stay open.",
    pdf: '/article/grothendieck-problem-three.pdf',
    src: 'docs/problem-three/article.tex',
    more: [{ label: 'Note de lecture (fr)', href: '/article/grothendieck-problem-three-note-fr.pdf' }],
  },
  {
    id: 'article-loday-filtration',
    title: 'The rank filtration on the n-cycles of the symmetric group algebra: Loday’s filtration conjecture in a notebook of Quillen',
    lang: 'English',
    what: 'Draft, under review: in notebook 1983-6 (21 July 1983) Quillen writes the vanishing of the rank filtration F_i k(U_n) for i ≤ n/2 as the form of a conjecture of Loday. Exact computation for n ≤ 8: it holds for 2i < n, and fails at n = 6, i = 3 (dimension 15, with an explicit sum of 36 six-cycles) and at n = 8, i = 4 (dimension 1708). On our reading, the Amitsur–Levitzki argument of Loday–Quillen 1984, §6.14, proves the vanishing for the annihilator filtration, not the rank filtration; this needs a specialist’s check. The homological statement is not touched.',
    pdf: '/article/grothendieck-loday-filtration.pdf',
    src: 'docs/loday-filtration/article.tex',
    more: [{ label: 'Note de lecture (fr)', href: '/article/grothendieck-loday-filtration-note-fr.pdf' }],
  },
  {
    id: 'article-polytopes',
    title: "Regular polytopes realised over arbitrary rings, after Grothendieck's working notes",
    lang: 'English',
    what: 'Folders 70, 72, 78 and 86, behind §4 of the Esquisse: regular polygons over a ring and the 2p-gons of characteristic p, the universal formulae in any dimension, pinned realisations by pseudo-reflections over a base, the icosahedron over ℤ[α] faithful in every characteristic and its conic modulo 5, the five trihedra and the hemi-icosahedron.',
    pdf: '/article/grothendieck-polytopes.pdf',
    src: 'docs/polytopes/article.tex',
    more: [{ label: 'Note de lecture (fr)', href: '/article/grothendieck-polytopes-note-fr.pdf' }],
  },
  {
    id: 'article-moduli',
    title: 'Small moduli problems over Spec ℤ: quadratic algebras, rotations in PGL₂ and the integral Schwarzian',
    lang: 'English',
    what: 'Folders 84, 83, 85, 64 and 93: quadratic algebras classified by triples when 2 is regular and their product, the line of twists and its Azumaya criterion in every characteristic, the orders of rotations in forms of PGL₂ and the string group G₂, the octahedral configuration in characteristic 5, and the Schwarzian with divided derivatives, rigid at level p only for p > 3.',
    pdf: '/article/grothendieck-moduli.pdf',
    src: 'docs/moduli/article.tex',
    more: [{ label: 'Note de lecture (fr)', href: '/article/grothendieck-moduli-note-fr.pdf' }],
  },
  {
    id: 'article-bridges',
    title: 'Topos-theoretic bridges as a theorem generator',
    lang: 'English and French',
    what: "Draft. O. Caramello's « bridges » read one invariant of a topos on two of its presentations, and her Mines talk (2024) proposes to generate theorems by combining a database of topos equivalences with a database of such readings. This text runs a small generator by hand and describes it as a software pipeline (registries, join, specialise, unfold, rewrite, verify in Lean and by hand, novelty filter), with five bridges proved in Lean in lean-pool as arches.",
    pdf: '/article/grothendieck-bridges.pdf',
    src: 'docs/bridges/article.tex',
    more: [{ label: 'Version française', href: '/article/grothendieck-bridges-fr.pdf' }],
  },
  {
    id: 'article-bridges-notes',
    title: "Bridges in Grothendieck's notes",
    lang: 'English and French',
    what: "Draft, companion to the previous one. Three more arches (two-valued, connected, presheaves on a preorder), proved in Lean and read on the decks of Grothendieck's notes; his own bridges in folders 161-3 (an exercise, proved in Lean), 37 and 161-2 (sub-theories and subtopoi); the topos of pseudo-fields with his three presentations, one of them checked, and the answer to his question on points (Makkai–Reyes); and the link with stacks, with the Picard group of [M₀,ₙ/𝔖ₙ₋₁] from folder 146 as a finer arch.",
    pdf: '/article/grothendieck-bridges-notes.pdf',
    src: 'docs/bridges/notes.tex',
    more: [{ label: 'Version française', href: '/article/grothendieck-bridges-notes-fr.pdf' }],
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
              About 159,000 lines of Lean in 448 files, drawing on 151 modules of the Stacks library.
            </p>
            <p className="mt-3 flex flex-wrap gap-x-5 gap-y-1 text-[13.5px]">
              <a href="/built/map/?layout=city&links=1" className={link}>See it in the city &rarr;</a>
              <a href="/built/map/" className={link}>Browse the treemap &rarr;</a>
              <a href="/article/grothendieck-lean.pdf" className={link}>Article &#8599;</a>
              <a href="https://github.com/Commutator-IO/GrothendieckArchivesProofs" className={link}>Lean code &#8599;</a>
            </p>
          </div>
        </section>

        <Articles id="articles" title="The articles" items={[...LEAN_ARTICLES].sort((x, y) => (STARS[y.id] ?? 0) - (STARS[x.id] ?? 0))} />
        <Articles id="preprints" title="Preprints" titlesOnly items={[...PREPRINTS].sort((x, y) => (STARS[y.id] ?? 0) - (STARS[x.id] ?? 0))} />
        <Articles id="drafts" title="Drafts" items={[...DRAFTS].sort((x, y) => (STARS[y.id] ?? 0) - (STARS[x.id] ?? 0))} />
        <p className="mt-2 text-[12.5px] text-ink-500">
          Stars give our estimate of each draft's interest, from ★ to ★★★: what it adds that is new or solid, not how finished it is
        </p>

        <section className="mt-16 max-w-[48em] text-[15px] leading-relaxed text-ink-700">
          <H2 id="reading-ega-sga">Reading EGA and SGA</H2>
          <P id="reading-ega-sga-why" className="mt-3">
            The notes assume EGA and SGA throughout. Nobody reads them cover to cover: they are references, read by chapters,
            with a modern companion open alongside, Vakil&rsquo;s <em>The Rising Sea</em>
            <Where online={[['online', 'https://math.stanford.edu/~vakil/216blog/']]} /> or Hartshorne II&ndash;III
            <Where ihp="Algebraic geometry Robin Hartshorne" />, and the Stacks Project
            <Where online={[['online', 'https://stacks.math.columbia.edu/']]} />, which cross-references EGA numbering. For the
            homology that SGA&nbsp;4 and SGA&nbsp;5 take for granted, Hatcher&rsquo;s <em>Algebraic Topology</em>, chapters 2&ndash;3, is
            an easy way in <Where online={[['online', 'https://pi.math.cornell.edu/~hatcher/AT/ATpage.html']]} ihp="Hatcher Algebraic topology" />.
            The section and exposé numbers below were checked against the volumes (Numdam for EGA, the Springer editions for SGA)
            on 1 November 2026.
          </P>
          <p className="mt-2 text-[12.5px] text-ink-500">
            « online » links go to a free legal copy (Numdam, arXiv, the authors&rsquo; pages); « IHP » opens a search of the
            Sorbonne Université catalogue, which lists the holdings of the Institut Henri Poincaré library
            (<a href="https://www.ihp.fr/fr/bibliotheque" className={linkCls}>ihp.fr/bibliotheque</a>); choose the IHP copy in the
            availability list to consult it there.
          </p>
          <ol className="mt-3 list-decimal space-y-1.5 pl-6">
            <li>
              <b>EGA I</b> (2nd ed., 1971): chapter I, chapter 0 as needed
              <Where online={[['1st ed., Numdam', NUMDAM('PMIHES_1960__4__5_0')]]} ihp="Éléments de géométrie algébrique Grothendieck Dieudonné" />.{' '}
              <b>EGA II</b>: §&nbsp;1 affine morphisms, §§&nbsp;2&ndash;4 Proj and
              ample sheaves, §§&nbsp;5&ndash;7 proper, finite, valuative criteria
              <Where online={[['Numdam', NUMDAM('PMIHES_1961__8__5_0')]]} ihp="Éléments de géométrie algébrique II étude globale élémentaire" />.
            </li>
            <li>
              <b>EGA III</b> §§&nbsp;1&ndash;4: cohomology of affine and projective morphisms, finiteness and formal functions; §&nbsp;5 for
              formal geometry
              <Where online={[['Numdam, part 1', NUMDAM('PMIHES_1961__11__5_0')], ['part 2', NUMDAM('PMIHES_1963__17__5_0')]]} ihp="Éléments de géométrie algébrique III étude cohomologique des faisceaux cohérents" />.
            </li>
            <li>
              <b>EGA IV</b> by topic: §§&nbsp;2, 11, 12 flatness and descent; §§&nbsp;5&ndash;6 dimension, depth, regularity; §&nbsp;8 limits;
              §§&nbsp;17&ndash;18 smooth, unramified and étale morphisms, the most used
              <Where
                online={[
                  ['Numdam, part 1', NUMDAM('PMIHES_1964__20__5_0')],
                  ['2', NUMDAM('PMIHES_1965__24__5_0')],
                  ['3', NUMDAM('PMIHES_1966__28__5_0')],
                  ['4', NUMDAM('PMIHES_1967__32__5_0')],
                ]}
                ihp="Éléments de géométrie algébrique IV étude locale des schémas"
              />.
            </li>
            <li>
              <b>SGA&nbsp;1</b> (étale morphisms, π₁, descent)
              <Where online={[['arXiv', 'https://arxiv.org/abs/math/0206203']]} ihp="Revêtements étales et groupe fondamental SGA 1" />, then{' '}
              <b>SGA&nbsp;4½</b> <Where ihp="Cohomologie étale SGA 4 1/2 Deligne" /> before <b>SGA&nbsp;4</b> (topoi I&ndash;IV, étale
              cohomology VII&ndash;IX, base change XII&ndash;XIII and XVI, duality XVIII)
              <Where ihp="Théorie des topos et cohomologie étale des schémas" />, then <b>SGA&nbsp;5</b>
              <Where ihp="Cohomologie l-adique et fonctions L SGA 5" />; by topic <b>SGA&nbsp;3</b> (group schemes)
              <Where online={[['new ed., online', 'https://webusers.imj-prg.fr/~patrick.polo/SGA3/']]} ihp="Schémas en groupes SGA 3" />,{' '}
              <b>SGA&nbsp;6</b> (Riemann&ndash;Roch) <Where ihp="Théorie des intersections et théorème de Riemann-Roch SGA 6" />,{' '}
              <b>SGA&nbsp;7</b> (monodromy) <Where ihp="Groupes de monodromie en géométrie algébrique SGA 7" />, <b>SGA&nbsp;2</b> (local
              cohomology) <Where online={[['arXiv', 'https://arxiv.org/abs/math/0511279']]} ihp="Cohomologie locale des faisceaux cohérents et théorèmes de Lefschetz SGA 2" />.
            </li>
          </ol>
          <P id="reading-ega-sga-shortest" className="mt-3">
            The shortest path to the notes is EGA&nbsp;I, then EGA&nbsp;IV §§&nbsp;17&ndash;18, then SGA&nbsp;1. The 1992 <em>Géométrie
            élémentaire schématique</em> at the BnF belongs next to EGA&nbsp;IV §&nbsp;18 and the never-published §&nbsp;24 of the 1965 plan
            (smooth forms and ordinary quadratic singularities, Montpellier folder&nbsp;25, p.&nbsp;134), with SGA&nbsp;3 for orthogonal group
            schemes.
          </P>
        </section>
      </main>

      <Footer />
    </>
  );
}
