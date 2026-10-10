import type { Finding } from '../lib/types.ts';

/**
 * Candidate findings, written by `/find-novelty` and rendered by the
 * Findings tab.
 *
 * Kept as data rather than prose because every one of these is a claim with a
 * status, and prose hides a status. The rule the skill enforces, and the
 * reason the shape has a `literature` field at all: a novelty is a claim about
 * the *literature*, never about Grothendieck. Nothing here says who was first.
 * Almost nothing in the fonds is dated — « [vers 1963-1973] » is an archivist's
 * guess from a verso — so precedence is not a claim this project is in a
 * position to make, about anyone.
 *
 * `matched` entries are kept, not deleted. A candidate that turned out to be
 * in the books is the most useful row on the page: it stops the next reader
 * spending a day on it, and it is the evidence that this list is pruned rather
 * than grown.
 */
export const FINDINGS: Finding[] = [
  {
    id: '161-3-product-converse',
    cote: '161-3',
    pages: '10–11',
    kind: 'mathematical',
    claim:
      'Top(X × Y) → Top(X) × Top(Y) is an equivalence under a hypothesis weaker than local compactness: that every non-empty locally closed subset of X has a point with a relatively quasi-compact neighbourhood in it.',
    basis:
      'Page 10 proves the sufficient direction by the tube lemma, then argues the converse by maximality — taking the largest open U′ with S ≥ U′ × V and deriving a contradiction from a point of U \\ U′ having a quasi-compact relative neighbourhood.',
    ours:
      'The reading supplies one step the page omits: the inclusion U″ ⊂ U′ ∪ ⋃_{i∈I_y} U_i, without which the contradiction does not follow. The hypothesis is the page’s; that link in the argument is the edition’s.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check whether this dévissage hypothesis, rather than local or core-compactness, appears in Johnstone (Stone Spaces II.4, Elephant C1.1 and C4.1) or in Isbell’s papers on locale products. If it is there, mark matched. An external review of the folder (Kimi, shared conversation of 2026-08) singles this proof out as one of the folder’s three strongest items and reports finding no such self-contained argument in the standard texts. That is a reason to search, not a search: the status stays unsearched until someone reads Johnstone with the page open.',
  },
  {
    id: '161-3-infinite-product-criterion',
    cote: '161-3',
    pages: '11–12',
    kind: 'mathematical',
    claim:
      'For an arbitrary family, Top(∏ Xᵢ) → ∏ Top(Xᵢ) is an equivalence when all but at most one factor have fundamental systems of quasi-compact neighbourhoods and all but at most one are quasi-compact — two separate "all but one" clauses.',
    basis:
      'Pages 11 and 12 run the finite argument over the restricted product ∏′ O_{Xᵢ} and the filtered union I = colim J_α, using quasi-compactness of the complementary factor to refine each cover on a finite J_β.',
    ours: null,
    literature: [],
    status: 'unsearched',
    settle:
      'Compare with the standard statement that a product of locales is spatial when almost all factors are compact and the rest locally compact, and check whether the two-clause form is a genuine weakening or a restatement. An external review of the folder (Kimi, shared conversation of 2026-08) compares the two-clause form directly with Johnstone’s « locally compact + compact » and calls the extra precision debatable — possibly novel, possibly implicit in the standard proof. That is the sharpest statement of the question so far and it is still the question, so the status is unchanged.',
  },
  {
    id: '161-3-fields-partition',
    cote: '161-3',
    pages: '39, 41',
    kind: 'mathematical',
    claim:
      'Fields are not definable as a full subtype of rings by finite limits alone, but become definable as soon as the localisation ℤ[t,t⁻¹] is available — and the axiom that appears is the map 𝒞ˣ + {0} → 𝒞 being bijective.',
    basis:
      'Page 39 sets the criterion — a subtype exists iff every ring inverting M is a field — and page 41 exhibits u₀ : ℤ[t] → ℤ[t,t⁻¹] × ℤ, whose transform is bijective exactly on fields.',
    ours:
      'The reading identifies S^T_λ₀ with the polynomial rings, which the page does not write, and excludes the zero ring by hand.',
    literature: [
      'M. Hakim, Topos annelés et schémas relatifs (1972) — the field object of the Zariski topos',
      'Johnstone, Elephant D3 — geometric theories and their classifying topoi',
    ],
    status: 'matched',
    settle:
      'Settled: this is the standard geometric axiom for a field object, and the distinction between essentially algebraic and geometric theories is classical. Kept as a killed candidate.',
  },
  {
    id: '151-hypercovering-any-index-category',
    cote: '151',
    pages: '10–14, 17',
    kind: 'mathematical',
    claim:
      'A hypercovering of a topos X indexed by an arbitrary small category A — rather than by a simplicial object — is characterised by a single axiom: the comparison map φ_!(lim_I F_i) → lim_I φ_!(F_i) is an epimorphism for every finite diagram in Â.',
    basis:
      'Pages 10–13 pose four separate axioms (Hyp 1, 1′, 2, 2′), reformulate them as three epimorphism conditions on φ_! at representables, and pages 13–14 and 17 show that the representable conditions propagate to arbitrary presheaves via F = colim_{A/F} α, collapsing the four into the one displayed condition. The page also identifies the iso-version with φ_! being left exact, i.e. with a morphism of topoi X → Â.',
    ours:
      'The reading names φ_! as the left Kan extension along Yoneda and states the adjunction φ_! ⊣ φ* explicitly; the manuscript writes both functors and calls them cocontinuous and continuous, but does not name the extension. Nothing else is supplied.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check whether the epimorphism form of flatness appears as a definition of hypercovering for a general index category, rather than only as the "covering flat" condition in Diaconescu-type theorems. Sources to try: SGA 4 V appendix and Artin–Mazur (simplicial hypercoverings); Dugger–Hollander–Isaksen, Hypercovers and simplicial presheaves (2004); Kondô–Yasuda and Shulman on covering-flat functors. If a category-indexed notion with this axiom is there, mark matched. An external review of the folder (Kimi, shared conversation of 2026-08) reads the displayed condition as covering flatness — flatness relative to the topology — standing in for Diaconescu flatness when A has no finite limits. That names the shelf to search rather than settling anything.',
  },
  {
    id: '151-tube-gluing-covering-pairs',
    cote: '151',
    pages: '62–68',
    kind: 'mathematical',
    claim:
      'A stratified space is recovered as the colimit of a diagram indexed only by the covering pairs of the poset of strata — three arrows per pair i ⋖ j, namely X_i* → V_{i,j} ← V*_{i,j} → X_j* — and no comparison between non-adjacent strata is needed.',
    basis:
      'Pages 62–63 prove that under three stated hypotheses (X_i* non-empty, X_i ⊂ X_j ⇒ i ≤ j, and closure of X_i* equal to X_i) these three are the only inclusions that exist between the elementary pieces; page 64 assembles them into the diagram Ĩ, with card I + 2e vertices and 3e arrows for e covering pairs; page 68 states the gluing theorem for that diagram. No proof is given — the page says the argument will be heuristic.',
    ours:
      'The word naming the operation on page 68 is illegible and « au topos » is struck out just before it; the reading takes it as the inductive limit, on the strength of the two-stratum case of page 28, and says so. The census argument of pages 62–63 is transcribed as a skeleton because the manuscript is written over, so the chain of implications in the reading is a reconstruction. Both are flagged in the reading’s footnotes.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check whether the reconstruction from covering pairs alone, rather than from the whole poset or the full exit-path category, is the standard statement. Sources to try: Quinn, Homotopically stratified sets (1988), on homotopy links; Hughes on teardrop neighbourhoods; Lurie, Higher Algebra A.9; Ayala–Francis–Tanaka, Local structures on stratified spaces; Douteau on stratified homotopy theory. If the covering-pair form is there, mark matched.',
  },
  {
    id: '151-mixed-tubes',
    cote: '151',
    pages: '59–60, 74',
    kind: 'mathematical',
    claim:
      'For i ≤ j ≤ k there is a family of tubes V^j_{i,k} interpolating monotonically between the punctured tube V*_{i,k} (at j = i) and the full tube V_{i,k} (at j = k), obtained by removing from the tube of X_i in X_k the union of two complementary pieces of the boundary of X_k.',
    basis:
      'Page 59 defines the family and states the two extreme values; page 60 notes that its fibre over X_i* may be singular of arbitrary type, which is why the programme ends by putting these last. Page 74 begins the crible-indexed generalisation V^{I‴}_{I′,I″} and the folder breaks off after two displayed formulas.',
    ours:
      'The definition is corrected. As the page writes it, the removed set is R_{j,k} ∪ S_{j,k}, which equals the boundary of X_k for every j, so the family would be constant and both identities the page draws from it would be false; the reading removes R_{i,k} ∪ S_{j,k} instead, under which both identities hold, the family interpolates, and the page’s own marginal note (S_{j,k} = ∅ for j = k, S_{j,k} = X_j for k a successor of j) is exact. One index of the manuscript is therefore the edition’s. The page also asserts R_{j,k} ∩ S_{j,k} = Ẋ_i, which cannot be read as written since neither side’s left-hand term involves i; the reading does not assert it.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check whether a poset-indexed family of tubular neighbourhoods interpolating between a stratum’s punctured tube and its full tube has a counterpart — Goresky–MacPherson’s stratified neighbourhoods, the generalised links of Thom–Mather theory, or the "unstable" strata of a filtration. If the object is standard under another name, mark matched. Note that the entry is a claim about the corrected definition, not about the sentence on the page.',
  },
  {
    id: '151-letterhead-1990',
    cote: '151',
    pages: '3, 5, 7, 8, 17, 18, 19',
    kind: 'codicological',
    claim:
      'Four of the mathematical pages of folder 151 are written on the verso of an administrative letter dated 6 December 1990, so those leaves cannot have been written before that date — later than the « (1981) » of the folder’s own title.',
    basis:
      'Pages 3, 5 and 7 are three copies of one letter (Inspection académique de Vaucluse, Avignon, 6 December 1990), scanned upside down and unrelated to the notes. Pages 8, 17, 18 and 19 carry mathematics written on the back of that same letterhead. The inventory’s dating, « [à partir de 1981-à partir de 1990] », is consistent with a range rather than a year.',
    ours:
      'The observation is the transcription’s; it was deliberately kept out of the \\dating{} field, which reproduces Montpellier’s claim and not ours. This entry is where it belongs.',
    literature: ['Transcription 151, batch 1 (batch-01.fr.tex), header and pages 3, 5, 7, 8, 17, 18, 19'],
    status: 'candidate',
    settle:
      'A person checks the letterhead and its date against the facsimile, and checks whether pages 8, 17, 18 and 19 are versos of the very copies bound at 3, 5 and 7 or of further copies. Note what this does and does not date: the leaves, not the mathematics they continue.',
  },
  {
    id: '151-page-17-intercalated',
    cote: '151',
    pages: '10–14, 17',
    kind: 'codicological',
    claim:
      'Page 17 sits inside a numbered series it does not belong to: materially it falls between the author’s sheets 1 and 2 of the (E_n, ∂_n, k_n) notes, but its content continues the text « Hyperrecouvrements » of pages 10–14.',
    basis:
      'Pages 16, 18 and 19 are numbered 1 to 3 by the author in a circle at the head of the page; page 17, intercalated, carries no such number and computes φ_!(F × G) by colimits together with the adjoint pair (φ_!, φ*) — the step the text of pages 13–14 needs and does not carry out there. It is written on the same 1990 letterhead as pages 8, 18 and 19.',
    ours:
      'The reading restores page 17 to its logical place, in the Hyperrecouvrements section, and says so at the point where it does. The transcription leaves it where the paper puts it, which is correct for a transcription.',
    literature: ['Transcription 151, batch 1 (batch-01.fr.tex), pages 13, 14, 16, 17, 18'],
    status: 'candidate',
    settle:
      'A person checks whether page 17 is a verso of one of the sheets of the numbered series — in which case the intercalation is an accident of the paper and not of the binding — or a separate leaf filed here.',
  },
  {
    id: '161-3-leaves-reversed',
    cote: '161-3',
    pages: '53–54',
    kind: 'codicological',
    claim:
      'The last two leaves are bound in reverse: the reading order is 52, 54, 53, and the folder does not end mid-sentence as the material order suggests.',
    basis:
      'Page 54 is written to the bottom edge and runs off on “it is the finest topology for which”; page 53 opens “the objects of C̃ are sheaves (or only separated presheaves)”, completing it. The theorem numbering agrees — Th. 1–2 on 54, Th. 3–5 on 53 — and page 53 stops around 60% down with the leaf blank below, the shape of a last page.',
    ours: null,
    literature: ['Facsimile 161-3, pages 53 and 54, read directly'],
    status: 'candidate',
    settle: 'Reviewed by a person against the two leaves.',
  },
  {
    id: '161-3-interleaved',
    cote: '161-3',
    pages: '34–48',
    kind: 'codicological',
    claim:
      'From page 34 two unrelated manuscripts are bound in alternation — even pages a course on topoi in English, odd pages a French run on espèces de structure — exactly through page 48.',
    basis:
      'Checked at the junction where it matters: page 39 is French on espèces de structure and bound inverted, page 40 is English and upright, ending on “Question. Can we have an equivalence Ĉ ≃ Top(X)?”, page 41 is French again and inverted.',
    ours: null,
    literature: ['Facsimile 161-3, pages 39, 40 and 41, read directly'],
    status: 'candidate',
    settle: 'Read the remaining even/odd pairs from 34 to 48 against the facsimile.',
  },
  {
    id: '161-3-missing-leaf',
    cote: '161-3',
    pages: '39, 41',
    kind: 'codicological',
    claim:
      'A leaf of the espèces-de-structure manuscript is missing from the folder between pages 39 and 41.',
    basis:
      'Page 39 ends “(Serait vrai pour toute sous-catégorie de (Ann)” and page 41 opens “… des corps)”; the two do not join. Grothendieck’s own numbering of this sequence falls on one page in two — 35 is his 1, 37 his 3 — which is consistent with a leaf absent rather than a sentence continued.',
    ours:
      'This entry corrects an earlier claim of ours that page 41 completed page 39’s sentence. It does not; it continues the enumeration of cases only. The facsimile refuted the stronger reading.',
    literature: ['Facsimile 161-3, pages 39 and 41, read directly (both bound inverted)'],
    status: 'candidate',
    settle:
      'Look for the missing leaf elsewhere in the fonds — the run is numbered in Grothendieck’s hand, so a stray page carrying his 6 would close it.',
  },
  {
    id: '48-chapter-number-discrepancy',
    cote: '48',
    pages: '1–2',
    kind: 'codicological',
    claim:
      'The folder’s cover and its contents disagree on which chapter of EGA the plan is for: the cover reads « Plan EGA VII », the first page of the plan itself « EGA Chap. VI ».',
    basis:
      'Page 1 is otherwise blank and carries only the title, in ink at the top right, the numeral boxed above and below; three strokes, read at 900 dpi, give VII. Page 2 opens « EGA Chap. VI » followed by the chapter title « Schémas en groupes et torseurs ». Both are in ink and both are legible. Nothing elsewhere in the folder reconciles them, and the inventory silently follows the cover.',
    ours:
      'Nothing of the reading is at stake. The modernised reading states the discrepancy and declines to resolve it; the \\dating{} and \\foldertitle{} fields keep Montpellier’s « VII », since those reproduce the inventory’s claim rather than ours.',
    literature: [
      'Transcription 48, batch 1 (batch-01.fr.tex), pages 1 and 2',
      'Catalogue entry for cote 48 in src/content/catalogue.ts, which reads « Plan EGA VII »',
    ],
    status: 'candidate',
    settle:
      'A person reads the two numerals against the facsimile at high resolution and decides whether either is a slip. If both stand, the question becomes which EGA numbering each belongs to, and that is answered from the other plan folders (26 for EGA VI, 35 for SGA 7) rather than from this one.',
  },
  {
    id: '48-typescript-leaves-reversed',
    cote: '48',
    pages: '3, 5',
    kind: 'codicological',
    claim:
      'Two leaves of an SGA typescript filed in this folder are ordered against their own pagination: the archivists’ page 5 carries the typescript’s (29) and the archivists’ page 3 its (30), so the demonstration reads 5 before 3.',
    basis:
      'Page 5 states Théorème 7.9 — the anti-equivalence between geometric points over X and fibre functors on the étale topos — and opens part a), pleine fidélité, with the fibre functor written as a filtered colimit. Page 3 continues with the comparison of (*) and (**) and opens part b), surjectivité essentielle, at 7.9.1. Each carries its own page number at the top right, (29) and (30) respectively. Neither leaf belongs to the plan the folder is named for.',
    ours:
      'The reading gives the two leaves in the order of their argument and says so; the transcription gives them in the archivists’ order, which is correct for a transcription. The page ranges of that section run 5 to 3 for this reason.',
    literature: ['Transcription 48, batch 1 (batch-01.fr.tex), pages 3 and 5'],
    status: 'candidate',
    settle:
      'A person checks the two numerals on the facsimile, and checks whether the leaves are rectos of one sheet — in which case the order is an accident of scanning rather than of filing. Identifying which SGA 4 exposé the typescript belongs to would also place the (29)/(30) pagination, which this entry does not attempt.',
  },
  {
    id: '66-two-ink-layers',
    cote: '66',
    pages: '1–4',
    kind: 'codicological',
    claim:
      'Folder 66 is a two-layer document: a list of twenty-eight thesis subjects dated 1964 in the author’s own hand, annotated later in a different ink with what became of several of them, the annotations naming work that postdates 1964.',
    basis:
      'The date is boxed at the top left of page 1 and is autograph, which is rare in this fonds — the inventory’s datings are almost all deductions from versos. The left margins carry short notes in another ink: « commencé par Raynaud » at subject 12, « résolu par Raynaud » at 17, « contre-exemple de Artin » at 16, « travail Saavedra en train » at 22, « faux, cf Mumford » at 25, and at subject 13 a note referring to « les résultats d’approximation d’Artin ». The last two name work later than the list itself.',
    ours:
      'The separation into two layers is the reading’s, inferred from the ink and the position of the notes; the transcription records the notes as marginalia without dating them.',
    literature: [
      'Transcription 66, batch 1 (batch-01.fr.tex), pages 1–4, marginal notes',
      'Modernised reading 66 (66.modern.tex), sections on subjects 12–17 and 22–25',
    ],
    status: 'candidate',
    settle:
      'A person compares the inks under the facsimile and dates the two works the margins name — Artin’s approximation results and Mumford’s on rational equivalence of zero-cycles — which together give a terminus post quem for the annotation layer. Note what this dates: the annotations, not the list.',
  },
  {
    id: '66-subject-22-commissioned',
    cote: '66',
    pages: '3',
    kind: 'codicological',
    claim:
      'The margin of subject 22 records that the tannakian subject — the structure of rigid tensor abelian categories, framed on the page as « préliminaire algébrique à la théorie des motifs » — was assigned and under way at the time the annotation was made.',
    basis:
      'Subject 22 asks for the structure of abelian categories with a ± rigid tensor product, in terms of linear representations of proalgebraic groups and of representations of gerbes, and calls itself an algebraic preliminary to the theory of motives. Its margin reads « travail Saavedra en train ». Subject 28, the last of the list, asks separately for the construction of an abstract theory of motives over schemes of finite type over Z.',
    ours:
      'The identification of subject 22 with what is now called a tannakian category is the reading’s, and rests on the two terms of the equivalence being written on the page rather than on any name it uses; the page names neither the notion nor a thesis.',
    literature: [
      'Transcription 66, batch 1 (batch-01.fr.tex), page 3, subject 22 and its margin',
      'Lending register 162-1, which records four sets of tannakian and Hodge material against the same name',
    ],
    status: 'unsearched',
    settle:
      'A person dates the annotation layer (see the entry above) and compares it with the date of the thesis. This entry says only what the margin says — that the work was commissioned and in progress — and deliberately makes no claim about who arrived at anything first, which these undated pages could not support.',
  },
  {
    id: '35-exposes-reassigned',
    cote: '35',
    pages: '1, 3',
    kind: 'codicological',
    claim:
      'The folder records the reassignment of individual SGA 7 exposés, with speakers’ names struck through and replaced in the margins and, at one bibliography entry, the author’s own name struck and another written above it.',
    basis:
      'Page 1 is a typescript table of exposés I to IX with a hand-added column of names in the left margin, most reading « Gr. ». Three lines depart from that: exposé V carries a circled « Mme Raynaud ? », the renumbered exposé carries one Raynaud written over another that is struck, and exposé VI carries a struck « Rim » with, in the title itself, the German parenthesis « ist bei Deligne ». At page 3, bibliography entry [19], « Grothendieck, A. » is struck and « Deligne » written above.',
    ours:
      'Nothing. The strikings and the substitutions are on the pages; the reading only groups them.',
    literature: ['Transcription 35, batch 1 (batch-01.fr.tex), pages 1 and 3'],
    status: 'candidate',
    settle:
      'A person reads the margin names against the facsimile — one of them, the civility or forename of the Raynaud written above the struck one, is marked uncertain in the transcription and the two Raynauds of that period are distinct people — and compares the assignments with the authorship of the published volumes.',
  },
  {
    id: '35-dependency-graphs-redrawn',
    cote: '35',
    pages: '5',
    kind: 'codicological',
    claim:
      'The last leaf carries three dependency graphs of the SGA 7 exposés, the first cancelled by four crossed strokes and replaced by two below it that split the seminar in two — one headed « Théorèmes qualitatifs », a branching tree, the other « Théorèmes quantitatifs », a near-linear chain.',
    basis:
      'The cancelled graph spans the upper half of the leaf and mixes both bodies of material. The two replacements are drawn beneath a rule: in the qualitative graph exposé I is a source with four outgoing arrows and IX a sink, with two parallel chains (II–IV and VI–VIII) converging on it; in the quantitative graph XI to XVI descend in sequence with a single branch through XIV, XVII and XVIII. The difference in shape is the content: several routes to one result on one side, one calculation in order on the other.',
    ours:
      'The two replacement graphs are transcribed arrow by arrow; the cancelled one is deliberately not redrawn, because its arrowheads run under the strokes and a dependency graph missing an arrow asserts an order nobody wrote. One arrow of the qualitative graph, between IX and V, carries its head against the direction of every other arrival on IX, and is transcribed in the direction the page draws rather than normalised.',
    literature: ['Transcription 35, batch 1 (batch-01.fr.tex), page 5'],
    status: 'unsearched',
    settle:
      'A person checks the arrowheads against the facsimile, in particular the reversed one, and compares the two graphs with the dependency structure of the published SGA 7 volumes. Whether the qualitative/quantitative split survives into print is the question this entry raises and does not answer.',
  },
  {
    id: '162-6-single-subject',
    cote: '162-6',
    pages: '1–5',
    kind: 'codicological',
    claim:
      'The folder the inventory calls « [Documents isolés] », and whose contents it does not describe, is five cards on one subject: the archimedean local factor of an L-function and the structures around it.',
    basis:
      'Card 1 gives the two elementary gamma factors and the recipe reading the exponents of a Hodge structure’s local factor off its Hodge numbers, split at the diagonal by the infinite Frobenius. Card 2 gives the real Weil group with σ² = −1 and the computation H²(Z/2, C*) = Z/2 that classifies that extension. Card 3 gives the norm on S_E and its relation to the idele class group; card 5 the diagram tying E*, I(E), C(E), S_E and S_E(A) together; card 4 the two compatibilities — the Tate twist shifting the argument by one, and the duplication relation between the two gamma factors.',
    ours:
      'The subject is the reading’s to name: no card carries a title and none refers to another. The ordering is the archivists’, and the reading keeps it rather than rearranging the cards to suit the argument.',
    literature: ['Transcription 162-6, batch 1 (batch-01.fr.tex), pages 1–5'],
    status: 'candidate',
    settle:
      'A person reads the five cards together and decides whether the coherence is real or imposed. Note that a title supplied by an archivist for an undescribed folder is the weakest kind of evidence about its contents, which is what makes this worth recording; the mathematics on the cards is standard and no part of this entry claims otherwise.',
  },
  {
    id: '162-1-date-precedes-inventory',
    cote: '162-1',
    pages: '2, 5',
    kind: 'codicological',
    claim:
      'The lending register carries an entry dated 10.I.66, earlier than the « [à partir de 1967] » the inventory assigns the folder, and the only other date in its nine pages is a letter of 21.9.67 mentioned in an entry.',
    basis:
      'Page 2 dates one entry, two letters concerning Atiyah–Adams, to 10.I.66. Page 5 records among the items lent a letter to Hartshorne of 21.9.67, on cohomological dimension of algebraic varieties. No other date appears on the nine pages, and nothing in the folder explains how the inventory arrived at its lower bound.',
    ours:
      'The observation is the transcription’s. The \\dating{} field keeps Montpellier’s « [à partir de 1967] » and its group range, since that field reproduces the inventory’s claim and not ours.',
    literature: ['Transcription 162-1, batch 1 (batch-01.fr.tex), pages 2 and 5'],
    status: 'candidate',
    settle:
      'A person checks both dates against the facsimile. The 10.I.66 sits in an entry that is struck through and partly illegible, which is exactly the kind of reading this register makes unsafe, so the entry should not be relied on until it has been looked at.',
  },
  {
    id: '108-dated-from-unrelated-verso',
    cote: '108',
    pages: '3',
    kind: 'codicological',
    claim:
      'The « [à partir de 1973] » the inventory gives folder 108 appears to come from a letter of 4 January 1973 on the verso of one leaf, which has nothing to do with the questions written on the recto.',
    basis:
      'The mathematical writing occupies the top half of page 3 and stops; the verso carries a private letter of that date and a printed page on an unrelated subject. Nothing on any of the five pages is dated by the author, and the questions themselves — on modelizers, test categories and contractors — carry no internal indication of when they were written.',
    ours:
      'The inference from the verso to the inventory’s bound is the reading’s, and it is an inference: the archivists do not say what they dated the folder from. The transcription notes the verso once, at the page where it occurs, and does not describe it further.',
    literature: ['Transcription 108, batch 1 (batch-01.fr.tex), page 3 and its note'],
    status: 'candidate',
    settle:
      'A person checks the letter’s date on the facsimile and considers what it dates: the leaf, and only the leaf. A reused sheet gives a lower bound for the writing on it and none at all for the writing on the other four.',
  },
  {
    id: '112-listing-paper-undated',
    cote: '112',
    pages: '1–4',
    kind: 'codicological',
    claim:
      'Folder 112 is written on computer listing paper of the same kind that dates folder 115, yet the inventory leaves 112 « s.d. » and dates 115 « [à partir de 1982] ».',
    basis:
      'All four leaves of 112 are continuous-feed listing paper, written across the printed columns, which show through every line and are what makes the folder so hard to read. Folder 115 is on listing paper too, and its listings carry a printed date of 02 JUN 82, which is the evident basis for its dating. No date has been read on 112’s listings.',
    ours:
      'The comparison between the two folders is the reading’s; neither transcription claims it. 112’s \\dating{} field keeps the inventory’s « s.d. ».',
    literature: [
      'Transcription 112, batch 1 (batch-01.fr.tex), header and pages 1–4',
      'Transcription 115, batch 1 (batch-01.fr.tex), header, which records listings dated 02 JUN 82',
    ],
    status: 'unsearched',
    settle:
      'A transcription pass over 112’s four leaves looking specifically for a printed date or job number in the listing, and a comparison of the stock and column layout with 115’s. If the stock matches and a date is found, 112’s « s.d. » can be narrowed; if the listings differ, this entry should be dropped. Note that the paper dates the leaf and not the mathematics on it.',
  },
  {
    id: '108-delta-op-not-test',
    cote: '108',
    pages: '2',
    kind: 'mathematical',
    claim:
      'The folder records a negative answer to whether Δ° is a test category, written as a bare underlined « non » with no argument and no definition of the notion on the page.',
    basis:
      'Question 6 of the list reads « Is the category Δ° a test category, or not? » and is answered « no », underlined, on the same line — the only one of the seventeen questions that carries its own answer. The list nowhere defines modelizer or test category, and gives neither proof nor counterexample. The question continues with a row of cubical and simplicial variants, one of whose symbols the transcription declines to name.',
    ours:
      'Nothing is supplied. The reading states the answer and explicitly declines to reconstruct an argument for it, since a counterexample invented here would be the edition’s and not the page’s.',
    literature: [],
    status: 'unsearched',
    settle:
      'Establish first which definition of test category is in play, since the page uses the term without defining it and the notion was still moving; then check the answer against the definitive treatments of test categories and modelizers. Until the definition is fixed the statement is not yet in a form that can be looked up, which is why this entry is unsearched rather than a candidate.',
  },
  {
    id: '115-wheel-eleven-curryings',
    cote: '115',
    pages: '5',
    kind: 'mathematical',
    claim:
      'A presheaf kernel X ∈ (A × B)^ is displayed as eleven functor categories in a wheel, all arrows equivalences: the kernel at the centre, the bare curryings on an inner ring, and the curryings after free (co)completion on the rim, one node per choice of variance in each argument.',
    basis:
      'Page 5 draws the wheel and its own margin tallies it — « 6 cas » for the two-argument forms, « 4 cas » for the mixed ones — which with the centre gives eleven, the two inner forms each appearing twice at the ends of a diameter. The exclamation marks on the rim record what an extension along Yoneda must preserve to be an equivalence.',
    ours:
      'The reading supplies the census that makes the count come out: separating centre, inner ring and rim, reading the four headless radii as a variance frame rather than as functors, and following the one inward diagonal the page draws against the other three. A first pass had reduced the wheel to eight radiating arrows.',
    literature: [
      'J. Bénabou, Les distributeurs (1973) — profunctors as two-variable presheaves and their curryings',
      'Kelly, Basic Concepts of Enriched Category Theory, ch. 4 — free cocompletion and extension along Yoneda',
    ],
    status: 'matched',
    settle:
      'Settled as mathematics: every node of the wheel is a standard currying of a profunctor, and the equivalences are the universal property of free (co)completion. What is not standard is the display — eleven presentations of one kernel laid out by variance — and that is a matter of exposition, not of theorem. An external review of the folder (Kimi, shared conversation of 2026-08, covering 115, 161-1 and 161-3) reached the same verdict independently, calling the perspective the folder’s contribution and the machinery known.',
  },
  {
    id: '115-isbell-reflexivity-left-open',
    cote: '115',
    pages: '7',
    kind: 'mathematical',
    claim:
      'The folder isolates the reflexivity question for Isbell duality — whether the unit and counit are isomorphisms only on representables — and answers it « sans doute pas », without proof.',
    basis:
      'Page 7 specialises the two-variable kernel to B = A^op with the hom as kernel, obtaining the adjunction between Â and (A^∨)^op, notes that unit and counit are isomorphisms on representables by Yoneda, and then asks whether they are so anywhere else. The answer on the page is a parenthesis, not an argument.',
    ours:
      'Nothing of the answer. The reading names the objects where η is invertible as the reflexive ones and links them to the envelope constructed on pages 10–13, which the page does not do in so many words; the transcription flags the words preceding « sans doute pas » as an uncertain reading.',
    literature: [
      'J. R. Isbell, Structure of categories, Bull. AMS 72 (1966) — the adjunction and its fixed objects',
      'Isbell, Adequate subcategories (1960) — the representables as the first reflexive objects',
    ],
    status: 'matched',
    settle:
      'Settled: reflexive objects strictly exceed the representables in general, so the folder’s « sans doute pas » is right and is the known answer. Kept as a killed candidate because the interest is that the question is posed and left open here, not that it is new.',
  },
  {
    id: '115-isbell-envelope-self-dual',
    cote: '115',
    pages: '10–13',
    kind: 'mathematical',
    claim:
      'The triples (H_*, H^*, α) with compatible pairing form a canonically self-dual completion Ã, into which both Â and (A^∨)^op embed, and inside whose self-dual part the Karoubi envelope of A sits — as an inclusion, not an equality.',
    basis:
      'Pages 10 and 11 build the triples out of a full embedding A ↪ B, show every full embedding induces B → Ã, and give the self-duality Ã^op ≃ (A^op)~ exchanging the two components. Page 13 places Cauchy completion at the centre and observes that retracts of representables are reflexive.',
    ours:
      'Two corrections the page does not carry. The manuscript writes A = Â ∩ A^∨°, an intersection of subcategories of different categories, which cannot be read literally; and equality with Kar(A) does not hold in general, reflexive objects being possibly strictly more numerous. The reading asserts only the inclusion, which is what the rest of the page uses.',
    literature: [
      'J. R. Isbell, Structure of categories (1966) — the construction now called the Isbell envelope',
      'Borceux, Handbook of Categorical Algebra I, §6.5 — Karoubi envelope as Cauchy completion for Ens-enriched categories',
    ],
    status: 'matched',
    settle:
      'Settled: this is the Isbell envelope, and the Kar(A) ⊂ reflexives inclusion is the standard statement. The external review named above independently flagged the same two literal impossibilities the reading corrects, which is evidence about the edition rather than about the mathematics.',
  },
  {
    id: '19-comonad-matrix-product-base',
    cote: '19',
    pages: '7–11',
    kind: 'mathematical',
    claim:
      'For an adjoint pair over a product base B = ∏ Bᵢ, the comonad φ = fg decomposes into a matrix φ_ji = f_j g_i : Bᵢ → B_j whose comultiplication becomes a family λ_kji : φ_ki → φ_kj φ_ji; for two factors with g′, g″ fully faithful the whole matrix collapses to two crossed functors φ′ : B″ → B′, φ″ : B′ → B″ and two units λ′, λ″.',
    basis:
      'Pages 7–11 set φ_ji = f_j g_i, obtain pr_j φ((Xᵢ)) = ∏ᵢ φ_ji(Xᵢ) under the assumption that the f_j commute with I-indexed products, and build λ_kji by inserting the unit id → g_j f_j in the middle of f_k g_i. The manuscript declines to write the coassociativity relations out, noting only that i = j = k gives back the comultiplication of φᵢ and that the cases with two coinciding indices are degenerate.',
    ours:
      'The finiteness/exactness proviso that makes pr_j φ = ∏ φ_ji hold is stated in the reading where the page leaves it implicit. The collapse to two crossed functors is the page’s own, worked there in detail.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look for the matrix decomposition of a comonad over a product base in the standard treatments — Barr–Wells, Toposes Triples and Theories ch. 3; Mac Lane CWM VI; and the descent literature, where the two-factor crossed form is closest to a gluing datum. An external review of the folder (Kimi, shared conversation of 2026-08) said it did not recognise this presentation in the standard texts, which is a reason to look rather than a result: nobody has yet searched.',
  },
  {
    id: '19-comonadicity-dating-cannot-support-precedence',
    cote: '19',
    pages: '3–6',
    kind: 'codicological',
    claim:
      'Nothing in the folder dates the comonadicity pages relative to Beck’s 1967 thesis: the inventory’s « [à partir de 1958-1973] » is an archivist’s range that straddles 1967, and no leaf of the batch carries a date.',
    basis:
      'The transcription of batch 1 records that the dating is the inventory’s own, for the whole shelfmark, and that nothing on these pages carries a date. The comonadicity statement occupies pages 3–6, inside a folder whose announced range opens nine years before Beck and closes six years after.',
    ours:
      'The reading names the theorem as Beck’s and says the monadic form is the 1967 thesis and the comonadic form its dual; the transcription flags the name « Beck » on the page itself as an uncertain reading. Neither claims a date for the leaves.',
    literature: [
      'J. Beck, Triples, algebras and cohomology, Columbia thesis (1967)',
      'Transcription 19, batch 1 (batch-01.fr.tex), header and pages 3–6',
    ],
    status: 'candidate',
    settle:
      'Only physical evidence would settle it — a dated verso, an institute letterhead, a numbered seminar reference among these particular leaves. Recorded because an external review of the folder (Kimi, shared conversation of 2026-08) read the inventory range as evidence that these pages precede Beck, which it cannot be: the range is a deduction about the shelfmark, not a reading of these leaves. This entry exists to stop the next reader making the same step. Whatever is found, priority is not a claim this project makes.',
  },
  {
    id: '19-adjoint-chains-length-n',
    cote: '19',
    pages: '79–80',
    kind: 'mathematical',
    claim:
      'For every n there exist presheaf topoi carrying a chain of n successive adjoint functors, none of them fully faithful; whether such a chain can be continued indefinitely in both directions is left open on the page.',
    basis:
      'Page 79 is struck through entirely — an attempt at the two-sided question — and page 80 states the positive result, that a chain of successive adjoints can be extended indefinitely downwards. The two-sided question is posed and not answered there.',
    ours:
      'The reading notes that an infinite chain in both directions is in fact impossible in general, and is explicit that this answer is not Grothendieck’s and is not on the page.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check the length-n construction against the literature on adjoint strings — where chains of length four and beyond on presheaf categories are classical — and establish whether the « none fully faithful » clause is what makes the statement non-trivial. The two-sided impossibility should be given its actual source rather than left as the reading’s aside.',
  },
  {
    id: '19-faithful-transportable-is-forgetful',
    cote: '19',
    pages: '71–75',
    kind: 'mathematical',
    claim:
      'A functor p : E → B is a forgetful functor of structure exactly when it is faithful and transportable — equivalently a fibration with preordered fibres; if it is moreover conservative the fibres are discrete and E is the category of elements of a presheaf on B.',
    basis:
      'Pages 71–75 define transportability by asking that E ×_B B^is → B^is be a fibration, note that every functor is isomorphic to a transportable one, and then read the answer off the fibres. The discrete case is identified with the category of elements.',
    ours:
      'The reading replaces the page’s « catégories ordonnées » by « préordonnées », antisymmetry not being automatic, and reconstructs the statements from a first third of page 72 that is rewritten twice and almost entirely struck out.',
    literature: [
      'Adámek–Herrlich–Strecker, Abstract and Concrete Categories, ch. 5 — concrete categories and transport of structure',
      'SGA 1, exposé VI — fibred categories, and the category of elements of a presheaf as the discrete case',
    ],
    status: 'matched',
    settle:
      'Settled: this is the standard characterisation of concrete categories over B, and the discrete case is the Grothendieck construction. Kept as a killed candidate — the interest is the formulation, which answers « what makes a functor a forgetting of structure » without presupposing what a structure is.',
  },
  {
    id: '135-sinh-theorem-classification',
    cote: '135',
    pages: '39–44, 46–58',
    kind: 'mathematical',
    claim:
      'A Gr-category is classified up to equivalence by π₀, π₁ and a class k(C) ∈ H³(π₀, π₁), the map C ↦ k(C) being a bijection onto H³(M,N) for fixed type (M,N) — Sinh’s theorem — with the folder carrying it in Hoàng Xuân Sính’s own typescript alongside Grothendieck’s notes.',
    basis:
      'The theorem is stated on page 41 in the typescript presented by Henri Cartan, and again on page 50 in the thirteen-page English manuscript outlining the thesis in three chapters; Grothendieck’s handwritten notes occupy pages 2–37.',
    ours:
      'The reading identifies a Picard category with a connective spectrum truncated in degree 1 and k(C) with its first Postnikov invariant, which the folder does not say in those terms.',
    literature: [
      'Hoàng Xuân Sính, Gr-catégories, thèse, Université Paris VII (1975)',
      'Sinh’s theorem as it stands in the modern literature on 2-groups and Picard groupoids',
    ],
    status: 'matched',
    settle:
      'Settled as mathematics: this is Sinh’s theorem, published in her thesis, and the folder is the working material behind it rather than an independent source for it. What the folder holds that the thesis does not is Grothendieck’s side of the work — including the closing page on non-commutative homological algebra, which is a programme and not a theorem, and is therefore not a candidate here.',
  },
  {
    id: '161-1-giraud-recognition-half-page',
    cote: '161-1',
    pages: '15',
    kind: 'mathematical',
    claim:
      'The folder derives the topos recognition criterion in half a page, as the converse to a fact it treats as already known: if φ : C → E is left exact and strictly generating, then E → Ĉ is fully faithful with the Kan extension φ̄ as left adjoint, so left exactness of φ̄ makes E a left-exact localisation of a presheaf category.',
    basis:
      'Page 15 poses the question « on sait que c’est OK si E est un topos. Réciproque ? » and sketches the converse immediately. An intermediate line, « il suffit que E soit un topos », is struck out on the page — it is the converse he is after. Pages 17–19 then do the general density computation the argument rests on, with α = i_! fully faithful and βα ≃ id.',
    ours:
      'The size hypotheses the page does not discuss — C small, E with small colimits — are stated in the reading, and the forward direction is named as the theorem now attached to Diaconescu, which the page does not name.',
    literature: [
      'J. Giraud, Analysis situs, Séminaire Bourbaki 256 (1963) and SGA 4 IV — the recognition theorem',
      'R. Diaconescu (1975) — left exactness of the Kan extension of a flat functor',
    ],
    status: 'matched',
    settle:
      'Settled: this is Giraud’s criterion in its localisation form, and the forward implication is standard. Kept as a killed candidate because the interest is the compression — half a page, obtained as a converse — and because the folder is undated, so nothing here bears on when it was written relative to the published statement. An external review of the folder (Kimi, shared conversation of 2026-08) called it « Giraud’s recognition theorem written down as a conjecture before it became a theorem »; that inference needs a date the folder does not carry.',
  },
  {
    id: '161-3-locale-spatiality-suprema-proof',
    cote: '161-3',
    pages: '9–14',
    kind: 'mathematical',
    claim:
      'The spatiality of the product locale is proved here in three passages to the supremum, a complete self-contained argument in the lattice of subobjects rather than the route the standard texts take.',
    basis:
      'Pages 9–14 identify Top(X × Y) and Top(X) ×_top Top(Y) as sheaves on the same site O_X × O_Y for two distinct topologies — the product topology π, whose sheaves are the bifaisceaux, and the topology π′ induced from X × Y — and close the gap between them in three passages to the supremum, X × Y being a supremum of rectangles.',
    ours:
      'The reading states the non-emptiness of X and Y that makes O_X × O_Y ⊂ O_{X×Y} injective where the page assumes it in passing, and names the two topologies, which the page distinguishes without labelling.',
    literature: [
      'Johnstone, Stone Spaces (1982), II — spatiality of locale products',
    ],
    status: 'unsearched',
    settle:
      'Read the three-suprema argument against the proof in Stone Spaces and against Isbell’s papers on locale products, and decide whether it is the same argument in other clothes or a distinct one. The claim here is about a proof, not a theorem: the theorem is certainly published, and what would make this row a finding is that the argument is not. An external review (Kimi, shared conversation of 2026-08) names it one of the three strongest items in the folders it read.',
  },
  {
    id: '161-3-two-product-by-intersection',
    cote: '161-3',
    pages: '3–8',
    kind: 'mathematical',
    claim:
      'The 2-product of topoi is obtained by exhibiting Π(C̃, D̃) as the intersection, inside the presheaf topos on C × D, of the inverse images of the two sub-topoi C̃ ⊂ Ĉ and D̃ ⊂ D̂ — an intersection-of-sub-topoi argument rather than the site-based or fibred route.',
    basis:
      'Pages 3–8 define Π(E,F) as the functors E^op → F commuting with limits, show a bifaisceau is one that is a sheaf in each variable separately, and conclude by the fact that sub-topoi of a topos correspond to topologies finer than the given one, form a complete lattice, and that intersection corresponds to the supremum of topologies. The 2-universal property follows, with the corollary that arbitrary families have a 2-product.',
    ours:
      'The reading supplies the lattice statement about sub-topoi and topologies that the page leans on without stating, and names the result as the 2-product in the 2-category of topoi.',
    literature: [
      'SGA 4, exposé IV — products of topoi',
    ],
    status: 'unsearched',
    settle:
      'Compare with the construction in SGA 4 IV and with the later treatments of 2-limits of topoi, and establish whether the intersection argument appears anywhere in print. Like the row above, the claim is about the route and not the theorem.',
  },
  {
    id: '115-isbell-duality-derived-from-kernels',
    cote: '115',
    pages: '3–7',
    kind: 'mathematical',
    claim:
      'Isbell duality is obtained here as a specialisation of a general kernel transform — set B = A^op and take the hom itself as kernel — rather than from duality theory, and nothing in the folder cites Isbell.',
    basis:
      'Pages 3 to 5 build the transform attached to a kernel X ∈ (A × B)^, pages 6 and 7 specialise it to H_A = Hom_A ∈ (A × A^op)^, which the margin of page 3 already marks as the canonical element of that category, and the adjunction O ⊣ Spec falls out. The names O and Spec are not the manuscript’s: it writes φ_A and Ψ_A.',
    ours:
      'The reading supplies the names O and Spec and the geometric reading — functions against points — that goes with them, and states that nothing in the folder cites Isbell.',
    literature: [
      'J. R. Isbell, Small subcategories and completeness, Math. Systems Theory (1968)',
      'Isbell, Structure of categories (1966)',
    ],
    status: 'unsearched',
    settle:
      'Establish whether any published account derives the duality this way — as one instance of a two-variable kernel calculus — rather than directly. The duality itself is Isbell’s and is not in question; what is in question is whether this derivation exists in print.',
  },
  {
    id: '161-1-contractions-string-calculus',
    cote: '161-1',
    pages: '11–12',
    kind: 'mathematical',
    claim:
      'The free symmetric monoidal category on A is extended by « contractions » — pairings L′_j ⊗ L″_j → 1 evaluated against each other — giving a diagrammatic calculus for monoidal categories with duals, with the strings drawn in the margin of page 12.',
    basis:
      'Pages 11 and 12 add to Φ(A) the operation of evaluating each paired factor against its partner, and page 12 draws the « ficelles » that record which factor is paired with which.',
    ours:
      'The reading names the construction a calculus for monoidal categories with duals; the page draws it and does not name it.',
    literature: [
      'Joyal–Street, The geometry of tensor calculus I, Adv. Math. (1991)',
    ],
    status: 'unsearched',
    settle:
      'Compare the marginal strings with the string-diagram calculus as it was eventually published, and decide whether this is the same device or a private notation that resembles it. Note that the folder is undated, so this row cannot become a statement about who drew such diagrams first, whatever the comparison shows.',
  },
  {
    id: '161-1-epsilon-sign-obstruction',
    cote: '161-1',
    pages: '9–12',
    kind: 'mathematical',
    claim:
      'The obstruction to an unordered tensor product of invertible objects is isolated as a single sign ε(L) ∈ Aut(1_C) with ε(L)² = 1: re-identifying along a permutation σ multiplies by ε(L)^{sign(σ)}, and the ambiguity vanishes exactly when ε(L) = 1.',
    basis:
      'Pages 9 to 12 construct Φ(A), the free symmetric monoidal category on A, and then examine what happens when two factors of a family are the same invertible object L: the symmetry becomes an automorphism of L ⊗ L of order two, which is ε(L).',
    ours: null,
    literature: [
      'Deligne, La formule de dualité globale, SGA 4 XVIII, and the Picard-category literature — the sign as the commutativity constraint',
      'Transcription 135 — the graded lines with the Koszul sign rule as the smallest non-strict Picard category',
    ],
    status: 'matched',
    settle:
      'Settled: ε(L) is the commutativity constraint of a Picard category, the Koszul sign rule is its standard example, and folder 135 works exactly that example. Kept as a killed candidate, and as the link between the two folders — the sign isolated abstractly in 161-1 is the sign computed concretely in 135.',
  },
  {
    id: '161-1-idempotent-adjunction-decomposition',
    cote: '161-1',
    pages: '3–5',
    kind: 'mathematical',
    claim:
      'An adjunction restricts to an equivalence between the full subcategories E₀ and F₀ where unit and counit are invertible, and an idempotent adjunction is exactly the data of a reflective subcategory, a coreflective subcategory, and an equivalence between them.',
    basis:
      'Pages 3 to 5 define E₀ and F₀ by invertibility of η and ε, prove the equivalence, and note that each of the four conditions ηv, vε, εu, uη invertible implies the other three.',
    ours:
      'The reading states the four-conditions equivalence as a classical fact; the page uses it without proving it.',
    literature: [
      'Borceux, Handbook of Categorical Algebra I, §3.4 and §4.2 — reflective subcategories and idempotent adjunctions',
    ],
    status: 'matched',
    settle:
      'Settled: this is the standard fixed-point decomposition of an adjunction. Kept as a killed candidate.',
  },
  {
    id: '114-total-asphericity-independent-of-localizer',
    cote: '114',
    pages: '3–5',
    kind: 'mathematical',
    claim:
      'The folder asserts (Proposition 4) that total asphericity does not depend on the basic localizer: for a small category A and a basic localizer W satisfying Loc 4), being totally W∞-aspherical, being totally W-aspherical, and being non-empty with a × b 0-connected in Â for all objects a, b are equivalent. As stated the assertion is false — the category of cubes □ satisfies the third condition and is not totally W∞-aspherical — and what stands is only the chain (i) ⟹ (ii) ⟹ (iii).',
    basis:
      'Proposition 4 states the three conditions and the proof turns on the sandwich W∞ ⊆ W ⊆ W₀ that every basic localizer satisfies, total asphericity being easier to obtain the larger the class of equivalences. The page stops at « namely » where W₀ should be named.',
    ours:
      'W₀ is identified in the reading as the maximal basic localizer, the one given by π₀-bijections — the only coherent reading, and flagged as the edition’s and not the page’s. The minimality of W∞, which the proposition needs and the page assumes, is attributed to Cisinski (2004) rather than to Grothendieck. Neither the page nor the reading proves (iii) ⟹ (i): the page breaks off at « namely », its continuation (typescript page 351) is not in the folder, and the reading, after « il reste à voir que la dernière condition est exactement (iii), puis qu’elle entraîne (i) », shows only the first half. The counterexample and the check that its products of representables are 0-connected are this pass’s (2026-09-26); the non-asphericity it rests on is Cisinski’s. The claim was corrected on 2026-09-26: it had stated the proposition as a fact and dropped the page’s hypothesis « satisfying Loc 4) ».',
    literature: [
      'D.-C. Cisinski, Le localisateur fondamental minimal, Cah. Topol. Géom. Différ. Catég. (2004)',
      'Cisinski, Les préfaisceaux comme modèles des types d’homotopie, Astérisque 308 (2006) — 3.3.4–3.3.6 (trivial and coarse localizers), 4.2.19–4.2.20 (W∞ minimal), 4.3.1–4.3.3 (total asphericity), 8.4.2, 8.4.13 and Remarque 8.4.33 (the category of cubes), 9.3.1–9.3.2 (non-coarse ⟺ contained in W₀); read 2026-09-26',
      'G. Maltsiniotis, La théorie de l’homotopie de Grothendieck, Astérisque 301 (2005) — Introduction (« la catégorie des cubes n’est pas une catégorie test stricte »), 1.1.29–1.1.32 (trivial, coarse and π₀ localizers), 1.6.1–1.6.7 (total asphericity), Exemple 1.6.21; read 2026-09-26',
    ],
    status: 'refuted',
    settle:
      'Refuted on 2026-09-26, by a counterexample the literature supplies rather than by a match; kept, like the killed candidates, so that the next reader does not take the proposition for a result. The category of cubes □ (faces and degeneracies, no connections; Cisinski 8.4.2) is non-empty, and for all m, n the presheaf □^m × □^n is 0-connected: every element has a vertex, and any two vertices are joined by edges — pairs of maps □¹ → □^m, □¹ → □^n with one coordinate a projection and the others constant — changing one coordinate at a time. So □ satisfies (iii). But Cisinski, Remarque 8.4.33: « On peut par exemple calculer explicitement le type d’homotopie de l’ensemble cubique □1 × □1 et vérifier qu’il n’est même pas simplement connexe », so □¹ × □¹ is not W∞-aspherical and □ is not totally W∞-aspherical — which is also what Maltsiniotis’s introduction says in « la catégorie des cubes n’est pas une catégorie test stricte », □ being a W∞-test category (Cisinski 8.4.13) and a strict test category being a test category that is totally aspherical (Maltsiniotis 1.6.7, Cisinski 4.3.3). Hence (iii) ⟹ (i) fails, and with it (ii) ⟹ (i) for W = W₀. What stands is (i) ⟹ (ii) ⟹ (iii), which is immediate from W∞ ⊆ W ⊆ W₀: the left inclusion is Cisinski’s minimality theorem (4.2.19), the right one holds exactly for the non-coarse localizers (Cisinski 9.3.2, « Les seuls localisateurs fondamentaux qui ne sont pas géométriques sont les localisateurs fondamentaux grossiers »). The page’s « satisfying Loc 4) » is load-bearing even for that chain: for the coarse localizer Wgr, Maltsiniotis 1.6.21 makes total asphericity mean only that A is non-empty and any two objects have a common source, and BG for a non-trivial group G is then totally Wgr-aspherical while G × G has as many components as G has elements. Neither Astérisque states that total asphericity is independent of W, and it is not. What is not known here is what Loc 4) says, and whether page 351 of the typescript, not in the folder, restricts the proposition further; the reading’s section title « L’asphéricité totale ne dépend pas du localisateur » and its Résumé state the proposition as true and need revising (/modernize-grothendieck). An external review (Kimi, shared conversation of 2026-08) had called it the folder’s sharpest result. Toën’s texts listed for 104 were searched on 2026-09-26 and do not bear on total asphericity or basic localizers.',
  },
  {
    id: '151-pi1-too-coarse-for-the-sphere',
    cote: '151',
    pages: '61–63',
    kind: 'mathematical',
    claim:
      'The Π₁ level of the stratified formalism is shown to be too coarse by computing it on P¹_C ≃ S², where the amalgamated sum of the tube diagram is homotopically trivial although the sphere is not; raising the level by one, to the gerbe, recovers H²(S², A) ≃ A.',
    basis:
      'The folder tests the gluing formalism on the stratification of P¹_C by a point, a plane and a circle, obtains a trivial answer at the level of the fundamental group, and repairs it over three pages by moving up a level.',
    ours:
      'Nothing of the computation. The reading states that what fails is an invariant and not the programme, which is how the page itself puts it in a single line.',
    literature: [],
    status: 'unsearched',
    settle:
      'Establish whether the failure of the 1-truncated gluing datum on a stratified sphere, and its repair by a 2-level datum, is stated anywhere in the stratified-homotopy literature — exit-path categories, conically stratified spaces, and the higher van Kampen theorems are where to look. The mathematics is certainly known; whether this diagnosis-and-repair is written down is not.',
  },
  {
    id: '112-linearization-beyond-the-simplex',
    cote: '112',
    pages: '1–4',
    kind: 'mathematical',
    claim:
      'The folder asks how far the Dold–Kan correspondence survives away from Δ: for a small category A, whether restricting to the « smooth » abelian presheaves — those along which linearisation does not vary — gives an equivalence with a derived category of locally constant complexes, the obstruction being that L_b carries twisted and not constant coefficients.',
    basis:
      'Pages 1 to 4 define smoothness by asking that the map induced by every arrow a → b of A be invertible, pose the equivalence question in several forms, and note the twisting of the coefficients of L_b.',
    ours:
      'The gloss on « lisse » as local constancy is the edition’s, chosen as the widest class the page allows; the definition of « négligeable » is left incomplete because the page is illegible on both sides of it, and the second factor of the tensor product is not legible either.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check the generalised Dold–Kan literature — Dold–Puppe, and the later work on Kan extensions of the correspondence along functors out of Δ — for a statement of this equivalence over a general small category. Note that this row rests on a folder the transcription reports as partly illegible, so the claim may not be recoverable in the form stated.',
  },
  {
    id: '29-ramification-domain-axioms',
    cote: '29',
    pages: '190–193',
    kind: 'mathematical',
    claim:
      'A « domaine de ramification » is axiomatised as a stack of multigaloisian categories over Ét(S) together with a continuous « geometric realisation » r into relative schemes, subject to four axioms R1–R4; and, given R1, R3 and R4, axiom R2 — that direct subobjects of X correspond bijectively to open-and-closed parts of r(X) — is equivalent to r being faithful.',
    basis:
      'Page 190 gives the definition and the four axioms; page 191 proves that the r-surjective families are the covering families of a topology and that base change is continuous. The equivalence R2 ⟺ r faithful is the proposition of page 193, which turns on r(X′ ∩ X″) = r(X′) ∩ r(X″) and on reducing to an inclusion X″ = X′ ⊔ X₁.',
    ours:
      'The reading separates the 1967 « donnée de ramification » (C, s) from this (R, r), which the folder gives nearly the same name; and it states the R2 ⟺ faithfulness proposition as an equivalence, which the page does but only in the direction « r fidèle ⟹ R2 ».',
    literature: [
      'A. Abbes and T. Saito, Ramification of local fields with imperfect residue fields, Amer. J. Math. 124 (2002), arXiv math/0010103 — §1 and §2 (« Filtration on Galois categories »: Proposition 2.1, Remark 2.2, Definition 2.3), read 2026-09-26; does not bear, see settle',
    ],
    status: 'unsearched',
    settle:
      'Three of R1–R4 read cleanly; R4 carries three \\ill{} in its statement and is not fully recoverable, and page 193 is cancelled by long diagonals, so the equivalence rests on a page its author struck. Any search should therefore first settle what R4 says, which is /transcribe-grothendieck’s work and not this skill’s. Then compare with the modern axiomatisations of a Galois category without a fibre functor (finite limits, disjoint distributive coproducts, an effective descent morphism to the terminal object with a finite decomposition property) and with the stack-theoretic treatments of tame coverings — Kerz–Schmidt, Generators and relations for the étale fundamental group, arXiv math/0703139, which reduces statements about open varieties to proper stacks by Abhyankar’s lemma. An orienting web search found the axiomatisation of Galois categories without a fibre functor, and the stack-theoretic treatment of tame π₁, but no axiomatisation of a stack of such categories carrying a realisation functor. That is a reason to look, not a search of the sources. Checked on 2026-09-26 against Abbes–Saito 2002, the one axiomatic passage of their ramification theory: §2 works inside a single Galois category (C, F) of finite étale K-algebras over one complete discrete valuation field, and axiomatises quotients F → F′ of its fibre functor (surjectivity and a cocartesian condition, Proposition 2.1; filtrations by such quotients, Definition 2.3) so as to cut out closed normal subgroups G^a. There is no base scheme, no stack over Ét(S), no realisation functor into schemes and nothing corresponding to R1–R4 or to R2 ⟺ r faithful; it does not bear on this row, and nothing was found there. The status stays unsearched, not candidate, because of R4 and the struck page 193, not for want of that check. Kerz–Schmidt and the fibre-functor-free axiomatisations named above remain unread.',
  },
  {
    id: '29-domram-morphisms-fully-faithful',
    cote: '29',
    pages: '197',
    kind: 'mathematical',
    claim:
      'The ramification domains over S form a 2-category in which every homomorphism is necessarily fully faithful: for (R, r) defined by a scheme Z with a finite group G of operators, Hom((R,r),(R′,r′)) is equivalent to the category of pairs (P′, α) with P′ a galoisian object of R′_S of group G and α a G-isomorphism r′(P′) ≃ Z.',
    basis:
      'Proposition 6 of page 197 establishes the equivalence, and the corollary drawn from it states that in any homomorphism (φ, λ) of ramification domains φ is necessarily fully faithful. A second corollary describes Hom, when (R′,r′) is defined by (Z′,G′), as the principal coverings P′ of Z′ of group G with a compatible G′-action and an isomorphism P′/G′ ≃ Z.',
    ours:
      'Nothing of the statement. The reading draws the consequence in prose — that a ramification domain maps into another only as a subdomain — which the page leaves implicit in the word « nécessairement ».',
    literature: [],
    status: 'unsearched',
    settle:
      'A rigidity statement of this shape — no non-trivial collapsing morphism between such objects — should be checked against the 2-categorical literature on stacks of Galois covers: Ramified Galois covers via monoidal functors (Transformation Groups 2016, arXiv 1507.05309) and Stacks of ramified Galois covers (arXiv 1307.1116) are where an equivalent statement would sit. Neither surfaced in an orienting search, which is not the same as their not containing it.',
  },
  {
    id: '29-degree-n-as-primitive',
    cote: '29',
    pages: '212, 214',
    kind: 'mathematical',
    claim:
      'The « degree n » of a morphism can be taken as primitive data on a category rather than derived from a fibre functor: six conditions on a class of degree-n morphisms — base change, finite additivity, isomorphisms of degree 1, a decomposition Y = ∐ₙ Yₙ with X ×_Y Yₙ → Yₙ of degree n, effective descent for degree ≥ 1, and emptiness in degree 0 — determine the notion uniquely, and it then coincides with « trivialised by a morphism of universal effective descent ».',
    basis:
      'The six conditions are item (3) of the inserted « feuille 1 bis » (page 212); the uniqueness is the Conclusion of page 214, proved by induction on n through the diagonal of X ×_Y X, which is a universal direct summand, giving X′ ≃ Y′ ⊔ X′₁ with X′₁ → Y′ of degree n−1.',
    ours:
      'The reading names what the axiomatisation is for — saying that a covering has n sheets without having points to count — and observes that condition d′) makes the degree a decomposition of the base rather than a number. Neither gloss is on the page.',
    literature: [],
    status: 'unsearched',
    settle:
      'Item (3) and the Conclusion read cleanly, but items (2) and (1) of the same sheet are largely illegible — « Tous les monomorphismes […] […] un […] » and « Existence des lim← finies […] » — so the four conditions A(iv) are not recoverable as a list and only the degree axioms themselves can be claimed. Compare with the fibre-functor-free axiomatisation of a Galois category, where the decomposition property already appears as part of the definition rather than as data: if the two coincide this is a match. An orienting web search located that axiomatisation but not the degree-as-primitive form nor the uniqueness statement.',
  },
  {
    id: '29-formal-tame-pi1-self-intersection',
    cote: '29',
    pages: '87–97',
    kind: 'mathematical',
    claim:
      'For a regular formal scheme 𝔛 whose special fibre X_o is a component of a normal crossings divisor D, the tame fundamental group π₁ᵗ(𝔛/D) is a central extension of π₁ᵗ(X_o/D′_o) by a quotient of μ^∞, and the class of that extension is the Chern class of the self-intersection of X_o in 𝔛; for X_o = P¹_k with D′_o empty the extension is μ_n(k) with n the prime-to-p part of the degree of X_o · X_o.',
    basis:
      'Lemme 1 (page 87) kills H¹ of the universal tame covering, which makes the Hochschild–Serre sequence usable in low degree; Lemme 2 (page 89) identifies ρ(α) with σ(β) for β the class of the normal bundle; page 93 relieves the obstruction using that the kernel of Pic(X_m) → Pic(X_o) is uniquely n-divisible; page 95 concludes through the Kummer theorem for 𝔛/D, and page 97 works the two examples.',
    ours:
      'The reading supplies the reason page 93 omits — n is invertible on X_o and the kernel is filtered by cohomology of O_{X_o}-modules — and separates the class of a line bundle in H¹(G_m) from its Chern class in H²(μ_n), which pages 89 and 95 write in the two different groups without comment.',
    literature: [
      'SGA 1, exposé XIII (Mme M. Raynaud), Appendice I « Variations sur le lemme d’Abhyankar », 5.1–5.7 (arXiv math/0206203), read 2026-09-26 — Corollaire 5.3 and 5.6: over a strictly local regular base, π₁ᵗ(U) ≃ ∏_{ℓ≠p} Z_ℓ[1]^r canonically; local only',
      'L. Illusie, An overview of the work of K. Fujiwara, K. Kato, and C. Nakayama on logarithmic étale cohomology, Astérisque 279 (2002), 271–322 — §1.7, §4 (4.6, Examples 4.7 (a)–(e)), §6.4, §8.1, read 2026-09-26',
      'A. Abbes and T. Saito, Ramification of local fields with imperfect residue fields (arXiv math/0010103), §1; Ramification and cleanliness (Tohoku Math. J. 63, 2011; arXiv 1007.3873), §1–2 and 7.19 — read 2026-09-26; do not bear, see settle',
    ],
    status: 'candidate',
    settle:
      'Checked on 2026-09-26. SGA 1 XIII 5.3 and 5.6 give the tame fundamental group of the strict localisation at a point of a normal crossings divisor, ∏_{ℓ≠p} Z_ℓ[1]^r with one factor per branch — the fibre of the extension, not the extension. Illusie’s overview gives the log fundamental group of an fs log scheme (4.6), the exact sequence 1 → I^log → π₁^log(s) → π₁(s) → 1 with I^log ≅ Hom(M̄^gp, Z′(1)) at a log point (4.7 (a)), and its identification with the Grothendieck–Murre tame fundamental group for a regular scheme with a normal crossings divisor (4.7 (c), citing Kato); it computes no global extension over a component of the divisor and nowhere relates an extension class to a normal bundle or a self-intersection. Neither source contains the statement; nothing was found. Abbes–Saito do not bear: the 2002 paper treats the ramification filtration of one complete discrete valuation field, where the tame part is only G^{0+}_log = wild inertia, and « Ramification and cleanliness » bounds wild ramification of torsors and sheaves along an snc divisor over a perfect field, invoking SGA 1 XIII 5.2 and 5.4 for the tame part (proof of 7.19). What remains, and would most likely settle it: Grothendieck–Murre, The tame fundamental group of a formal neighbourhood of a divisor with normal crossings on a scheme (LNM 208, 1971), whose subject is exactly this situation — not read, no copy reachable from here; Kato–Nakayama’s own papers; and, for the P¹ case, the classical computation of the local fundamental group at a contracted smooth rational curve of self-intersection −d (cyclic of order d over C), which is what the example should reduce to and was not looked up. Transcription: « auto » in « d’auto-intersection » (Lemme 2, page 89) and « du degré » (page 97) are \\uncertain{}; the general conclusion on page 95, « [self-intersection de X_o dans 𝔛] », reads cleanly, and page 89’s formula 𝓛_{X_o/𝔛} ≃ i*(L(X_o)) fixes the meaning independently of the uncertain word. Pages 91 and 93 are the faintest of the run and much of their connective prose is illegible, so what can be claimed is the two lemmas and the two examples, not the passage between them.',
  },
  {
    id: '29-fundamental-group-scheme-via-torsors',
    cote: '29',
    pages: '124–129, 136–142',
    kind: 'mathematical',
    claim:
      'The fundamental group scheme — the pro-object classifying pointed torsors under finite group schemes, infinitesimal part included — is obtained by strict pro-representability of the pointed-torsor functor alone, with no Tannakian input, and computed on an abelian variety as lim← ₙX, Cartier-dual to the ind-algebraic lim→ ₙX*.',
    basis:
      'The letter to Serre of 18 October 1959 (pages 124–129) sets the conditions (i)–(vi), proves Z(S,a;G) commutes with products and with kernels of pairs, and derives the filtered projective system from the minimal couples; the handwritten pages 136–142 prove the injectivity of u ↦ u_*(α) on which the uniqueness of the transition morphisms rests, and construct π₁^C(S,ξ) from the same two formal properties.',
    ours:
      'The reading identifies the letter’s Z(S,a;G), the feuilles anciennes’ ℨ and the π¹(S,ξ;G) of pages 164–169 as one functor under three notations, which no single page states; and it corrects page 137’s ×_G G′ to ×_{G′} G, the extension of the structure group.',
    literature: [
      'M. V. Nori, On the representations of the fundamental group (Compositio Math. 33, 1976) and The fundamental group-scheme (Proc. Indian Acad. Sci. 91, 1982) — the second construction, by the filtered category of pointed torsors under finite group schemes, is this route',
      'C. Gasbarri, on the fundamental group scheme of an integral scheme over a connected Dedekind base as the projective limit of the finite flat group schemes occurring in pointed torsors',
    ],
    status: 'matched',
    settle:
      'Killed. The published literature already credits the conjecture that such a group scheme exists to Grothendieck, and Nori gave two constructions, the second of which is exactly this one: the category of pointed torsors under finite group schemes is filtered, and the group scheme is the projective limit of the groups occurring in it — a statement the literature records as equivalent to the existence of the fundamental group scheme. The abelian-variety computation and its Cartier duality are Nori’s theorem. Kept as a killed candidate. One residue is not killed and is worth a separate look: the letter works over a base scheme S merely reduced, connected and pointed, with an auxiliary category G and an exact functor F, rather than over a field or a Dedekind base — whether the construction has been carried out at that generality is a different question from the one settled here. Nothing in this row is a claim about who was first; the folder is undated apart from the letter itself.',
  },
  {
    id: '29-kummer-gerbe-root-stack',
    cote: '29',
    pages: '199–200',
    kind: 'mathematical',
    claim:
      'The tame coverings of a pair (S, D) are constructed as the finite étale coverings of the stack associated to the gerbe whose objects over S′ are the families of equations of the D_i and whose morphisms are the families ξ with b_i = a_i ξ_i^{n_i} — an abelian μ_n-gerbe whose obstruction to a global section is the cohomology class of the D_i.',
    basis:
      'Example 2 of page 200 defines the groupoid, identifies the automorphism group of an object as μ_n, and states the obstruction: « L’existence d’une section dépend de la nullité d’un élément de H²(X, μ_n), qui n’est autre, comme on devine, que la classe de cohomologie des D_i ». Example 1 is the trivial-gerbe case with global equations, and the two « bis » examples take the limit over n.',
    ours:
      'The reading names the object and separates the two exponents of H, which the page writes in one hand that does not distinguish 1 from the roman numeral; the class of a line bundle is in H¹(G_m) and its Chern class in H²(μ_n).',
    literature: [
      'C. Cadman, Using stacks to impose tangency conditions on curves (2007), and Abramovich–Graber–Vistoli — the root stack construction',
      'Abramovich–Olsson–Vistoli, Tame stacks in positive characteristic (Ann. Inst. Fourier 58, 2008)',
      'Biswas–Borne, Tamely ramified torsors and parabolic bundles',
      'Kerz–Schmidt, Generators and relations for the étale fundamental group (arXiv math/0703139) — tame π₁ by reduction to proper stacks',
    ],
    status: 'matched',
    settle:
      'Killed as an object: this is the root stack of the divisors D_i with multiplicities n_i, its inertia gerbe, and its obstruction class, all of which are in the sources listed, and the identification of tame coverings of a pair with étale coverings of that stack is standard. Kept as a killed candidate so that the next reader does not spend a day on it. What is NOT killed by this row is the axiomatisation those examples instantiate, which is filed separately as 29-ramification-domain-axioms.',
  },
  {
    id: '29-h1-five-classes-infinite-group',
    cote: '29',
    pages: '170–171',
    kind: 'mathematical',
    claim:
      'For a discrete and possibly infinite group G, the classification of G-torsors is compared across five classes of covering families — fppf quasi-compact, finite type, quasi-finite, finite principal, finite étale principal — with H¹_{C₃} ≃ H¹_{C₂} in general, H¹_{C₂} ≃ H¹_{C₁} over a Dedekind ring, H¹_{C_i} ≃ H¹(V̂/V, −) for i = 1,2,3 over a complete discrete valuation ring with algebraically closed residue field, and H¹_{C₅} ≃ H¹_{C₄} ≃ H¹_{C₃} together with H¹_{C_i}(V,−) ≃ H¹_{C_i}(k,−) over a complete local ring.',
    basis:
      'Pages 170 and 171 define H¹_C(S,G) = lim→_{T/S} H¹(π₀(K_{T/S}), G), list the five classes, observe that for G finite every comparison map is bijective and the whole apparatus collapses to Hom(π₁(S,a),G)/int(G), and then state the four comparisons above. These two pages are written out fair and carry only five \\ill{} between them, which makes them the most legible support of any row for this cote.',
    ours:
      'The reading supplies the reason the finite case collapses — G_T is then affine over T and fpqc descent for affine morphisms is effective — which the page asserts without argument, and which is what makes the infinite case the only one with content.',
    literature: [],
    status: 'unsearched',
    settle:
      'Compare with the pro-étale fundamental group of Bhatt–Scholze (2015) and with the enlarged fundamental group of SGA 3 X, both of which classify locally constant objects with infinite fibres, and check whether the four comparison statements across these five classes are recorded anywhere in that form. The complete-local statement H¹_{C_i}(V,−) ≃ H¹_{C_i}(k,−) is the one most likely to be standard and is the place to start.',
  },
  {
    id: '29-inertia-matrix-determinant',
    cote: '29',
    pages: '120',
    kind: 'mathematical',
    claim:
      'For a morphism between strictly local regular schemes with normal crossings divisors, the map on tame inertia is given by the matrix N of multiplicities in f*(Ē_{c′}) = Σ_c n_{c,c′} D̄_c, and N is an isomorphism if and only if card C = card C′ and the ordinary integer det N is ± a power of the residue characteristic — in which case the inertia subgroups of H at y are exactly the conjugates of the images of those of G at x.',
    basis:
      'Number 4 of the typescript « Comportement fonctoriel des groupes d’inertie » (page 120) draws the commuting square between G_ξ → H_y and the map N on ∏_{ℓ≠p} Z_ℓ(1)^C, with the canonical epimorphisms of (3.1) as the vertical arrows, and states the criterion.',
    ours:
      'Nothing of the statement; the typescript is legible throughout. The reading supplies the one-line reason the criterion takes that form — N must be invertible over ∏_{ℓ≠p} Z_ℓ, so det N must be prime to every ℓ ≠ p, so a power of p up to sign — which the page does not give.',
    literature: [
      'SGA 1, exposé XIII (Mme M. Raynaud), Appendice I, 5.1–5.6 (arXiv math/0206203) — Corollaire 5.3: π₁ᵗ(U) ≃ ∏_{ℓ≠p} Z_ℓ[1]^r canonically for X strictly local regular, D with r branches; read 2026-09-26',
      'L. Illusie, An overview of the work of K. Fujiwara, K. Kato, and C. Nakayama on logarithmic étale cohomology, Astérisque 279 (2002) — 1.6 (Kummer maps of monoids), 1.7, 2.8–2.9 (Kummer homeomorphisms), 4.6 and Examples 4.7 (a), (c), (d) (log inertia I^log ≅ Hom(M̄^gp, Z′(1)), compared with Grothendieck–Murre); read 2026-09-26',
      'A. Abbes and T. Saito, Ramification and cleanliness, Tohoku Math. J. 63 (2011), arXiv 1007.3873 — §2, Lemma 2.13 and Lemma 2.15 (inertia groups under specialisation and under pull-back of a Galois torsor); read 2026-09-26',
    ],
    status: 'candidate',
    settle:
      'Checked on 2026-09-26; the criterion was not found written in the sources listed. It is, however, one step from what they do contain, and should be expected to be folklore. SGA 1 XIII 5.3 makes the tame inertia at a point with r branches canonically ∏_{ℓ≠p} Z_ℓ[1]^r, one factor per branch, and Illusie 4.7 (a) gives the log inertia as Hom(M̄^gp, Z′(1)), contravariant in the log structure; for normal crossings M̄ is free on the branches and f* acts on it by the multiplicity matrix, so the map on inertia is N (up to transposition), an isomorphism if and only if N is invertible over Z′ = ∏_{ℓ≠p} Z_ℓ, that is det N ∈ Z ∩ Z′^× = {± p^k} — the reading’s one-line argument. Neither source writes that step, the determinant form, or the conjugacy statement. Abbes–Saito Lemma 2.15 gives only the inclusion I_{y′} ⊂ I_y of inertia groups under pull-back of a Galois torsor along any morphism of normal schemes, not the equality up to conjugacy under the determinant condition. Illusie’s 1.6 is the monoid-level form of the same condition (Kummer: injective with torsion cokernel), and « Kummer with cokernel of p-power order » is what det N = ± p^k says for free monoids, but the overview states it for Kummer étale maps (cokernel prime to p), not for isomorphism on prime-to-p inertia. What remains (cited from memory, not read): Kato, Logarithmic structures of Fontaine–Illusie (1989) and its part II on the Kummer-étale topology, Nakayama’s and Vidal’s papers on the log fundamental group, and Grothendieck–Murre LNM 208, where a functoriality statement for tame inertia would naturally sit. If any of them states the invertibility criterion on inertia for a morphism of normal crossings pairs, mark matched.',
  },
  {
    id: '29-order-not-chronology',
    cote: '29',
    pages: '1–11, 124–129, 141–160, 188–216',
    kind: 'codicological',
    claim:
      'The shelfmark’s pagination is not its order of composition: the 1967 exchange with Murre is bound out of chronological order within itself, the earliest dated piece in the folder — a letter to Serre of 18 October 1959 — sits at page 124, and the synthesis the folder builds towards is undated and at the end, so a reader following the argument must cross the pagination in both directions.',
    basis:
      'The letters date themselves. The archive order of pages 1–11 is: Murre 16 May 1967 (pages 2–3), Murre 29 March 1967 (4–5), Grothendieck’s undated reply (7–8), Grothendieck 29 April 1967 (9–11) — that is, the last letter of the exchange first. The 1959 letter is at pages 124–129, the chemise « Compléments SGA / 1960 » covers pages 144–160, the 1969 exchange is at pages 77–85, and the domaines de ramification run at 188–216 carries no date at all. Grothendieck paginates six of his own runs and restarts each time — I–VI (46–57), 1–4 (60–63), A–L (65–76), 1–6 (87–97), 1–10 then 11–16 (190–206), and 1–6 with inserted 1 bis and 1 ter (208–216) — so his own numbers, not the archivists’, are what a cross-reference such as « cf. p. 12 » follows.',
    ours:
      'The reconstruction of the 1967 sequence is the transcription’s, from the datelines and from Murre’s reference to the enclosed sketch; the six paginations are recorded batch by batch in the transcription headers. The modernised reading states the consequence — that the argument and the pagination cross — which no single page can.',
    literature: [],
    status: 'unsearched',
    settle:
      'Checkable directly against the facsimile: read the four datelines of pages 2, 4 and 9 and the undated reply at 7, and confirm the six self-paginations in the top corners. Nothing here depends on the literature. What is not established, and is not claimed, is any date for the undated runs: the inventory’s « 1959-1969 » is its own and covers the shelfmark whole.',
  },
  {
    id: '54-universal-extension-de-rham-dual',
    cote: '54',
    pages: '2, 4',
    kind: 'mathematical',
    claim:
      'The folder computes the Lie algebra of the universal vector extension of an abelian variety A as the de Rham cohomology H¹_dR(B) of the dual, identifies the resulting extension of tangent spaces with the Hodge filtration of B, and deduces the duality of H¹_dR(A) and H¹_dR(B) by transposition.',
    basis:
      'Page 2 classifies extensions of A by a vector group V as Hom(H¹(A,𝒪_A)^∨, V), takes the universal one at V = t_B^∨, passes to tangent spaces to get 0 → ť_B → t_E → t_A → 0, asserts that this sequence is S_B and that it is the transpose of S_A, and boxes the conclusion. Page 4 carries the same statement to every degree through the exterior algebra on the degree-1 part.',
    ours:
      'Three things. S_A and S_B are used on the page and defined nowhere; the reading supplies the identification with the Hodge filtration sequences, which is the only reading under which both assertions made about them hold. The caron of ť_B is read as the linear dual, a convention the page does not state. And the sentence introducing the universal extension is reworked twice on the leaf with two words illegible between the states, so the prose framing the construction — not the formulas — is partly the edition’s.',
    literature: [
      'B. Mazur and W. Messing, Universal Extensions and One Dimensional Crystalline Cohomology, LNM 370 (1974) — §I, the universal extension and its Lie algebra',
      'W. Messing, The Crystals Associated to Barsotti–Tate Groups, LNM 264 (1972)',
      'D. Mumford, Abelian Varieties, §13 (the dual abelian variety and Ext by G_a)',
      'Transcription 54, batch 1 (batch-01.fr.tex), pages 2 and 4',
    ],
    status: 'matched',
    settle:
      'Settled: the identification of Lie E(A) with H¹_dR(B), the comparison of the vector-extension filtration with the Hodge filtration, and the resulting duality are the content of Mazur–Messing. Kept as a killed candidate because it is the entry a reader of this folder will most want to open, and because the tempting next step — reading the inventory’s deduced « [à partir de 1971] » as evidence of precedence — is the one thing this folder cannot support. See 54-dating-cannot-support-precedence.',
  },
  {
    id: '54-frobenius-kernels-orthogonal',
    cote: '54',
    pages: '4, 6',
    kind: 'mathematical',
    claim:
      'In characteristic p the folder asserts that ker F_A ⊂ A[p] and ker F_B ⊂ B[p] are orthogonal to each other for the Weil pairing, and that A[p] is the canonical extension of D(ker F_B) by ker F_A.',
    basis:
      'Page 4 fixes ker F_A = gr(t_A) inside A[p], corrects its rank from p^2d to p^d in the author’s own hand, and states the orthogonality as a claim — « Je dis que » — with no argument. Page 6 draws the Frobenius and Verschiebung rows as two transposed sequences and writes the exact sequence 0 → Gr(t_A) → A[p] → D(Gr(t_B)) → 0, calling A[p] the canonical extension of D(F^B) by F^A.',
    ours:
      'The two-line verification is the edition’s: for H ⊆ A[p] the annihilator is D(A[p]/H), the factorisation p = VF gives A[p]/ker F_A ≅ ker V_A, and Cartier duality exchanges F and V, so (ker F_A)^⊥ = D(ker V_A) = ker F_B. The page asserts the orthogonality and proves nothing. The third node of the diagram’s top row is written as a bare V-shaped stroke and is read as A by symmetry with the row below; the transcription flags it.',
    literature: [
      'D. Mumford, Abelian Varieties, §15 (the Weil pairing, and the duality of Frobenius and Verschiebung)',
      'T. Oda, The first de Rham cohomology group and Dieudonné modules, Ann. Sci. ÉNS 2 (1969)',
      'W. C. Waterhouse, Introduction to Affine Group Schemes, ch. 2 (Cartier duality)',
      'Transcription 54, batch 1 (batch-01.fr.tex), pages 4 and 6',
    ],
    status: 'matched',
    settle:
      'Settled: that D(ker F_A) = ker V_B and hence that the Frobenius kernels of A and of its dual are exact mutual annihilators is standard, and the exact sequence is the usual filtration of A[p]. Kept because it is the only result the folder states without proving, which makes it look like a candidate, and because the parallel the folder draws between this sequence and the universal vector extension — which it poses as a question and leaves on two question marks — is answered by the crystalline comparison, not by anything on these leaves.',
  },
  {
    id: '54-dating-cannot-support-precedence',
    cote: '54',
    pages: '1–7',
    kind: 'codicological',
    claim:
      'Nothing in the folder dates these leaves: the inventory’s « [à partir de 1971] » is the archivists’ deduction for the shelfmark, the folder’s own title records it as « s.d. », and no leaf of the batch carries a date.',
    basis:
      'The transcription records that no page of the folder bears a date. The inventory title is « Dualité en cohomologie des V. A [variétés abéliennes] : notes manuscrites (s.d.) » — sans date on the archive’s own reading — while the catalogue entry carries the bracketed range « [à partir de 1971] », the brackets being the archivists’ convention for a date deduced rather than read. The two versos that could have dated the folder do not: the flatness typescript of pages 3 and 5 is undated, and the Bourbaki typescript of page 7 carries an internal document number but no year the transcription records.',
    ours:
      'Nothing of the dating, which is copied verbatim from the inventory into both editions. The reading names Mazur–Messing (1974), Oda (1969) and Raynaud–Gruson (1971) as the places the folder’s material now sits, and in each case footnotes that the concordance of subjects is not evidence about order.',
    literature: [
      'Montpellier inventory, cote 54 (title and dating, both reproduced in src/content/catalogue.ts)',
      'Transcription 54, batch 1 (batch-01.fr.tex), all pages',
    ],
    status: 'candidate',
    settle:
      'Only physical evidence would settle it — a dated verso, a letterhead, or an identification of the Bourbaki typescript on page 7, whose internal number would place that sheet and therefore give a terminus for the leaf whose recto it is. This entry exists to stop the next reader treating « [à partir de 1971] » as a reading of these leaves: it is a deduction about the shelfmark. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '54-flatness-typescript-fragment',
    cote: '54',
    pages: '3, 5',
    kind: 'codicological',
    claim:
      'Pages 3 and 5 are two leaves of a typescript on flatness that does not otherwise survive in this folder, and its Proposition 4.1 cannot be evaluated from them: the statement as the leaves carry it, after the author’s own correction, admits a counterexample, so hypotheses standing elsewhere in the lost document are load-bearing.',
    basis:
      'The typed Proposition 4.1 supposes I nilpotent and concludes that M is free or flat over A; the author strikes « nilpotent » in ink and rewrites the conclusion as: for all n, M ⊗_A A/I^(n+1) is free (resp. flat) over A/I^(n+1). Taken with only the hypotheses printed on the leaf, that fails: A = ℤ, I = (p), the one-member family A_1 = ℚ (so the intersection of the kernels of A → A_i is 0), M = ℤ/p. Then M ⊗ A/I = ℤ/p is free of rank 1 over ℤ/p and M ⊗ ℚ = 0 is free of rank 0 over ℚ, but M ⊗ ℤ/p² = ℤ/p is not free over ℤ/p². A joint faithful flatness condition on the family — which ℚ alone fails — would kill the example, and is the kind of standing hypothesis a typescript states once and early.',
    ours:
      'The counterexample is the edition’s; the leaves carry the statement and no proof of the corrected form, the typed argument below it treating the nilpotent case the author has just removed. The modernised reading reports the corrected statement without certifying it, and this entry says why.',
    literature: [
      'Transcription 54, batch 1 (batch-01.fr.tex), pages 3 and 5',
      'A. Grothendieck, EGA IV, §11 (critères de platitude) — the family the typescript’s numbering suggests, not yet collated against it',
      'M. Raynaud and L. Gruson, Critères de platitude et de projectivité, Invent. Math. 13 (1971) — for the flattening stratification of page 5',
    ],
    status: 'candidate',
    settle:
      'Identify the typescript. If it is a draft of a published section, its standing hypotheses settle the question at once and this entry becomes matched. Two internal clues are available without leaving the fonds: the leaves cite « Prop. A » in a typed correction over a struck reference to 4.1, and page 5’s heading « Corollaire 4.1. ter » is renamed « Proposition A » in ink, so the document had at least the statements 4.1, 4.1 bis, 4.1 ter and 4.1 quater and was being restructured while it was typed. A search of the neighbouring shelfmarks of the group « 45-54 » for the missing leaves would be the next step.',
  },
  {
    id: '26-sga4-viii-79-draft',
    cote: '26',
    pages: '3, 5',
    kind: 'codicological',
    claim:
      'Pages 3 and 5 are a typescript of SGA 4 VIII 7.9.1–7.9.3 in a state earlier than the published text, and they differ from it at two points: the folder reads « préschéma » where the published text reads « schéma », and the folder’s displayed equivalence reads « φ(U) ≠ ∅ ⇔ x ∈ U » where the Orgogozo re-edition prints « φ(U) = ∅ ⇔ x ∈ U », which is false as printed.',
    basis:
      'The two leaves, paginated 31 and 32 by the machine and struck through with one diagonal, carry 7.9.1 (a fibre functor is the filtered colimit of its neighbourhoods), 7.9.2 (fibre functors of a localised topos) and 7.9.3 (every point of the étale topos is a geometric point), in wording that tracks the published exposé sentence by sentence. At the close of 7.9.3 the folder has « le préschéma lim des X′ … existe et est un localisé strict Z de X », the published text « le schéma lim des X′ … ». The transcription notes that the final s of « les préschémas » was overtyped, so the word is the typist’s own and not a slip. Since EGA renamed préschéma to schéma in its 1971 second edition, the folder’s wording is the earlier of the two.',
    ours:
      'The identification with SGA 4 VIII 7.9 is the edition’s: the leaves carry no title, only the internal numbering 7.9.1 to 7.9.3, and the modernised reading proposed the match on that numbering and the content. The comparison recorded here was then made against the Orgogozo re-edition, which is what the second half of the claim rests on.',
    literature: [
      'Transcription 26, batch 1 (batch-01.fr.tex), pages 3 and 5',
      'SGA 4, Exposé VIII (Foncteurs fibres, supports, étude cohomologique des morphismes finis), §7.9.1–7.9.3, in the re-edition by F. Orgogozo (normalesup.org/~forgogozo/SGA4/08), consulted directly',
    ],
    status: 'candidate',
    settle:
      'Collate the two leaves against the 1972 Lecture Notes in Mathematics 270 printing, which was not consulted here. That decides both halves at once: whether « préschéma » stood in the first printing, and whether the « = ∅ » is a misprint of the re-edition or is inherited from 1972. If it is inherited, the folder’s leaves carry the correct form of a line that has been wrong in print since.',
  },
  {
    id: '26-wrapper-numbered-v',
    cote: '26',
    pages: '1',
    kind: 'codicological',
    claim:
      'The folder’s own wrapper numbers the chapter V, not VI: the inventory’s title « EGA VI » is the archivists’ identification of the contents, not a reading of the leaf.',
    basis:
      'Page 1 is a brown wrapper carrying, in ink in the top right corner, an underlined « V » and beneath it « Plan » and « Notations », and nothing else. The note isolated on page 4 refers the reader for the general material to a chapter it writes with the same underlined V. The contents — descent, quotients, Hilbert, Picard, methods of construction — are those the plan printed in EGA I (1960) assigns to chapter VI, « Technique de descente. Méthodes générales de construction de schémas », chapter V there being « Procédés élémentaires de construction de schémas ».',
    ours:
      'The discrepancy is on the leaf; what the edition supplies is the comparison with the 1960 plan, and the observation that the folder’s two uses of V are consistent with each other.',
    literature: [
      'Transcription 26, batch 1 (batch-01.fr.tex), pages 1 and 4',
      'Catalogue entry for shelfmark 26 in src/content/catalogue.ts, which follows the Montpellier inventory',
      'A. Grothendieck and J. Dieudonné, EGA I (Publ. Math. IHÉS 4, 1960), the plan of the treatise printed in the introduction',
    ],
    status: 'candidate',
    settle:
      'Whether the fonds holds another folder whose wrapper numbers a chapter, and how those numbers line up with the 1960 plan. If a second wrapper shows the same shift by one, the folder is witness to an intermediate renumbering of the treatise rather than to a slip.',
  },
  {
    id: '26-later-annotation-campaign',
    cote: '26',
    pages: '10',
    kind: 'codicological',
    claim:
      'The answers in the margin of the open-problems list were added in a later campaign than the list itself, so the folder records two moments and the inventory’s single date « [après 1967] » covers only the earlier.',
    basis:
      'The list is written in one hand and one ink; the marginal material beside it is not. « OK par Raynaud » is boxed, « Oui » is circled, and the « VI » of the two « Chap VI » references is gone over in felt-tip, a medium used nowhere else on the leaf. The answers respond to the items rather than accompanying them: item b) asks for Hilbert and Picard without a projective hypothesis and is marked with partial results, then the dual of a non-projective abelian scheme is marked done.',
    ours:
      'The reading of the marginal word attached to the Raynaud note is uncertain in the transcription — « Dual » is given under reserve — so the identification of which theorem is being marked off is the edition’s inference from the line above it, which is not in doubt.',
    literature: [
      'Transcription 26, batch 1 (batch-01.fr.tex), page 10',
      'M. Raynaud, Faisceaux amples sur les schémas en groupes et les espaces homogènes, Lecture Notes in Mathematics 119 (1970) — the published form of the result the margin appears to mark off, not collated against the leaf',
    ],
    status: 'unsearched',
    settle:
      'This cannot be settled by a publication date. Raynaud was Grothendieck’s student and the result circulated before it was printed, so the margin bears no terminus of its own. What would settle it is the leaf: whether the felt-tip and the boxed and circled marks form one campaign, and whether the same medium appears on dated material elsewhere in the fonds.',
  },
  {
    id: '161-2-lambda-types-split-with-161-3',
    cote: '161-2',
    pages: '89–91, 92, 97–106',
    kind: 'codicological',
    claim:
      'The manuscript on λ-types is divided between two shelfmarks: the fair copy ①–⑩ of 161-2 (pages 97–106), with the dictionaries of pages 89–91, and the odd-numbered French run of folder 161-3 (pages 35–43) belong to one campaign of work, and the half-legible line of 161-2 page 92 is the argument written out on 161-3 pages 39–41.',
    basis:
      'Both use the same private notation and the same numbered statements: (Cat_λ), λ-types, S^T_λ and R^λ_T, the square T(Ĉ) → Hom_λ(C°, S) marked « 2-cart », the diagram of restriction (λ-types) → (λ′-types) for λ ⊂ λ′ with a « ? » on the dashed arrow, and the case λ = (λ←, ∅). Folder 161-3, page 41, sets λ = λ₀ and takes « les anneaux de polynômes » as S^T_λ, then exhibits ℤ[t] → ℤ[t, t⁻¹] × ℤ as the map whose transform is bijective exactly on fields; folder 161-2, page 92, carries the same map, « ℤ[H] → ℤ[t, t⁻¹] × ℤ », in a line half of which the transcription could not read, and page 93 continues with ℤ[t, t⁻¹] = ℤ[x, y]/(xy − 1). The 161-3 leaves are drafts on the versos of a lecture plan in English; the 161-2 leaves are the fair copy and its working papers.',
    ours:
      'The comparison is the edition’s; neither folder refers to the other. The reading of 161-2 page 92 leaves the pseudo-field line unreconstructed, and this entry says what it is without repairing the transcription.',
    literature: [
      'Transcription 161-2, batches 5 and 6 (batch-05.fr.tex, batch-06.fr.tex), pages 89–106',
      'Transcription 161-3, batches 2 and 3 (batch-02.fr.tex, batch-03.fr.tex), pages 35–43, and the finding 161-3-fields-partition',
    ],
    status: 'candidate',
    settle:
      'Compare the paper, the hand and the ink of 161-3 pages 35–43 with 161-2 pages 89–106 on the facsimiles, and check whether the alinéa numbers on the 161-3 leaves (« 1 » and « 3 » in his hand) fit between the [1]–[8] of the fair copy or precede it as a draft. Neither facsimile was examined for this.',
  },
  {
    id: '161-2-section-9-bound-before-its-text',
    cote: '161-2',
    pages: '89, 97–106',
    kind: 'codicological',
    claim:
      'The leaf at page 89 carrying the single heading « 9. Relation avec analyseurs de Lazard » is the section that was to follow alinéa [8] of the fair copy ①–⑩, which ends on page 106 in mid-sentence; the leaf is bound seventeen pages before the text it continues.',
    basis:
      'The fair copy numbers its alinéas [1] to [8] in squares, [8] being the case λ→ = ∅, and stops on page 106 after « On voit alors que l’on trouve ainsi une ». Page 89 is a half-sheet on λ-categories in the same notation (Σ = R° ⊂ S ⊂ R̂°, the properties a)–d) of S), photographed with an otherwise blank leaf on which « 9. Relation avec analyseurs de Lazard » stands alone in his hand. No other run in the folder carries a section 9, and the fair copy is the only one numbered.',
    ours:
      'The inference from the numbering is the edition’s. The transcription of page 89 reads the name as « Lazare » and gives « Lazard » under reserve; the identification with Lazard’s analyseurs is supported by the margin of page 22, which uses the word « analyseur » for the free theory on the base objects.',
    literature: [
      'Transcription 161-2, batch 5 (batch-05.fr.tex), page 89, and batch 6, pages 101–106',
      'M. Lazard, Lois de groupes et analyseurs, Ann. Sci. ENS 72 (1955) — the source of the word, not collated',
    ],
    status: 'candidate',
    settle:
      'Look at the facsimile of page 89 beside pages 97–106: same paper and pen would settle it. The half-sheet and the blank leaf were photographed together, which suggests they were found together; whether they were found next to the fair copy is what the binding order does not say.',
  },
  {
    id: '161-2-field-classifier-absolutely-flat-site',
    cote: '161-2',
    pages: '41–42, 92–95',
    kind: 'mathematical',
    claim:
      'The classifying topos of fields is presented as the topos of sheaves on the opposite of the finitely presented commutative absolutely flat (von Neumann regular) rings, for the topology generated by the covers Spec A_f ⊔ Spec A/f → Spec A, with the generic field as its structure sheaf — the field classifier obtained by first passing to the presheaf classifier of absolutely flat rings and then imposing one covering condition.',
    basis:
      'Page 94 factors the map e ⊔ O* → O of the universal ring through i : D → O, a morphism of R (the affine schemes of finite type over ℤ); inverting the morphisms i gives a category of fractions R′ whose presheaf topos « classifies the pseudo-fields » (page 41: pseudo-field = compact reduced ring = A ≅ A_f × A/f for every f, page 42); then e ⊔ O* → O has to be made a monomorphism, and page 95 concludes that the universal category is « la catégorie des faisceaux sur R′ pour la topologie de Zariski », a topos whose structure sheaf is the universal field.',
    ours:
      'The identification of the pseudo-fields with the absolutely flat rings, and of R′ with the opposite of the finitely presented ones, is the edition’s (the page says « catégorie de fractions de R » and « schémas compacts réduits »); so is the reading of « Zariski sur R′ » as the topology generated by {V(f), D(f)}, which on absolutely flat schemes is the same as the topology of the page 41 article 11 (« sections sur chaque fibre »). Page 94 is a fast draft with several illegible connectives; the two displayed conclusions are the page’s.',
    literature: [
      'P. T. Johnstone, Rings, fields and spectra, J. Algebra 49 (1977) — the classifying topos of fields; cited from memory, not consulted for this entry',
      'O. Caramello, De Morgan classifying toposes (arXiv 0808.1519) — the field classifier and its largest De Morgan subtopos; found by search, the site used there not checked',
      'J. C. Berni, H. L. Mariano, Classifying toposes for some theories of C∞-rings (arXiv 1811.08838) — the presheaf classifier of von Neumann regular C∞-rings; found by search',
      'Web search, 5 September 2026: « classifying topos of fields sheaves on finitely presented von Neumann regular rings absolutely flat » — no source describing the field classifier over the absolutely flat site',
    ],
    status: 'candidate',
    settle:
      'Open Johnstone 1977 and Caramello 0808.1519 and read which site each takes for the theory of fields. If it is the finitely presented rings with the covers {A_f, A/f}, the passage to the absolutely flat site is an exercise on the comparison lemma and the entry becomes matched; if the absolutely flat site appears there, matched outright.',
  },
  {
    id: '161-2-vn-regular-cartesian-presheaf-classifier',
    cote: '161-2',
    pages: '41–42',
    kind: 'mathematical',
    claim:
      'Commutative von Neumann regular rings (« pseudo-corps », compact reduced rings) form a cartesian theory — for every f there is a unique idempotent e with ef invertible in eA and (1 − e)f = 0, i.e. A ≅ A_f × A/fA — and their classifying topos is therefore a presheaf topos, on the opposite of the finitely presented absolutely flat rings.',
    basis:
      'Page 42, article 13: « ∀ f ∈ A(U), A(U) ≅ A_f × A/fA, i.e. ∃(!) e ∈ A(U), e² = e, ef inv., e(1 − f) = 0 », the universal case being that i₁ : D₁ → A is an isomorphism, and X_{ps.corps} ≅ R̂_cons.',
    ours:
      'The word « cartesian » and the general fact that cartesian theories are of presheaf type are the edition’s; the unique-existence form of the axiom is the page’s.',
    literature: [
      'J. C. Berni, H. L. Mariano, Classifying toposes for some theories of C∞-rings (arXiv 1811.08838) — Sets^(C∞vNRng_fp) is the classifying topos of von Neumann regular C∞-rings, by the same route; the argument transfers verbatim to ordinary rings',
      'P. T. Johnstone, Sketches of an Elephant, D1.3 and D3.1 — cartesian theories are of presheaf type',
    ],
    status: 'matched',
    settle:
      'Settled to the extent that the C∞ case is in print and the ordinary case is its special case of the same proof; kept as a killed candidate. A reference stating it for ordinary rings would close it entirely.',
  },
  {
    id: '161-2-definite-characteristic-join-of-subtopoi',
    cote: '161-2',
    pages: '47–49',
    kind: 'mathematical',
    claim:
      'The rings that are locally of characteristic p for some prime p or of characteristic 0 are classified by a subtopos of the classifying topos of rings which is not coherent and is not presented by an open condition, but is the join of the open subtopos X_{car > 0} = ⋃_p X_{ℤ/p} and the non-open subtopos X_ℚ = ⋂_n X_{ℤ[1/n]}; and the join of two subtopoi V, W of a topos B is obtained by gluing along an open when there are opens Z′ of V and Z″ of W with Z″ ∧ V open in V, Z′ ∧ W open in W, V = sup(Z′, Z″ ∧ V) and W = sup(Z″, Z′ ∧ W).',
    basis:
      'Page 47 writes the axiom as the epimorphicity of {V(p·1_A) → e, ⋂_n (e)_{n·1_A} → e}, notes that the infinite intersection « ne donne pas l’existence d’un topos classifiant » by the open-condition route, defines the topology « top car » as the infimum of the « top car p » and observes it is not quasi-compact; pages 47–48 work out the gluing criterion and check it for V = X_{car > 0}, W = X_{car 0}, where V ∧ W is the open of the zero ring; page 49 proposes X_car ≅ R̂_car for R_car the schemes of finite type over the prime fields, glued under the empty scheme.',
    ours:
      'The statement of the gluing criterion in the form above is the edition’s mise en forme of a brouillon (page 48); the reading records that X_car ≅ R̂_car is posed without proof and that the ℚ-schemes lie in Pro R rather than in R. The non-coherence is the page’s (« topos non cohérent », encircled).',
    literature: [
      'M. Hutzler, Syntactic presentations for glued toposes and for crystalline toposes (arXiv 2206.11244) — presentations of a topos from a cover by open subtoposes; found by search, the characteristic example not seen there',
      'P. T. Johnstone, Sketches of an Elephant, A4.5 — joins and meets of subtoposes; cited from memory',
      'O. Caramello, Lattices of theories (arXiv 0905.0299) — the lattice of subtoposes as a lattice of quotient theories; found by search',
      'Web search, 5 September 2026: « classifying topos rings of characteristic p or characteristic zero geometric theory subtopos union open » — nothing on this theory',
    ],
    status: 'candidate',
    settle:
      'Two checks: whether « rings of definite characteristic » occurs as an example of a non-coherent quotient of the theory of rings anywhere (Johnstone 1977, Elephant D3, Hutzler); and whether the join sup(V, W) in Elephant A4.5 terms is the glued topos the page describes, which would make the criterion a corollary of the general theory of joins.',
  },
  {
    id: '161-2-irreducible-and-zero-dimensional-not-coherent',
    cote: '161-2',
    pages: '39, 41–42',
    kind: 'mathematical',
    claim:
      'The classifying subtopoi of the rings with irreducible spectrum (nilradical prime) and of the rings with zero-dimensional spectrum are not coherent, their presenting topologies on the affine schemes of finite type over ℤ not being quasi-compact, although each is a subtopos of the coherent classifying topos of rings; whether they have enough points is left open.',
    basis:
      'Page 39: « Cette topologie n’est pas quasi-compacte : il y a des recouvrements qui n’admettent pas de sous-recouvrement fini », for the topology where a family covers iff over every irreducible component one member has a section on the reduced structure; page 42, margin: « topologie non cohérente ! A-t-elle assez de pts ?? », for the topology presented by the infinite family of monomorphisms D_n → A; page 41, margin: « encore un topos non cohérent (bien que sous-topos d’un topos cohérent) ».',
    ours:
      'The diagnosis that the failure comes from an infinite disjunction hidden in « nilpotent » is the edition’s; the exponent n in the equations of D_n was restored by the reading, the page writing them without it.',
    literature: [
      'O. Caramello, De Morgan classifying toposes (arXiv 0808.1519) — coherent theories of rings, the Zariski topos; found by search',
      'P. T. Johnstone, Sketches of an Elephant, D3.3 — coherent theories, Deligne’s theorem; cited from memory',
      'Web search, 5 September 2026: « classifying topos irreducible rings nilradical prime not coherent geometric theory » — nothing on these two theories',
    ],
    status: 'candidate',
    settle:
      'Find « ring with irreducible spectrum » or « zero-dimensional ring » treated as a geometric theory with its classifying topos (Johnstone 1977 treats dimension of rings in a topos; the Elephant’s D3 examples), and whether non-coherence or the existence of points is stated there.',
  },
  {
    id: '31-phi-specialisation-criterion',
    cote: '31',
    pages: '64–70',
    kind: 'mathematical',
    claim:
      'A function φ on the points of a noetherian scheme bounds étale cohomological dimension as soon as it satisfies two purely local conditions — φ(x) ≥ cd_ℓ(k(x)) at every point, and φ(y) < φ(x) − cd_ℓ(O_{X,ȳ} ⊗ k(x)) at every proper specialisation — giving H^i(X,F) = 0 above sup over the support of φ, for every ℓ-torsion sheaf F.',
    basis:
      'Page 66 states the two conditions and the conclusion; pages 66–67 prove it by noetherian induction, reducing to F = g_*(G) on the closure of a point and running the spectral sequence H^p(X, R^q g_*(G)) against the boxed estimate φ(R^q g_*(G)) ≤ φ(x) − q, itself read off R^q g_*(G)_ȳ = H^q(K_ȳ, G) and its vanishing above cd_ℓ(K_ȳ). Page 69 exhibits a φ satisfying both conditions — φ(x) = sup over y in the closure of x of (cd_ℓ k(y) + 2 dim O_{x̄,y}) — under the hypothesis cd_ℓ K_{x,ȳ} ≤ dim O_{X,ȳ}, and concludes cd_ℓ(X) ≤ φ(X).',
    ours:
      'The reading names the two conditions (a floor at the residue fields, a strict decrease along specialisations) and says why the subtracted term is the one it is; the statements, the proof and the boxed estimate are the page’s. What the entry does not rest on: the prose around condition b) on page 66 is largely illegible, and a marginal note of his queries that very condition. The displayed formula it turns on is clean.',
    literature: [],
    status: 'unsearched',
    settle:
      'Open SGA 4 Exposé X (M. Artin, « Dimension cohomologique : premiers résultats »), §§2–3, and Exposé XVIII, and check whether the criterion is stated in this two-condition form for an arbitrary φ, or only through the particular functions it gets applied to. If the general form is there, mark matched with the reference.',
  },
  {
    id: '31-imperfection-bound-conjectures',
    cote: '31',
    pages: '84',
    kind: 'mathematical',
    claim:
      'Where ℓ is the residue characteristic, the folder conjectures that the bound on the cohomological dimension of an affine scheme is governed by the degree of imperfection ν(k), defined by ℓ^ν(k) = [k : k^ℓ], rather than by the dimension: cd_ℓ(X) ≤ sup(cd_ℓ k(x), ν(V(ℓ)) + 3), and cd_ℓ(U) ≤ dim A + ν(k) + cd_ℓ(k) for U open in the spectrum of a henselian local domain of residue characteristic ℓ whose fraction field has characteristic 0.',
    basis:
      'Page 84, headed « Conjectures sur la cohomologie des schémas affines », states 1°), 2°) and 4°), and defines ν(Z) for a scheme of characteristic ℓ as the supremum of ν(k(z)) over its maximal points. Page 60, a pencil leaf otherwise unconnected to the folder, works with the same invariant through the condition k ⊂ ℓ(K^p).',
    ours:
      'Nothing: the statements are the page’s and are labelled conjectures there. The entry claims that the folder states them, not that they hold — the constant 3 in 2°) is unexplained on the leaf. The intermediate conjecture 1 bis) is written three times over, each pass cancelling the last, and is not recoverable; nothing here rests on it.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check whether bounds of this shape — cd_ℓ in characteristic ℓ controlled by the degree of imperfection rather than the dimension — appear in SGA 4 Exposé X §5, or in the later literature on p-cohomological dimension in characteristic p (Kato, Gabber). A source that states either inequality, or refutes it, settles this entry.',
  },
  {
    id: '31-local-ring-cd-lower-bound',
    cote: '31',
    pages: '22',
    kind: 'mathematical',
    claim:
      'For a noetherian local domain A with fraction field K and residue field k, cd_r(K) ≥ cd_r(k) + dim A for every prime r, with exactly two possible exceptions: r is the characteristic of K, or r = 2 and some point of Spec A has an orderable residue field k(x) with cd_2 k(x)(√−1) finite — the second exception disappearing when A is regular, and refining to « k itself real » when A is catenary and universally japanese.',
    basis:
      'Page 22 states the inequality, the two-item exception list, the refinement under the catenary hypothesis, and the disappearance of the exception for A regular. The margin carries the example that keeps the second exception alive: A = R[X,Y]/(X²+Y²), localised — a real domain whose only real point is the origin.',
    ours:
      'Nothing substantive; the reading restates the page. The first clause of item b) is struck through on the leaf and rewritten, and the transcription marks the cancelled version; the entry rests on the surviving clause, which is legible.',
    literature: [],
    status: 'unsearched',
    settle:
      'Compare with Serre, Cohomologie galoisienne II §4.2, which gives cd_p(K) ≤ cd_p(k) + tr.deg for fields rather than this lower bound for a local ring, and with SGA 4 Exposé X. His own margin — « cette restriction est-elle essentielle ??? » — records that the sharpness of the exception list was open to him; showing the list is or is not sharp settles the entry either way.',
  },
  {
    id: '31-torsion-module-leaves-out-of-order',
    cote: '31',
    pages: '10, 12, 14, 16',
    kind: 'codicological',
    claim:
      'The four leaves carrying the construction of an f-torsion module whose quotient M/fM is not of finite type are bound out of the order in which their text runs: the argument goes 10 → 14 → 12 → 16, not 10 → 12 → 14 → 16.',
    basis:
      'Page 14 ends on « Le premier résulte de (a_n) et f·A/fA = 0 », opening the verification of the three induction hypotheses (a_{n+1}), (b_{n+1}), (c_{n+1}); page 12 opens on « la deuxième … voulue » and carries out the second of the three. The transcription gives the pages in text order and records the break at the foot of page 14.',
    ours:
      'The ordering is the transcription’s, arrived at from the broken sentence; the folder’s pagination is untouched, and the modernised reading follows the transcription.',
    literature: ['Transcription 31, batch 1 (batch-01.fr.tex), header and pages 10, 12, 14, 16'],
    status: 'candidate',
    settle:
      'A person checks on the facsimile that the foot of page 14 and the head of page 12 join, and whether 10–11, 12–13, 14–15, 16–17 are recto/verso pairs of single leaves — in which case the disorder belongs to the stack of typescript he wrote on, not to the binding.',
  },
  {
    id: '31-typescript-runs-reversed',
    cote: '31',
    pages: '11–17, 25, 27, 83–87, 99, 101',
    kind: 'codicological',
    claim:
      'Three of the folder’s four typescript runs are bound in reverse of their own pagination and the fourth is not: pages 11 to 17 carry the typist’s leaves 30, 29, 28, 27; page 27 precedes page 25 in text order; pages 99 and 101 carry « VII – 9 – » and « VII – 7 – » of one Bourbaki draft, n° 339; while pages 83, 85, 87 run 3.1, 4.6, 4.7 forwards.',
    basis:
      'The typist’s leaf numbers stand on the leaves of pages 11 to 17, and the internal numbering 5.9 to 5.16 runs continuously from page 17 back to page 11; the text of page 27 continues on page 25; the typed headers « VII – 9 – » and « VII – 7 – » stand on pages 99 and 101 respectively, both above « n°339 »; and the statements 3.1, 3.2, 4.6, 4.7 run forwards across pages 83, 85 and 87.',
    ours:
      'Nothing: the observation is the transcriptions’, which give each run in text order and say so in their headers. The headers of pages 99 and 101 were read directly from the facsimile for this entry, those two leaves having no transcription — they carry nothing in his hand.',
    literature: [
      'Transcription 31, batches 1, 2 and 5 (batch-01, batch-02, batch-05.fr.tex), headers and the typescript sections',
      'Facsimile 31, pages 99 and 101 (typed headers only)',
    ],
    status: 'candidate',
    settle:
      'A person checks the typist’s leaf numbers on the facsimile of pages 11 to 17 and the two headers on pages 99 and 101. Whether the reversal belongs to the stack, the binding or the scan is not determined by the pages. Separately: the typescripts of pages 11–17, 71 and 83–87 are, by content and by their internal references (Exp VIII, Exp IX, SGA VIII 2.1), leaves of the seminar on group schemes and not of SGA 4; matching their numbering against the published volume would confirm that identification and situate the leaves within its redaction.',
  },
  {
    id: '16-graded-ring-lefschetz-criterion',
    cote: '16',
    pages: '4–17',
    kind: 'mathematical',
    claim:
      'The folder gives a criterion for the hard Lefschetz package that mentions no underlying module at all: for a graded ring ℰ and an element L of degree 2, the existence in ℰ of one-sided inverses wᵢ to Lⁿ⁻ⁱ is enough for the grading projectors, the pseudo-inverse Λ and every projector of the primitive decomposition to lie in ℰ — and the whole argument runs over ℤ.',
    basis:
      'His no. 4 converts the module-theoretic conditions (4.1)–(4.3) into the internal (4.4)ᵢ; no. 5, on the inserted leaf « 5 bis », derives πᵢ ∈ ℰ from it through v′ᵢ = π₂ₙ₋ᵢ vᵢ πᵢ and w′ᵢ = πᵢ wᵢ π₂ₙ₋ᵢ, whose products are πᵢ and π₂ₙ₋ᵢ; and no. 6 proves the equivalence by a double descending induction with the explicit formulas (6.9), (6.10), (6.12) and (6.13).',
    ours:
      'The reading restores the theorem to three clauses. The manuscript’s list (i) to (vi) on page 9 is struck and renumbered three times and only its skeleton reads, and page 12 marks one implication « Démonstration à fournir »; the three clauses stated are those pages 10 to 12 actually prove. The normalisation of Λ as a two-sided pseudo-inverse rather than the Kähler adjoint — which is what keeps the argument integral — is read off the relations (6.7); the pages never remark on it.',
    literature: ['arXiv API search (export.arxiv.org), 2026-09-19: queries on «standard conjectures» + «Lefschetz», «Artinian Gorenstein» + «strong Lefschetz», «Poincare duality algebra» + «Lefschetz element», «weak Lefschetz» + «standard conjecture». General web search was unavailable (Google and DuckDuckGo both served bot challenges, which this pass does not complete), and the decisive print sources were not consulted.'],
    status: 'unsearched',
    settle:
      'Open Kleiman, « Algebraic cycles and the Weil conjectures » (Dix exposés sur la cohomologie des schémas, 1968) §1–2 and « The standard conjectures » (Motives, Proc. Sympos. Pure Math. 55.1, 1994) §2, where Λ is introduced for a Weil cohomology, and check whether the criterion is anywhere stated for an abstract graded ring with no module and over ℤ. If it is, mark matched.',
  },
  {
    id: '16-universal-lefschetz-ring',
    cote: '16',
    pages: '13–16',
    kind: 'mathematical',
    claim:
      'The folder constructs a universal graded ring Φ₀ = ℤ[L₀, Λ₀] acting on an exterior algebra, with explicit generators φ^{β,α}ᵢ and a multiplication table independent of the chosen (M₀, ξ₀), and makes the Lefschetz conditions on (ℰ, L) equivalent to the existence of a graded ring homomorphism Φ₀ → ℰ carrying L₀ to L and the πᵢ to the πᵢ, unique when it exists.',
    basis:
      'Page 14 lists the generators with their index ranges and the two cases α ≤ β and α ≥ β; the Proposition of pages 14–15 states the equivalence and the uniqueness, and the Corollaire of page 16 draws the module-free consequence that the πᵢ are then determined by the graded ring structure of ℰ alone. Page 13, re-read from the tiles, carries both the contraction formula and the sentence identifying it with the operator of (6.15).',
    ours:
      'Page 13 was re-read from the tiles on 2026-09-19 and this is now settled, against the entry’s first version. The leaf defines Λ₀ by the contraction ξ₀* ⌐ − and then asserts « et que Λ₀ est l’opérateur associé défini par (6.15) » — it identifies the two. They are not the same operator: (L₀, Λ₀) is the classical symplectic sl₂-pair, for which Λ₀L₀ acts on a primitive class of degree i by n − i, and Λ₀L₀(1) = ⟨ξ₀*, ξ₀⟩ = n where (6.15) demands 1; the factor moves with the rank of M₀, so no rescaling repairs it and the identification holds only for n = 1. The error is the page’s. The reading keeps Λ₀ in the sense of (6.15), which is what the Proposition’s proof actually uses, and footnotes the discrepancy; Φ₀ is therefore not the enveloping-algebra ℤ-form the contraction would give.',
    literature: ['arXiv API search (export.arxiv.org), 2026-09-19: queries on «standard conjectures» + «Lefschetz», «Artinian Gorenstein» + «strong Lefschetz», «Poincare duality algebra» + «Lefschetz element», «weak Lefschetz» + «standard conjecture». General web search was unavailable (Google and DuckDuckGo both served bot challenges, which this pass does not complete), and the decisive print sources were not consulted.'],
    status: 'unsearched',
    settle:
      'The transcription question is closed. What remains is to compare Φ₀ — the ring generated by L₀ and the pseudo-inverse, not by the contraction — with the « Lefschetz algebra » of the Hodge-theory literature and with the Kostant ℤ-form of U(sl₂) acting on ΛM₀, which it is precisely not, and to check whether a universal ring with this presentation, and the equivalence with a graded ring homomorphism out of it, is stated anywhere. Kleiman 1968 §1 and 1994 §2 remain the places to look first.',
  },
  {
    id: '16-algebraic-iso-suffices',
    cote: '16',
    pages: '47–48',
    kind: 'mathematical',
    claim:
      'The folder’s Lefschetz-type conjecture follows from D(X) together with the existence, for each i < n, of some algebraic isomorphism H^{2n−i}(X) → H^i(X) — an arbitrary one, with no requirement that it invert L^{n−i}.',
    basis:
      'The letter of page 47 takes the given algebraic isomorphism u and the algebraic v induced by L^{n−i}, forms the algebraic automorphism w = uv, and reads off Cayley–Hamilton that w⁻¹ is a combination of the wⁱ with coefficients ±σᵢ(w)/σ_b(w); D(X) makes those rational, so w⁻¹ is algebraic and so is w⁻¹u = v⁻¹. The Corollary of page 48 extends it to any algebraic isomorphism H^i(X) → H^{i+2j}(X′) between varieties satisfying the conjecture.',
    ours:
      'The reading restates the Cayley–Hamilton relation in w; the typescript writes it in u while its coefficients are those of w. Nothing else is supplied — the argument is complete on the leaf.',
    literature: ['arXiv API search (export.arxiv.org), 2026-09-19: queries on «standard conjectures» + «Lefschetz», «Artinian Gorenstein» + «strong Lefschetz», «Poincare duality algebra» + «Lefschetz element», «weak Lefschetz» + «standard conjecture». General web search was unavailable (Google and DuckDuckGo both served bot challenges, which this pass does not complete), and the decisive print sources were not consulted.'],
    status: 'unsearched',
    settle:
      'Read Kleiman 1994 §2, where the equivalences for the Lefschetz standard conjecture are collected, and Kleiman 1968 §4. This argument is short and memorable enough that it is more likely in the books than not; a reader who finds it there should mark this matched with the reference.',
  },
  {
    id: '16-weak-variants-imply-strong',
    cote: '16',
    pages: '49',
    kind: 'mathematical',
    claim:
      'The two critical-dimension variants A′⁰ and A″⁰ — statements about which classes become algebraic on a hyperplane section — together imply A⁰, so that the folder’s C(X) is equivalent to C(Y) + A′⁰(X×X) + A″⁰(X×X) and, by descent along a chain of hyperplane sections, to those two conditions alone on all of X×X, Y×Y, Z×Z, …',
    basis:
      'The page factors the critical-dimension operator through the section: L_T² : H^{2m−2}(T) → H^{2m+2}(T) as φ*, then φₓ, then L_T when dim T = 2m, and H^{2m}(T) → H^{2m+2}(T) as φ* then φₓ when dim T = 2m+1. Both factorisations are written out on the leaf, with the arrow names inked by hand.',
    ours: null,
    literature: ['arXiv API search (export.arxiv.org), 2026-09-19: queries on «standard conjectures» + «Lefschetz», «Artinian Gorenstein» + «strong Lefschetz», «Poincare duality algebra» + «Lefschetz element», «weak Lefschetz» + «standard conjecture». General web search was unavailable (Google and DuckDuckGo both served bot challenges, which this pass does not complete), and the decisive print sources were not consulted.'],
    status: 'unsearched',
    settle:
      'Check Kleiman 1968 §3 and the later literature on reductions of the Lefschetz standard conjecture to the critical dimension, and in particular whether these two one-sided variants appear under any name. Note that the folder’s letters use A, C and D in senses of January 1967 that do not match the published labels, so the comparison has to be made statement by statement and not letter by letter.',
  },
  {
    id: '16-hodge-algebras-order-2',
    cote: '16',
    pages: '24–28',
    kind: 'mathematical',
    claim:
      'The folder axiomatises a graded anticommutative algebra k, V, kξ ⊕ W, V̌, kξ² by three data — an alternating form φ on V, a map ψ : Λ²V → W, a symmetric form Q on W — reduces associativity to one quadrilinear identity, and shows that the Lefschetz condition and the Poincaré condition are each equivalent to the non-degeneracy of exactly one of φ and Q; a second formulation then makes the polarisation ξ a parameter of the structure rather than part of its definition.',
    basis:
      'Page 24 fixes the five graded pieces, the two structure maps α and β, derives every remaining product, and states the three conditions in that order; page 26 introduces the quadrilinear χ by xyzt = χ(x,y,z,t)ξ² and rewrites the datum as (V, χ, (W̃, Q̃, α), ξ).',
    ours:
      'The reading separates these φ, ψ, Q, χ from the inclusion φ and the cohomology index χ of the later pages; the collision of letters is the folder’s. The closing passage of page 28, on the finiteness of an orbit, is an unreconstructible sketch and no part of this claim rests on it.',
    literature: ['arXiv API search (export.arxiv.org), 2026-09-19: queries on «standard conjectures» + «Lefschetz», «Artinian Gorenstein» + «strong Lefschetz», «Poincare duality algebra» + «Lefschetz element», «weak Lefschetz» + «standard conjecture». General web search was unavailable (Google and DuckDuckGo both served bot challenges, which this pass does not complete), and the decisive print sources were not consulted.'],
    status: 'unsearched',
    settle:
      'Compare with the literature on graded Poincaré duality algebras of formal dimension 4 and on the classification of cohomology rings of algebraic surfaces, and check in both directions that his « algèbre de Hodge d’ordre 2 » and the standard notion define the same objects. The point to test is the claimed separation — one condition per datum — rather than the axiomatisation itself.',
  },
  {
    id: '16-page-21-not-gorenstein',
    cote: '16',
    pages: '21',
    kind: 'mathematical',
    claim:
      'The six-dimensional graded algebra of page 21, in which L is Lefschetz while L′ is not although L′³ = L³, separates the Lefschetz property from the non-vanishing of the top power — but its middle pairing is degenerate, so it is not a counterexample within graded Artinian Gorenstein algebras, where that separation is standard.',
    basis:
      'The relations L⁴ = 0, L′² = LL′, L²L′ = L³, L³L′ = 0 give the basis 1 | L, L′ | L², LL′ | L³. L carries the degree-2 basis to the degree-4 basis and is an isomorphism there, while L′ sends both L and L′ to LL′ and has rank 1; and L′³ = L·L′² = L²L′ = L³ ≠ 0.',
    ours:
      'The pairing computation is the edition’s: the page states the relations and the conclusion about L and L′ and nothing more. All four products of the degree-2 basis with the degree-4 basis equal L³, so the pairing into degree 6 has matrix [[1,1],[1,1]] and rank 1. An earlier draft of the modernised reading framed the example as bearing on the strong Lefschetz property of Artinian Gorenstein algebras; that framing was wrong and has been corrected in the reading, the algebra being degenerate in the middle. What the example does separate is the Lefschetz condition from the Poincaré condition — the two that his own pages 24 to 28 impose separately.',
    literature: [
      'arXiv API search (export.arxiv.org), 2026-09-19: queries on «standard conjectures» + «Lefschetz», «Artinian Gorenstein» + «strong Lefschetz», «Poincare duality algebra» + «Lefschetz element», «weak Lefschetz» + «standard conjecture». General web search was unavailable (Google and DuckDuckGo both served bot challenges, which this pass does not complete), and the decisive print sources were not consulted.',
      'Artinian Gorenstein / strong Lefschetz literature located by that search: Stanley’s theorem on monomial complete intersections and its extensions (arXiv math/0506537), the Hessian criterion for Lefschetz elements (arXiv 0903.3581), Hilbert functions of Artinian Gorenstein algebras with the strong Lefschetz property (arXiv 2007.10684)',
    ],
    status: 'matched',
    settle:
      'Nothing further on the mathematics: the distinction between Lⁿ ≠ 0 and the strong Lefschetz property is standard in that literature, and this algebra falls outside it for want of Poincaré duality. Kept as a killed candidate and as the record of a framing that had to be corrected.',
  },
  {
    id: '16-letters-and-interrupted-run',
    cote: '16',
    pages: '30, 31, 39–41, 43, 47',
    kind: 'codicological',
    claim:
      'One argument of the folder runs across a foreign leaf, two of its leaves are covers bearing only a title in his hand, and its two letters are dated by him a year apart although the later-dated one answers a question the earlier-dated one leaves open.',
    basis:
      'Page 39 breaks off mid-sentence on « Mais » and page 41 opens with no heading on the same discussion of C(X) and C(Y); page 40, between them, is an unrelated typescript. Pages 30 and 31 are otherwise blank leaves carrying only « Algèbres de Hodge » and « Formulaire de L, Λ », the titles of the runs they sit with — page 30’s naming the run that precedes it. The letters carry « 4.1.67 » on page 43 and « 6.1.1966 » on page 47, both in his hand; the second opens a proposition showing Cχ(X) independent of the polarisation, which is precisely what the first says it is not clear to him how to prove in characteristic p.',
    ours:
      'The connection of pages 39 and 41 is the edition’s: the two leaves were transcribed in different batches, by passes that could not see each other, and the join was made afterwards with both in view. Each side’s note now names the other. The reading transcribes both dates and reconciles neither.',
    literature: [
      'Transcriptions 16, batches 1, 2 and 3 (batch-01, batch-02, batch-03.fr.tex), headers and the sections on pages 30–31, 39, 41, 43 and 47',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile that page 39’s last line and page 41’s first join, that pages 30 and 31 carry nothing but their titles, and that the two dates read as transcribed. Whether « 6.1.1966 » is a slip for 1967 is not something the leaves settle; Coates’s own papers, or the notes of the talk both letters comment on, would.',
  },
  {
    id: '12-immersion-level-bound',
    cote: '12',
    pages: '115, 117, 119',
    kind: 'mathematical',
    claim:
      'For an immersion f : X → Y with X regular and n the dimension of the closure of f(X), the folder bounds the constituents of R^i f_* ℚ_ℓ by weight ≤ 2 inf(i, n) and level ≤ inf(i, n − 1), the level rising from 0 and falling back to 0 at weight 2n — one less than the level 2n − i allowed for H^i of an n-dimensional smooth variety when i ≥ n.',
    basis:
      'Page 115 factors f as an open immersion g into a regular Y′ with normal-crossings complement Z = ΣZᵢ followed by a proper h, writes R^q g_* ℚ_ℓ = ⊕ ℚ_ℓ(−q) on the q-fold intersections, and bounds each E₂^{pq} = R^p h_*(R^q g_* ℚ_ℓ); pages 117 and 119 tabulate weight and level of each term for i ≤ n − 1 and i ≥ n, and page 119 boxes the result. The whole argument is conditional on resolution, purity and the Weil conjectures, as the folder’s notes of pages 104–114 are.',
    ours:
      'The boxed bound is legible and is the page’s; the table entries leading to it are written fast and overwritten, and neither the transcription nor the reading verifies them column by column, so the entry rests on the box, not on the tables. That the bounds on the E₂ terms pass to the abutment (stability of « effectively admissible » under subquotients and extensions, Proposition 4.2 a) of page 112) is not written on the sheets. One check is the edition’s, made for this entry and not in the reading: for Y the affine cone over a curve C of genus ≥ 1 and X = Y minus the vertex (n = 2), the stalk of R²f_* at the vertex is H¹(C)(−1), of weight 3 and level 1 = n − 1, so the n − 1 is attained there. The two extensions that follow on page 119 — « + j » for F strictly special of weight j, and the relative case with n = d_y(f) — carry his own « ? » and are not part of the claim.',
    literature: [],
    status: 'unsearched',
    settle:
      'Translate « level ≤ ν » into Hodge types p, q ≥ (w − ν)/2 on a weight-w piece, or into divisibility of Frobenius eigenvalues by q^{(w − ν)/2}, and look for the bound inf(i, n − 1) on R^i j_* for an open immersion in Deligne, Théorie de Hodge III §8.2, in Durfee, « Mixed Hodge structures on punctured neighborhoods » (Duke 1983), in Steenbrink’s work on the mixed Hodge structure of links, and ℓ-adically in SGA 7 exposé XXI §5. If the bound is stated there, mark matched. A web search was attempted for this pass on 2026-09-23 and refused by the network, so nothing has been read yet.',
  },
  {
    id: '12-weights-paper-typescript',
    cote: '12',
    pages: '95–98',
    kind: 'codicological',
    claim:
      'The folder holds the typed introduction, credited « par A. GROTHENDIECK » and corrected in his hand, and the handwritten ten-section plan of a paper « Filtration et poids des espaces de cohomologie des variétés algébriques », under a cover of his reading « Poids et niveaux d’espaces de cohomologie ℓ-adiques (base var. quelconque) »; only the introduction is drafted on these leaves, and its reference list has empty brackets.',
    basis:
      'Page 95 is the cover; pages 96–97 are the typescript § 0, which states the method (weight arguments reducing geometric statements to a finite base field), says the idea « remonte à 1964 », and cites SGA 7 and Deligne’s Hodge theory; page 98 is the plan, §§ 0–9 with a doubled « 8 », and six references — SGA 4, Deligne / Hodge, Tate / conjectures, Kleiman conj. standart, Weil conj., SGA 7 — each behind « [ ] ».',
    ours:
      'The reading’s identification of pages 103–121 as the working notes behind this plan is the edition’s inference from their content, not something the leaves say. The entry claims only what the leaves carry; it makes no claim about when the paper was planned, and no claim that it was never published.',
    literature: ['Transcription 12, batch 5 (batch-05.fr.tex), pages 95–98'],
    status: 'unsearched',
    settle:
      'Look the title up in the published lists of his writings (for instance the bibliography in The Grothendieck Festschrift, vol. I, 1990) and in the Montpellier inventory for another copy of the typescript or of its later sections. If the paper or any section of it appears there, record where.',
  },
  {
    id: '12-deligne-report-one-text',
    cote: '12',
    pages: '122, 120',
    kind: 'codicological',
    claim:
      'The two typed French leaves presenting Deligne’s work are consecutive pages of one report, to be read 122 then 120: page 122 carries its point 4 (the degeneration of the Leray spectral sequence of a smooth projective morphism) and ends « la « théorie des motifs », qui se », and page 120 opens « une sorte de synthèse géométrico-arithmétique des nombreuses théories cohomologiques » before its point 5 (Deligne’s λ-structure on K•(X) of perfect complexes).',
    basis:
      'The numbering 4) on page 122 and 5) on page 120, and the sentence that runs from the foot of one into the head of the other. Both leaves are typed in French and corrected by hand; page 122 names the writer as « rapporteur » in one of its two occurrences.',
    ours:
      'The join is the reading’s; the transcription gives each leaf as isolated. The last word of page 122 is overwritten by hand and transcribed as « se » followed by an illegible stretch, so the continuous sentence rests on an unread word — which is why the status is no higher. The numbering 4) → 5) supports the order independently but not that no leaf is missing between them.',
    literature: ['Transcription 12, batches 6 and 7 (batch-06.fr.tex p. 120, batch-07.fr.tex p. 122)', 'Modernised reading 12, section XI'],
    status: 'unsearched',
    settle:
      'A person reads the overwritten last word of page 122 on the facsimile and checks that the two leaves are the same paper and typeface. Separately, whether points 1 to 3 of the report survive elsewhere in the fonds would say what the report was for; the leaves do not.',
  },
  {
    id: '12-positive-forms-leaves-order',
    cote: '12',
    pages: '158–167',
    kind: 'codicological',
    claim:
      'The last run of the folder, on positive forms on motives, is bound with page 158 before page 160 although page 160 poses the axioms (i)–(iii) that page 158 already uses; in the text order 160, 158, 162, 164, 166, the typed pages on the other faces run VII.20, VII.19, VII.18, VII.17, VII.15 — descending — which fits a stack of someone else’s typescript written on in order with its first two leaves swapped.',
    basis:
      'Page 158 discusses the sign changes φᵢ ↦ εᵢφᵢ and finds that (i) and (iii) survive while (ii) forces εᵢεⱼ = εᵢ₊ⱼ, which is the tensor-product axiom (ii) of page 160; page 162 opens as the direct sequel of page 160. The typed faces are recorded as VII.19 on page 159 (batch 8) and VII.20, VII.18, VII.17, VII.15 on pages 161, 163, 165, 167 (batch 9), an English typescript on Brauer groups of regular domains with nothing of his on it.',
    ours:
      'The logical order 160 → 158 is the transcription’s and the reading’s. The pairing of each handwritten face with the typed face that follows it in the scan (158 with 159, 160 with 161, and so on) is the edition’s assumption, made for this entry; with the other pairing (159 with 160, …) the typed numbers are not monotone and the observation lapses.',
    literature: [
      'Transcription 12, batch 8 (batch-08.fr.tex), header and notes on pages 158, 159, 160',
      'Transcription 12, batch 9 (batch-09.fr.tex), header and note on page 162',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile which typed face backs which handwritten one on pages 158 to 167. If 158|159, 160|161, … are leaves, the swap of the first two leaves is confirmed; if not, only the logical order 160 → 158 stands.',
  },
  {
    id: '14-albanese-equivalence-ring',
    cote: '14',
    pages: '23–29, 33',
    kind: 'mathematical',
    claim:
      'The folder defines an « Albanese equivalence » on cycles of every codimension — z ~ 0 when z = Z_*(t) for a cycle Z on X × T, T smooth projective connected, and t a 0-cycle of degree 0 on T with alb_T(t) = 0 — shows it lies between rational and algebraic equivalence and passes to products, pull-backs and proper push-forwards, identifies it with rational equivalence on divisors and with degree and Albanese sum on 0-cycles, and proves that in the quotient ring the product of two algebraically trivial classes is zero.',
    basis:
      'Définition 1.1 (p. 23), with « projectif » and « connexe » added by him in brackets; Prop. 1.2 (pp. 23–27) for the subgroup, the ideal, f^* and f_*; Th. 1.4 (p. 28) for divisors and 0-cycles; Th. 1.6 (p. 29), whose proof is that ((x) − (y)) × ((x′) − (y′)) has zero Albanese sum on T × T′; Cor. 2.3 and 2.4 (p. 33) for divisibility and for the product of an algebraically and a τ-trivial class. Prop. 1.2 (iii) is stated for morphisms of varieties read « q.p. » under reserve.',
    ours:
      'Parts of the proofs are the edition’s. The page leaves the moving argument of Prop. 1.2 (iii) « à vérifier » (p. 27) and does (iv) « par l’AQT », an abbreviation not reconstructed; the reading replaces all three by identities of intersection theory on classes. Th. 1.4 (i) cites « [ , 1.2.] » with its first term blank, and the reading fills it with Cor. 1.2 of p. 51. Cor. 2.4 has no proof on the page and the reading supplies one. The words « adequate equivalence » are the reading’s, not the page’s.',
    literature: [],
    status: 'unsearched',
    settle:
      'Read A. Weil, « Sur les critères d’équivalence en géométrie algébrique » (Math. Ann. 128, 1954), which the margin of page 23 itself says to consult, and P. Samuel, « Relations d’équivalence en géométrie algébrique » (ICM Edinburgh, 1958), for this relation under any name; then U. Jannsen, « Equivalence relations on algebraic cycles » (The Arithmetic and Geometry of Algebraic Cycles, 2000), and the filtrations of Bloch, S. Saito and Murre, where products of algebraically trivial classes fall into a second filtration step. Th. 1.6 is close to formal once the relation is defined, so the question is whether the relation itself — the adequate relation generated by the Albanese kernels of parameter varieties — is defined in print. If Weil 1954 has it, mark matched.',
  },
  {
    id: '14-nakai-euler-characteristic-criterion',
    cote: '14',
    pages: '93–94',
    kind: 'mathematical',
    claim:
      'The folder states, as a theorem it credits to Mumford and Nakai, that an invertible sheaf L on a projective scheme is ample as soon as χ(O_Z ⊗ L^{⊗n}) → +∞ for every integral closed subscheme Z of dimension ≥ 1 — a condition on the growth of the Euler characteristic rather than on the sign of its leading coefficient (L^{dim Z} · Z) — and the same with dim H⁰ in place of χ.',
    basis:
      'Page 93, headed « Th. de Mumford-Nakai », lists a) to c″) as equivalent conditions: b) for every coherent F with support of dimension ≥ 1, b′) for F = O_Z, c) and c′) with dim H⁰. Page 94 calls a) ⇒ b), c) « bien connu », b) ⇒ b′) ⇒ b″) and c) ⇒ c′) ⇒ c″) trivial, and sketches the rest by induction on dim X through Lemme 1 (H^i(X, L^{⊗n}) = 0 for i ≥ 2 and n large once L is ample on every proper integral subscheme) and Lemme 2 (the map to ℙH⁰(X, L^{⊗n}) is everywhere defined and non-constant once some power has a section), both sent to « lettre de Mumford » and not proved on the leaf.',
    ours:
      'The observation that b′) and c′) are a priori weaker than the positivity of (L^{dim Z} · Z), and the check that the induction closes for them — Lemme 1 turns χ(O_Z ⊗ L^{⊗n}) → +∞ into a non-zero section of some L^{⊗n}|Z, whose zero locus is non-empty and carries L ample, so (L^{dim Z} · Z) > 0 — are the edition’s, made for this entry; the reading presents the page simply as the Nakai–Moishezon criterion. The sentence carrying b″) ⇒ c″) breaks off at « Grâce au ». For Z of dimension ≥ 2, b″) as written asks for χ ≥ 1 at a single n, which the sketched route does not reach unless that n can be taken beyond the n₀ of Lemme 1, so the claim is restricted to b), b′), c), c′). The margin « on peut se borner à Z normaux » is read under reserve and no part of the claim rests on it.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look for « χ(L^{⊗n}|Z) → +∞ », or « h⁰(L^{⊗n}|Z) → +∞ », in place of « (L^{dim Z} · Z) > 0 » in Y. Nakai, « A criterion of an ample sheaf on a projective scheme » (Amer. J. Math. 85, 1963), S. Kleiman, « Toward a numerical theory of ampleness » (Ann. of Math. 84, 1966), ch. III, and R. Hartshorne, Ample subvarieties of algebraic varieties (LNM 156, 1970), ch. I. The page credits the theorem to Mumford and Nakai and both lemmas to a letter of Mumford, so this form may well be Nakai’s own or Mumford’s; if it is in any of these, mark matched.',
  },
  {
    id: '14-two-albanese-redactions',
    cote: '14',
    pages: '23–38, 47–69',
    kind: 'codicological',
    claim:
      'The folder holds two separate numbered redactions of the degree-one theory of cycles — « Théorie de l’équivalence d’Albanese des cycles » (pp. 23–38) and « Sorites sur VA, Picard, Albanese » (pp. 47–69) — which reuse the numbers 1.6, 2.2 and 2.7 for different statements, and the first leaves a reference blank, « [ , 1.2.] », at the one point where it needs what is Corollaire 1.2 of the second.',
    basis:
      'Th. 1.6 is on p. 29 and on p. 55, Cor. 2.2 on p. 33 and on p. 61 (with a third, struck, at the foot of p. 60), Prop. 2.7 on p. 34 and on p. 67. Th. 1.4 (i) on p. 28 takes its converse direction from « [ , 1.2.] », the first term left blank by him; that direction needs a correspondence to send a 0-cycle of zero Albanese sum to one of zero Albanese sum, which is Cor. 1.2 of p. 51.',
    ours:
      'Pointing the blank reference at p. 51 is the reading’s inference, stated there as its own; the transcription records only the blank. The Cor. 1.2 of p. 51 itself rests on an uncertain reading: its « = 0 » is written over the start of a struck ending. Neither run says which was written first, and the entry claims no order.',
    literature: [
      'Transcription 14, batch 2 (batch-02.fr.tex), pages 23–38',
      'Transcription 14, batches 3 and 4 (batch-03.fr.tex, batch-04.fr.tex), pages 47–69',
      'Modernised reading 14, « Les moutures, gardées distinctes » and « Ce que seule une lecture d’ensemble peut dire »',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile that the reference on p. 28 is blank in its first term and not merely faint, and compares paper, ink and hand of pp. 23–38 with pp. 48–69. Whether « 1.2 » was meant for p. 51 or for a text not in the folder, the leaves do not settle.',
  },
  {
    id: '14-brauer-typescript-shared-with-12',
    cote: '14',
    pages: '3–15',
    kind: 'codicological',
    claim:
      'The folder’s first run is written on the backs of leaves of an English typescript on the Brauer group of a ringed space, typed pages III.4 to IV.2, whose chapter-and-page numbering and subject are consistent with the English typescript on Brauer groups of regular domains, typed pages VII.15 to VII.20, that backs the last run of folder 12 — so the two folders may be written on one and the same typescript.',
    basis:
      'Transcription 14, batch 1, records typed faces at pp. 3, 5, 7, 9, 11, 13 and 15, scanned upside down, with nothing of his on them. Transcription 12 records VII.19 at p. 159 and VII.20, VII.18, VII.17, VII.15 at pp. 161–167, also upside down and unmarked, on regular and unique factorisation domains, reflexive modules and B(A) ⊂ B(K), with the colophon « Radcliffe Institute for Independent Study, Wellesley College » on VII.20.',
    ours:
      'The comparison is the edition’s, made for this entry from the two transcriptions’ headers; neither transcription mentions the other, and no facsimile was looked at. Nothing is claimed about the typescript’s author or date, nor about when either folder was written.',
    literature: [
      'Transcription 14, batch 1 (batch-01.fr.tex), header',
      'Transcription 12, batch 8 (batch-08.fr.tex), header on p. 159',
      'Transcription 12, batch 9 (batch-09.fr.tex), header on pp. 161–167',
    ],
    status: 'candidate',
    settle:
      'A person sets the typed faces of folder 14, pp. 3–15, beside those of folder 12, pp. 159–167, and compares typeface, paper, margins and running heads; a title or colophon on any folder 14 leaf would decide it. Folder 16, batch 2, lists a Brauer-group typescript among its typed versos without describing it, and is the next place to look.',
  },
  {
    id: '15-real-fibre-functor-criterion',
    cote: '15',
    pages: '116–118',
    kind: 'mathematical',
    claim:
      'For a motivic category over ℚ with commutative band G, Tate character ε and weight cocharacter j with εj(λ) = λ², and U = Ker(ε|G°) with U° a compact torus, the folder shows that the category admits a fibre functor with values in real vector spaces if and only if U is connected, that otherwise U ≃ U° × μ₂, and hence that its even-weight subcategory, of group G/j(μ₂), always admits one.',
    basis:
      'Proposition 1 and Proposition 2 of page 116 state the two alternatives, each as three equivalent conditions; the page proves (iii) ⇒ (ii) of Proposition 1 by the existence of an alternating fundamental form (an object of odd degree has even rank over ℝ) and (i) ⇒ (iii) by H²(ℝ, T) = 0 for a compact torus T, then derives the Corollary on 𝓜^pair from j = 2j′, εj′ = id. Page 118 adds that, when a real fibre functor exists, its isomorphism classes form a torsor under H¹(ℝ, U) ≃ (ℤ/2)^{dim U}. The compactness of U° comes from the Riemann-algebra argument of pages 83–87.',
    ours:
      'Condition (ii) of both propositions is the edition’s. In Proposition 1 it is partly illegible (« ε est … dans l’ens. des caractères », one word illegible); in Proposition 2 the transcription reads « ε n’est pas un carré normalisé », which the reading inverts to « est un carré normalisé » because the page’s own remark that (ii) of 1 is the negation of (ii) of 2 requires it. The direction (iii) ⇒ (i) passes on the page through that (ii), and the reading supplies its link to (i) by computing the character group X(G°)/ℤε. In the key step H²(ℝ, T) = 0 the exponent is read doubtfully and « compact » is uncertain, and the word « normalisé » qualifying the fibre functor is a pencil addition the page does not define. The bijection of page 118 between real fibre functors and « structures polarisantes » is left out: the domain of i₁ is read μ₂ where the stated conditions look like those of μ₄, and the reading does not decide it.',
    literature: [],
    status: 'unsearched',
    settle:
      'Read Deligne and Milne, « Tannakian categories » (LNM 900, 1982) §5, on Tannakian categories over ℝ, polarisations and the remark on supersingular elliptic curves; Milne, « Motives over finite fields » (Motives, Proc. Sympos. Pure Math. 55.1, 1994) §§2–3, on fibre functors of the category of motives over 𝔽_q and its even-weight part; and Saavedra Rivano, Catégories tannakiennes (LNM 265, 1972) ch. V–VI. If the criterion « real fibre functor ⟺ Ker(ε|G°) connected », or the corollary for even weights, is stated there for commutative bands, mark matched.',
  },
  {
    id: '15-brandt-picard-category',
    cote: '15',
    pages: '71–77',
    kind: 'mathematical',
    claim:
      'For a Deuring category C over a Dedekind ring — equivalent to the invertible modules over an order 𝔬 in an algebra E whose automorphisms are all inner, and whose invertible two-sided (𝔬, 𝔬)-bimodules inside E commute — the folder puts on the 2-group Eqv(C) of autoequivalences a strictly commutative symmetric structure, by embedding bimodules in E and using LM = ML, proves that it does not depend on the object used to identify Eqv(C) with bimodules, and concludes that all Deuring categories of one type are torsor-categories under a single strict Picard category, the « catégorie de Picard de Brandt », the 2-category they form being equivalent to that of torsor-categories under it.',
    basis:
      'Page 73 states condition (C) and defines c : L ⊗_𝔬 M ≃ L′M′ = M′L′ ≃ M ⊗_𝔬 L through embeddings L ≃ L′ ⊂ E, M ≃ M′ ⊂ E, noting that the category of special bimodules has associativity and commutativity constraints that are identities; page 75 checks independence of the embeddings and proves the Proposition (independence of X) by L ↦ PLP⁻¹, « OK »; page 77, headed « Conclusion », states the strict Picard category ℬ, the torsor structure on each Eqv(C, C′), the equivalence of 2-categories ℬ₀ → torsor-categories under ℬ, and the compatibility with base change A → A′.',
    ours:
      'That condition (C) holds for maximal orders is the edition’s, citing Auslander–Goldman and Reiner: the page’s margin only believes it locally (« Je crois … cf. Auslander », read under reserve). The 2-categories ℬ₁, ℬ₂ of page 71 on which the construction rests are written fast, with several words illegible; the claim rests on pages 73–77, which read through.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look for a symmetric — in particular strictly commutative — monoidal structure on the Picard groupoid of invertible bimodules of a maximal order, independent of a base object, in A. Fröhlich, « The Picard group of noncommutative rings, in particular of orders » (Trans. AMS 180, 1973), H. Bass, Algebraic K-theory (1968) ch. II, I. Reiner, Maximal Orders (1975) §§22 and 37, and the thesis of Hoàng Xuân Sính on Gr-catégories (1975). If the structure, or the description of these categories as torsors under one Picard category, is there, mark matched.',
  },
  {
    id: '15-leaf-141-read-after-142',
    cote: '15',
    pages: '140–143',
    kind: 'codicological',
    claim:
      'In § 1 of « Motifs essentiellement abéliens et théorie du corps de classes », the sentence cut at the foot of page 140 resumes at the head of page 142, and page 141, which sits between them, carries Corollary 1 and the proof of (iv) ⇒ (ii) and is to be read after page 142: the text order is 140, 142, 141, 143.',
    basis:
      'Page 140 ends « et E₁ (donc F) est un » and page 142 opens « s-groupe discret de rang r₁ + r₂ − 1 », completing the proof of (i) ⇒ (iii); page 142 then proves (iii) ⇒ (iv); page 141 opens « Pour expliciter la condition (iii) », states Corollaire 1 and ends with (iv) ⇒ (ii) « de la dernière assertion du corollaire »; page 143 opens with Corollaire 2.',
    ours:
      'The order is the transcription’s, recorded in the headers of batches 7 and 8 and followed by the reading. Whether page 141 is a separate sheet, as batch 8 describes it, or the back of page 140 written on afterwards, is not settled by the transcriptions.',
    literature: [
      'Transcription 15, batch 7 (batch-07.fr.tex), page 140 and its closing note',
      'Transcription 15, batch 8 (batch-08.fr.tex), header and notes on pages 141 and 142',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile that page 140’s last line and page 142’s first line join, and whether page 141 is the verso of page 140 or a sheet of its own. If it is a verso, the « misplacement » is only the scan’s recto–verso order.',
  },
  {
    id: '15-brauer-section-5-leaves',
    cote: '15',
    pages: '175, 178',
    kind: 'codicological',
    claim:
      'Pages 178 and 175 are two leaves of a numbered handwritten redaction on the Brauer group, a § 5 with (5.1), Proposition 5.4, Corollary 5.5 and Theorem 5.6, to be read 178 then 175 although filed the other way, and the displayed isomorphism announced by page 178’s closing colon, together with the statement (5.3) that page 175 invokes, is on neither leaf.',
    basis:
      'Page 178 gives the exact sequence (5.1) 0 → 𝔾_{m,X} → R*_X → 𝒟iv_X → 0 and ends « isomorphisme de faisceaux étales : », with a margin « Démonstration du corollaire 5.4 »; page 175 opens « on tire aisément de (5.3.) », then states Proposition 5.4, Corollary 5.5 and Theorem 5.6 a), which breaks off. Both leaves sit among the calculations of the absolute cohomology of ℤ(n) (pages 172–177) and have no written link to them.',
    ours:
      'The reading adds that these statements are found, under another numbering, at the start of « Le groupe de Brauer II »; that comparison has not been made against the printed text for this entry. The margin of page 178 calls 5.4 a corollary where page 175 calls it a proposition; the entry records the mismatch and resolves nothing from it.',
    literature: [
      'Transcription 15, batch 9 (batch-09.fr.tex), header and pages 175 and 178',
      'Modernised reading 15, section XI',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile that nothing below page 178’s colon or above page 175’s first line has been missed, then compares the leaves with § 1 of « Le groupe de Brauer II » (Séminaire Bourbaki 1965–66, exp. 297; Dix exposés sur la cohomologie des schémas, 1968) to see whether they are a draft of it and where the numbering diverges. The other leaves of the § 5, if they survive, would be in another folder of the fonds.',
  },
  {
    id: '15-unites-leaf-other-hand',
    cote: '15',
    pages: '167',
    kind: 'codicological',
    claim:
      'The leaf « Unités » is not in his hand: it is written in blue ink on squared, perforated paper, in a round and careful script unlike his on every other handwritten leaf of the folder, and it proves that every unit of a number field K ⊂ ℂ has a real power if and only if K is real or a CM field.',
    basis:
      'Transcription 15, batch 9, describes the hand of page 167 as « quite unlike his elsewhere in the batch » and transcribes the statement, its proof by comparing unit ranks, and the example ℚ(ζ); the proof keeps a leftover « [K : K′] = 2 » from a version in which the extension was assumed quadratic.',
    ours:
      'The description of the hand is the transcription’s and has not been compared with other hands in the fonds. That the statement is contained, for « weilien » fields, in Corollary 1 of page 141 is the reading’s remark, not the leaf’s.',
    literature: [
      'Transcription 15, batch 9 (batch-09.fr.tex), header and page 167',
      'Modernised reading 15, section X',
    ],
    status: 'candidate',
    settle:
      'A person compares the hand of page 167 with his and with the other hands known in the fonds. Identifying the writer would say whether the leaf is a correspondent’s answer to a question of the folder or a stray. The pencil cover of page 179, which repeats the title of page 171, is the other leaf whose hand the transcription leaves undecided.',
  },
  {
    id: '15-two-typescripts',
    cote: '15',
    pages: '58–62, 80–81',
    kind: 'codicological',
    claim:
      'The « tapuscrit » of the folder’s title is three typed leaves from two different typescripts: « Catégories de Deuring », § 1 (p. 58), continued in his hand on pages 59–62, and « Localisation pour les variétés abéliennes », § 1 (pp. 80–81), which breaks off mid-sentence two-thirds down page 81 without reaching abelian varieties. Every other typed leaf in the folder is foreign material used as paper.',
    basis:
      'Page 58 is headed « Catégories de Deuring. » and « 1. Catégories A-linéaires et ⊗-enveloppes. », with typed and handwritten corrections; pages 59–62 continue its last handwritten sentence. Page 80 is headed « Localisation pour les variétés abéliennes. », § 1 a)–b), and page 81 gives c)–e), ending « et c’est une catégorie de Deuring, », with page 82 blank. The batch headers identify the other typed leaves as foreign: courses on analytic functions, an étale-cohomology typescript, English translations, Bourbaki drafts n° 370, 403, 413 and Tribu 59 and 99, typed errata to an exposé on groups of multiplicative type (p. 117), an administrative sheet dated 1.4.68 (p. 135) and a computer listing (p. 180).',
    ours:
      'Matching the inventory’s word « tapuscrit » to these three leaves is the edition’s, since the inventory does not say which leaves it means. That the two typescripts are two texts rests on their titles and on each opening a § 1. Nothing is claimed about which was typed first or whether the second was meant as a sequel to the first.',
    literature: [
      'Transcription 15, batches 3, 4 and 5 (batch-03, batch-04, batch-05.fr.tex), pages 58–62 and 80–81 and their headers',
      'Transcription 15, batches 2 and 6–12, headers (the foreign typed leaves)',
      'Modernised reading 15, header « Scope » and sections III and IV',
    ],
    status: 'candidate',
    settle:
      'A person compares typeface, paper and margins of page 58 with pages 80–81 on the facsimile. Further leaves of either typescript — a § 2 of « Catégories de Deuring », or the part of « Localisation » that reaches abelian varieties — would be looked for in the Montpellier inventory and the neighbouring folders of the group [10–18].',
  },
  {
    id: '51-albanese-good-reduction-codim-two',
    cote: '51',
    pages: '16–17, 20',
    kind: 'mathematical',
    claim:
      'If X is projective and flat over a discrete valuation ring V, with fibres smooth outside a closed subset of codimension ≥ 2 and generic fibre geometrically integral and normal, then Alb(X_K) and (Pic⁰_{X_K})_red have good reduction — the special fibre being allowed singularities in codimension 2 — by way of a complete-intersection curve C ⊂ X smooth over V, the surjection Pic⁰(C_K) → Alb(X_K), and the Koizumi–Shimura theorem on quotients.',
    basis:
      'Page 16 states the Proposition for X projective over V « [plat, fibres simples en codim ≤ 1] » and any A_K generated by a rational map from X_K: a « courbe générique » C, simple over V, maps to A_K and generates it, so Pic⁰(C_K) → A_K is surjective, Pic⁰(C_K) has good reduction through Pic⁰(C), and Koizumi–Shimura gives the rest. Page 17 applies it, under « fibres simples en codim ≤ 1 », to the Albanese map defined by a section obtained after an unramified extension, and passes to Pic⁰ by isogeny. The hypothesis « simples en codim ≤ 1 » is legible on both pages; on page 17 it replaces a struck « simples séparables ». Page 20 later cites good reduction of the abelian part of Pic⁰(X_K) as « le théorème de Koizumi ».',
    ours:
      'Much of the frame is the edition’s. The geometric normality of X_K is added by the reading, so that (Pic⁰)_red is an abelian variety. On page 17, « irréd. » in « X_K géom. irréd. » is uncertain, and so is the exponent read « red », which is overwritten. The existence of C and the fact that C_K → A_K generates are « on sait que cela existe… » and « je dis qu’on sait que » on the page, and the reading supplies them as Bertini- and Lefschetz-type statements it does not prove. The reading also asserts, without argument, that the fibres of C are geometrically connected. « Successivement simple » is a conjecture on a word reduced to a stroke. The page’s conclusion « Pic A se réduit bien » is read as A_K. The page reduces to an algebraically closed field where the reading uses an unramified extension, justified by Néron–Ogg–Šafarevič. The section is taken through a smooth point of X_k by Hensel’s lemma. The last step of page 17 uses duality where the page uses an isogeny. The entry makes no claim about the page 18–21 family theorem, whose statement the reading had to repair.',
    literature: [],
    status: 'unsearched',
    settle:
      'The page itself credits the Picard statement to Koizumi (p. 20), so the question is only whether the published hypotheses already allow a special fibre singular in codimension 2, or require it non-singular. Read S. Koizumi’s paper on the specialisation of Albanese and Picard varieties (Mem. Coll. Sci. Univ. Kyoto, c. 1960) and G. Shimura, « Reduction of algebraic varieties with respect to a discrete valuation of the basic field » (Amer. J. Math. 77, 1955), both cited from memory. Then read FGA, exposé 236, M. Raynaud, « Spécialisation du foncteur de Picard » (Publ. Math. IHÉS 38, 1970), and Bosch–Lütkebohmert–Raynaud, Néron Models, ch. 8–9. The ℓ-adic form of the same argument is short: H¹ of X_K̄ injects into H¹ of a Lefschetz curve with good reduction, so it is unramified. The statement may therefore stand in print as a remark rather than a theorem, and Serre–Tate, « Good reduction of abelian varieties » (Ann. of Math. 88, 1968), is the place to look for that form. If the codimension-2 hypothesis is in any of these, mark matched. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '51-author-number-11-on-page-21',
    cote: '51',
    pages: '10–11, 18–21',
    kind: 'codicological',
    claim:
      'Page 21 concludes the argument begun on page 18 and carries, top right in his hand, the number « 11 », the only author’s number in the folder, and that number fits no run the folder shows.',
    basis:
      'Page 21 opens « Donc l’image de A est P », answering the question on which page 20 closes, so it is the fourth page of the argument of pages 18–21. Counted from page 2, the first page of mathematics, it is the twentieth page. If pages 2–21 were rectos and versos of ten sheets, it would be the verso of the tenth. A run of eleven one-sided leaves ending there would begin at page 11, but page 11 opens « conclusion. », completing the « D’où la » at the foot of page 10.',
    ours:
      'The arithmetic is the edition’s, made for this entry from the transcriptions alone; no facsimile was consulted. The two transcriptions describe the numbering differently. Batch 1’s header says « He does not paginate ». Batch 2’s header says page 21 « continues a run he paginated from batch 1 », and no note in batch 1 bears that out. The reading says it does not know what the number counts. Neither transcription records which pages are rectos and which versos of one sheet.',
    literature: [
      'Transcription 51, batch 1 (batch-01.fr.tex), header and pages 10–11, 18–20',
      'Transcription 51, batch 2 (batch-02.fr.tex), header and note on page 21',
      'Modernised reading 51 (51.modern.tex), footnote on the kernel of u',
    ],
    status: 'candidate',
    settle:
      'A person looks on the facsimile for faint numbers at the head of pages 2–20, since a pencil figure is easily passed over, and establishes which pages share a sheet. If none of this yields a run ending at 11 on page 21, the number belongs to a sequence partly outside the folder. The neighbouring folders of the group « Variétés abéliennes » (45–56) are then the place to look.',
  },
  {
    id: '67-involution-modules-triples',
    cote: '67',
    pages: '90, 99',
    kind: 'mathematical',
    claim:
      'For any ring k and any k-module M on which multiplication by 2 is injective, the folder shows that an involution σ of M amounts to a triple (P, Q, m) — P = M₊ and Q = M₋ the ±1-eigenmodules, both 2-regular, and m ⊂ P/2P ⊕ Q/2Q a sub-(k/2k)-module meeting each summand trivially, that is, the graph of an isomorphism between a submodule of P/2P and one of Q/2Q — the functor (M, σ) ↦ (P, Q, m) being an equivalence of categories, with no finiteness or projectivity hypothesis on M.',
    basis:
      'Page 90 proves M₊ ∩ M₋ = 0 from 2-regularity, 2M ⊂ M₊ ⊕ M₋ from 2x = (x + σx) + (x − σx), and M′ ∩ P = 2P, M′ ∩ Q = 2Q for M′ = 2M, then reconstructs (M, σ) from (P, Q, m) through the isomorphism 2 · id : M → M′, and states the Proposition. Page 99 draws the Corollary for k principal and 2-regular with k/2k a field: m is zero or a line distinct from P/2P and Q/2Q, giving two conjugacy classes of involutions ≠ ±1 in GL₂(k), represented by diag(1, −1) and the matrix (1 1; 0 −1), which for k = ℤ is the reflection of the hexagonal lattice. The folder uses it for the two lattice types E_a, E′_a of real elliptic curves (p. 92). The uncertain words on page 90 (« par exemple » before « commut. », « on vérifie », « D’ailleurs ») carry no part of the statement.',
    ours:
      'The check that the equivalence needs no finiteness — a σ-map is determined by its restriction to P ⊕ Q, since M ⊂ ½(P ⊕ Q) and the target is 2-regular — is the edition’s, made for this entry; the page states the Proposition without restriction and does not discuss it. The reading corrects the scratch computation of page 91 (σ(x, y) = x − y for (x, −y)), which the entry does not use. The first Corollary of page 90, for M projective of rank 2 over a connected k, is partly illegible and cut at the right edge, and no part of the claim rests on it; on page 99, « à isom. près » and « projectifs » are uncertain.',
    literature: [],
    status: 'unsearched',
    settle:
      'The case k = ℤ is classical — two conjugacy classes of involutions ≠ ±1 in GL₂(ℤ), equivalently the three indecomposable ℤ[C₂]-lattices (I. Reiner, « Integral representations of cyclic groups of prime order », Proc. AMS 8, 1957; Curtis–Reiner, Methods of Representation Theory I, §34) — so the question is only the general Proposition. Since k[C₂] is the fibre product k ×_{k/2k} k when 2 is regular, look first in L. S. Levy, « Modules over pullbacks and subdirect sums » (J. Algebra 71, 1981), whose separated modules over a pullback are described by triples of this shape; then in J. Milnor, Introduction to Algebraic K-theory (1971), §2, for the projective case. All three references are cited from memory. If the Proposition is there, or is a direct instance of Levy’s description, mark matched. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '67-canonical-metrics-leaf-order',
    cote: '67',
    pages: '26–45',
    kind: 'codicological',
    claim:
      'The run « Métriques canoniques sur les surfaces conformes » is to be read 26, 44, 27, 45, 28–40, 41–43 — pages 44 and 45 being inserts between his sheets 1 and 2 and between his sheets 2 and 3, and pages 41–43 continuing his sheet 15 — and his circled numbers bear this out: pages 26–43 carry 1 to 18 in one series, page 45 carries 2′ and page 44 very probably 1′.',
    basis:
      'Page 44 carries a « Corollaire 3 » after Cor. 1 and 2 of page 26, refers to « (i) ci-dessus », page 26’s condition (i), and ends « On trouve donc de plus », which page 27, noted as lacking its lead-in, continues with « les surfaces suivantes ». Page 45 completes case (1) of page 27 (the unique metric of curvature −1 when X is compact) and breaks off in case 2) on « La constante multiplicative », which page 28, noted as lacking the start of case 2, continues with « déterminée par la condition que l’aire totale de X soit = 1 ». Page 40 breaks off on « la deuxième », and page 41 goes on with the conformal surfaces with boundary begun on page 39. Batch 2 records his numbers 1–15 on pages 26–40; batch 3, revised on the facsimile on 2026-09-23, records 16, 17, 18 on pages 41–43, 1′ (probable) on page 44 and 2′ on page 45, and puts pages 44–45 on another paper than pages 41–43.',
    ours:
      'The order is the reading’s, established from the text. When this entry was first written, batch 3 read the numbers of pages 41–45 as « 10 », « 11 », « 12 », « 17 », « 21 » and said sheets 13–16 and 18–20 were missing; the entry conjectured that « 17 » and « 21 » were « 1′ » and « 2′ ». The facsimile, read on 2026-09-23, gave 16–18 and 1′ (probable), 2′, and batch 3 and the reading were corrected. The join 40 → 41 remains the weakest, since the first word of page 41 is illegible. That the inserts go after his sheets 1 and 2 is inferred from the text and from the primes.',
    literature: [
      'Transcription 67, batch 2 (batch-02.fr.tex), header and pages 26–28, 35–40',
      'Transcription 67, batch 3 (batch-03.fr.tex), header and pages 41–45',
      'Modernised reading 67 (67.modern.tex), header « Order of the leaves » and « L’ordre des feuillets sur les métriques canoniques »',
    ],
    status: 'candidate',
    settle:
      'The numbers were read on the facsimile on 2026-09-23 (16, 17, 18; 1′ probable; 2′), but not by a person. A person confirms them, in particular the prime of page 44, which « 17 » cannot be entirely ruled out as, and compares the paper of pages 44–45 with the tractor-feed sheets of pages 26–40.',
  },
  {
    id: '68-orientation-stokes-axioms',
    cote: '68',
    pages: '49, 51',
    kind: 'mathematical',
    claim:
      'On the groupoid of finite-dimensional real vector spaces, the folder defines a « theory of orientation » as a functor Ω to two-element sets with Ω(0) ≃ {±1} and, for every hyperplane W ⊂ V and half-space V′ bounded by W, a bijection St_{V′} : Ω(V) → Ω(W), natural in (V, V′), which changes by the involution of Ω(W) when V′ is replaced by the opposite half-space; and it shows that every morphism of such theories is an isomorphism and that any two theories are related by exactly one isomorphism, the action of GL(n, ℝ) on Ω(ℝⁿ) being forced to be sg ∘ det.',
    basis:
      'Page 49 states two lemmas on two-element sets, the data a)–c), the two axioms and their equivalent form « Ω(W, V) ∧ Ω(V) ≃ Ω(W) », and a Theorem: a) every morphism of theories is an isomorphism, b) between two theories there is a unique isomorphism, c) a theory exists; it proves a) and the uniqueness in b) by induction on the dimension through the Stokes maps. Page 51 reduces a theory in dimension n to a character ε_n of GL(n, ℝ) and a Stokes bijection ω_n → ω_{n−1} for the half-space ℝ^{n−1} × ℝ₊, writes the compatibility with its stabiliser as ε_n(u_n) = sg(λ) ε_{n−1}(u_{n−1}), and concludes ε_1 = sg and ε_n = sg ∘ det « de proche en proche »; a boxed passage, struck with a large cross, draws the conclusion that all ω_n are identified with {±1}.',
    ours:
      'The reading supplies the step that « de proche en proche » leaves out: every homomorphism GL(n, ℝ) → {±1} factors through the determinant, so ε_n is fixed by its values on diag(1, …, 1, λ). It reads « St_V » in the second axiom as St_{V′}, and the Stokes datum written « Ω(V, W) ∧ Ω(W) → Ω(W) » as … ∧ Ω(V) → Ω(W). The page first justifies the bijectivity of St by the cardinal alone, which does not suffice; the claim uses bijectivity as the axiom the page states. « Dem_{W,V} », the name of the set of half-spaces, is read under an erasure, and « vectoriels » and the margin word « choisi » on page 51 are uncertain; none carries the statement. Existence, c), is only the usual orientations and is not part of the claim; page 49 marks it « ? » and the conclusion that would give it is in the struck passage. The comparison of the page’s inward-last normalisation with the geometers’ outward-first convention, by a sign (−1)^{dim V}, is the reading’s and the entry does not use it.',
    literature: [],
    status: 'unsearched',
    settle:
      'That Hom(GL(n, ℝ), {±1}) = {1, sg ∘ det} is classical, and so is the orientation torsor; the question is only whether orientation has been characterised, up to unique isomorphism, by axioms on its boundary (Stokes) maps for half-spaces. Look in Bourbaki’s treatment of the orientation of vector spaces over an ordered field (Algèbre), in P. Deligne and D. Freed, « Sign manifesto » (Quantum Fields and Strings: A Course for Mathematicians, vol. 1, AMS, 1999), in the discussions of boundary-orientation conventions in Bott–Tu, Differential Forms in Algebraic Topology, and in Greub, Linear Algebra, and, for the determinant analogue that page 55 prepares, in Knudsen–Mumford (Math. Scand. 39, 1976). All are cited from memory. If the characterisation is stated in any of them, mark matched. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '68-games-redactions-order',
    cote: '68',
    pages: '1, 3, 6, 23–28, 33',
    kind: 'codicological',
    claim:
      'Of the two long redactions on positional games, the transcriptions support reading the pencil layer of the first (pages 1–13) as earlier than the second (pages 23–33): the second carries through, on pages 26–28, the well-ordering proof of the fixed-point theorem that the first begins on page 6 and cancels, and the first bears blue-ink corrections on pages 1 and 3 that bring its initiative map and its sets of non-terminal positions to the conventions the second uses from its first page.',
    basis:
      'Batch 1 records that page 6 is crossed by a long oblique stroke and that its argument — a well-order on R(x), winning strategies Σ_y, the least y(z) from which z is reached, a decreasing and so stationary sequence — breaks off at « Donc pour n assez grand ». Batch 2 records the same construction on pages 26–28, with reachability taken through Σ_{x₁}-parties, E(x), ε(x) = min E(x), carried to « absurde ». Batch 1 records that « ∖ C₀ » in the arrow i and in the decomposition of page 1 is added in blue ink, that the NB which the restriction made pointless is struck through in blue, and that « ∖ C₀(j) », « ∖ C̄₀(j) » and « R(x) ⊂ G(j) » on page 3 are blue additions; page 23 defines α on C ∖ C₀ and C̄(j) = (C ∖ C₀) ∖ C(j) from the start. Batch 2 records page 33, the last page of the second redaction, in blue ink.',
    ours:
      'The inference to an order is the edition’s, made for this entry. The reading says the order of the three redactions « n’est pas établi », and neither transcription proposes one. It is not claimed that the blue of pages 1 and 3 is the ink of page 33: the transcriptions say only « encre bleue », which they also use for pages 16, 20–21 and 49–53. The one-page third redaction (p. 47) has no bearing on the claim. No facsimile was consulted.',
    literature: [
      'Transcription 68, batch 1 (batch-01.fr.tex), pages 1, 3 and 6 and their notes',
      'Transcription 68, batch 2 (batch-02.fr.tex), header and pages 23, 26–28 and 33',
      'Modernised reading 68 (68.modern.tex), « Le fil du dossier » and sections I–II',
    ],
    status: 'candidate',
    settle:
      'A person compares on the facsimile the blue ink of the corrections on pages 1 and 3 with that of page 33 and of the other blue-ink leaves, and the paper of pages 1–13 with that of pages 23–33. A shared ink would make the corrections to the first redaction and the end of the second one campaign. Without it, only the textual argument remains: the second redaction completes the first’s cancelled proof, which does not by itself exclude a later pass over the first.',
  },
  {
    id: '68-epousailles-typescript',
    cote: '68',
    pages: '49–54',
    kind: 'codicological',
    claim:
      'The blue-ink notes on orientation, pages 49, 51 and 53, alternate with three copies of one typed page headed « XVIII Les épousailles (2) », a list of paired words such as « lumière et ombre » with handwritten corrections, and the orientation text runs straight across them from page 49 to 51 to 53.',
    basis:
      'Batch 3 records pages 50, 52 and 54 as three copies of a typescript page headed « XVIII Les épousailles (2) » (paired words: « lumière et ombre », …), with handwritten corrections, not mathematics and not transcribed, and says the orientation run continues p. 49 → p. 51 → p. 53 across them; page 51 opens with a note that it follows page 49 and that page 50 is an unrelated typescript. Batch 1 records one other typed leaf in the folder, page 17, an administrative table (a list of promotions), between the scratch computations of page 16 and the run that begins on page 18.',
    ours:
      'The reading adds that page 52 carries « 82 » by hand, which no transcription records; re-checked on the facsimile on 2026-09-23, the number is on that copy alone (pp. 50 and 54 lack it, and p. 52’s type is darker, perhaps the top copy), in a hand the scan does not let one attribute. It also compares the theme of paired contraries with the yin and yang of Récoltes et semailles, while saying that nothing shows the typescript to be a state of it; the entry keeps that comparison out of the claim. The transcriptions do not record whether each typed face is the back of the blue-ink page before it, and no facsimile was consulted.',
    literature: [
      'Transcription 68, batch 3 (batch-03.fr.tex), header and note on page 51',
      'Transcription 68, batch 1 (batch-01.fr.tex), header (page 17)',
      'Modernised reading 68 (68.modern.tex), « Le fil du dossier », item 6 and its footnote',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile whether pages 50, 52 and 54 are the backs of pages 49, 51 and 53. If they are, the orientation notes were written on the backs of three copies of the typed page and are not earlier than it. The same person reads the heading, the « 82 » and the corrections. The typed page is then compared with the typescripts of Récoltes et semailles, part III (« La Clef du yin et du yang »), and of La Clef des songes, looking for a chapter XVIII or a section « Les épousailles ». A match would bound the date of the orientation leaves more closely than the inventory’s « [à partir de 1978-à partir de 1983] ».',
  },
  {
    id: '81-inventory-title-on-no-leaf',
    cote: '81',
    pages: '1, 13, 40',
    kind: 'codicological',
    claim:
      'The inventory’s title for the folder, « Immersions du disque et de la circonférence », is written on none of the transcribed leaves and describes none of them: the folder’s three covers carry, in his hand, « Cartes sphériques en général » (p. 1), « Décompositions n-aires (et découpages) d’espaces topologiques » (p. 13) and « relations d’équi. non parallèles » (p. 40), and no leaf treats immersions.',
    basis:
      'The three transcriptions record pages 1, 13 and 40 as sheets otherwise blank, inscribed in pencil in his hand, whose words head the sections that follow. The rest of the folder is spherical maps and rational functions (pp. 2–5), drawings of discs cut by chords (pp. 9–11), cuts of a topological space and binary decompositions (pp. 14–39), non-crossing parts of a polygon (pp. 41–52) and the gluing of two maps along an edge (pp. 53–54). The leaves left untranscribed are described in batch 1’s header: pages 6–7 in another hand on Fermat’s last theorem, page 8 blank but for a faint pencilled name and dates, page 12 a table that is not mathematics; batch 2’s header gives page 30 as blank.',
    ours:
      'That no leaf treats immersions is the reading’s judgement of the whole, which the entry adopts. The reading’s conjecture that the title may point to S. Blank’s work on extending immersions of the circle to the disc, by way of the chords of pages 9–11, is its own, marked there as unsupported by the pages, and no part of the claim. Pages 8 and 12 are described in the header, not transcribed, so their words are not on record. No facsimile was consulted.',
    literature: [
      'Transcription 81, batches 1–3 (batch-01, batch-02, batch-03.fr.tex), headers and the notes on pages 1, 13 and 40',
      'Modernised reading 81 (81.modern.tex), header « Scope » and the footnote to « Les stations »',
    ],
    status: 'candidate',
    settle:
      'A person looks on the facsimile for the title on every leaf, the untranscribed pages 6–8 and 12 and the backs of the covers included. If it is on none, the question goes to the Montpellier archives: whether it was read from an outer wrapper that was not digitised, or supplied by the cataloguers, in which case it would carry the brackets their other supplied titles carry.',
  },
  {
    id: '81-dessins-dating-cannot-support-precedence',
    cote: '81',
    pages: '2–5, 12',
    kind: 'codicological',
    claim:
      'Nothing in the folder dates the pages on spherical maps and « special » rational functions relative to Belyi’s theorem (1979), to La Longue Marche à travers la théorie de Galois (1981) or to the Esquisse d’un programme (1984): the one year the transcriptions record anywhere in the folder is 1981, the latest year of a table on page 12 that is not mathematics, and the inventory’s « [à partir de 1981] » is a lower bound for the shelfmark, not a reading of pages 2–5.',
    basis:
      'Batch 1’s header records that page 12 is a table in his hand, not mathematics, whose latest year, 1981, agrees with the archivists’ « [à partir de 1981] », and that page 8 carries faint pencilled dates read through the paper, which it does not give. Pages 2–5 carry no date; pages 3 and 5 are the versos of 2 and 4 and hold cancelled algebra and the second derivative of P/Q. The inventory’s title calls the folder « notes manuscrites (s.d.) ».',
    ours:
      'The reading names Belyi’s theorem and the Esquisse, footnotes that the inventory’s date makes it possible that he knew Belyi’s work while nothing on the page cites it, and notes that Belyi’s theorem is not needed in genus 0. Its résumé called page 2 « le point de départ » of what the Esquisse names dessins d’enfants, an order the folder does not date; the reading was rephrased on 2026-09-23 after this entry, and now says only that these are the objects the Esquisse (1984) calls dessins d’enfants and that the leaves cite neither Belyi nor the Esquisse. That page 12’s table is what the archivists dated the folder from is an inference, since they do not say. No facsimile was consulted.',
    literature: [
      'Transcription 81, batch 1 (batch-01.fr.tex), header and pages 2–5',
      'Modernised reading 81 (81.modern.tex), résumé and the footnotes to « Le dictionnaire (page 2) »',
    ],
    status: 'candidate',
    settle:
      'Only physical evidence would settle it: whether pages 2–5 and page 12 share a paper or a sheet, what the dates of page 8 are, and a comparison with the dated texts where a person would look for the same observation — La Longue Marche (written in the first half of 1981), the Esquisse (January 1984), both dates cited from memory, and folder 88, whose page 15 the reading says stops at the same point for its maps of type (p, q). This entry exists to stop the next reader treating « [à partir de 1981] » as a date for page 2. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '81-fermat-leaves-other-hand',
    cote: '81',
    pages: '6–7',
    kind: 'codicological',
    claim:
      'Pages 6–7 are not in his hand: they carry an attempted proof of Fermat’s last theorem — a^q + b^q = c^q worked through Newton’s binomial expansion, with a boxed example for q = 2 (3-4-5) — in a rounded school hand, and concern nothing else in the folder.',
    basis:
      'Batch 1’s header describes pages 6–7 so and leaves them untranscribed as unrelated. They fall between the note on the Galois action (p. 4) with its cancelled verso (p. 5) and the blank page 8, which is followed by the drawings of discs cut by chords (pp. 9–11).',
    ours:
      'The description of the hand is the transcription’s and has not been compared with other hands in the fonds. The reading leaves the pages undescribed. No facsimile was consulted.',
    literature: ['Transcription 81, batch 1 (batch-01.fr.tex), header'],
    status: 'candidate',
    settle:
      'A person compares the hand of pages 6–7 with his and with the other hands known in the fonds, and establishes whether 6 and 7 are the two sides of one sheet and whether page 8, whose faint pencilled name and dates are read through the paper, belongs with them. That would say whether the sheet is a correspondent’s, a stray, or paper he reused.',
  },
  {
    id: '81-cover-13-names-both-redactions',
    cote: '81',
    pages: '13–14, 30–31, 37',
    kind: 'codicological',
    claim:
      'The pink cover of page 13 names two redactions, not one: its title, « décompositions n-aires … d’espaces topologiques », is the title of Version II (p. 31) and uses a term the folder defines only in Version II’s margin (p. 37), while « et découpages », added in interline, is the word of Version I (p. 14), which never speaks of n-ary decompositions.',
    basis:
      'Batch 1 records page 13 as a pink sheet, otherwise blank, inscribed in pencil « décompositions n-aires (et découpages) d’espaces topologiques », with « et découpages » added in interline; page 14, headed « Version I » over a struck « V », proposes to study « le “découpage” de X » and speaks only of binary and ternary partitions. Batch 2 records page 31 headed « Décompositions n-aires d’un espace topologique », with « Version II » in the margin, and the margin of page 37 naming a « décomposition n-aire » when card A = n; it also records page 30, just before, as a blank pink sheet.',
    ours:
      'The comparison of the words is the edition’s, made for this entry from the transcriptions; neither transcription nor the reading draws it, and the reading places the cover at the head of pages 13–24, Version I alone. Nothing is claimed about whether the cover was written before, with or after either redaction: the interlinear addition shows only that « et découpages » came after the rest of the cover’s title. No facsimile was consulted.',
    literature: [
      'Transcription 81, batch 1 (batch-01.fr.tex), header and pages 13–14',
      'Transcription 81, batch 2 (batch-02.fr.tex), header and pages 31 and 37',
      'Modernised reading 81 (81.modern.tex), « Les stations » and sections III and V',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile whether the pink sheets of pages 13 and 30 are the two halves of one folded chemise and, if so, which leaves it enclosed: pages 14–29 would put Version I and the unlabelled redaction of pages 25–29 under a title taken from Version II, with Version II itself outside. The same person compares the pencil of the title with that of « et découpages » and of the « Version I » on page 14.',
  },
  {
    id: '133-centre-and-derived-group-from-two-crossed-modules',
    cote: '133',
    pages: '35–36, 45–53',
    kind: 'mathematical',
    claim:
      'For a group G with normal subgroups N ⊃ D(G) and N′ ⊂ Cent(G), seen as two crossed modules N → G/N′ and N′ → G/N sharing π₁ = N ∩ N′ and π₀ = G/NN′, the folder shows that N′ = Cent(G) if and only if a map Ψ_G : ℨ → Hom(π₀, π₁) is injective, ℨ being a subgroup of G/N′ determined by the two crossed modules alone, and that N = D(G) if and only if an alternating pairing λ_G : π₀ ⊗ π₀ → (N_ab)_{G/N′} is surjective; and that when G is replaced by another group G₁ realising the same two crossed modules, obtained from a central extension E of π₀ by π₁, both maps change only through the commutator pairing c_E of E: Ψ_{G₁} = Ψ_G + c̃_E α up to sign, and λ_{G₁} = λ_G + β c_E.',
    basis:
      'Page 45 sets out the data — 𝒞 = (N, M, d, Θ), 𝒞′ = (N′, M′, d′, Θ′) and isomorphisms of their π₀ and π₁ compatible with the actions — and the groups H = NN′ and K = G/π₁ they determine, and it states, without proof, an obstruction in H³(B_{π₀}/X, π₁) and an indeterminacy H² = Extop(π₀, π₁). Page 46 defines ℨ = [Cent(K)/(N′/π₁)] ∩ Ker Θ, factors the action of G on the inverse image of ℨ through φ_G : π₀ → Hom(ℨ, π₁), reinterprets it as Ψ_G, and boxes « Ψ_G injectif » as equivalent to N′ = Cent(G). Page 48 defines c_E from the commutators of E and writes « On doit trouver, au signe près » Ψ_{G₁} = Ψ_G + c̃_E α. Pages 51–52 define 𝒟 = (N_comm)_M and λ_G by lifting commutators, write N/DG ≃ 𝒟/λ_G(π₀ ⊗ π₀) and λ_{G₁} = λ_G + β c_E. Pages 50–53 then split each condition into a part independent of G, b), and a part that depends on it, c). Pages 35–36, under « Solution », set the same problem for a formal group, with L₁ = Cent G and D₁ = D(G). The uncertain words (« du » centre on page 46, « de passage au quotient » for α and the parenthesis on the sign on page 48, the S of M′(S) on page 52) carry none of the formulas.',
    ours:
      'The reading supplies the hypothesis [N, N′] = 1, without which G/N′ does not act on N, and the additivity and nullity checks that make Ψ_G a homomorphism, which the page sums up as « triviale sur N′ et sur ℨ ». The formula for Ψ_{G₁} is announced by the page (« on doit trouver ») and verified by the reading. Condition b) of page 50, which the page states as N′ = Cent(H) with « (condition ?) » in the margin, is repaired by the reading to N′ = H ∩ Cent(G), so the claim leaves out the b)/c) splitting for Ψ. The obstruction and the indeterminacy are unproved on the page; their identification with Eilenberg–Mac Lane’s theory of extensions with non-abelian kernel is the reading’s, and neither is part of the claim. π₀ is taken commutative, as the margin of page 48 says and as N ⊃ D(G) forces. The reading’s closing reduction to linear algebra on alternating forms, through the surjectivity of H²(π₀, π₁) → Alt(π₀, π₁), is its own and is not claimed. On page 35 the labels L₀ and D₀ pair the wrong quotients, and the reading repairs them from the arcs of page 36.',
    literature: [],
    status: 'unsearched',
    settle:
      'The obstruction in H³ and the torsor under H² are Eilenberg and Mac Lane’s (« Cohomology theory in abstract groups. II », Ann. of Math. 48, 1947) and Mac Lane and Whitehead’s (1950), so the question is only the part about the centre and the derived group. Look first at isoclinism, whose invariant is G/Cent(G), D(G) and the commutator map: P. Hall, « The classification of prime-power groups » (J. reine angew. Math. 182, 1940); F. R. Beyl and J. Tappe, Group Extensions, Representations, and the Schur Multiplicator (LNM 958, 1982), on central extensions and their commutator forms; N. S. Hekster, « On the structure of n-isoclinism classes of groups » (J. Pure Appl. Algebra 40, 1986). Then look in the crossed-module literature, R. Brown, P. J. Higgins and R. Sivera, Nonabelian Algebraic Topology (EMS, 2011), and in Hoàng Xuân Sính’s thesis, Gr-catégories (Paris VII, 1975; folder 135). All are cited from memory. If a group is described in any of them by these two crossed modules, with the conditions for its centre and derived group to be exactly N′ and N, mark matched. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '133-affine-quotient-not-constructible',
    cote: '133',
    pages: '42–43',
    kind: 'mathematical',
    claim:
      'For smooth group schemes with connected fibres over a base of mixed characteristic, the largest affine quotient of the fibres does not vary constructibly: an extension G of an abelian scheme A by 𝔾_a that is non-trivial at a point y of characteristic 0 and trivial at a specialisation s of characteristic p has (G_y)_aff = 1 and (G_s)_aff ≃ 𝔾_a.',
    basis:
      'Page 43, in an NB, says that the construction of G_aff « n’est pas de nature « constructible » en général », gives this example, and adds that « en égales car. résiduelles » it is constructible, the last without argument. The example rests on page 42: in characteristic 0 the extension of A by 𝔷 given by φ : D(𝔷) → Pic has Z_aff = 1 exactly when φ is injective, so a non-trivial extension by 𝔾_a has no non-trivial affine quotient; at s the extension is A × 𝔾_a. The subject of the sentence is an interlinear addition of which only « un G » is read, « prouve » and « sur » are uncertain readings, and the page’s « groupe affine lisse à fibres connexes » contradicts its own example.',
    ours:
      'The reading reads « groupe lisse » for the page’s « groupe affine lisse », which the example, an extension of an abelian scheme, requires. It also sharpens the example: in characteristic p an extension of A by 𝔾_a never has trivial G_aff, by page 42’s « bien connu », which the page does not prove, so over a base dominating Spec ℤ the locus where G_aff is trivial lies in the characteristic-0 fibre. That sharpening is not part of the claim. Neither the page nor the reading exhibits such an extension; over ℤ_p, the class p·ω of a basis vector ω of H¹(A, 𝒪_A) gives one, a check made for this entry. The constructibility in equal residue characteristic is the page’s assertion and is not claimed.',
    literature: [],
    status: 'unsearched',
    settle:
      'The difference between the characteristics is classical: in characteristic 0 a non-trivial extension of an abelian variety by a vector group can have trivial affine quotient, in characteristic p it cannot (M. Rosenlicht, « Extensions of vector groups by abelian varieties », Amer. J. Math. 80, 1958; M. Brion, « Anti-affine algebraic groups », J. Algebra 321, 2009). The question is whether the consequence for families is stated. Look in SGA 3, exposé VI_B, on affine quotients of group schemes over a base; in M. Raynaud, Faisceaux amples sur les schémas en groupes et les espaces homogènes (LNM 119, 1970); in Brion, « Some structure theorems for algebraic groups » (Proc. Sympos. Pure Math. 94, 2017); and in the work on anti-affine group schemes over a base. All are cited from memory. If the non-constructibility is stated in any of them, mark matched, and the equal-characteristic assertion becomes the thing to look up. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '133-dating-cannot-support-precedence',
    cote: '133',
    pages: '10–16, 23–26, 48–49',
    kind: 'codicological',
    claim:
      'Nothing in the folder dates the pages on functors from finite sets and injections (pp. 23–26) relative to Joyal’s species (1981) or to the FI-modules of Church, Ellenberg and Farb (2015): the only dates the folder carries are the printed 1974 of the Laborde offprints (pp. 10–16) and 19 and 5 June 1975 on two typed notices (pp. 47, 49) filed within another run, and the inventory’s « 1974-[à partir de 1975] » gives the end of its range only as « à partir de 1975 ».',
    basis:
      'Batch 1’s header dates the offprints 24 June and 16 September 1974. Batch 3’s header records pages 47 and 49 as typed USTL thesis-defence notices addressed to him, dated 19 and 5 June 1975, filed inside the run of pages 45–53 that he paginates 1–7; since its revision of 2026-09-23 it no longer calls them the versos of 46 and 48, the facsimile not settling it (a hole in mirror position favours 49 as the back of 48 without proving it). Batch 2’s header calls its five runs undated; pages 23–25 are in black ink and page 26 in blue, and no leaf of pages 17–28 carries a date. All three batches copy the inventory’s dating for the whole shelfmark.',
    ours:
      'The reading once said that species and FI-modules were « postérieurs de plusieurs années à la page, qui ne pouvait pas les connaître » and that these objects were studied « une quarantaine d’années plus tard »; both presupposed a date for pages 23–26 the folder does not give, and were rephrased on 2026-09-23 after this entry. If the notices are not the backs of his pages, they date nothing in his hand; if page 49 is the back of page 48, only his page 3 of that run is not earlier than 5 June 1975. The facsimile was examined for the notices in the revision, not for this entry’s claim.',
    literature: [
      'Transcription 133, batch 1 (batch-01.fr.tex), header',
      'Transcription 133, batch 2 (batch-02.fr.tex), header and pages 23–26',
      'Transcription 133, batch 3 (batch-03.fr.tex), header',
      'Modernised reading 133 (133.modern.tex), résumé, « Le fil du dossier » and the footnote on species and FI-modules in section III',
    ],
    status: 'candidate',
    settle:
      'Only physical evidence would narrow it: whether pages 47 and 49 are the backs of 46 and 48, whether the paper and ink of pages 23–26 match those of a dated leaf, and what the notice of page 49 announces. This entry exists to stop the next reader taking the inventory’s range, or the reading’s footnote, as placing pages 23–26 before species or FI-modules. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '133-laborde-offprints-after-witt-run',
    cote: '133',
    pages: '7, 10–16',
    kind: 'codicological',
    claim:
      'The two 1974 Comptes rendus notes of O. Laborde bound at pages 10–16 come directly after the run « Groupes de Witt et variantes », whose page 7 reports at second hand, « il paraît (Laborde dixit) », that (M, q) ⊕ (M, −q) is of the form E ⊕ Ě on an affine scheme without 2 being invertible; neither the transcriptions nor the reading record whether either note contains that statement.',
    basis:
      'Batch 1 records page 7’s sentence, with the interlinear « α(E) = » and the parenthesis saying that it fails on B_{O(n)}. Page 8 ends the run and page 9 is blank. Pages 10–12 are an offprint of a note on the Skolem–Noether theorem for graded Azumaya algebras over a semi-local ring (C. R. Acad. Sc. Paris 279, 16 September 1974, Série A, 447–449), and pages 13–16 one of « Formes quadratiques, algèbres de Clifford et signatures » (C. R. 278, 24 June 1974, Série A, 1599–1602), with nothing in his hand on any leaf, checked at 250 dpi and by an ink-colour count. The run that follows them (pp. 17–20) is on G-sets and does not mention quadratic forms.',
    ours:
      'The reading proves the statement attributed to Laborde by a bilinear lift of q, and that proof is not part of the claim. The reading says outright that, the offprints not being transcribed, it does not know whether the statement is in them. Nothing in the transcriptions shows whether the offprints are where he filed them or where the archivists put them. No facsimile was consulted.',
    literature: [
      'Transcription 133, batch 1 (batch-01.fr.tex), header, pages 6–7 and the note before page 17',
      'Modernised reading 133 (133.modern.tex), section II, « Les tirés à part »',
    ],
    status: 'candidate',
    settle:
      'A person reads the two notes, on the facsimile or in the Comptes rendus, for the hyperbolicity of (M, q) ⊥ (M, −q) without 2 invertible. If it is there, that note is the likely source of « Laborde dixit » — a source, not a date, since « il paraît » may as well report a conversation. If it is not, the offprints bear on pages 5–8 only through their subject and their place in the folder.',
  },
  {
    id: '161-4-pages-19-21-after-course',
    cote: '161-4',
    pages: '19–31',
    kind: 'codicological',
    claim:
      'Pages 19–21, bound before the course pages 22–31, come after them in the argument: they use notation those pages introduce and treat matter those pages list or announce, page 21 as the functoriality of the spectrum that a margin of page 30 schedules, pages 19–20 as « Compléments » to items (9)–(10) on limits and sums in Aff_k.',
    basis:
      'Page 21 writes the affine spaces in gothic letters with V_{k(x)} → V_A, S = V_k and a marginal « exemple du produit 𝔼¹ × 𝔼¹ », and uses the base of opens X_f and the closed sets V(J); 𝔼^I_k is introduced on page 22, V_A on page 23, 𝔛 = V_A and the spectrum with its X_f on pages 28–29. The margin of page 30 lists « Spec(A_f) ≃ X_f (homéomorphisme) — 10′) Fonctorialité de Spec A — 11) », and page 21 carries a struck « homéomorphismes X_f ≃ Spec A_f », then « Spec(A_f) ≃ X_f » and the maps φ(x_𝔭), φ⁻¹(V(J)), φ⁻¹(Y_f) for u : A → B. Pages 19–20 are headed « Compléments sur le formalisme des lim et des sommes dans Aff_k », write Γ_k = ⨿_Γ e_k = V_{k^Γ} with e_k, which page 26 defines as V_k, describe I_k in a margin as the functor of idempotent decompositions indexed by I, as page 27 describes homomorphisms out of ∏ A_i, and take Spec of I_k. The papers differ: page 21 is black ink on squared paper, pages 19–20 ink on white ruled paper, pages 22–24 black ink on spiral-pad sheets, pages 26–31 blue ink on plain paper.',
    ours:
      'The observation for page 21 is the transcription’s (batch 2 header: « likely later in the argument than page 22 despite the archivists’ order »), and the reading adopts it; the placing of pages 19–20 is the reading’s, and the entry checks both against the transcriptions. Batch 2 notes that the margin of page 30 « renvoie par une flèche » to a line of page 21, which cannot be a physical arrow between two leaves of different paper; the entry rests on what the margin says, not on that arrow. The margin numbers the functoriality 10′, before item (11), while page 21 uses the topology that item (11) builds; the entry claims only that page 21 comes after the pages whose notation it uses. No facsimile was consulted.',
    literature: [
      'Transcription 161-4, batch 1 (batch-01.fr.tex), header and pages 19–20',
      'Transcription 161-4, batch 2 (batch-02.fr.tex), header and pages 21–31',
      'Modernised reading 161-4 (161-4.modern.tex), « Le fil du dossier » and sections VI–VII',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile what the arrow in the margin of page 30 points to, and whether the squared sheet of page 21 or the ruled sheet of pages 19–20 matches the paper of any course page. A match of paper would say where the sheets were inserted; without it, the order stays an order of the argument, not of the writing.',
  },
  {
    id: '161-4-topos-leaves-continue-161-6',
    cote: '161-4',
    pages: '15, 17',
    kind: 'codicological',
    claim:
      'The two topos leaves filed in this course folder read in the order 17, 15, and page 17 opens by continuing the question written on page 22 of folder 161-6: that page ends on case c), E = D̂, where γ(C, E) is « le morph. de topos évident » (C × D)^ → Ĉ × D̂, and page 17 begins « donc la question est si c’est une équiv. de topos », numbering its display (2) after that page’s boxed (1).',
    basis:
      'Page 17 opens mid-argument on « donc » with the display (2) (C × D)^ ≈? Ĉ × D̂ and settles it when C and D have finite limits; it then writes « c) Dans le cas général », builds the square α, β, γ, γ′ with C → C′ and E ↪ D̂, and proves the corollary that γ(C, E) is a plongement. Page 15, a fragment at the head of an otherwise empty leaf, opens « Or », uses C′, D̃ and π(C′, D̂), and reduces to showing that γ(C, D̂)_* and γ(C′, D̃)_* are essentially surjective, which presupposes page 17’s corollary. Page 22 of 161-6, written the other way up and cancelled by a cross, defines π(C, E) and the boxed « (1) » γ(C, E) : π(C, E) → Ĉ × E, asks whether it is always an equivalence, and lists a) sums, b) C a groupoid, c) E = D̂; page 23 of 161-6 is blank. One detail does not fit a direct continuation: page 17 letters the general case c), the letter 161-6 gives to E = D̂.',
    ours:
      'The link between the two folders is the readings’: 161-4’s says page 17 « reprend exactement là », 161-6’s that « on ne sait pas lequel précède l’autre ». The entry claims a continuity of the text, not an order of writing. The observation that « donc » picks up the last line of 161-6 page 22, and the mismatch of the letter c), are made for this entry from the two transcriptions; neither reading remarks the letter. No facsimile was consulted.',
    literature: [
      'Transcription 161-4, batch 1 (batch-01.fr.tex), header and pages 15 and 17',
      'Transcription 161-6, batch 2 (batch-02.fr.tex), header and page 22',
      'Modernised reading 161-4 (161-4.modern.tex), section VIII',
      'Modernised reading 161-6 (161-6.modern.tex), the footnote on 161-4 to the section on π(C, E)',
    ],
    status: 'candidate',
    settle:
      'A person compares on the facsimile the paper and ink of 161-6 page 22 with those of 161-4 pages 15 and 17, and looks for a leaf, in either folder or elsewhere in the fonds, on which the E = D̂ case is lettered b), which would explain page 17’s c). If the leaves are one run, the inventory’s datings of the two shelfmarks, [après 1961] and [à partir de 1973-vers 1977], bear on each other; they date the shelfmarks, not the leaves.',
  },
  {
    id: '161-4-course-unnamed-undated',
    cote: '161-4',
    pages: '9, 14, 16, 22–31',
    kind: 'codicological',
    claim:
      'The folder names neither the place nor the year of the course it prepares: page 22 speaks only of « our summer course », in English and in two parts, « Introduction to A.G. » and « Introduction to algebraic groups », and the one outside reference on any leaf, « EGA II 4.5 » in the margin of page 9, is on a sheet of another run — so nothing dates the functorial pages 14, 16 and 22–31 relative to Demazure–Gabriel (1970) or to the second edition of EGA I (1971).',
    basis:
      'Batch 2 transcribes page 22: « Prerequisites for the courses I and II », « in our summer course », « The content of I are prerequisites for II! », followed by the French items (1)–(8). Batch 1 gives page 9, with its « EGA II 4.5 » margin, as one of the loose sheets of pages 7–9 in the hand and blue ink of the descent run of pages 2–6; the functor pages are page 14 (ink, yellow paper), page 16 (pencil, then ink) and pages 22–31 (black ink on spiral-pad sheets, then blue ink on plain paper). No leaf carries a date, and both batches copy the inventory’s dating for the group 161-1 to 162-6, [après 1961-vers 1977], the folder’s own being [après 1961].',
    ours:
      'The reading already declines to identify the course (« On ne cherche pas à l’identifier ») and says its comparison of page 16 with Demazure–Gabriel « ne dit rien de l’ordre des dates ». Its header says the pages support only « after EGA II (margin p. 9) »; that margin dates the sheet of page 9 at most, not the course pages, and the entry narrows it so. Its résumé calls the descent pages « une autre strate, plus ancienne peut-être »; no date on the leaves supports « plus ancienne », and the entry does not adopt it. The Buffalo comparison in the settle field is ours, from memory. No facsimile was consulted.',
    literature: [
      'Transcription 161-4, batch 1 (batch-01.fr.tex), header and pages 9, 14 and 16',
      'Transcription 161-4, batch 2 (batch-02.fr.tex), header and page 22',
      'Modernised reading 161-4 (161-4.modern.tex), header, résumé, « Le fil du dossier » and the footnote on Demazure–Gabriel in section IV',
    ],
    status: 'candidate',
    settle:
      'A person compares pages 22–31 with the notes of the summer school Grothendieck gave at Buffalo in 1973, « Introduction to functorial algebraic geometry, part 1: affine algebraic geometry », written up by Federico Gaeta — title, year and editor cited from memory and unchecked — for the order of items (1)–(11), the notation 𝔼^I_k, V_A, e_k, and the example G/B = e_k « ce qui est idiot ! ». A match would identify course I of page 22 and date the course leaves, not the descent pages 2–6 nor the topos leaves 15, 17 and 25. This entry exists to stop the next reader taking page 16’s « la notion de schéma est explicitée sans recours à la notion d’espaces topologiques » as placed before or after anyone’s published account. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '161-5-annotations-later-than-offprints',
    cote: '161-5',
    pages: '9, 15, 16, 19, 20',
    kind: 'codicological',
    claim:
      'The five red-ink annotations on Serre’s two offprints are later than the offprints: they report as done, or as just published, work that — if « Inventions », « Annals » and « le livre de T. Springer sur les alg. de Jordan récemment paru chez Springer-Verlag » are S. Sen’s papers in Inventiones Math. 17 (1972) and Ann. of Math. 97 (1973) and Springer’s Jordan Algebras and Algebraic Groups (1973) — appeared in 1972–1973, so the inventory’s 1967–1969 dates the printing of the offprints, not the hand that annotated them, which the transcription could not identify as his.',
    basis:
      'Batch 1 transcribes five marginal notes in one red ink and one hand: « En fait, on a M = I_alg (Sen) » (p. 9), « voir Sen (Annals) » (p. 15), « démontré par S. Sen (Inventions) » (p. 16), « ceci a été démontré par S. Sen (Annals) » (p. 19) and « voir à ce sujet le livre de T. Springer sur les alg. de Jordan récemment paru chez Springer-Verlag » (p. 20). Each marks a remark or a question of the printed text as settled or treated elsewhere: Serre’s question w = e_K·v + O(1) on page 16, his conjecture on H_V° without solvability on page 19, the attempt at a classification for n₁ > 1 on page 20. The offprints are Serre’s Driebergen paper (Springer, 1967) and his résumé of the Collège de France course of 1967–1968 (Annuaire, 68e année, 1968–1969). « Annals » is an uncertain reading on page 15 and a clear one on page 19; the claim rests on pages 16, 19 and 20. The blue correction of a printed sign on page 15 is attributed to no one and plays no part.',
    ours:
      'The identification of the three references is the transcription’s, given in its header as inference and kept out of its dating line, and the reading adopts it; the margins give no year, no title and no initial beyond « S. Sen » and « T. Springer ». That the five annotations are one campaign rests on the transcription’s « same red ink and same hand ». The claim says nothing about whose hand it is. No facsimile was consulted.',
    literature: [
      'Transcription 161-5, batch 1 (batch-01.fr.tex), header and pages 9, 15, 16, 19 and 20',
      'Modernised reading 161-5 (161-5.modern.tex), section I and « Ce que les annotations disent de leur date »',
    ],
    status: 'candidate',
    settle:
      'A person checks the three references against the printed passages they face: S. Sen, « Ramification in p-adic Lie extensions » (Invent. Math. 17, 1972), against page 16; Sen, « Lie algebras of Galois groups arising from Hodge-Tate modules » (Ann. of Math. 97, 1973), against pages 15 and 19; T. A. Springer, Jordan Algebras and Algebraic Groups (Ergebnisse 75, 1973), against page 20 — all cited from memory. Sen also has an earlier Annals paper, « On automorphisms of local fields » (Ann. of Math. 90, 1969), so « Annals » alone does not date; it is the subject of page 19 that points to 1973. The same person compares the red hand on the facsimile with his and with Serre’s. If it is his, the annotations date a reading of the offprints, not their arrival in the folder.',
  },
  {
    id: '161-5-leaves-undated-mysterious-functor',
    cote: '161-5',
    pages: '22–28',
    kind: 'codicological',
    claim:
      'Nothing in the folder dates the manuscript leaves, pages 22–28, relative to Grothendieck’s public statement of the « mysterious functor » problem in 1970 or to Fontaine’s period rings: the leaves carry no date, the inventory itself calls them « notes manuscrites (s.d.) », its 1967–1969 is the date of the printed offprints they are filed with, their one reference, « par Tate », bounds them only from below, and the one datable layer in the folder, the red annotations on the offprints, points, if its references are as the transcription proposes, to 1973 or after.',
    basis:
      'Batch 2’s header describes pages 22–28 as leaves in three media — ink on squared paper (pp. 22–23), pencil on ruled paper (pp. 24–26), pencil on squared paper (pp. 27–28) — with a separate ink computation on the lower half of page 28, and records no date on any of them; both batches copy the inventory’s « 1967-1969 », and the folder title reads « tirés à part annotés (1967-1969), notes manuscrites (s.d.) ». The leaves cite no author but Tate, for the full faithfulness of page 22 (« Foncteur pl. fid. (par Tate) »), and do not refer to the offprints. Their vocabulary — « BT à isog. près », « catégorie tannakienne », « F-isocristal », a « L-foncteur fibre filtré » — is the only other internal evidence, and bounds nothing without a dated comparison.',
    ours:
      'The reading’s résumé says that Grothendieck « l’appellera en 1970 » the problem of the « foncteur mystérieux » and that Fontaine « y répondra »; section II calls it the question he « posera publiquement en 1970 »; its footnotes say that the pages « ne les connaissent pas », Fontaine’s constructions, and that of Kottwitz’s G-isocrystals « rien de cela n’est connu des pages ». Each presupposed a date the folder does not give; the entry adopts none of them, and the reading was rephrased on 2026-09-23 after this entry to say only what the leaves contain and do not cite. The reading’s footnote on the annotations offers the name « Barsotti-Tate » as « un indice, faible » that the leaves too are later than 1967–1969; the entry does not adopt that either. The identification of the Question of page 23 with the mysterious functor is the reading’s and is not part of the claim. No facsimile was consulted.',
    literature: [
      'Transcription 161-5, batch 1 (batch-01.fr.tex), header',
      'Transcription 161-5, batch 2 (batch-02.fr.tex), header and pages 22–28',
      'Modernised reading 161-5 (161-5.modern.tex), résumé, « Ce que les annotations disent de leur date » and its footnote, and the footnotes on Fontaine and on Kottwitz in sections II and III',
    ],
    status: 'candidate',
    settle:
      'Only physical or documentary evidence would narrow it: the paper and ink of pages 22–28 against dated leaves elsewhere in the fonds, and whether he or the archivists put the leaves with the offprints. A comparison of the notation — ℳ^BT, T_cr, T_DR, T_Hdg, the torsors 𝔓 and Q, the data 1)–6) — with his Nice address « Groupes de Barsotti-Tate et cristaux » (Actes du Congrès international des mathématiciens, 1970) and his Montréal lectures Groupes de Barsotti-Tate et cristaux de Dieudonné (from the summer course of 1970, published 1974), both cited from memory, would show a resemblance, not a date. This entry exists to stop the next reader taking the reading’s future tense as placing the leaves before 1970, or before or after anyone’s published account. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '161-6-leaves-12-15-reversed',
    cote: '161-6',
    pages: '12–15',
    kind: 'codicological',
    claim:
      'Pages 12–15 are bound in the reverse of the order in which both of their layers run: the ink computation on the fifth roots of unity passes from page 14 to page 12, and the pencil run on ordered sets from page 15 to page 13 and then, by « TSVP », to the foot of page 12 — so in each layer the text on pages 14–15 comes before the text on pages 12–13.',
    basis:
      'Batch 1 transcribes page 14 ending on the norm « N γ = γγ^α = (ζ + ζ⁻¹)(ζ² + ζ⁻²) = », left at the sign, and page 12 opening on « ζ³ + ζ⁻¹ + ζ + ζ⁻³ = ζ + ζ² + ζ³ + ζ⁴ = −1 », which is that product expanded, followed by « L’équation de γ est donc γ² + γ − 1 = 0 ». It notes that the last computation of page 15, γ̄(W ∧ W′) = …, continues at the head of page 13, which goes on with the point γ) after the α) and β) of page 15; that page 13 ends « TSVP »; and that the continuation is, « selon toute apparence », the two pencil lines d) and e) at the foot of page 12, written head to tail with respect to the ink, as page 13 is. Pages 15 and 13 are crossed by a long diagonal; pages 12 and 14 are ink.',
    ours:
      'The ink order 14 → 12 is the reading’s (section III, which says the transcription does not record it); the pencil order 15 → 13 → foot of 12 is the transcription’s. Putting the two together, and inferring from « TSVP » that pages 12 and 13 are the two faces of one leaf, is the edition’s, made for this entry. Neither file records which faces are rectos and versos, nor whether pages 14 and 15 are one leaf; the claim is about the order of the text, not of the sheets. Which layer was written first is not claimed. No facsimile was consulted.',
    literature: [
      'Transcription 161-6, batch 1 (batch-01.fr.tex), header and pages 12–15 with their notes',
      'Modernised reading 161-6 (161-6.modern.tex), « Le fil du dossier », section III and its first footnote, section V',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile whether pages 12/13 and 14/15 are the two faces of two sheets. If they are, both the ink and the pencil were written with the sheet of pages 14–15 first, and the pencil run’s orientation and its order 15 → 13 → foot of 12 are what one gets by writing on the pair turned over and upside down; the archivists’ order then reverses the two sheets, and pages 14, 12 and 15, 13 should be read in that order.',
  },
  {
    id: '161-6-om-run-opening-missing',
    cote: '161-6',
    pages: '12–13, 15',
    kind: 'codicological',
    claim:
      'The pencil run of pages 15, 13 and the foot of page 12 begins on a leaf that is in no transcribed folder of the fonds: the name « (OM) » occurs nowhere else in the transcriptions, and neither do the two-factor hypotheses a)–d) that page 15 invokes; the nearest matches are 161-2, page 80, whose item (4″) describes in his words the category the run uses, without that name, and 161-3, page 11, which uses the same restricted product ∏′ with all but finitely many entries equal to the top element.',
    basis:
      'Page 15 opens « Alors α, β : I → K, J → K [font de K une somme de I, J dans (OM)] », with a margin « sont dans (OM) (grâce à a) b)) », and later cites « en vertu de d) »; batch 1 says the run begins before page 15 and that its hypotheses are not in the batch, and batch 2 (pp. 21–33) does not contain them. Page 13 sets the infinite form over ∏′ I_λ, « formée des (V_λ) tels que V_λ = 1_{I_λ} pour presque tout λ ». In 161-2, batch 4, page 80 lists among the cases to treat « (4″) Cat. préordonnées avec inf finis, sup quelconques, que inf distributifs par sup quelc., foncteurs commutant aux inf finis et sup quelc. ». In 161-3, batch 1, page 11 runs the infinite-product argument on « ∏′ 𝒪_{X_i} », families with « U_i = X_i … pour presque tout i ». The letters (OM) are marked uncertain on page 13 and read without doubt on page 15.',
    ours:
      'The reading identifies (OM) with the category of frames from what the proofs use and says so; the match with 161-2 page 80 (4″), which is independent evidence in his hand for that identification, is the edition’s, made for this entry, as is the link to 161-3. That the run’s hypothesis e) is, for frames of opens, the kind of statement 161-3 pages 10–12 prove for spaces is the edition’s reading and no part of the claim. The search was a text search of the 77 transcribed folders for « OM » as a category name and for the phrases « Inf finis » and « Sup quelc. »; untranscribed folders were not searched. No facsimile was consulted.',
    literature: [
      'Transcription 161-6, batch 1 (batch-01.fr.tex), header and pages 12, 13 and 15; batch 2 (batch-02.fr.tex), header',
      'Transcription 161-2, batch 4 (batch-04.fr.tex), page 80',
      'Transcription 161-3, batch 1 (batch-01.fr.tex), pages 10–12',
      'Modernised reading 161-6 (161-6.modern.tex), section V and its footnotes',
    ],
    status: 'candidate',
    settle:
      'A person looks, as further folders are transcribed and on the facsimiles of 161-2, 161-3 and 161-6, for a pencil leaf that names (OM) and states the two-factor hypotheses a)–d), and reads the two letters on pages 13 and 15. If the opening turns up in 161-3, the run is the frame-side half of that folder’s argument on products of spaces, and the two shelfmarks bear on each other as 161-4 and 161-6 do through 161-4-topos-leaves-continue-161-6.',
  },
  {
    id: '161-6-graph-embeddings-dating-cannot-support-precedence',
    cote: '161-6',
    pages: '24–30',
    kind: 'codicological',
    claim:
      'Nothing in the folder dates the pages on isotopy classes of embeddings of a 1-complex in an oriented surface, pages 24–30, relative to Y. Ladegaillerie’s work on the same subject or to the Esquisse d’un programme (1984): no leaf carries a date, and the inventory’s « [à partir de 1973-vers 1977] » is the archivists’ estimate for the shelfmark, not a reading of these pages.',
    basis:
      'Batch 2’s header describes pages 24–30 as loose leaves with no pagination of his own and records no date on any of them; both batches copy the inventory’s dating line, which batch 2 calls « the inventory’s own, for the shelfmark and its group ». The pages cite no one: « groupe de Teichmüller » (p. 28) is the only name, and they give no reference for Th 1, Th 2 or the classification of planar embeddings.',
    ours:
      'Batch 2’s header calls pages 24–30 the « graphes » of the folder title « well before the Esquisse »; the reading’s résumé and its footnote on rotation systems say that Grothendieck « reviendra » to these objects in the Esquisse, « un contexte postérieur ». Both took the inventory’s estimate as a date for these leaves; the entry adopts neither, and both files were rephrased on 2026-09-23 after this entry (the reading now says these are objects the Esquisse (1984) also studies, which the pages do not cite). The reading’s footnote names Ladegaillerie’s « Classes d’isotopie de plongements de 1-complexes dans les surfaces » (Topology, 1984), « issu d’un travail fait à Montpellier dans les années 1970 », « sans pouvoir dire s’il y a un lien »; the entry adds nothing to that. That Ladegaillerie was Grothendieck’s doctoral student at Montpellier is from memory, unchecked, and no part of the claim. No facsimile was consulted.',
    literature: [
      'Transcription 161-6, batch 2 (batch-02.fr.tex), header and pages 24–30',
      'Modernised reading 161-6 (161-6.modern.tex), résumé and section VII with its footnotes',
    ],
    status: 'candidate',
    settle:
      'Only physical or documentary evidence would narrow it: the paper and ink of pages 24–30 against dated leaves of the fonds, and a comparison with Ladegaillerie’s thesis and his Topology 23 (1984) paper — its notation, its model surfaces and whether it states Th 1, Th 2 and the Question of page 29 — and with G. A. Jones and D. Singerman, « Theory of maps on orientable surfaces » (Proc. London Math. Soc., 1978), all cited from memory. A resemblance would show a shared subject, not an order. This entry exists to stop the next reader taking « well before the Esquisse » or « reviendra » as a date, or treating these pages as placed before or after a student’s or anyone’s published account. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '162-5-formal-categories-flat-conormal-de-rham',
    cote: '162-5',
    pages: '21–26',
    kind: 'mathematical',
    claim:
      'Over a scheme X₀ of characteristic 0, the functor sending an I-adic formal category over X₀ (a complete pro-ring with augmentation and a coassociative, counital Δ, no inverse being assumed) to the differential graded algebra (Λ^•Ω, δ) on its conormal Ω = I/I² is an equivalence between such formal categories with Ω flat and the De Rham complexes on Λ^•Ω with Ω flat, with no finiteness hypothesis on Ω and no smoothness hypothesis on X₀.',
    basis:
      'Page 26 (§ 6) states it as « Th. de Quillen », without proof or reference: the functor A ↦ (Ω*, δ) « induit une équivalence entre la catégorie des catégories formelles I-adiques sur X₀ dont le Ω est plat, et la catégorie des complexes de De Rham … dont le Ω est plat », and it « contient le th. de Cartan sur les groupes formels en car. nulle ». Pages 21–22 define the formal categories and the degree-0 differential; page 21 asks in brackets, without answering, whether such a category is necessarily a groupoid. « I-adiques » and the characteristic-0 hypothesis are ink additions, « lorsque » being an uncertain reading. The bracket saying that the A in question are those for which Sym Ω → Gr(A) is an isomorphism rests on the uncertain readings « isomorphisme » and « signifie ».',
    ours:
      'The page names no morphisms; the variance (covariant in the pro-ring A, contravariant in the category) and the covariant equivalence 𝒞 ↦ 𝔤^𝒞 with Lie algebroids when Ω is locally free of finite type are the reading’s. The reading takes the bracket as a description of the A concerned and says it does not know whether, in characteristic 0, flatness of Ω implies Sym Ω ≃ gr A; the claim inherits that uncertainty about which formal categories are meant. The page’s Remarque 1 (pp. 22–23), that δ² = 0 follows from α)–γ), is false, and the reading corrects it. The claim uses the definition of a De Rham complex, in which δ² = 0 is required, and not the Remarque.',
    literature: [],
    status: 'unsearched',
    settle:
      'The equivalence of formal groupoids with Lie algebroids in characteristic 0, for Ω locally free of finite rank, is expected to be in the books, and that case alone does not settle the entry. The question is the flat, non-finite case, and categories with no inverse assumed. Look in Grothendieck, « Crystals and the de Rham cohomology of schemes » (Dix exposés, 1968), on formal groupoids and stratifications; P. Berthelot, Cohomologie cristalline des schémas de caractéristique p > 0 (LNM 407, 1974), chapter II; L. Illusie, Complexe cotangent et déformations II (LNM 283, 1972); M. Kapranov, « Free Lie algebroids and the space of paths » (Selecta Math. 13, 2007); D. Gaitsgory and N. Rozenblyum, A Study in Derived Algebraic Geometry, vol. II (2017), on formal groupoids and Lie algebroids. For X₀ a point with Ω infinite-dimensional, look in the literature on Lie coalgebras (W. Michaelis) and on formal groups (Dieudonné, Lazard, and Milnor and Moore, 1965). All are cited from memory. If any of them states the equivalence with Ω flat and no finiteness, or proves that a formal category in this sense is automatically a groupoid, mark matched. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '162-5-de-rham-hochschild-flat-formal-category',
    cote: '162-5',
    pages: '27–30',
    kind: 'mathematical',
    claim:
      'Under the same hypotheses (X₀ of characteristic 0, a formal category 𝒞 over X₀ with flat conormal Ω), descent data on an 𝒪-module M relative to 𝒞 correspond to integrable Ω-connections on M, and the De Rham complex Λ^•Ω ⊗ M is canonically quasi-isomorphic, in the derived category, to the Hochschild (Čech–Alexander) complex C^•(𝒞, M).',
    basis:
      'Page 30 (§ 11) states both parts, without proof, « sous les conditions du th. de Quillen ». § 7 (p. 27) shows how descent data give the operator δ_M and says its square vanishes by the descent condition, and asks without answering whether order 2 suffices. A slanted margin asks to relate the comparison to the « th. fondamental du dévissage des cristaux », its last line uncertain. A word before « (dans la catégorie dérivée) » is illegible, and the notes stop on the heading « Variante à puissances divisées ».',
    ours:
      'The page says « Ω-connexions », without « intégrables »; the adjective is the reading’s, required by § 7. The page does not define C^•(𝒞, M); the cobar complex on strings of composable arrows is the reading’s, taken from the two names the page uses. The reading identifies two special cases: for 𝒞 the completed diagonal of a smooth X₀ over ℚ, the comparison of de Rham and infinitesimal cohomology in Grothendieck’s notes on crystals; for X₀ a point, the cohomology of a formal group against that of its Lie algebra. Those are matches and are not the claim.',
    literature: [],
    status: 'unsearched',
    settle:
      'The question is only a general formal category with flat, not necessarily finite, Ω. Look in Grothendieck’s « Crystals » exposé (1968), on Čech–Alexander complexes; P. Berthelot and A. Ogus, Notes on Crystalline Cohomology (1978); M. Crainic, « Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic classes » (Comment. Math. Helv. 78, 2003); and Gaitsgory and Rozenblyum, vol. II (2017), on the cohomology of formal groupoids. All are cited from memory. If the comparison is stated for formal groupoids, or for formal categories, with flat Ω over a base of characteristic 0, mark matched. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '162-5-bordism-correspondences-universal',
    cote: '162-5',
    pages: '43–45',
    kind: 'mathematical',
    claim:
      'On closed manifolds with homotopy classes of maps, the category 𝐁 whose morphisms X → Y are unoriented bordism classes of manifolds over X × Y is universal among categories receiving a covariant and a contravariant functor that agree on objects and satisfy base change for transverse cartesian squares: any such pair (F′_•, F′^•) already identifies bordant correspondences, a correspondence Z → X × Y with components p, q going to F′_•(q) ∘ F′^•(p).',
    basis:
      'Pages 43–45 (the annotated copy; the same typescript is at pp. 12–14 of the photocopy) pose the universal problem, say « Quillen prouve » that 𝐁 solves it, define the factorisation on arrows by X′ → Z′ → Y′, and sketch why it is well defined. The bordism T is doubled into a manifold T̄ over S¹, transverse over two points with fibres Z₀ and Z₁, and the two composites are compared through the cartesian square of inclusions X_s → X over S¹ × X, whose lower arrow i_s does not depend on s up to homotopy. The sketch ends « Le reste est sans doute l’AQT », with nothing on compatibility with composition or on uniqueness. The labels of the composite and the arrows of the square are ink in blanks of the typing; the first label is read α_i without a visible asterisk, and batch 3 leaves the labels of the composite doubtful.',
    ours:
      'The page does not say « compactes »; the reading adds closed manifolds, which the pushforwards and the composition in 𝐁 need, and only the photocopy carries a margin « (compactes ?) ». The composition law of 𝐁, the contravariant F^• : 𝒱° → 𝐁 (the typing has C → 𝐁), and the order of the base-change identity α_{s•}α_s^• = Γ^• i_{s•} are the reading’s. That the factorisation is unique, because every morphism of 𝐁 is F_•(q) ∘ F^•(p), is the edition’s, made for this entry; the page asserts the universal property without saying so.',
    literature: [],
    status: 'unsearched',
    settle:
      'Without the bordism relation this is the universal property of spans with base change: look in R. Dawson, R. Paré and D. Pronk, « Universal properties of Span » (Theory Appl. Categ. 13, 2004), and in J. Bénabou (1967). The candidate is only that homotopy invariance and transverse base change force bordant correspondences to act alike. Look in D. Quillen, « Elementary proofs of some results of cobordism theory using Steenrod operations » (Adv. Math. 7, 1971), § 1; W. Fulton and R. MacPherson, Categorical Framework for the Study of Singular Spaces (Mem. Amer. Math. Soc. 243, 1981), on the universal bivariant theory; S. Yokura, « Oriented bivariant theories, I » (Internat. J. Math. 20, 2009); H. Emerson and R. Meyer, « Bivariant K-theory via correspondences » (Adv. Math. 225, 2010); and M. Levine and F. Morel, Algebraic Cobordism (2007), chapter 2. All are cited from memory. If any of them states this universal property of the bordism correspondence category, mark matched. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '162-5-photocopy-taken-after-ink',
    cote: '162-5',
    pages: '2–17, 32–41, 43–48',
    kind: 'codicological',
    claim:
      'The folder’s two copies of the typescript « Tapis de Quillen » are one typed top copy in two states: pages 32–41 and 43–48 are the top copy with its handwritten layer, and pages 2–17 a black photocopy of it taken after that layer was written, which then received about a dozen marks of its own. Folder 111, a third reproduction of the typescript, carries the same marks in the same strokes.',
    basis:
      'Batch 1’s header, as revised against the annotated copy, records the same line breaks and typewriter x-outs, the right edge clipped on most leaves of the photocopy, and the annotated copy’s handwriting reproduced on it: the date, the framed note of p. 8, the margins of pp. 9, 11 and 17, the insertions of pp. 12–17. It lists the marks only the photocopy carries: « Si ! » (p. 4), « t une » and « cond. » (p. 9), « (compactes ?) » (p. 12), « NB H*(X) » and « i.e. l’enveloppe “karoubienne” » (p. 14), « = karoubienne + additive », « en » and two Λ in blanks (p. 15), « él. des » (p. 16), the struck t of « Quillent » and « cf exposé Karoubi à Bourbaki ! » (p. 17). Its note on each says the annotated copy does not carry it. Folder 111’s revised header describes its own handwritten layer as the annotated copy’s ink photocopied plus these marks, with the same breaks, slant and wavy underline, and records text at the right edge (pp. 7, 13) that the photocopy of 162-5 has lost.',
    ours:
      'The relation between the witnesses is the transcriptions’, set out in the revised headers of 162-5 batch 1 and of 111, and the reading adopts it. Batch 3’s header, written before those revisions, calls 111’s notes « pencil notes » and says the two handwritten layers differ; 111’s revised header says the pencil is not supported, and the entry follows the revision. The reading counts five notes proper to the photocopy; batch 1 lists more, and the entry follows batch 1. The transcriptions do not say whether the marks proper to the photocopy were written on it or on an intermediate from which both it and 111 were taken. No facsimile was consulted.',
    literature: [
      'Transcription 162-5, batch 1 (batch-01.fr.tex), header and the notes to pages 4, 9 and 12–17',
      'Transcription 162-5, batches 2 and 3 (batch-02.fr.tex, batch-03.fr.tex), headers',
      'Transcription 111, batch 1 (batch-01.fr.tex), header, « Relation to folder 162-5 »',
      'Modernised reading 162-5 (162-5.modern.tex), header, « Les deux exemplaires du tapuscrit » and « La photocopie et ses notes propres »',
    ],
    status: 'candidate',
    settle:
      'A person lays the three witnesses side by side on the facsimiles and checks whether the marks proper to the photocopy are ink on its paper or part of the photocopied image. If they are ink on it, 111 was taken from the photocopy before its right edge was lost; if they are image on both, the photocopy and 111 descend from a lost annotated intermediate.',
  },
  {
    id: '162-5-karoubi-note-later-than-typescript',
    cote: '162-5',
    pages: '17',
    kind: 'codicological',
    claim:
      'If the note « cf exposé Karoubi à Bourbaki ! » at the foot of page 17, proper to the photocopy, points to M. Karoubi’s Bourbaki exposé « Cobordisme et groupes formels (d’après D. Quillen et T. tom Dieck) » of 1971–1972, it is later than that exposé and so later than the « notes du 10.9.68 » it annotates; nothing in the folder says whether the other marks proper to the photocopy were written with it.',
    basis:
      'Batch 1 transcribes the note, underlined, at the foot of page 17, and says the annotated copy does not carry it; folder 111 carries it at the foot of its page 16. The note gives no year, no title and no number. The questions of page 45 on the lift H^•(X) → B_•(X) and on its compatibility with products and Gysin maps concern the subject of that exposé, as the reading notes. Neither batch 1 nor 111 says that the marks proper to the photocopy share one ink or one campaign.',
    ours:
      'The identification with the exposé of 1971–1972 is the reading’s, which gives it as « selon toute vraisemblance » and as « une inférence, non une date lue ». The reading draws from it that the notes proper to the photocopy are all later than the exposé; the entry narrows that to this note. The title, number and date of the exposé are cited from memory. No facsimile was consulted.',
    literature: [
      'Transcription 162-5, batch 1 (batch-01.fr.tex), header and page 17',
      'Transcription 111, batch 1 (batch-01.fr.tex), header and page 16',
      'Modernised reading 162-5 (162-5.modern.tex), « La photocopie et ses notes propres » and the footnote on Quillen’s 1969 note in section III',
    ],
    status: 'candidate',
    settle:
      'A person checks the list of Karoubi’s exposés at the Séminaire Bourbaki (the one on Quillen and tom Dieck is, from memory, no. 408, February 1972) for any other the note could mean, and compares on the facsimile the ink and hand of the note with the other marks proper to the photocopy. If they are one campaign, that whole layer is bounded below by the exposé; the inventory’s « 1968-[à partir de 1970] » and its « copies de tapuscrits (1968, s.d.) » already leave room for that. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '162-5-annotated-copy-ink-undated',
    cote: '162-5',
    pages: '32, 39, 41, 45–46, 48',
    kind: 'codicological',
    claim:
      'Nothing in the folder dates the handwritten layer of the annotated copy. It is not one campaign, since the answer on page 39 is in another ink, and the one date on the typescript, « notes du 10.9.68 », names the notes. The margins that turn two typed results into questions (p. 45) and those that answer typed questions (pp. 39, 41, 46, 48) are therefore bounded below by the typing, and above only by the photocopy of pages 2–17 that reproduces them, which is itself undated.',
    basis:
      'Batch 2 gives « notes du 10.9.68 » as a margin at the head of page 32, and notes on page 39 that the answer « non, on a un foncteur pl. fidèle (?) mais pas ess. surjectif » is « d’une autre encre ». Batch 3 gives, on page 45, « il est douteux qu’il soit » over « compatible avec multiplication » and « [Quillen ignore si » over a struck « Le », which turn the typed a) and b) from results into a doubt and a question; on page 41, « oui » against the question whether Quillen has a more direct simplicial definition of the K_i; on page 46, the struck question on the noetherianity of Λ answered by « qui est abélienne bien que Λ ne soit pas noethérien … »; on page 48, « oui, car son anneau affine … » against « d’après Quillen, il serait pro-unipotent ». None carries a date. Batch 1 finds each of them reproduced on the photocopy.',
    ours:
      'The reading’s footnote on page 45 says the two questions are those Quillen’s 1969 note on the formal group laws of cobordism would settle, and that « ces notes du 10 septembre 1968 ne pouvaient pas le savoir »; its résumé reads the margins as « une conversation mathématique en train de se faire ». Both take the ink to be of the typescript’s date, and the entry adopts neither. The reading’s footnote on the « oui » of page 41, « la marge n’est pas datée », is the limit of what the folder supports. Batch 2’s header says the date is in his hand; batch 3 and the reading attribute no hand, and the entry attributes none. No facsimile was consulted.',
    literature: [
      'Transcription 162-5, batch 2 (batch-02.fr.tex), header and pages 32 and 39',
      'Transcription 162-5, batch 3 (batch-03.fr.tex), header and pages 41, 45, 46 and 48',
      'Transcription 162-5, batch 1 (batch-01.fr.tex), header',
      'Modernised reading 162-5 (162-5.modern.tex), résumé and the footnotes to part III on the relèvement and to part II on the « oui »',
    ],
    status: 'candidate',
    settle:
      'Only physical evidence would narrow it: how many inks the annotated copy carries, and which margins share the ink of the date on page 32, checked on the facsimile. A comparison of the answers with Quillen’s « On the formal group laws of unoriented and complex cobordism theory » (Bull. Amer. Math. Soc. 75, 1969), cited from memory, would show a shared subject, not an order. This entry exists to stop the next reader taking the typescript’s date as the date of its margins. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '10-hodgian-polarisations-torsor',
    cote: '10',
    pages: '11–16',
    kind: 'mathematical',
    claim:
      'For a real algebraic group G with homomorphisms 𝔾_m → G → 𝔾_m (i, then ε), η = i(−1) and G′ = Ker ε, the folder shows that two elements C, C′ of G′(ℝ) with C² = C′² = η that both define polarisations of Rep(G) are, after conjugation by G′(ℝ)°, related by C′ = zC with z central of order dividing 2, and that z ≠ 1 gives a different polarisation, so that the polarisations definable by such a C (« hodgiennes ») form a torsor under a 2-torsion group of central elements; and that on any graded ⊗-category over K ⊂ ℝ the ⊗-automorphisms z of the identity with z² = 1 acting trivially on K(1) act freely on the set of polarisations.',
    basis:
      'Page 11 defines C-polarisations (φ(x, Cy) symmetric positive definite) and proves they are Weil forms; page 12 shows they form a polarisation when ε(C) = 1; page 13 proves the centraliser of C in G′(ℝ) is a maximal compact subgroup; page 15 argues that C and C′ can be conjugated so that gCg⁻¹C′⁻¹ lies in the centre, that z² = 1, and that for z ≠ 1 a representation where z acts by −id gives φ^{C′} = −φ^C, « absurde », and concludes « forme un torseur sous ₂Z(ℝ) »; page 16 proves u^{*(φ^z, ψ^z)} = u^{*(φ,ψ)} for z in ₂Aut_⊗(id) and concludes that ₂Z′(ℝ) « opère librement sur Pol(ℳ) », then asks whether Pol(ℳ) is a pseudo-torsor under ₂Z(ℝ). The conjugacy step of page 15 is three abbreviated lines with four illegible words and « des groupes compacts maximaux » uncertain; the representation where z acts by −id is qualified « fidèle », an uncertain word; the freeness on page 16 rests on « ne peut », uncertain, followed by an illegible word.',
    ours:
      'The page moves between ₂Z′(K), ₂Z′(ℝ) and ₂Z(ℝ) (Z the centre of G, Z′ that of G′); for zP to be defined z must commute with G, and for the Tate object to be respected it must lie in G′, so this pass takes the acting group to be the 2-torsion of Z ∩ G′ — that reading is the edition’s, made for this entry. The reading says « torseur sous la 2-torsion de Z(ℝ) » on page 15 and « la 2-torsion de ce groupe opère librement » on page 16, following the page; this pass reads the page differently on this point and says so here. The reading drops « fidèle » from page 15, rightly: a faithful representation need not have z acting by −id, and what the argument needs is an irreducible one on which the central z acts by −1. The maximality of the centraliser (page 13), which the transitivity uses, is reconstructed by the reading from a page with long cancelled passages. The open question of page 16 is not part of the claim. Written on Opus 5.5 against a reading made on Opus 5.',
    literature: [],
    status: 'unsearched',
    settle:
      'The link between a polarisation of Rep(G) and a Cartan involution given by C is expected to be in the books, and the reading footnotes it; the question is only the torsor statement and the free action. Look in N. Saavedra Rivano, Catégories tannakiennes (LNM 265, 1972), chapters V–VI on polarisations; in P. Deligne and J. S. Milne, « Tannakian categories » (LNM 900, 1982), § 5, on polarisations of Rep(G) attached to an element C with C² central; and in P. Deligne, « La conjecture de Weil pour les surfaces K3 » (Invent. Math. 15, 1972), § 2, on Weil forms. All are cited from memory. If any of them says how the polarisation depends on C, up to conjugation and central elements of order 2, mark matched. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '10-numerical-character-rank-one-torus',
    cote: '10',
    pages: '62–65',
    kind: 'mathematical',
    claim:
      'A tannakian category over a field k whose band is a one-dimensional torus is determined up to equivalence by its « numerical characters » — the set Σ of classes of simple objects, the structure constants of K(𝓜), the pairs (Z_σ, ξ_σ ∈ Br(Z_σ)) of centres and Brauer classes of the endomorphism algebras, and the rank — because for the norm-one torus G of a quadratic extension Z/k the map H²(k, G) → H²(k, R_{Z/k}𝔾_m) = Br(Z) is injective.',
    basis:
      'Pages 62–63 define the four numerical characters and warn that they do not in general determine the category, even for representations of a finite group; pages 64–65 treat a band G of multiplicative type, recover G = D(Γ) from the numerical data, write u_σ : G → Z_σ* ≃ ∏_{Z_σ/k} 𝔾_m with u_σ(ξ) = ξ_σ, and reduce the question to whether the class ξ ∈ H²(k, G) of the tannakian gerbe is known from the u_σ(ξ); « C’est le cas pour G diagonalisable (pro-dénombrable ?) ». Exemple 1 takes G a one-dimensional torus, split by a quadratic Z, writes 0 → G → Z* → 𝔾_m → 0 with the norm, and concludes by Hilbert 90 that Ker(H²(k, G) → H²(k, Z*)) is zero, « Donc dans le cas envisagé, le caractère numérique détermine 𝓜 à équivalence près ». Exemple 2 is cancelled and the typescript stops. The statements used carry no uncertain or illegible word.',
    ours:
      'The page asserts u_σ(ξ) = ξ_σ and the equivalence between the numerical character and the data (G, u_σ(ξ)) with « on vérifie aussitôt » and no argument. That the embedding G → Z* of Exemple 1 is one of the u_σ — the orbit {1, −1} of the character group ℤ, on which Galois acts by −1, with Z_σ = Z — is checked by this entry and not by the page. The reading’s example of the dihedral and quaternion groups of order 8, for the negative statement, is the edition’s and no part of the claim. The general question for bands of multiplicative type is left open by the page and is not part of the claim.',
    literature: [],
    status: 'unsearched',
    settle:
      'The injectivity itself is a one-line consequence of Hilbert 90; the question is whether the determination of a tannakian category, or a gerbe with abelian band, by these numerical data has been stated. Look in J. Giraud, Cohomologie non abélienne (1971), IV.3, on gerbes with abelian band; in Saavedra, Catégories tannakiennes (LNM 265, 1972), chapter III; in Deligne–Milne (LNM 900, 1982), § 3; for the general case, in J.-J. Sansuc, « Groupe de Brauer et arithmétique des groupes algébriques linéaires sur un corps de nombres » (J. reine angew. Math. 327, 1981), on H² of tori; and, for the finite-group side, in P. Etingof and S. Gelaki, « Isocategorical groups » (IMRN 2001). All are cited from memory. If the rank-one case, or a general criterion containing it, is there, mark matched. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '10-split-ring-ga-rtimes-gm',
    cote: '10',
    pages: '187–188, 191–197',
    kind: 'mathematical',
    claim:
      'Over a field of characteristic 0, for G = 𝔾_a ⋊ 𝔾_m with 𝔾_m acting by λ ↦ λ^p (p ≥ 1), the folder classifies the indecomposable rational representations as the e_{n,k} = σ_n ⊗ e_{0,k} (n ∈ ℤ, k ≥ 1), e_{0,k} being k[Z]/Z^k with the generator of Lie 𝔾_a acting by Z and weights 0, p, …, p(k−1), pairwise inequivalent, with dual e_{−n−p(k−1),k}; and shows that the ring of classes of representations with basis the indecomposables is the polynomial ring ℤ[ℤ][ξ] over the group ring of ℤ, ξ = e_{0,2}, with ξ̌ = σ_{−p}ξ.',
    basis:
      'Page 191 writes the Lie algebra relation [Y, X] = pX, decomposes V = ΣV_n under Y, and gets X_{ji} = 0 unless j − i = p; page 192 shows the non-zero V_n of an indecomposable are the V_{n+pk}, forms the chain u_i : E_i → E_{i+1} and states Lemme 1 (injective); page 193 proves it by splitting off Σ E″_j; page 194 concludes that the u_i are bijections and the E_i one-dimensional, and states the Proposition with e_{n,k} = σ_n ⊗ e_{0,k} and ě_{n,k} = e_{−n−p(k−1),k}. Pages 195–197 compare R(H) → R(G) → R(F), use R(F) = ℤ[e_2] from pages 187–188, show that ξ^n = Σ_{i ≤ n+1} c_{ni} e_{0i} with c_{n,n+1} = σ_α, and prove α = 0 by weights. The characteristic-0 hypothesis on page 191 stands among illegible words; the head of page 193 is cancelled; the proof of Lemme 2 is a line of illegible words; much of page 197’s argument is illegible, with « poids » uncertain.',
    ours:
      'p ≥ 1 is the edition’s; the page never states it, and for p = 0 the reduction « mod p » of page 192 has no sense. The reading supplies that V restricted to 𝔾_m is semisimple by case II, reconstructs the supplements of Lemme 1 from three successive states of which two are struck, and gives no argument for Lemme 2; the classification therefore rests partly on the edition. On page 197 the page writes « pα ≤ pn, d’où α ≤ 0 », and the reading repeated it (as written this gives α ≤ n) until its revision of 2026-09-23, which adopts α + pn ≤ pn. This pass reads the inequality as α + pn ≤ pn — the highest weight of e_{α,n+1} against n times the highest weight p of ξ — which page 196 writes as « α + pn »; and it reads the page’s « c_{p,p+1} » and « e_{0,p+1} », where p is the weight, as c_{n,n+1} and e_{0,n+1}. On both points this pass read the folder differently from the reading as it then stood. Written on Opus 5.5 against a reading made on Opus 5.',
    literature: [],
    status: 'unsearched',
    settle:
      'The one-variable case R(𝔾_a) = ℤ[ξ], the Clebsch–Gordan rule for nilpotent Jordan blocks, is expected to be classical, and the reading footnotes it; the question is the semi-direct product. Rep(G) is the category of finite-dimensional ℤ-graded k[X]-modules with X of degree p acting nilpotently, and for p = 2 (resp. p = 1) G is a Borel subgroup of SL₂ (resp. PGL₂). Look for the decomposition of tensor products of graded Jordan blocks and for the split Grothendieck (Green) ring of graded k[X]-modules: A. Martsinkovsky and A. Vlassov, « The representation rings of k[x] » (from memory, c. 2004); J. C. Jantzen, Representations of Algebraic Groups, part II, on representations of B; and work on the Jordan type of tensor products in graded settings. All are cited from memory. If the ring ℤ[ℤ][ξ] or the list e_{n,k} with its tensor products is there, mark matched. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '10-sga3-typescript-cites-1966-67',
    cote: '10',
    pages: '32–57, 47, 110',
    kind: 'codicological',
    claim:
      'The typescript of pages 32–57, numbers 10 and 11 of an exposé of SGA 3, was not typed, at least on page 47, before a seminar of « 1966/67 » could be cited: its Remarque 11.10.1 sends the reader, in the typed layer, to « un exposé de Serre dans SGA (1966/67) », which a handwritten correction first completes as « SGA 6 » and then strikes, putting in its place J.-P. Serre, « Sur les Groupes de Grothendieck des schémas en groupes réductifs déployés », Pub. Math. n° [34], p. 37–52.',
    basis:
      'Batch 3 transcribes page 47 with « voir à ce sujet un exposé de Serre dans SGA (1966/67) » struck, « 6 » added after « SGA », and the Publ. Math. reference added; its header says both typescripts of the batch are corrected in his hand and that the Remarque replaces « a reference to a seminar by the Publ. Math. paper ». The number « 34 » is marked uncertain; the year 1966/67 is typed and not in doubt. The typescript refers throughout to other exposés of the same work (Exp. I 4.2, IV 4.4.3, VI_A 2.1.1, VIII 5.5) and to its own §§ 1, 3, 6, 7 and 9. Page 110, in his hand, cites « SGAD VI_B 11.2 » for C(G) ≃ Ind C_f(G); in the typescript that statement is Corollaire 11.10, and 11.2 is the compatibility of X ⇝ Spec 𝒜(X) with finite products.',
    ours:
      'That the typescript is Exposé VI_B of SGA 3 is inferred from its internal references and from page 110, and the identification of the published text is from memory; the transcriptions and the reading say « SGA 3, n° 10 et 11 ». That Serre’s article appeared in Publ. Math. IHÉS 34 in 1968 is from memory, unchecked. The bound is on the typing of page 47 and on its correction, not on the other leaves of the typescript, and not on the mathematics. The mismatch between page 110’s « 11.2 » and the typescript’s numbering is recorded, not explained: it may be a slip, or a numbering other than that of the leaves filed here. The inventory’s « [à partir de 1958] » for the shelfmark is not contradicted. No facsimile was consulted.',
    literature: [
      'Transcription 10, batch 2 (batch-02.fr.tex), header and pages 32–40',
      'Transcription 10, batch 3 (batch-03.fr.tex), header and pages 41–57, in particular page 47',
      'Transcription 10, batch 6 (batch-06.fr.tex), page 110',
      'Modernised reading 10 (10.modern.tex), « Deux numéros de SGA 3 » and its footnote on Remarque 11.10.1',
    ],
    status: 'candidate',
    settle:
      'A person reads on the facsimile the number of the Publ. Math. volume and checks whether « 6 » and the replacement are in the same ink as the other corrections of the typescript; then compares the leaves with SGA 3, Exposé VI_B (LNM 151, 1970), §§ 10–11, including what its 11.2 and 11.10 say and whether Remarque 11.10.1 there cites Serre’s article. The contents of SGA 6 decide whether an exposé of Serre was ever part of it. None of this dates the mathematics; priority is not a claim this project makes, about anyone.',
  },
  {
    id: '10-polarisation-leaves-undated-against-p108',
    cote: '10',
    pages: '3–30, 101–108',
    kind: 'codicological',
    claim:
      'Nothing in the folder dates the handwritten axiomatics of polarisations (pages 3–16) or the « Notes anciennes » (pages 18–30) relative to the typed programme of page 108 — « Il y a lieu de faire une étude axiomatique abstraite d’une telle notion de polarisation […] On pourra en rediscuter à l’occasion » — or to the work of Saavedra, to whom the typescript of pages 101–108 is addressed: no leaf carries a date, and « anciennes » is his heading, older than nothing it names.',
    basis:
      'Batch 1 describes pages 3–16 as one blue-ink draft under the cover « Polarisations sur les ⊗-catégories graduées », numbered by him 1) to 19), and pages 18 and 20 as black ink on yellowed paper headed « Notes anciennes » in his hand; batch 2 continues these at pages 22–30; neither records a date. Batch 6 transcribes page 107 (« Je laisse le soin à Saavedra de déterminer … ») and page 108, item 6), which calls for the axiomatic study; batch 5 gives the cover « Notes Saavedra » of page 99. All batches copy the inventory’s « [à partir de 1958] » for the whole shelfmark.',
    ours:
      'The reading said of page 108 « Cette étude axiomatique est faite : ce sont les pages 3 à 16 » and that it « explique pourquoi les trente premiers feuillets du dossier existent », and described pages 18–30 as written « d’une encre et d’un papier plus anciens » — all three rephrased in its revision of 2026-09-23, after this entry; batch 1’s header calls them « a second, older run » with « une notation plus ancienne ». These take the subject, the heading and the yellowing of the paper for an order; the entry adopts none of them. The typed « il y a lieu de faire » fits a study not yet written and a study already sketched and proposed to someone else equally. That Saavedra’s thesis has chapters on polarisations and filtrations is from memory and no part of the claim. No facsimile was consulted.',
    literature: [
      'Transcription 10, batch 1 (batch-01.fr.tex), header and pages 3–20',
      'Transcription 10, batch 2 (batch-02.fr.tex), header and pages 22–30',
      'Transcription 10, batch 5 (batch-05.fr.tex), header and page 99',
      'Transcription 10, batch 6 (batch-06.fr.tex), header and pages 101–108',
      'Modernised reading 10 (10.modern.tex), « Les stations » and « 6) La polarisation, renvoyée »',
    ],
    status: 'candidate',
    settle:
      'Only physical evidence would narrow it: the paper and ink of pages 3–16 against those of pages 18–30 and of the typescript of pages 101–108. A comparison of pages 3–16 — Weil forms, compatibility, prepolarisation, C-polarisation, « hodgien » — with N. Saavedra Rivano, Catégories tannakiennes (LNM 265, 1972), chapters V–VI, cited from memory, would show a shared subject, not an order. This entry exists to stop the next reader taking page 108 as the occasion of pages 3–16, or those pages as written before or after Saavedra’s account. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '10-cover-140-and-dictionary-order',
    cote: '10',
    pages: '117–136, 140, 142–179',
    kind: 'codicological',
    claim:
      'The cover of page 140 names the two handwritten runs bound after it in the reverse of their binding order — its first line, « Structures supplémentaires sur des vectoriels, et algèbres de Hopf top. », fits pages 156–179, and its second, « Anneaux des représentations de certains groupes algébriques », pages 142–154 — and nothing in the folder dates the run of pages 156–179 relative to the typescript « ⊗-catégories » of pages 117–136.',
    basis:
      'Batch 7 transcribes the brown cover of page 140 with a struck first line beginning « Fasc… », then the two titles, « top. » uncertain; batch 8’s header says the batch opens the run announced by the cover’s second line. Pages 156–160 build the complete linearly topologised algebra U of an abelian class of k-modules, with « Première structure supplémentaire » (p. 158) and « Autres structures supplémentaires » (p. 160); pages 161–179 add duality, a diagonal U → U ⊗̂ U, an augmentation and an involution, and end on « K-catégorie ⟺ K-bigèbre U ⟺ hyperalgèbre commutative A ». No leaf of pages 117–179 is dated; page 136 of the typescript refers to « mes notes sur les ⊗-catégories » without saying which.',
    ours:
      'That the first line names pages 156–179 is the edition’s, made for this entry from the vocabulary of those pages; neither transcription assigns it, and batch 7’s header speaks of the cover as naming « the run that begins after this batch ». The reading does not mention the cover. It called pages 156–179 « le dictionnaire refait à la main », « la seconde construction du dictionnaire, faite de rien », « en repartant de zéro » (rephrased in its revision of 2026-09-23, after this entry), and the typed pages the « dictionnaire énoncé » of which these are the « démontré »; that is an order of the binding and of the argument, which the reading also says are « indépendamment » established, and the entry adopts it as neither. Which notes page 136 means is not said, and the entry does not guess. No facsimile was consulted.',
    literature: [
      'Transcription 10, batch 7 (batch-07.fr.tex), header and pages 136 and 140',
      'Transcription 10, batch 8 (batch-08.fr.tex), header and pages 142–160',
      'Transcription 10, batch 9 (batch-09.fr.tex), header and pages 161–179',
      'Modernised reading 10 (10.modern.tex), « Le dictionnaire, construit deux fois » and « Le dictionnaire, à la main » (titled « Le dictionnaire refait à la main » before 2026-09-23)',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile whether the cover of page 140 physically wraps pages 142–179, reads « top. » and the struck line, and compares the paper and ink of pages 156–179 with those of pages 142–154 and with the typescript of pages 117–136. A shared wrapper would make the reversed order one of filing, not of the titles; nothing of this would order the handwritten run and the typescript in time.',
  },
  {
    id: '104-pinned-posets-nonsingular-presheaves',
    cote: '104',
    pages: '12–16',
    kind: 'mathematical',
    claim:
      'For a category M whose arrows are all monomorphisms and whose endomorphisms are all identities, the folder asserts that the presheaves on M which are unions of their subobjects isomorphic to objects of M are equivalent to « M-pinned » posets — a poset K with a strictly increasing type map τ_K to the poset of isomorphism classes and, for each ξ ∈ K of type n, an isomorphism u_ξ : I_n ≅ K_{≤ξ} from the poset of subobjects of the model, subject to τ_K ∘ u_ξ = τ_n and u_ξ ∘ u_y = u_{u_ξ(y)} — morphisms of presheaves corresponding to the type-preserving strictly increasing maps compatible with the pinnings and monomorphisms to the injective ones, and that this class is stable under sums and under amalgamated sums along monomorphisms, with X ↦ X̃ commuting to both.',
    basis:
      'Page 12 defines the subcategory 𝔹₀ of M̂ by two conditions and the pinning a), b) of the poset K = X̃ of model subobjects; page 13 writes the axioms (1) and (2), asserts that the category of admissible objects « est équivalente à » that of M-pinned posets, and describes the maps f : K → L by τ_L ∘ f = τ_K and a commutative triangle; page 14 treats injective f, closed subsets and the induced pinning; page 15 gives the gluing condition for pinnings given on the maximal elements; page 16 states the stability under sums and amalgamated sums, « de façon évidente », and the N.B. on objects of finite type. No proof is written. On page 13 the word just before « celle des ens. ordonnés M-épinglés » is illegible, « homs. » in « les flèches les homs. entre eux » is uncertain, and the sentence introducing the maps f reads « les objets quelconques de M̂ et leurs » followed by an illegible word, « se reconstituent également, ce sont les applications strictement croissantes », the last three words uncertain.',
    ours:
      'The reading renders that sentence as the description of the morphisms between admissible objects, which the page does not say in those words; it calls 𝔹₀ a full subcategory, and it sketches why the equivalence holds (every element of an admissible X is a monomorphism, and X is the colimit of its model subobjects indexed by K); the proof is not on the page. This pass reads the folder differently from the reading on one point and says so: the first condition of page 12 holds exactly when every element D_n → X is a monomorphism, the second then follows from (i) alone — a subpresheaf of a representable is a union of representables, as the reading itself notes for page 16 but not for page 12 — and K with its type map and pinning is then the category of elements of X, which (i) and (ii) make a poset. The asserted equivalence would then be the restriction of the classical equivalence between presheaves on M and discrete fibrations over M to the presheaves whose category of elements is a poset; the reading names face posets, CW posets and regular CW complexes but not this match. Written on Opus 5.5 against a reading made on Opus 5.',
    literature: [
      'D.-C. Cisinski, Les préfaisceaux comme modèles des types d’homotopie, Astérisque 308 (2006), chapter 8, §8.1 (catégories squelettiques, 8.1.1–8.1.37) and §8.2 (8.2.1–8.2.6, préfaisceaux réguliers) — read 2026-09-26',
    ],
    status: 'unsearched',
    settle:
      'First check that the M-pinned poset of X is its category of elements; if so, the general statement is the correspondence between presheaves and categories fibred in sets of SGA 1, exposé VI, restricted, and the entry should be marked matched with that reference. What would remain is only the order-theoretic form of the three cases of page 10 — non-singular semi-simplicial, semi-cubical and globular sets described by posets with pinnings. Look in A. Björner, « Posets, regular CW complexes and Bruhat order » (Europ. J. Combin. 5, 1984); R. P. Stanley, « f-vectors and h-vectors of simplicial posets » (J. Pure Appl. Algebra 71, 1991); F. Waldhausen, B. Jahren and J. Rognes, Spaces of PL Manifolds and Categories of Simple Maps (Annals of Math. Studies 186, 2013), on non-singular simplicial sets; and D.-C. Cisinski, Les préfaisceaux comme modèles des types d’homotopie (Astérisque 308, 2006), on skeletal categories. All are cited from memory. No web search was available for this pass (2026-09-23), so nothing has been read. On 2026-09-26 Cisinski’s chapter 8 was read. Its 8.2.1 defines a regular presheaf on a skeletal category as one whose non-degenerate sections are all monomorphisms, and 8.2.2 (iii) makes representables regular exactly when the arrows of A₊ are monomorphisms; when every arrow of M is a monomorphism, as here, every section is non-degenerate and « regular » is exactly the first condition of page 12. 8.2.6 then makes A/X a regular skeletal category. Nothing there describes A/X as a poset, or regular presheaves by posets with pinnings; the pinned-poset equivalence was not found. The status stays unsearched rather than candidate because the check the entry puts first — the category of elements and SGA 1 VI — has still not been made, and because the description of morphisms rests on words the transcription marks \\uncertain{}. Toën’s texts (Homotopical algebraic geometry I, II; Champs affines; Vers une axiomatisation de la théorie des catégories supérieures; the survey « Derived algebraic geometry ») were searched on 2026-09-26 for this vocabulary and do not bear on this row.',
  },
  {
    id: '104-trial-sheets-undated-against-fair-copy',
    cote: '104',
    pages: '1–5, 6–16',
    kind: 'codicological',
    claim:
      'Nothing in the folder dates the five trial sheets of pages 1–5 relative to the fair copy of pages 6–16: their place before it, and the reading of page 5 as a first state of pages 6–9, are orders of the binding and of the argument; the one physical fact recorded that bears on page 5 is that it is written on the back of a page of an English typescript which already sets B = (Gr-stacks) and calls B(0) the full subcategory of the base objects D_n, n ∈ N.',
    basis:
      'The transcription records pages 1–5 as five loose sheets written across the leaf on paper at hand — page 2 the back of an envelope addressed to him, pages 3 and 5 the backs of typed pages — and pages 6–16 as ink in portrait under his pagination 1 to 6. No leaf carries a date, and no postmark is recorded for the envelope. Its note on page 5 says the typed side sets B = (Gr-stacks), says that inductive limits there are computed componentwise, and calls B(0) the full subcategory of the base objects D_n, n ∈ N, all underlined. Page 5 names the poset of classes I and leaves the cube count as 1 + n·2 + … + 2ⁿ = (1 + 2)ⁿ; pages 6–10 name it with the barred N and write Card I_n = 3ⁿ. Neither run refers to the other.',
    ours:
      'The transcription’s header calls pages 1–5 « the same construction seen earlier and from further off », page 5 « the draft of pages 6 to 9 », and its cube count one « that page 10’s margin will reduce to Card I_n = 3^n »; the reading calls page 5 « le premier état des pages 6 à 9 » and repeats « que la page 10 réduira ». These take a change of notation and an unsimplified sum for an order of writing; the entry adopts neither. The reading compares « Gr-stacks » with Pursuing Stacks, « rédigé en anglais en 1983 », and says this is « un rapprochement et non une datation »; the entry leaves it there. Whether the typed side of page 5 was typed before the leaf was written on is not recorded; if it was, as with reused paper, the notes of page 5 are not earlier than that typed page. The transcription’s note says the typed page « nomme les D̃_n » while transcribing its objects as D_n underlined; the entry claims only the latter. The quoted wording of the transcription header and of the reading was rephrased in their revision of 2026-09-23, after this entry, and the page 5 note now says the typed page names the D_n, the D̃_n being in his hand (checked on the facsimile then; not for this entry’s claim).',
    literature: [
      'Transcription 104, batch 1 (batch-01.fr.tex), header and pages 2, 3, 5 and 6',
      'Modernised reading 104 (104.modern.tex), header and « Feuillets d’essai (pages 1 à 5) », page 5 and its footnote',
    ],
    status: 'candidate',
    settle:
      'A person checks the envelope of page 2 for a postmark, reads the typed sides of pages 3 and 5 in full, and looks for the page behind page 5 in the typescript of Pursuing Stacks. A match would bound the handwriting of page 5 below by that typed page, if the typing came first, and would say nothing about pages 6–16. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '106-section-criterion-span-faithfulness',
    cote: '106',
    pages: '9–15',
    kind: 'mathematical',
    claim:
      'For a category with weak equivalences W and cofibrations satisfying Baues’s axioms C1–C3 in which every object is cofibrant, the folder asserts that the functor to W⁻¹C from the category whose arrows x → y are the connected components of the category of spans x → ỹ ← y, the first arrow a cofibration and the second in W, is faithful — hence an isomorphism — if and only if, for every f : x → y in W with two sections i and i′, the spans (1_x, i) and (1_x, i′) lie in the same component.',
    basis:
      'Page 9 defines q : C̃ → W⁻¹C, (f, i) ↦ [i]⁻¹[f], and proves it bijective on objects and full for page 5’s spans, whose backward arrow is in cof ∩ W; page 11 says its faithfulness « n’est pas clair », doubts that inverting W ∩ cof suffices, and moves the cofibration condition to the numerator (f ∈ cof, i ∈ W); page 13 factors a map as a cofibration followed by a weak equivalence with a section; page 15, with the pushout squares in the margin of page 14, compares two factorisations through a third, states (**), and closes « Cette condition est (nec. et) suffis. pour que C̃ → W⁻¹C soit fidèle (donc un iso) ». No proof of sufficiency is written. Page 13 is almost wholly illegible and its marginal note is not restored; the reduction on page 15 that leads to (**) stands among illegible words; « deux i, i′ ∈ W » in (**) is an interlinear addition.',
    ours:
      'The reading reconstructs page 13’s construction « dans la forme que les pages 14 et 15 permettent de reconstituer », supplies the necessity argument (f i = 1_y gives q′(1_x, i) = [f] = q′(1_x, i′)) and the fullness of the rectified functor, and renders the page’s « [f_0, i] = [id_ȳ, i] ∘ (f, id_ȳ) » as (f_0, i) = (id_ȳ, i) ∘ (f_0, id_ȳ) without a footnote. The composition of the rectified spans is written neither on the page nor in the reading; it needs the pushout of a weak equivalence along a cofibration to be one. This pass reads the literature differently from the reading on one point and says so: the reading’s last footnote says the literature describes these arrows by fractions « à homotopie près, et non à composante connexe près d’une catégorie de diagrammes », « à notre connaissance »; from memory, the homotopy calculus of fractions of W. G. Dwyer and D. M. Kan and M. Weiss’s hammock localisation in Waldhausen categories describe the hom-spaces of the localisation by nerves of categories of such spans, whose π₀ would then be the hom-sets of W⁻¹C — in Weiss, under cylinder hypotheses and perhaps with the backward arrow a trivial cofibration, as in page 5’s first definition, the one page 11 abandons. If so, faithfulness is matched for that variant, and what remains is the criterion (**) and the rectified variant. Whether (**) holds under C1–C3 is not decided here. Written on Opus 5.5 against a reading made on Opus 5. The reading was revised on 2026-09-23 after this entry: the page 15 factor is now footnoted, its last footnote no longer says the literature does not use π₀ of span categories and names Dwyer–Kan and Weiss itself (cited from memory), and its Baues footnote now states the pushout clause the composition of rectified spans needs; the disagreements recorded above are therefore with the reading as it then stood.',
    literature: [
      'D.-C. Cisinski, Catégories dérivables, Bull. SMF 138 (2010), 317–393 — §1 (1.1, 1.4–1.8) and §3 (3.1–3.13), read 2026-09-26',
      'A. Rădulescu-Banu, Cofibrations in Homotopy Theory (arXiv math/0610009), §6.4 — Theorems 6.4.1, 6.4.4 and 6.4.5; read 2026-09-26',
      'B. Toën and G. Vezzosi, Homotopical algebraic geometry I: topos theory (arXiv math/0207028), §2.1–2.2 (simplicial localisation); read 2026-09-26, does not bear',
    ],
    status: 'candidate',
    settle:
      'Checked on 2026-09-26; not found in the three sources read. Rădulescu-Banu 6.4.4 (Brown’s homotopy calculus of fractions, in a precofibration category with A, B cofibrant) writes every arrow of Ho(A, B) as a left fraction s⁻¹f, s ∈ W, and identifies two fractions when there are weak equivalences s′, t′ with s′s ≃ t′t and s′f ≃ t′g — homotopy, not strict commutation; 6.4.5 is the variant with f and f + s cofibrations and s a trivial cofibration (page 5’s first definition), with s′s = t′t but still s′f ≃ t′g. Neither is π₀ of a category of spans, and neither says when strict components suffice, which is what (**) decides. Cisinski 2010 is the dual (fibrant) setting: 1.6 records that Ho A_f is obtained from π A_f by a calculus of right fractions up to homotopy and that π A_f → Ho A_f is faithful (citing Brown, I.2, theorem 1), and §3 is about the functoriality and the approximation property (3.9–3.12), not about hom-sets as components. Toën–Vezzosi 2.2 recalls only that Ho L(C, S) is the Gabriel–Zisman localisation S⁻¹C; it does not bear. The original instructions stand for what was not read: if a source proves, under C1–C3 or for cofibration categories with every object cofibrant, that W⁻¹C(x, y) is π₀ of the category of spans x → ỹ ← y with f ∈ cof and i ∈ W, then (**) follows by the necessity argument and the entry is matched. Look in W. G. Dwyer and D. M. Kan, « Calculating simplicial localizations » (J. Pure Appl. Algebra 18, 1980), on homotopy calculi of fractions; M. Weiss, « Hammock localization in Waldhausen categories » (J. Pure Appl. Algebra 138, 1999); D.-C. Cisinski, « Catégories dérivables » (Bull. SMF 138, 2010), § 3; A. Rădulescu-Banu, Cofibrations in Homotopy Theory (arXiv, 2006), chapter 6; K. S. Brown, « Abstract homotopy theory and generalized sheaf cohomology » (Trans. AMS 186, 1973); and H.-J. Baues, Algebraic Homotopy (1989), chapter II. All are cited from memory. If only the trivial-cofibration variant is there, the criterion (**) and the rectified variant stay unsearched. No web search was available for this pass (2026-09-23), so nothing has been read. Of that list, Dwyer–Kan, Weiss, Brown and Baues remain unread after 2026-09-26; Weiss’s hammocks are still the likeliest place for the π₀ description.',
  },
  {
    id: '106-listing-dates-not-notebook',
    cote: '106',
    pages: '1–16',
    kind: 'codicological',
    claim:
      'The machine dates « 24 AUG 82 » and « 25 AUG 82 » printed on the listing sheets of pages 12 and 14 bound below only his handwriting on those two sheets; nothing in the folder dates the eight notebook leaves (pages 1, 3, …, 15, his 1 to 8), and nothing orders the pushout squares in the margin of page 14 relative to the diagram of page 15 that uses the same squares.',
    basis:
      'The transcription describes the folder as eight spiral-notebook leaves in ink, recto only, under his pagination 1) to 8), interleaved with sheets of a computer listing used as scrap; it records the machine date 24 AUG 82 on page 12, whose bottom margin carries two unlabelled trial figures of his, and 25 AUG 82 on page 14, whose right margin carries the three pushout squares; it records no date for the listing of page 2 and none on any notebook leaf. Page 15’s diagram, x ∨ x → ȳ ⊔ ȳ′ over ∇_x with the left square marked « cocart », shares the pattern of page 14’s squares; neither page refers to the other.',
    ours:
      'The transcription’s note on page 12 says the printed dates of pages 12 and 14 « datent le dossier », and its header calls page 14’s squares « the block of amalgamated-sum squares that page 15 uses »; the reading’s résumé says the notebook leaves were « écrits en août 1982 ou après », and its footnote calls page 14’s block « la préparation de ce diagramme ». These take the interleaving of the sheets and a shared diagram for a date and an order; the entry adopts neither. The interleaving may be his filing or the archive’s. The inventory’s « [à partir de 1982] » is not contradicted. The reading cites Baues’s axioms from Algebraic Homotopy (1989); that is its own reference, the leaves write only « C1 : C3 de Baues » and do not say which text of Baues he used, so it dates nothing either. No facsimile was consulted. Written on Opus 5.5 against a reading made on Opus 5. The four wordings quoted above (« datent le dossier », « that page 15 uses », « écrits en août 1982 ou après », « la préparation de ce diagramme ») were rephrased in the revision of the transcription and reading on 2026-09-23, after this entry.',
    literature: [
      'Transcription 106, batch 1 (batch-01.fr.tex), header and pages 2, 12, 14 and 15',
      'Modernised reading 106 (106.modern.tex), « Résumé », the footnote on Baues’s axioms in « Le fil du dossier, et les conventions », and the footnote on page 14’s block',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile whether the listing of page 2 carries a date, whether the notebook leaves show any physical tie to the listing sheets — ink offset, a shared fold, writing that runs from one onto the other — and compares the ink of page 14’s margin with that of page 15. A physical tie would bound the notebook leaves by the listing; a shared ink would suggest one sitting, not an order. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '11-simplicial-bivariant-poincare-equivalence',
    cote: '11',
    pages: '37, 41',
    kind: 'mathematical',
    claim:
      'The folder asserts, without proof, that evaluation at a one-element set is an equivalence between the simplicial bivariant algebras — contravariant functors from non-empty finite sets and all maps to the bivariant graded algebras of page 33 — whose value at a point is a Poincaré algebra, and the Poincaré algebras; and that A(·) ↦ (A(pt), Δ), with Δ = δ_*(1) of degree d(A), is fully faithful into gauged algebras equipped with such a Δ, the axioms on Δ left to be stated.',
    basis:
      'Page 37 defines the simplicial bivariant algebras (« pas ½ simpliciale ! »), calls them « spécial » when A(I′) ⊗ A(I″) → A(I′ ⊔ I″) is an isomorphism, and in the next sentence states the equivalence for those with A(Δ(0)) = A_0 Poincaré, the argument A(Δ(0)) reading poorly; page 41 adds (α ⊔ β)_* = α_* ⊗ β_* to « spécial », repeats the equivalence with its source struck and illegible, writes the functor (A(0), δ) with Δ ∈ [A ⊗ A]^{d(A)} in the target, and carries the margin « à vérifier ; il faut d’abord […] connaître δ_* : A → A ⊗ A ; en posant Δ = δ_*(1) » and « il convient de préciser les axiomes à mettre sur ce Δ ». Neither page names « spécial » in the sentence of the equivalence.',
    ours:
      'The reading restricts the equivalence to special objects, which the sentence on either page does not say — without it nothing ties A(I) for |I| ≥ 2 to A(pt) —, sketches why it is plausible (A(I) = A(pt)^{⊗I}, pull-backs by surjections as multiplications, push-forwards fixed by page 33), restricts the full faithfulness to special objects, and footnotes the axioms on Δ as the zigzag identities of a Frobenius algebra, citing Abrams (1996) on 2-dimensional TQFTs; it names no match for the equivalence itself. This pass reads the pages as close to a known correspondence and says so, from memory: a symmetric monoidal functor on finite sets carrying a pull-back and a push-forward with the projection formula makes A(pt) a commutative algebra with a coassociative comultiplication δ_* that is a bimodule map — once the gauge supplies a counit, a commutative Frobenius algebra in Abrams’s sense, where non-degeneracy is automatic; exchange for the square of two diagonals would force μ ∘ δ_* = id, the « special » Frobenius algebras that correspond to cospans of finite sets (Lack; Rosebrugh, Sabadini and Walters), whereas in cohomology μ ∘ δ_*(1) is the Euler class — which is why the page’s definition rightly asks for no exchange, as the reading notes. The page’s « spécial » (Künneth) is not the modern « special » (μ ∘ δ = id). Whether the page’s axioms supply that counit, and so whether the Poincaré hypothesis is redundant, is not decided here. Written on Opus 5.5 against a reading made on Opus 5. Since the revision of 2026-09-23 the reading cites « un théorème d’Abrams (référence citée de mémoire) », without a year, and footnotes « spéciales » as the edition’s, with a counterexample without it.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check whether the equivalence, for special objects, is stated or follows at once from the description of commutative Frobenius algebras by a Frobenius comultiplication: L. Abrams, « Two-dimensional topological quantum field theories and Frobenius algebras » (J. Knot Theory Ramifications 5, 1996) and « Modules, comodules, and cotensor products over Frobenius algebras » (J. Algebra 219, 1999); J. Kock, Frobenius Algebras and 2D Topological Quantum Field Theories (LMS Student Texts 59, 2004), chapters 2–3; A. Carboni and R. F. C. Walters, « Cartesian bicategories I » (J. Pure Appl. Algebra 49, 1987); S. Lack, « Composing PROPs » (Theory Appl. Categ. 13, 2004); R. Rosebrugh, N. Sabadini and R. F. C. Walters, « Generic commutative separable algebras and cospans of graphs » (Theory Appl. Categ. 15, 2005). If it is there in substance for graded commutative Frobenius algebras, mark matched and keep the note on the two meanings of « special ». All are cited from memory. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '11-tautological-diagonal-product-rule',
    cote: '11',
    pages: '50–56',
    kind: 'mathematical',
    claim:
      'For X whose point class y has y² = 0 in degree n, with Euler characteristic χ, the folder computes the subalgebra of H*(X^k) generated by the classes y_i and the partial diagonals — relations for k = 2, 3 including δ² = χ y₁y₂ on X², and δ² = 0 and δ₁₂δ = χ y₁y₂y₃ for the small diagonal δ of X³ —, indexes spanning classes by pairs (R, J) of a partition and a pointed block, proves s + s′ ≤ k + 1 for two polydiagonals of s and s′ blocks meeting in the small diagonal of X^k, with the small diagonal in the case of equality and zero when k > s + s′, and concludes that the system is stable under ⊠, pull-backs and push-forwards by projections and composition, generated via ⊠ by y and the δ_I.',
    basis:
      'Page 50 gives generators, relations and « bases » for H*(X), H*(X × X) and H*(X³); page 52 the generators of H*(X^k), then the heading « relations », where the page stops; page 54 the pairs (R, J), the sets Z_{R,J}, the vanishing when J ∩ J′ ≠ ∅ or when the blocks generated by J and J′ coincide, and a general product formula whose exponents and indices are overwritten beyond reading; page 56 the codimension count, the boxed s + s′ ≤ k + 1, the case k = s + s′ left as a struck χ, an uncertain y_{X^k} and a « ? », the stabilities a)–c), a struck d), « Stable par comp. » and the boxed conclusion. Page 50 writes δ ∈ H^n(X) for the diagonal of X × X; page 56 writes « on trouve δ_I » with a stroke on the index.',
    ours:
      'The reading supplies the setting (X smooth projective over C or any Weil cohomology, the page’s H*(X) read as the tautological part k ⊕ k·y), states the complete product rule as a Proposition, restores χ in the case k = s + s′ by the excess intersection formula and checks it against page 50’s two relations, treats the pointed blocks and identifies the excess bundle — its footnote says these are its own —, corrects the push-forward to δ_{I∖{i}}, and derives stability under diagonal embeddings and composition, which the page asserts in three words. So the full multiplication table is the edition’s; the bound, the equality and degree cases, the relations for k = 2, 3 and the boxed conclusion are the page’s. This pass notes, from memory, matches the reading does not name: the relations (a ⊗ 1)Δ = (1 ⊗ a)Δ and Δ² = χ·y ⊗ y are those of the diagonal class in the models of configuration spaces of Kriz, Totaro and Lambrechts–Stanley, and composing such correspondences is the 2-dimensional TQFT of the commutative Frobenius algebra H*(X), each closed loop contributing the Euler class. Written on Opus 5.5 against a reading made on Opus 5.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look for the product rule of pointed polydiagonal classes in H*(X^k), with χ from excess intersection, and for the stability of the subalgebra generated by the point class and the diagonals, in W. Fulton, Intersection Theory (1984), chapter 6; I. Kriz, « On the rational homotopy type of configuration spaces » (Ann. of Math. 139, 1994); B. Totaro, « Configuration spaces of algebraic varieties » (Topology 35, 1996); P. Lambrechts and D. Stanley, « Poincaré duality and commutative differential graded algebras » (Ann. Sci. ÉNS 41, 2008); M. Lehn and C. Sorger, « The cup product of Hilbert schemes for K3 surfaces » (Invent. Math. 152, 2003); A. Beauville and C. Voisin, « On the Chow ring of a K3 surface » (J. Algebraic Geom. 13, 2004). If either is there, mark matched. All are cited from memory. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '11-leaves-undated-moutures-unordered',
    cote: '11',
    pages: '2–56',
    kind: 'codicological',
    claim:
      'Nothing in the folder dates its leaves, among themselves or against the literature: that pages 41–47 are a « seconde mouture » of pages 2–16, or that page 56 takes up page 39, are orders of the binding and of the argument; page 22’s « dans car. 0 si on admet la résolution des singularités » does not place the page before Hironaka’s theorem (1964); and nothing places any leaf before or after the correspondences of Manin or Kleiman, Green functors or the Frobenius-algebra literature the reading cites. The only physical fact recorded that could bound a date is that pages 2–20 are written on the backs of an English typescript on geometric invariant theory.',
    basis:
      'All three batches copy the inventory’s « [à partir de 1961] » and record no date on any leaf; batch 1 says its ten leaves carry « no date and no pagination of his own » and describes the versos, pages 3–19, as a typescript in English on geometric invariant theory with pages headed -2.24- to -2.33-, -3.1-, -3.2-; batches 2 and 3 describe the typescript of their versos only as English and unrelated. Page 41 redefines the category and page 45 notes « axiome cartésien oublié ! », but no leaf refers to another by page or date.',
    ours:
      'The reading’s header calls pages 41–47 « a SECOND MOUTURE » and says the second formalism « oublie d’abord l’axiome d’échange »; batch 3’s header says page 39’s Proposition « is taken up again » on page 56; the reading’s résumé says of the category of correspondences « On la retrouvera aussi sous les noms de foncteur de Green, d’algèbre de Frobenius … », its footnote on page 28 that the Koszul rule « ne porte pas encore ce nom sur la page », and its footnote on page 22 sets « démontrée par Hironaka en 1964 » beside the page’s « si on admet ». These can be read as orders in time; the entry adopts none of them. The reading’s own header says nothing on the leaves names Manin, Kleiman, Demazure, motives, Green functors or Frobenius algebras, and that the dating is the archivists’. Whether the typescript was typed before his notes were written on its backs is not recorded. No facsimile was consulted. Written on Opus 5.5 against a reading made on Opus 5. The transcription headers and the reading were revised on 2026-09-23 after this entry: batch 1’s typescript headings now read, from the facsimile, -3.2- (p. 3), -3.1- (p. 5), -2.33- down to -2.28- (pp. 7–17) and -2.26- (p. 19), with no -2.27-; and the reading no longer carries « On la retrouvera aussi sous les noms… », « ne porte pas encore ce nom » or the mention of Hironaka 1964. The quotations above are of the files as they then stood.',
    literature: [
      'Transcription 11, batch 1 (batch-01.fr.tex), header and pages 2–20',
      'Transcription 11, batch 2 (batch-02.fr.tex), header and pages 22–39',
      'Transcription 11, batch 3 (batch-03.fr.tex), header and pages 41–56',
      'Modernised reading 11 (11.modern.tex), header, « Résumé », « Le fil du dossier, et les conventions », and the footnotes on pages 22 and 28',
    ],
    status: 'candidate',
    settle:
      'A person identifies the typescript of pages 3–19 — its headings -2.24- to -2.33-, -3.1-, -3.2- and its subject — and checks whether the versos of batches 2 and 3 belong to it; if it is a datable text typed before his notes were written on its backs, it bounds those leaves from below, and only those. Paper and ink of pages 2–30 against pages 41–47 would say whether the two formalisms were written in one campaign, not in which order. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '11-page-47-breaks-off',
    cote: '11',
    pages: '41–47',
    kind: 'codicological',
    claim:
      'The run of pages 41–47 on correspondences between powers X^I breaks off mid-sentence at page 47 — « On voit que sous ces conditions, » — after announcing that associativity and the units remain to be checked; the next leaf in his hand, page 50, opens a new heading, so the continuation is not in the folder.',
    basis:
      'Batch 3 transcribes the last lines of page 47 with the note « La page s’arrête sur cette virgule »; its header records page 48 as the back of the English typescript and page 49 as bearing no writing of its own, and page 50 opens on « Sous-algèbre tautologique de H*(X^n) ». « définir » in « Il faut encore définir l’associativité » is uncertain.',
    ours:
      'The reading says the same (« la suite n’est pas dans le dossier ») and supplies that associativity and units were done in the first formalism on pages 4 and 6. Whether the continuation was lost or never written is not settled by the transcription, which does not say whether the lower part of page 47 is blank. No facsimile was consulted. Written on Opus 5.5 against a reading made on Opus 5. Since the revision of 2026-09-23 the reading says « ce que les pages 4 et 6 font pour la première mouture », the folder’s order and not a date.',
    literature: [
      'Transcription 11, batch 3 (batch-03.fr.tex), header and pages 45–50',
      'Modernised reading 11 (11.modern.tex), « Unités, et l’arrêt »',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile whether the comma of page 47 falls at the foot of the leaf or above blank space, and whether any leaf of the fonds carries the sentence on. Blank space below would make the stop an abandonment rather than a loss.',
  },
  {
    id: '113-listing-stamps-bound-below-only',
    cote: '113',
    pages: '2–12',
    kind: 'codicological',
    claim:
      'The machine stamp « 16 SEP 82 » on the listings of pages 4 and 12 bounds from below only the handwriting written across or around those two listings; nothing in the folder bounds any leaf from above, so nothing places its tensor product of k-linear categories, or of their categories of modules, before or after the text of Kelly (1982) or the tensor product of abelian categories of Deligne (1990) that the reading cites.',
    basis:
      'The transcription records that the listings of pages 4 and 12 are stamped 16 SEP 82 and that page 12’s footer announces the machine’s shutdown for Friday 17 September — 17 September 1982 was a Friday, so the two agree; that page 2 is written landscape across its listing and page 12 in the two free margins of its own, page 12 being the reverse of page 11; that pages 4, 6, 8 and 10 are listings « of that run » with nothing of his on them; and it records no stamp on pages 4–10 and no date in his hand on any leaf. The leaves cite nobody.',
    ours:
      'The transcription’s header says « The versos date the folder »; the reading’s footnote on page 2 says « Le listing est daté du 16 septembre 1982 », and its footnote on Application 2 names « G. M. Kelly, 1982 » and « P. Deligne … (1990) », calling Deligne’s product « un cousin », while noting that the leaves cite nobody. Read together these can suggest a date for the whole run, or a place for it between the two publications; the entry adopts neither. The stamp dates the printing. It bounds the handwriting of pages 3–11 only if their listings belong to the same job and were printed before he wrote on their backs — the usual order for scrap paper, but not recorded; that pages 4–10 are the other faces of pages 3–9 is inferred from pages 1–2 and 11–12, not stated. The inventory’s « [à partir de 1982] » is not contradicted. Whether Kelly’s text of 1982 states the tensor product of cocomplete k-linear categories, as the footnote’s date implies, is not checked here. No facsimile was consulted. Written on Opus 5.5 against a reading made on Opus 5. Revised 2026-09-23 after the transcription and reading were checked on the facsimile: the 16 SEP 82 stamp is on the listings of pages 4 and 12 (page 4’s reads « 11.07.13 AM 16 SEP 82 »), not 2 and 12; the pages 1–2 leaf carries none; and the wordings quoted above (« The versos date the folder », « Le listing est daté du 16 septembre 1982 ») are gone from the files.',
    literature: [
      'Transcription 113, batch 1 (batch-01.fr.tex), header and pages 2, 11 and 12',
      'Modernised reading 113 (113.modern.tex), header, the footnote on page 2 and the footnote on Application 2 (page 7)',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile whether the listings of pages 4, 6, 8 and 10 carry the job header or stamp of page 12, and whether pages 3–11 are the blank backs of those listings. A match bounds the whole run from below by 16 September 1982 and bounds nothing above. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '113-cover-word-and-verso-unattached',
    cote: '113',
    pages: '1–12',
    kind: 'codicological',
    claim:
      'The cover leaf carries two things the rest of the folder does not take up: the word « Abelianization » of page 1, from which the inventory takes the folder’s title, appears nowhere on pages 3–12, whose own heading is « ⊗ dans Cat »; and page 2, the other face of the same leaf, is a calculation on semi-simplicial « MM-fibrés » that mentions neither abelianisation nor k-additive categories and is continued on no other leaf of the folder.',
    basis:
      'The transcription records page 1 as an otherwise blank listing carrying « Abelianization » top right and the number 377 top left, both in his hand; page 2 as its other face, written landscape: chains α ↠ β ↩ γ over X ↠ Y ↩ Z, objects M(ξ₀, …, ξₙ) joined by arrows marked « subm », « multibundle » struck for « MM-fibré », and a sufficient condition for ∫_I X(i) not to leave the semi-simplicial MM-fibrés, the word qualifying f in its condition c) read « submersion » as uncertain and preceded by an illegible word. Pages 3–12 carry his boxed heading « ⊗ dans Cat » and his circled pagination 1 to 5, and speak of « topos abélien » and « topos k-abéliens » but never of abelianisation.',
    ours:
      'The transcription’s header says the word is where the inventory’s title comes from, « which is therefore his and not the archivists’ »; the reading repeats it, calls page 2 « un calcul indépendant » and says it does not identify the notion. That the word titles pages 3–12 — the passage from a k-additive P to the abelian P^k would fit it — is stated by neither file and is not adopted here; nor is any order between the two faces of the leaf. Neither file explains the number 377. No facsimile was consulted. Written on Opus 5.5 against a reading made on Opus 5.',
    literature: [
      'Transcription 113, batch 1 (batch-01.fr.tex), header, cover and pages 2–3',
      'Modernised reading 113 (113.modern.tex), « Au dos du feuillet de titre (page 2) » and its footnote',
      'Every transcription in transcripts/ searched for « MM-fibr », « multibundle », « Abelianization » and « 377 » (2026-09-23): no hit outside folder 113',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile whether 377 recurs, in his hand and in the same corner, on the covers of neighbouring folders of the fonds — a series number would make page 1 a filing cover and say nothing about page 2 — and, as further folders are transcribed, looks for the MM-fibrés or multibundles of page 2 elsewhere in the fonds.',
  },
  {
    id: '116-presheaf-gluing-continuous-gluing-functor',
    cote: '116',
    pages: '6–7',
    kind: 'mathematical',
    claim:
      'The folder asserts, without proof, that a topos glued from an open subtopos X₀ and its closed complement X₁ along a left exact φ : F(X₀) → F(X₁) is a presheaf topos Top(X) exactly when X₀ and X₁ are presheaf topoi Top(X₀), Top(X₁) and φ commutes with all projective limits, the gluing datum then being a bifunctor h : X₀^op × X₁ → (Ens).',
    basis:
      'Pages 6–7 write « Un cas particulièrement important pour nous est celui où X est de la forme Top(X), [illegible] X dans (Cat), il revient au même de dire que » X₀, X₁ are of the form Top(X₀), Top(X₁) and that φ commutes with arbitrary projective limits, i.e. has a left adjoint f^*, defined by a functor X₁ → X̂₀ extended by continuity in inductive limits, « correspondant i.e. à un bifoncteur » (x₀, x₁) ↦ h(x₁, x₀). « Top(X) » is written over a struck illegible word, « Top(X₀), Top(X₁) » over a struck « X̂₀, X̂₁ »; the words before « X dans (Cat) », before « un adjoint à g. » and at the start of the parenthesis on continuity are illegible. None of them carries the equivalence.',
    ours:
      'Every step of the proof is the reading’s, footnoted as its own: a subterminal of a presheaf topos is a sieve, cutting X into the full sieve X₀ and the cosieve X₁; the gluing functor is then restriction of a right Kan extension, hence continuous, and h(x₁, x₀) = Hom_X(x₀, x₁); conversely any h defines a category — the collage, or cograph, of the profunctor h — whose presheaf topos is the gluing. The reading sets this out as a forward statement followed by « Réciproquement »; this pass reads the page’s « il revient au même » as an equivalence and checks both halves. From memory, the direction from a profunctor to a gluing is standard; if anything here is a candidate it is the necessity half — a gluing that is a presheaf topos has a continuous gluing functor — which follows in two lines from subterminals of presheaf topoi being sieves and is likely folklore. Written on Opus 5.5 against a reading made on Opus 5.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look for the statement that an Artin gluing is a presheaf topos if and only if both parts are and the gluing functor preserves all limits — equivalently, that presheaf topoi with an open subtopos are exactly the collages of profunctors — in SGA 4, IV 9.5 and the exercises that follow it; P. T. Johnstone, Sketches of an Elephant (2002), A2.1 and A4.5, on Artin glueing and open and closed subtoposes; G. C. Wraith, « Artin glueing » (J. Pure Appl. Algebra 4, 1974); A. Carboni and P. T. Johnstone, « Connected limits, familial representability and Artin glueing » (Math. Structures Comput. Sci. 5, 1995). If both halves are there, mark matched. All are cited from memory. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '116-leaves-undated-vocabulary-dates-nothing',
    cote: '116',
    pages: '1–10',
    kind: 'codicological',
    claim:
      'Nothing in the folder dates his handwriting: its only date, 19 June 1981, is that of the administrative notice of page 10, which the transcription records as bearing nothing of his and as tied to no leaf he wrote on, so it bounds no leaf; and neither his vocabulary nor his two substitutions of « équivalence faible » for « asphérique » place the leaves in time, among themselves or against the literature the reading names.',
    basis:
      'The transcription records page 1 as the kraft wrapper carrying « Mapping cone » alone, page 2 as its other face, pages 3–7 in ink on white leaves under his title, page 8 blank but for the show-through of page 9, page 9 a separate leaf, and page 10 a notice of the Université des Sciences et Techniques du Languedoc dated 19 June 1981; it records no date in his hand, and says the notice is « presumably » how the archivists reached « [à partir de 1981] », « though nothing says so ». The substitutions are interlinear, on pages 3 and 5; page 4 keeps « strict. asphérique » unstruck.',
    ours:
      'The reading’s résumé says « Le vocabulaire est celui du début des années 1980 », on the strength of the two substitutions; that dates the leaves by their words and is not adopted here — a struck word orders two wordings of one line, not the leaves against anything. Its header lists as modern names, « given and footnoted as ours », Artin gluing (SGA 4 IV 9.5), the Sierpiński topos, cohomology with supports, the collage of a profunctor and Quillen’s Theorem A; nothing places any leaf before or after them. The reading calls pages 2 and 9 separate notes; this pass notes that page 2’s « induit iso sur Γ, puis H* » has the shape of page 3’s cohomology isomorphism, and adopts no link or order between them. The inventory’s « [à partir de 1981] » is not contradicted. No facsimile was consulted. Written on Opus 5.5 against a reading made on Opus 5.',
    literature: [
      'Transcription 116, batch 1 (batch-01.fr.tex), header, cover and pages 2–5',
      'Modernised reading 116 (116.modern.tex), header, « Résumé » and the footnotes on pages 3, 5 and 7',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile whether the notice of page 10 carries anything of his on either face, whether it was folded inside the wrapper with the leaves of pages 3–7, and whether its paper matches theirs; a physical tie would bound the leaves it touches from below and nothing from above. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '125-cd-complement-formal-comparison',
    cote: '125',
    pages: '2, 4, 7',
    kind: 'mathematical',
    claim:
      'The folder asserts, without proof, that for P^n ⊃ X^r ⊃ Y^m with r > m > 0, the vanishing H^p(X − Y, F) = 0 for p ≥ m and every coherent F is equivalent — through H^p_Y(X, F) → H^p(X, F) being bijective for p > m and surjective for p = m, and a duality with Ext^q(−, Ω^r) on X and on its formal completion X̂ along Y — to H^q(X, F) → H^q(X̂, F̂) being bijective for q < r − m and injective for q = r − m for F locally free, each step reduced to twists O(n).',
    basis:
      'Page 2 is a chart of boxed statements joined by vertical equivalences, one of them labelled « dualité », with a right-hand column reducing each to O(n), n grand, and an N.B. dispensing with the case p = m because H^m(X, O(−n)) = 0 for n large; page 4 writes H^p_Y(X, F) = lim Ext^p(P; O_{Y_n}, F), H^p(X − Y, F) = lim Ext^p(P; J^n, F) and the dual inverse limit on the completion; page 7 boxes H^i(P̂, Ω^r_P(−n)) = 0 for 0 < i < r − m with the margin « ⟺ P − X est de dim. coh. r − m ». Under the chart: the bound of page 2’s first display is illegible, « réduit à » in the right-hand column is uncertain, « [m = dim Y] » stands between two illegible stretches, and the diagonal N.B. at the foot is legible only in fragments.',
    ours:
      'The reading names no published statement for the chart: it gives it as one chain of equivalences, states the duality as a perfect pairing, and footnotes the fifth box as « la forme sous laquelle l’énoncé est aujourd’hui le plus reconnaissable » without naming it. This pass reads the chart, from memory, as Hartshorne’s comparison between the cohomological dimension of X − Y and the formal completion along Y (Ample Subvarieties of Algebraic Varieties, 1970, chapter III, for X non-singular projective), the page’s m playing the part of its q, and records the entry as a guard to be marked matched rather than as a candidate. It also reads the folder differently from the reading in four places: Ω^r_{X/k} is a dualizing sheaf only for X smooth, which neither the page nor the reading states; the reading’s single notation — P = P^n, X of dimension r — does not fit pages 4 and 7, which write P^r ⊃ X ⊃ Y and Ω^r_P, so that there r is the dimension of the ambient space; the reading’s footnote that every coherent sheaf is a quotient of a sum of O(n), n large, should read O(−n), as page 2’s N.B. has it; and its footnote to page 7 folds page 2’s complement X − Y into page 7’s P − X, which are different statements. Page 7’s second boxed line, H^r(P, Ω^r(−n)) ≅ H^r(P̂, Ω̂^r(−n)), cannot hold as transcribed when the hat is a completion along a closed subset of smaller dimension — its right side is then zero — and the reading reproduces it without comment. Written on Opus 5.5 against a reading made on Opus 5.',
    literature: [],
    status: 'unsearched',
    settle:
      'Read R. Hartshorne, Ample Subvarieties of Algebraic Varieties (LNM 156, 1970), chapter III, §3, the formal duality theorem and the comparison theorem that follows it; R. Hartshorne, « Cohomological dimension of algebraic varieties » (Ann. of Math. 88, 1968); SGA 2, exposé XII, on a projective scheme and its formal completion; R. Hartshorne, Local Cohomology (LNM 41, 1967), for H^p_Y = lim Ext^p(O_{Y_n}, −) and H^p(X − Y, −) = lim Ext^p(J^n, −); A. Ogus, « Local cohomological dimension of algebraic varieties » (Ann. of Math. 98, 1973). If page 2’s equivalence is there for X smooth projective, mark matched and cite the section. All are cited from memory. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '125-typescript-leaves-unattributed',
    cote: '125',
    pages: '3, 6',
    kind: 'codicological',
    claim:
      'The folder’s two typescript leaves, headed « - III-18 - » and « - III-5 - », stand among his leaves in reverse order of their numbers, are annotated in a hand the transcription records as unlike his and does not attribute, and come from a text neither file identifies — one that cites itself as « (II, 2, 7, prop. 17) » or « (I, 1, 4, th. 2) » and works with préschémas.',
    basis:
      'The transcription’s header and its notes on pages 3 and 6 describe typescript leaves headed III-18 (page 3) and III-5 (page 6), annotated in ink and pencil and highlighted in yellow, the annotating hand « round, careful and upright », not like the fast angular hand of pages 2, 4, 5, 7 and 8 — « Whose it is, the folder does not say »; page 3 cites « (II, 2, 7, prop. 17) », « (I, 2, 7, prop. 19) », « (I, 4, 1, prop. 4) » and « (I, 1, 4, th. 2) », page 6 its own « n° 1 » and « la prop. 1 », and page 6’s Proposition 2 carries the interlinear « un préschéma ». Several words of the annotations, including a pencil note on page 3, are illegible.',
    ours:
      'The reading’s footnote on the two leaves repeats that the edition does not decide whose hand annotates them, but its résumé calls them « des pages d’un tapuscrit qu’il a annotées », which attributes the annotations to him; this pass takes the transcription as governing and does not adopt the attribution. The reading also says the « préschéma » correction keeps the hypothesis from bearing on « le mauvais objet », which the typed « si X est noethérien » does not bear out: both wordings are about X. From memory, this pass notes that page 6’s Proposition 2 and its Corollary state what EGA III, §1.2, states — the Čech cohomology of the complement of V(f) computed by the Koszul complex, and the vanishing on an affine as a consequence; the leaves’ citation style is not that of the printed EGA, so they may be a draft of it or another text. That identification is not adopted and not checked. No facsimile was consulted. Written on Opus 5.5 against a reading made on Opus 5.',
    literature: [
      'Transcription 125, batch 1 (batch-01.fr.tex), header and pages 3 and 6',
      'Modernised reading 125 (125.modern.tex), « Résumé », « Le dossier, sa charpente et ses notations » and its footnote, and the sections on pages 3 and 6',
      'Every transcription in transcripts/ searched for « III-18 », « III-5 » and the Koszul identification C^{p+1}((f), M) (2026-09-23): no hit outside folder 125',
    ],
    status: 'candidate',
    settle:
      'A person compares the typed text of pages 3 and 6 with EGA III, §1.1–1.2, with the printed EGA’s cross-references, and with any duplicated drafts held elsewhere in the fonds, to identify the typescript; and compares on the facsimile the annotating hand with his own. An identification would say which text the leaves come from, not when his own leaves of the folder were written.',
  },
  {
    id: '125-leaves-undated-no-order-against-literature',
    cote: '125',
    pages: '1–8',
    kind: 'codicological',
    claim:
      'Nothing in the folder dates its leaves: « [avant 1970] » is the inventory’s, and no leaf carries a date in his hand or on the typescript, so nothing places the chart of page 2 or the programme of pages 7–8 before or after EGA III, SGA 2 or Hartshorne’s work of 1968–1970 on cohomological dimension and formal completion; the names Greenberg and Néron on page 8 could bound that page from below only through works the page does not cite.',
    basis:
      'The transcription and the reading carry the inventory’s « [avant 1970] », which the catalogue gives beside « notes manuscrites (s.d.) »; the transcription records no date on the cover or on any leaf, the typescript leaves carry only their headings III-18 and III-5, and page 8 stops two-thirds down with no sequel. Page 8’s item 6 names « Greenberg » and « Néron », underlined, with two illegible words in the sentence; page 7’s item 2 names « Lefschetz » and a second name read « Grauert » as uncertain.',
    ours:
      'The reading’s footnote to item 1 of the programme says that calling the theorem on formal functions « fondamental » beside finiteness « est ce que fera EGA III », which places the page before EGA III; the entry adopts no such order, and identifying the typescript leaves (see 125-typescript-leaves-unattributed) would date the typescript, not his leaves. The reading names no work for the chart of page 2; this pass’s match with Hartshorne 1970 (see 125-cd-complement-formal-comparison) is an identity of statements, not an order, and « [avant 1970] » beside it is not to be read as precedence. The reading’s résumé calls the programme « écrit à l’usage de personne » and speaks of the order in which it was « mis au propre »: the arrow and the circled 2 of page 7 record a renumbering on the page, not when, why or for whom it was written. No facsimile was consulted. Written on Opus 5.5 against a reading made on Opus 5.',
    literature: [
      'Transcription 125, batch 1 (batch-01.fr.tex), header, cover and pages 3, 6, 7 and 8',
      'Modernised reading 125 (125.modern.tex), « Résumé » and the footnotes on items 1, 2 and 6 of the programme',
      'Catalogue entry for folder 125 (src/content/catalogue.ts)',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile whether the cover, any leaf or the typescript carries a date, a stamp or a watermark, and whether pages 2, 4, 5, 7 and 8 share paper and ink with the typescript leaves. A physical tie would bound his leaves by the typescript from below only. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '134-1-picard-sign-sequence',
    cote: '134-1',
    pages: '3–5',
    kind: 'mathematical',
    claim:
      'The folder asserts, as heuristic, that for abelian sheaves M, N on a topos there is a canonical distinguished triangle E(M,N) → E′(M,N) → Hom(M, ₂N)[−2], with E(M,N) = τ≤2 RHom(M,N), whence an exact sequence of sheaves 0 → Ext²(M,N) → P(M,N) → Hom(M, ₂N) → 0 in which P(M,N) is the sheaf of Picard stacks pinned by M, N up to equivalence and the last map is the symmetry invariant of L ⊗ L; and that this sequence can be built « à la main » without the triangle.',
    basis:
      'Page 3 defines E(M,N) and draws (T), the arrow running from E to E′, with no shift marked on the return arrow; page 4 writes (*), names its middle term P(M,N), and reads E′ heuristically as the strict Picard 2-stack of not necessarily strict Picard stacks pinned by M, N, and E as the strict ones; pages 4–5 say (*) is built canonically by hand, its middle term the sheaf of pinned Picard stacks up to equivalence and σ the symmetry of L ⊗ L read as a section of ₂N. E′ is never defined on the page. The word before « à « équivalence » près » is read « données » as uncertain (folder 103’s copy of the same leaves reads « classes », also uncertain), and « (T) » in the closing question is uncertain.',
    ours:
      'The reading supplies, each flagged as its own, a definition of E′ as τ≤2 RHom computed over the sphere spectrum, the pinning isomorphisms, the sheafification of P(M,N), the proof that σ is additive and killed by 2, the shift on the return arrow, and the correction of page 4’s « invariants … ceux de E(M,N) en degré i+2 ». This pass reads its proof of (T) differently from the reading and says so: truncating the triangle RHom_HZ(HM, HN) → RHom_𝕊(HM, HN) → RHom_HZ(F, HN), F the fibre of HZ ∧ HM → HM, does not give a triangle whose third term is Hom(M, ₂N)[−2]; its long exact sequence runs 0 → Ext²(M,N) → P(M,N) → Hom(M, ₂N) → Ext³(M,N) as sheaves, and the reading’s « L’exactitude à droite est gratuite … H³(E) = 0 » assumes the triangle it is proving. Exactness on the right is the page-5 claim (see 134-1-sign-realisation-universal-argument), not a consequence of truncation. What stands without it is the left part, 0 → Ext² → P(M,N) → Hom(M, ₂N), with a pinned stack strict exactly when σ = 0. From memory, over a point this is the classification of Picard categories by π₀, π₁ and a homomorphism π₀/2 → π₁, with Ext² = 0; on a topos it is the low corner of the spectral sequence Ext^p(π_q(HZ ∧ HM), N) ⇒ Ext^{p+q}_𝕊(HM, HN). Written on Opus 5.5 against a reading made on Opus 5.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look for the sheaf-level statement — pinned Picard stacks, strict or not, up to equivalence, as an extension of (a subsheaf of) Hom(M, ₂N) by Ext²(M,N) — in SGA 4, exposé XVIII, 1.4 (Deligne); P. Deligne, « Le déterminant de la cohomologie » (Contemp. Math. 67, 1987), § 4; Hoàng Xuân Sính, Gr-catégories (thèse, Paris VII, 1975); L. Breen, « Extensions du groupe additif » (Publ. Math. IHÉS 48, 1978), on the spectral sequence for stable Ext; L. Breen, « On the classification of 2-gerbes and 2-stacks » (Astérisque 225, 1994); N. Johnson and A. M. Osorno, « Modeling stable one-types » (Theory Appl. Categ. 26, 2012). If the left-exact part is there for stacks on a topos, mark matched. All are cited from memory. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '134-1-sign-realisation-universal-argument',
    cote: '134-1',
    pages: '5',
    kind: 'mathematical',
    claim:
      'The folder asserts, « sauf erreur » and without the argument, that on any topos every homomorphism M → ₂N is the symmetry invariant of a Picard stack pinned by M, N — the a priori obstruction in Ext³(X; M, N) being killed by a « universal » argument — so that every section of Hom(M, ₂N) over any object U lifts to P(M,N), and even to ℍ²(U, E′(M,N)).',
    basis:
      'Page 5: « Je sais prouver (sauf erreur) que tout hom. M → ₂N provient d’un champ de Picard convenable (épinglé par M, N) (a priori l’obstruction est dans Ext³(X; M, N), mais un argument « universel » prouve qu’elle est nulle) », followed by the « section ensembliste » and the refinement to ℍ²(U, E′(M,N)), where « i.e. » before ℍ² is uncertain. No word of the statement itself is illegible; the page gives no argument.',
    ours:
      'The reading endorses the statement, gives the obstruction group as ℍ³(X, E(M,N)) ⊂ Ext³(X; M, N), and reconstructs the « universal » argument as its own: realise q by hand for M free, on the split stack M × BN with an antisymmetric form b such that b(eᵢ, eᵢ) = q(eᵢ), then pass to general M « par une résolution ». This pass reads the statement differently and says so, from memory and without having checked it: the passage through a resolution is where it fails, since the construction depends on a basis. On the classifying topos of abelian groups (functors from finitely presented abelian groups to sets), a Picard stack pinned by the generic group U and U/2U with σ the projection is a pseudo-functor A ↦ P(A) whose values have invariants (A, A/2A, projection), that is, Moore spectra truncated above π₁; it would make Moore spectra functorial on finitely presented groups, since the truncation does not change maps between them, whereas the homotopy category of Moore spectra is, as this pass recalls, a non-split linear extension of that of abelian groups. If so, the obstruction does not vanish universally, and (*) is not exact on the right on that topos. The statement does hold over a point and for M constant and free. Neither Grothendieck’s argument nor a counterexample is on the page, and the question is not decided here. Written on Opus 5.5 against a reading made on Opus 5.',
    literature: [],
    status: 'unsearched',
    settle:
      'Decide whether Moore spectra truncated above π₁ admit a functorial choice on finitely presented abelian groups — equivalently, whether the universal obstruction in Ext³ on the classifying topos of abelian groups vanishes. Look in H.-J. Baues, Homotopy Type and Homology (Oxford, 1996), on the homotopy category of Moore spaces as a linear extension; H.-J. Baues and W. Dreckmann, « The cohomology of homotopy categories and the general linear group » (K-Theory 3, 1989); M. Jibladze and T. Pirashvili, « Cohomology of algebraic theories » (J. Algebra 137, 1991), for Mac Lane cohomology as Ext in functor categories; L. Breen, « Extensions du groupe additif » (Publ. Math. IHÉS 48, 1978); P. Deligne, « Le déterminant de la cohomologie » (Contemp. Math. 67, 1987), § 4. If a functorial choice exists, the page’s claim stands and this pass’s doubt is withdrawn; if not, the page’s statement holds over a point and for free M only. All are cited from memory. No web search was available for this pass (2026-09-23), so nothing has been read.',
  },
  {
    id: '134-1-first-four-of-eight-pages',
    cote: '134-1',
    pages: '3–6',
    kind: 'codicological',
    claim:
      'The folder holds only the first four pages of the letter headed « Lodève le 27.8.74 »: folder 103 keeps a reproduction of the same leaves, page break for page break, that runs four pages beyond the closing question of page 6 — relative cohomology for a morphism of topoi, a question for Illusie, Gr-stacks pinned by (G, N) — so page 6 is not the end of the letter, and no signature is transcribed on this copy.',
    basis:
      'This folder’s transcription ends page 6 on the question to « les compétents » and records no signature; its header says folder 103’s copy is « four pages longer ». Folder 103’s transcription gives its pages 8–11 as this folder’s pages 3–6, with the same page breaks (« à « équivalence » près des » at the foot of the second page, ℍ² at the foot of the third), and reads its pages 8–11, 14–15, 12–13 as continuous, the leaf after its page 13 missing there too.',
    ours:
      'The transcription’s header also calls pages 3–6 « a single letter, complete », and the reading’s résumé says the folder holds « une seule lettre, de quatre pages », whose last section says the letter « s’achève » on its question, and « Elle ne conclut pas : elle demande »; the reading of pages 3–6 is not affected, but these descriptions are not borne out by folder 103 and are not adopted. Whether Deligne forwarded only these four pages or the rest was separated later, neither transcription says; the entry adopts neither. Folder 103’s transcription is a Fable 5.1 pass and is used here only as a record of what that copy carries. No facsimile was consulted. Written on Opus 5.5 against a reading made on Opus 5.',
    literature: [
      'Transcription 134-1, batch 1 (batch-01.fr.tex), header and pages 3–6',
      'Modernised reading 134-1 (134-1.modern.tex), « Résumé » and « La question, et ce qu’on en sait aujourd’hui »',
      'Transcription 103, batch 1 (batch-01.fr.tex), header and pages 8–15',
    ],
    status: 'candidate',
    settle:
      'A person compares on the two facsimiles pages 3–6 here with pages 8–11 of folder 103, and checks whether page 6 here, at its foot or on its back, shows any trace of the pages that follow in folder 103. The answer says what Breen received, not when.',
  },
  {
    id: '134-1-margin-notes-forwarding-undated',
    cote: '134-1',
    pages: '1–6',
    kind: 'codicological',
    claim:
      'The two reproductions of the letter do not carry the same marginalia — Deligne’s signed note to Breen runs up the left margin of page 3 here and is not on folder 103’s copy, whose first page carries instead « Je n’ai pas retrouvé la lettre sur les Gr-champs que tu cites », absent here — so, unless a margin was cropped, neither note was on the leaves when the other copy was made; neither note is dated, so nothing in the folder dates the forwarding to Breen, and the cover’s « Lettres Breen 75, 76 » is a date neither of this letter, headed 27.8.74, nor of its forwarding.',
    basis:
      'The transcription records Deligne’s note as a marginal on page 3, running vertically in the left margin, in another hand than the letter’s and signed « P. Deligne », and records the cover of page 1 as carrying only « Lettres Breen 75, 76 »; folder 103’s transcription records on its page 8 the other note, vertical in the left margin, in a hand it does not distinguish from the letter’s, and says the page does not say whose it is. The date reads « 27.8.74 » here with « 8.74 » uncertain, and on folder 103’s copy with the « 2 » uncertain. The docket « 9/74 Envoyé par Grothendieck » of folder 103 is on the typescript of its page 1, not on the letter.',
    ours:
      'The transcription’s header says the two copies show « the same strokes line for line »; that holds for the letter, not for the margins. The reading gives the date as 27.8.74 and footnotes its reading; it says the date « s’accorde » with folder 103’s letter of 23 June 1974, which is consistency, not a date for the forwarding. Its footnote on page 6 calls « η s’envoie sur {−1} » a standard fact « postérieur en tout cas à la mise en forme de la lettre », an order in time that nothing in either folder supports and that is not adopted. The entry places neither the letter nor its forwarding before or after any publication; the reading itself abstains on who knew what and when in its closing section. No facsimile was consulted. Written on Opus 5.5 against a reading made on Opus 5.',
    literature: [
      'Transcription 134-1, batch 1 (batch-01.fr.tex), header, cover and page 3',
      'Modernised reading 134-1 (134-1.modern.tex), the footnotes on the date (page 3) and on the example (page 6)',
      'Transcription 103, batch 1 (batch-01.fr.tex), header and pages 1 and 8',
    ],
    status: 'candidate',
    settle:
      'A person checks on the two facsimiles whether each margin note is in ink on its copy or reproduced with the leaves, and whether either copy’s left margin is cropped; and looks in the other parts of folder 134 for the letters of 1975–76 the cover names. None of this would place the letter before or after anything published. Whatever is found, priority is not a claim this project makes, about anyone.',
  },
  {
    id: '27-semicontinuity-proof',
    cote: '27',
    pages: '27–36',
    kind: 'mathematical',
    claim:
      'For a smooth, separated group scheme of finite presentation over any base, the dimension of the affine part, the nilpotent, affine-nilpotent and unipotent ranks are upper semicontinuous and the abelian rank, the abelian-plus-reductive rank and the semisimple rank lower semicontinuous — with a proof, where SGA 3 X 8.7 states these inequalities without one.',
    basis:
      'Page 28 fixes the invariants of a smooth connected group over an algebraically closed field through its Chevalley decomposition; page 29 numbers the inequalities (1)–(10) and the implications between them; page 31 states the theorem; pages 31–36 prove it by reduction to a discrete valuation ring, a split maximal torus in the special fibre, the prolongation of its n-torsion to finite étale subgroups H(n) whose centralisers give a Cartan subgroup, and — for the abelian rank — the action of the fundamental group of a henselian trait on the Tate module through the cyclotomic character.',
    ours:
      'The modernised reading supplies the two examples that show which way the inequalities go (an elliptic curve degenerating to G_m, and Spec A[x, (1 + πx)⁻¹]); it notes that the page\'s « comme d\'habitude » reduction to a trait assumes the invariants locally constructible, which neither the page nor the reading checks; and it cannot justify the equivalence (3) ⇔ (9) the page asserts. The comparison with SGA 3 was made by reading the texts side by side on 26 September 2026, not by a specialist.',
    literature: [
      'SGA 3, Exp. X 8.7 (Gille–Polo re-edition) — the inequalities ρ_ab ≤ ρ′_ab, ρ_r + ρ_ab ≤ ρ′_r + ρ′_ab, d_s ≤ d′_s, ρ_n ≥ ρ′_n, ρ_u ≥ ρ′_u stated without proof; editors\' note (71): « Donner une référence pour ces résultats ? »',
      'SGA 3, Exp. XV 4.2 and 8.19 — the result invoked as « annoncée dans Exp. X 8.7 »',
      'SGA 3, Exp. XII 1.7 — the affine case, ρ_r and ρ_n only, proved',
      'FGA, TDTE VI (Bourbaki 236), Remarque 2.8 — α ≤ α′, λ ≥ λ′ conjectured for group preschemes',
    ],
    status: 'candidate',
    settle:
      'Look for a published proof of X 8.7 outside SGA 3 — SGA 7 IX (Néron models and semi-stable reduction), Bosch–Lütkebohmert–Raynaud, Néron Models, chapter 7, and the literature on Chevalley decompositions over a base (Conrad, Brion) — and check whether the Gille–Polo re-edition answers its own note (71) elsewhere. If a proof is there, mark matched and say whether it takes this route; if not, what an expert should judge is the argument on pages 32–36, and in particular the constructibility the reduction to a trait takes for granted.',
  },
// find-novelty pass on folder 8, Opus 5.5 (claude-opus-5-5) on an Opus 5.5 reading (8.modern.tex, Pass 2026-10-03). Three entries, all unsearched.
// Dropped as matches already footnoted in the reading: n_G = ω_G for BT_1 (p. 12), the Hodge–Tate weights of the Lubin–Tate character (pp. 51–55), ℓ^{D(M)} ≃ M ⊗^L O_S and the Postnikov class ξ as a mod-p² lifting obstruction (pp. 77–80; the page itself cites Illusie).
// Not entered: the triangle (III) / Frobenius-descent programme (pp. 1–21), the category C (p. 24), and the lattice question α = 0 (p. 49). The folder poses them as programmes or questions and does not establish them.
  {
    id: '8-lubin-tate-via-hodge-filtration',
    cote: '8',
    pages: '43–49',
    kind: 'mathematical',
    claim:
      'When πA has divided powers, the Lubin–Tate lift of G₀(A, π) to A can be obtained from crystalline deformation theory alone: the Hodge filtration of Ω ⊗_{ℤ_p} A has to consist of A ⊗_{ℤ_p} A-modules, and the condition that A act naturally on t_G forces t_G to be the base change of Ω̌ ⊗ A along the multiplication map A ⊗ A → A, so that the lift exists and is unique; without divided powers, the same argument still gives uniqueness up to isogeny.',
    basis:
      'Page 43 states the lifting problem and cites Lubin–Tate for the result. Page 45 assumes that πA is stable under divided powers and reduces the lift to lifting the filtration of M ⊗_W k to M_A as A ⊗ A-modules. Page 47 derives t_G ≃ Ω̌ and ω_G ≃ Ω through p₀ and says that this recovers Lubin–Tate « sous une forme moins forte » for uniqueness. Pages 47–49 give the isogeny version over K. The sentence on page 45 that turns « A acts naturally on t_G » into the condition on p₀ is largely \\ill{} and \\uncertain{}.',
    ours:
      'The reading translates « πA stable par puissances divisées » into e ≤ p − 1 and names the deformation theory Grothendieck–Messing; the page names neither. It also reconstructs the p₀ step, whose key sentence is mostly illegible on page 45. This pass adds one point the reading does not raise: lifting over A = lim A/πⁿ normally needs topologically nilpotent divided powers, which may require e < p − 1 rather than e ≤ p − 1 (as in the case p = 2, A = ℤ₂). That point is the pass’s own and is not checked.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look for this route to Lubin–Tate, lifting the Hodge filtration as A ⊗ A-modules by Grothendieck–Messing, in Messing, The crystals associated to Barsotti–Tate groups (LNM 264, 1972), Fontaine, Groupes p-divisibles sur les corps locaux (Astérisque 47–48, 1977), and Hopkins–Gross on Lubin–Tate spaces. If it appears there, mark the entry matched. Also settle whether the hypothesis must be e < p − 1. A web search (2026-10-10) did not turn up a direct treatment. That search opened no source, so it does not count as a search of the literature.',
  },
  {
    id: '8-dim-one-A-module-homs',
    cote: '8',
    pages: '39–41',
    kind: 'mathematical',
    claim:
      'Let G₀ and G′₀ be one-dimensional Barsotti–Tate groups of height [K : ℚ_p] over 𝔽_q with an A-action, given by triples (Ω, ν, ϖ) and (Ω′, ν′, ϖ′), where ν records the twist between the two k-structures on ω. They are isogenous if and only if ϖ = ϖ′, and then Hom_A(G₀, G′₀) is Hom(Ω′, Ω) when ν ≤ ν′ and π·Hom(Ω′, Ω) when ν > ν′.',
    basis:
      'Page 39 states the proposition (i)⇔(ii)⇔(iii), with M = Ω ⊗ W and F_M = id ⊗ σ + pr_ν[(ϖ − 1) ⊗ σ]. It then gives the general Hom criterion val(v₀) + Σ₀^ν r_i − Σ₀^ν r′_i ≥ 0. Page 41 specialises this to dimension 1. On page 39 the primes on the r_i are \\uncertain{}. On page 41 the comparison sign between ν and ν′ is under an ink stain, recorded as illegible, with ≤ expected.',
    ours:
      'The edition fixes the hidden sign as ≤ by redoing the computation, and places the primes in the sums of page 39 the same way. It also supplies the argument that moves the unit u from F_{f−1} to F_{ν₀}. The case split, which is the substance of the claim, therefore rests on a sign that nobody has read.',
    literature: [],
    status: 'unsearched',
    settle:
      'First, a person reads the stained sign on page 41 in the facsimile. Then compare with the classification of one-dimensional formal A-modules and their homomorphisms over 𝔽_q in Hazewinkel, Formal groups and applications (1978, chapters on formal A-modules), and in Drinfeld, Coverings of p-adic symmetric domains (1976). The non-strict cases ν ≠ 0, where A acts on Lie through a Frobenius twist, are the part to check: the strict case ν = 0 is very likely a restatement of Lubin–Tate.',
  },
  {
    id: '8-interleaved-typescripts',
    cote: '8',
    pages: '6, 8, 10, 14, 31, 61–73',
    kind: 'codicological',
    claim:
      'The crystal notes are interleaved with leaves from at least two, and probably three, unrelated French typescripts on étale cohomology and semi-stable reduction. They carry handwritten corrections and SGA-style cross-references, and their leaf numbers collide with one another.',
    basis:
      'Pages 6, 8, 10 and 14 are typescript leaves numbered 32, 33, 35 and 37.1, ending the proof of a proper base change theorem (5.1) and giving Lemmas 8.3 and 8.4, with a reference « IX 1.2 ». Page 31 is a leaf numbered 34, on semi-stable reduction of abelian varieties (« critère galoisien 3.5 », Remarque 5.13.1), with « (pro-ℓ-) » and « (C’est vrai pour ℓ ≠ p.) » added by hand. Pages 61–73 are six leaves numbered 28–35, on smooth S-pairs, Kummer theory, Theorem 3.10 and Hochschild–Serre, with references « (IX 3.2) », « (VIII 5.5) » and « (cf. XII 6.5) ». Their numbering collides with the first group, and page 31 is numbered 34 like one of them.',
    ours:
      'The reading suggests SGA 4 for the first group and SGA 7 IX for page 31, and says it has not checked either. The grouping into three typescripts rests on leaf numbers and subject, not on paper or typeface. The correcting hand is not identified.',
    literature: [],
    status: 'unsearched',
    settle:
      'Compare the leaves with the printed SGA 4 XII–XIII (proper base change), SGA 4 XVI/XIX (cohomological purity, smooth pairs) and SGA 7 I, exposé IX (3.5, 5.13.1). Check typeface and paper in the facsimile to decide whether there are two typescripts or three. A web search (2026-10-10) could not confirm the SGA 7 IX numbering, and it is not a reading of the printed text.',
  },
  {
    id: '60-inertia-average-duality',
    cote: '60',
    pages: '38–58',
    kind: 'mathematical',
    claim:
      'For an ℓ-adic sheaf E_η at the generic point of a curve over 𝔽_p, replacing each ramified fibre E^{I_x} by the average of E over inertia modulo an open subgroup acting unipotently gives a virtual sheaf E_η^♮ whose L-function is additive and local in (E, x), unlike that of i_*E_η; the folder computes its Verdier dual as Ě_η^♮(1)[2] plus local terms μ_x(E) = α_x(E_η)^∨ − α_x(Ě_η)(1), and asks (p. 52, « ?? ») whether δ^♮(E_η)² = q^{χ^♮(E_η)} for self-dual E_η of weight ρ.',
    basis:
      'Page 36 shows L* is not additive; pages 38–46 define the averaging functor E ↦ E^I = Im π, π = (1/N)Σ g over I/I₁, with its trace formula, and the virtual sheaf E_η^♮ = u_!(E°) + Σ_x j_{x*}(E_η^{♮(x)}); pages 48–50 give the boxed duality with μ_x and the NB that α_x is not additive but μ_x is; page 52 states the question; page 58 reduces problem c) to b) « moyennant un signe » and stops.',
    ours:
      'Three things are the edition’s, not the page’s. (i) The reading proves μ_x(E) = 0 for every E_η (via [H⁰(I_x, G)] − [H¹(I_x, G)] = [G^♮] − [G^♮(−1)] and the ℓ-adic monodromy theorem, which the page assumes without naming), so the page’s correction terms vanish, λ_x = 1, and its question is answered yes; the page itself carries μ_x as a non-trivial term. (ii) The identification E_η^{♮(x)} = inertia invariants of the Weil–Deligne representation with N forgotten, i.e. of the semisimplification of E restricted to D_x, is the reading’s translation. (iii) The arguments pt, qt of λ_x are restored. On the page, the reading « ℚ_ℓ − ℚ_ℓ(1) » in μ_x (p. 48) is marked \\uncertain{douteuse}, and pp. 40–46 around the definition carry many \\ill{}, though the averaging operator, Im π and the virtual sheaf are read.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check whether the identity α_x(Ě) = α_x(E)^∨(−1) — equivalently, an unadjusted functional equation for the L-function built from the semisimplified local representations — is stated in Deligne, « Les constantes des équations fonctionnelles des fonctions L » (Antwerp II, LNM 349, 1973) §8, or in Tate, « Number theoretic background » (Corvallis 1979) §4.1–4.2, where L and ε of a Weil–Deligne representation are compared with those of its N-forgotten part (Tate 4.1.6). If it is there, mark matched; the averaging construction would then be a different route to a known object, and the entry should say which.',
  },
  {
    id: '62-bourbaki-versos',
    cote: '62',
    pages: '19, 21, 23, 28–40 (even), 42–54 (even)',
    kind: 'codicological',
    claim:
      'The typed versos of the folder are leaves of two Bourbaki drafts: the Archives Bourbaki catalogue lists rédaction n° 276 as « Algèbre commutative. Chapitre II. Filtrations et topologies (état 3) », by R. Godement, dated 1957-06, and n° 272 as « Algèbre Commutative. Chapitre V. Valuations (état 5) », by J.-P. Serre, whose ENS copy is annotated « Archives, Serre, Juin 1957 ».',
    basis:
      'The batch headers record typed leaves numbered « n° 276 » (filtered modules, m-adic topologies, completions, Zariski rings; page 19 is its typed p. 20, headed « §2 Anneaux m-adiques noethériens », with Artin–Rees) and « n° 272 » (valuations; typed pp. 39, 43–47). The catalogue gives n° 276 the sections § 1 « Généralités sur les anneaux et les modules filtrés », § 2 « Anneaux m-adiques noethériens », § 3 « Compléments » over 37 numbered pages, and n° 272 52 pages. Number, subject, section title and page ranges all agree. The pencilled marginalia on pp. 21, 23 and 42 are attributed to him only tentatively by the transcription.',
    ours:
      'The identification is this pass’s, from the catalogue. The transcriptions only give the number and the subject, calling them « Bourbaki-style ». No typed leaf has been compared with the scanned drafts. The consequence is that the sheets he wrote on carry text typed in or after mid-1957. That is a lower bound for the rectos and is weaker than the archivists’ « [à partir de 1963] », so it neither confirms nor narrows it.',
    literature: [
      'Archives Bourbaki (archives-bourbaki.ahp-numerique.fr), item 733: Rédaction n° 276, Godement, 1957-06, catalogue page and table of contents read 2026-10-10; scan not compared',
      'Archives Bourbaki, item 731: Rédaction n° 272, Serre, catalogue page read 2026-10-10 (no catalogue date; ENS copy annotated « Archives, Serre, Juin 1957 »)',
      'Archives Bourbaki, search « Filtrations et topologies »: the other drafts of that chapter are n° 218 (1955), 280, 282 (1958), 338 (1960), 356, 360 (1961), so n° 276 is the only one with that number',
    ],
    status: 'candidate',
    settle:
      'A person compares the typed page 19 (typed p. 20, § 2) and pages 21, 23 (typed pp. 9, 10) with the corresponding pages of the n° 276 scan on the Archives Bourbaki site, and one n° 272 leaf (typed p. 39 or 43–47) with the n° 272 scan. If the text matches line for line, the identification stands. The marginalia on pp. 21, 23 and 42 could then be read against the printed text they annotate.',
  },
  {
    id: '62-triples-rigidified-moduli',
    cote: '62',
    pages: '41–53',
    kind: 'mathematical',
    claim:
      'Over a base with 6 invertible, the folder describes triples (X, X′, s), with X a genus-0 curve, X′ an étale trisection and s a section disjoint from X′, in three equivalent ways. They are an S₃-torsor T with a function t on T, t and t − 1 invertible, satisfying g·t = g(t); or an invertible sheaf with a zero-sum étale trisection of its vector bundle (barycentre); or, through the degree-6 quotient q : X → P¹, an invariant j ∈ Γ(S, O_S) that determines the triple where j(j − 1) is invertible. These descriptions were not found stated in this form in the sources listed.',
    basis:
      'Page 49 states the torsor description, with « fonctoriel » in the margin against « non fonctoriel » for the coordinate description over a complete local ring. Pages 51–53 give the barycentric section and the « somme nulle » statement. Pages 41–47 give q, j and the reductions to Z/2 and Z/3 at j = 0 and j = 1. The transcription is heavily illegible exactly here: page 49’s opening, the « Dém. » of the example and most of pages 51 and 53 are \\ill{} or \\uncertain{}, and the statement of page 53 has illegible words in its subject (« La donnée d’un système \\ill{} portés sur S \\ill{} \\uncertain{équivalente} … »).',
    ours:
      'The reading supplies the identification with the quotient stack [(P¹ ∖ {0, 1, ∞})/S₃]. It also supplies the link to elliptic curves (X = C/±1, X′ the image of the non-zero 2-torsion points, s the image of the origin, the curve recovered only up to quadratic twist) and the translation into cubics. This pass disagrees with the reading on one point. For an arbitrary invertible sheaf 𝓜, rescaling the coordinate by u acts on x³ + bx + c by weights (2, 3), (b, c) ↦ (u²b, u³c), and not (u⁴b, u⁶c) as the reading says. Weights (4, 6) hold only when 𝓜 = 𝓛^⊗2 comes from a curve. Read with weights (2, 3), the triples form the μ₂-rigidification of M_{1,1}[1/6], the weighted projective stack P(2, 3) minus the discriminant, rather than M_{1,1}[1/6] itself.',
    literature: [
      'Web search (2026-10-10) for the μ₂-rigidification of the moduli stack of elliptic curves and for genus-0 curves with a section and an étale trisection. Result snippets state that M_{1,1} is a μ₂-gerbe over a rigidification isomorphic to P(2, 3). Those sources were not opened, and none of them mentions the trisection description.',
      'T. Phillips, « Points of bounded height in images of morphisms of weighted projective stacks … », arXiv:2201.10624 v5, § 5.1 (Prop. 5.1.7, rigidification of modular curves along μ₂, citing [AGV08, App. C]). Read: it does not state the triple, torsor or barycentre description.',
    ],
    status: 'candidate',
    settle:
      'This search was thin, and the pass expects a match. Look in Katz–Mazur, Arithmetic Moduli of Elliptic Curves, ch. 2 and the Legendre-family discussion of level-2 structures; in Deligne–Rapoport (1973) for M_{1,1}[1/2] and its coarse space; in Abramovich–Graber–Vistoli (2008) App. C and Abramovich–Corti–Vistoli (2003) on μ₂-rigidification; and in Fulton–Olsson, « The Picard group of M_{1,1} » (2010). All are cited from memory. Mark the entry matched if any of them states that genus-0 curves with an étale trisection and a disjoint section are classified by [(P¹ ∖ {0, 1, ∞})/S₃], or by zero-sum étale trisections of a line bundle (weights 2, 3). Before relying on the page-53 statement, re-read pages 49–53 on the facsimile (/transcribe-grothendieck).',
  },
  // Folder 121, find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, on the Opus 5.5 reading of 2026-10-03.
  {
    id: '121-coarsest-cell-decomposition',
    cote: '121',
    pages: '3–8, 13–16',
    kind: 'mathematical',
    claim:
      'For a Boolean algebra 𝓕 of subsets of a topological space that is closed under closure, whose members each contain a dense open subset of their closure, and in which every descending chain of closed members, each nowhere dense in the one before, terminates at ∅, every finite subfamily 𝓛 ⊂ 𝓕 admits a finite partition into members of 𝓕 that satisfies the frontier condition and makes each element of 𝓛 a union of pieces, and among such partitions there is one coarser than all the others (with connected pieces when components of locally closed members are finite in number and in 𝓕).',
    basis:
      'Page 14 states the existence and the coarsest one and proves existence by induction, removing the nowhere-dense union of boundaries and using condition e) to stop; page 8 proves that boundaries are nowhere dense; page 16 gives the connected-pieces version, with « plus grossière » written plainly (on page 14 the word replacing a struck « fine » is hard to read, and « grossière » is the transcription’s reading from the sense).',
    ours:
      'The page asserts that the result is the coarsest without justifying it. The argument for coarsest-ness is the edition’s: a cell meeting ∂Y lies in ∂Y. The reading also completes the page-8 proof that boundaries are nowhere dense, whose end is heavily crossed out, and reads condition d) with the interior taken relative to the closure rather than in X as the literal line says.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check whether a coarsest frontier-condition partition compatible with a finite family is in the o-minimal literature (van den Dries, Tame topology and o-minimal structures, ch. 4; Coste, An introduction to o-minimal geometry; Loi on definable stratifications) or in the PL and stratified-space literature: King–Sullivan’s intrinsic stratification of CS sets, which coarsens all others, is the nearest known statement, though there regularity is imposed and not a bare frontier condition. Then check whether the abstract axioms a) to e) on a single space appear anywhere. One web search on this pass (2026-10-10) found no statement of the coarsest version. That is not a reading of these sources, so the status stays unsearched.',
  },
  {
    id: '121-cell-decomposition-open-quotient',
    cote: '121',
    pages: '10–13',
    kind: 'mathematical',
    claim:
      'The finite partitions of a space X that satisfy the frontier condition and have pairwise distinct closures correspond exactly to the finite T₀ quotients X → I whose quotient map is open: the incidence order is the specialisation order of I, and the frontier condition is the openness of the map.',
    basis:
      'Page 13 shows that condition (1), the closure of each cell being a union of cells, means that the quotient map is open, and that condition (2) means that the finite quotient is « primitif », defined on the page as \\overline{\\{i\\}} = \\overline{\\{j\\}} ⇒ i = j. Pages 10–11 show that the cells are then locally closed, and that (1) together with local closedness gives back (2).',
    ours:
      'The word « primitif » is an uncertain reading, but the page writes out its definition, which is the T₀ condition. The reading writes out the proof that (1) is equivalent to the map being open, where the page only states the conclusion.',
    literature: [
      'L. Waas, J. Woolf, S. Yokura, On stratifications and poset-stratified spaces, arXiv:2407.17690 (2024): Prop. 4.1 (frontier condition ⇔ decomposition map open, for Alexandrov decompositions), Lemma 2.7 and Cor. 4.3 (locally closed strata ⇔ poset)',
      'D. Tamaki (2017), Lemma 2.3, as cited in Remark 4.2 of the paper above (openness of a poset-stratified space characterised by X_i ⊂ closure(X_j) ⇔ i ≼ j)',
      'L. Waas, Decomposition spaces and poset-stratified spaces, arXiv:1912.00339 (open decomposition map: proset is a poset iff pieces are locally closed)',
    ],
    status: 'matched',
    settle:
      'Settled as a match: this is the known equivalence between the frontier condition and openness of the map to the Alexandrov space of strata (Waas–Woolf–Yokura 2024, Prop. 4.1, which traces it to Tamaki 2017). Proposition 4.1 was checked through the arXiv HTML text. The Tamaki lemma was not opened and is cited at second hand. Kept as a killed candidate.',
  },
  // 134-2, find-novelty pass on Opus 5.5 (claude-opus-5-5), the model the reading names, 2026-10-10.
  // No mathematical entry: every statement of pp. 38–77 that the reading situates is either a match it
  // already footnotes (Giraud, Deligne SGA 4 XVIII, Breen 1994, Lurie HTT/HA, Hoyois 2018, Artin–Milne,
  // Bégueri, Barwick–Glasman–Haine), a programme the letters sketch without establishing, or a
  // statement the reading had to correct by one degree (pp. 48, 54). Two codicological entries follow.
  {
    id: '134-2-breen-letters-printed',
    cote: '134-2',
    pages: '37–77',
    kind: 'codicological',
    claim:
      'The 1983 note to the Appendix and the three 1975 letters to Breen (pp. 37–77), which the modernised reading treats as left out of the printed Pursuing Stacks, are printed as the Appendix to Chapter I in an available edition of the 1983 typescript.',
    basis:
      'The reading’s header and résumé say Maltsiniotis’s vol. I “ne contient pas” the Breen letters and read them for that reason. The same pages, from “In this appendix, I am including three letters to Larry Breen” through “Villecun 5.2.1975”, “Villecun le 17.2.1975” and “Villecun 17/19 July 1975 / Dear Larry”, appear as “Appendix: Three letters to Larry Breen” in the Scrivener edition extended by Carmona and Buchholtz.',
    ours:
      'The pass disagrees here with the reading, made on the same model: the reading says the printed volume does not include these letters. The pass checked the Carmona–Buchholtz edition only. It did not see the SMF volume, so the reading’s statement about that volume itself is unverified, not refuted. The Künzer–Brown–Maltsiniotis note says vol. I “comportera les cinq premiers chapitres du tapuscrit”, and the p. 14 slip places the Appendix inside Chapter I. Both make it likely that vol. I prints it too.',
    literature: [
      'A. Grothendieck, Pursuing Stacks, Scrivener edition extended by M. Carmona with U. Buchholtz, arXiv:2111.01000v2 (2021), Appendix: Three letters to Larry Breen (text searched for “Breen”, “Villecun”, “Dear Larry”)',
      'M. Künzer (ed.), with R. Brown and G. Maltsiniotis, Correspondance Alexandre Grothendieck – Ronald Brown, preprint (agrb_web.pdf, Maltsiniotis’s web page), “Note des éditeurs” and letters of 25.3.1982, 15.4.1982, 24.5.1982',
    ],
    status: 'matched',
    settle:
      'Open the table of contents of Maltsiniotis (ed.), À la poursuite des champs, vol. I, SMF Documents mathématiques 20 (2022). If the Appendix to Chapter I is there, the reading’s scope statement and résumé need correcting, which is /modernize-grothendieck’s work. That correction would not make the reading’s commentary on these pages wrong.',
  },
  {
    id: '134-2-july-letter-junction',
    cote: '134-2',
    pages: '56–57',
    kind: 'codicological',
    claim:
      'In the 1983 typescript as printed, the July 1975 letter runs without a break from the last line of folder p. 56 to the first line of p. 57. The jump in the letter’s own pagination (1 to “-12-”) and in Grothendieck’s 1983 pagination (40 to 42) therefore does not, on this evidence, mark text lost from this folder.',
    basis:
      'In the transcription, p. 56 ends “Thus I am entirely in agreement with your observations on p. 5.” and p. 57 begins “On the other hand, I am still intrigued by the following question”. In the arXiv:2111.01000v2 edition the two sentences are consecutive in one paragraph sequence of App. 9, with nothing between them. The transcription notes “-12-” overwritten to 42 on p. 57 and says “La suite de la p. 56 n’est donc pas immédiate”.',
    ours:
      'This disagrees with both the transcription note on p. 57 and the reading’s section “Ce que le dossier n’établit pas”, which say pp. 2–11 of the letter are missing from the folder and infer that they held the replies to Breen’s questions 1–6. The pass compared the text with one printed edition, not with the facsimile. If that edition was set from a copy that also lacked a leaf 41, the agreement proves nothing, so the explanation is still open: Grothendieck may have cut the letter in 1983, or a leaf may have been lost before the edition’s copy was made.',
    literature: [
      'A. Grothendieck, Pursuing Stacks, arXiv:2111.01000v2 (Carmona–Buchholtz edition), Appendix, opening of the letter of 17/19 July 1975 and App. 9',
      'Correspondance Grothendieck – Brown (Künzer ed., preprint), letter of R. Brown, 24.5.1982, on the difficulty of reading the copy of the “final long letter” and his informal translation',
    ],
    status: 'candidate',
    settle:
      'Look at the facsimile of pp. 56–57 for the struck or overwritten 1983 page numbers and any trace of a leaf 41. Then compare with Brown’s 1982 translation of the July letter (its pp. 2–11) or with the SMF vol. I edition’s note on this letter. If those pages hold mathematics answering Breen’s questions, the 1983 typescript omits them by design, and the transcription note and reading should say “omitted in 1983” rather than “missing from the folder”.',
  },
  // Folder 6 — /find-novelty pass on Opus 5.5 (claude-opus-5-5), reading 6.modern.tex made on Opus 5.5 (same model). No literature was searched in this pass.
  {
    id: '6-ordinary-moduli-complete-intersection',
    cote: '6',
    pages: '52–56',
    kind: 'mathematical',
    claim:
      'For a polarisation of any degree, including degree divisible by p, the local ring at a point of the moduli scheme of polarised ordinary abelian varieties in characteristic p (fixed polarisation degree, Jacobi level structure) is a complete intersection, locally irreducible, with smooth reduced scheme, because the formal moduli of compatible pairs of extensions is the kernel of a homomorphism α − β of formal tori, a formal group of multiplicative type.',
    basis:
      'Pages 52–53 identify the formal moduli of an extension of an étale Barsotti–Tate group by one of multiplicative type with a torsor under the formal torus T_p(M_0)^∨ ⊗ N_0; page 54 represents the compatible pairs (ξ, ξ′) as the kernel of α − β : G × G′ → H; pages 55–56 apply this to polarised ordinary abelian varieties and conclude « intersection complète », « loc. irréductible », « M_red lisse sur k », with smoothness when the degree is prime to p.',
    ours:
      'Much of pages 52–56 is illegible (fast, pale hand); the reading reconstructs the argument from its formulas and says so. « M_0 étale » is an hypothesis the reading supplies. Several words carrying the conclusion are \\uncertain on the page: « équivaut à » (p. 52), « lisse sur k » and « ordinaires » (p. 56), and the name of α − β and its two terms (p. 55). The page starts mid-sentence: its first premise is on a leaf not in the folder.',
    literature: [],
    status: 'unsearched',
    settle:
      'The case of degree prime to p is matched (Katz, Serre–Tate local moduli, 1981; Deligne–Illusie 1981), and the reading says so. What is open is the case p | degree: check Norman and Oort, Moduli of abelian varieties (Ann. of Math. 1980), Oort’s 1971 Compositio paper on local moduli of abelian varieties, and de Jong, The moduli spaces of polarized abelian varieties (Math. Ann. 1993), for the local structure of the ordinary locus of A_{g,d} when p divides d. If it is stated there, mark matched.',
  },
  {
    id: '6-formal-group-not-in-abelian-variety',
    cote: '6',
    pages: '49–50',
    kind: 'mathematical',
    claim:
      'Over a finite field k, twisting the formal group of a supersingular elliptic curve E (all endomorphisms defined over k) by a unit θ of End(E) ⊗ Z_p whose reduced norm is transcendental gives a form of G_{1,1} that embeds in the formal group of no abelian variety over k, nor over any finite extension of k, because the Weil conjectures force det(θφ) to be algebraic.',
    basis:
      'Page 49 sets up E, the quaternion order 𝒜 = End(E) ⊗ Z_p, the twist φ′ = θφ, and the Weil obstruction on det φ′ = det φ · det θ; page 50 completes it in one line: « il est facile de trouver Θ unité de 𝒜 tel que det Θ ne soit pas algébrique ».',
    ours:
      'The reading supplies why such a θ exists (the reduced norm 𝒜* → Z_p* is surjective, and Z_p* contains transcendental elements) and why a finite extension of k changes nothing (φ′ is replaced by a power). On the page, « unité », « formelle » and « à multiplic. complexe définie dans k » are \\uncertain, and a four-line struck block on page 49, read only in fragments, sits in the middle of the Weil step.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look for the statement that not every p-divisible (or formal) group over a finite field is a subgroup, up to isogeny, of that of an abelian variety, with the transcendental-norm twist or the integrality of the Frobenius characteristic polynomial as the obstruction: Tate, Endomorphisms of abelian varieties over finite fields (1966); Honda (1968); Manin, The theory of commutative formal groups over fields of finite characteristic (1963); and Oort’s surveys on p-divisible groups of abelian varieties. It is likely to be standard; if it is stated in any of them, mark matched.',
  },
  {
    id: '6-same-formal-group-not-isogenous',
    cote: '6',
    pages: '47–48',
    kind: 'mathematical',
    claim:
      'Over an algebraically closed field of characteristic p there are simple abelian surfaces with the same formal group Ĝ_m × G_{1,1} that are not isogenous, so Barsotti’s isogeny question has a negative answer once the supersingular hypothesis is dropped; the argument is that the simple ones form a non-empty open U of Manin’s two-dimensional family, the isogeny class of each is defined over finite extensions of its field of definition, and points of U of different transcendence degree over F_p therefore cannot be isogenous.',
    basis:
      'Pages 47–48: Manin’s family N of dimension 2, the non-simple members as images of the ordinary modular curve under E ↦ E × F, the open U of simple surfaces, the discreteness of an isogeny class, and the transcendence-degree comparison (0, 1 or 2).',
    ours:
      'The page reads « de dim 2 au plus » where the argument needs 1; the reading corrects it, and the digit is \\uncertain on the page. The reading supplies the justification of discreteness (finitely many finite subgroups of each order of Ĝ_m × G_{1,1} × Q_p/Z_p). The sentence asserting discreteness is partly \\ill, and « hypersingulière » throughout is \\uncertain.',
    literature: [],
    status: 'unsearched',
    settle:
      'Probably a match: isogeny classes are countable while the p-rank-one stratum of A_2 is positive-dimensional. Check Manin 1963 (Russian Math. Surveys 18), Oort, Subvarieties of moduli spaces (Invent. Math. 1974), and Oort, Foliations in moduli spaces of abelian varieties (JAMS 2004), on isogeny leaves; mark matched with the reference if the statement is there.',
  },
  {
    id: '6-leaves-35-36-reversed',
    cote: '6',
    pages: '33–36',
    kind: 'codicological',
    claim:
      'Pages 35 and 36 are in the wrong order: the notes on the reduction of elliptic curves read 33, 34, 36, 35.',
    basis:
      'Page 36 ends on « Je conjecture » after the case of non-integral j (multiplicative reduction); page 35 opens « que cet élément a une image non nulle dans Z_p, donc que l’extension ne provient pas d’une extension de groupes p-divisibles sur A », which can only continue that case, and then moves on to 2º (characteristic p).',
    ours:
      'The transcription keeps the facsimile order; the reordering is the reading’s, and it rests on the text, not on the paper.',
    literature: ['Transcription 6, batch 2 (batch-02.fr.tex), pages 33–36', 'Reading 6.modern.tex, section on pages 32–36'],
    status: 'candidate',
    settle:
      'A person checks against the facsimile whether 35 and 36 are the two sides of one leaf (then the order is a matter of which side was scanned first) or two leaves bound out of order.',
  },
  {
    id: '6-eleven-leaves-not-in-sequence',
    cote: '6',
    pages: '38–39, 52, 61',
    kind: 'codicological',
    claim:
      'From facsimile page 39 to the end, the archivists’ pencil numbers run eleven ahead (39 is pencilled 50, 66 is pencilled 77), so eleven leaves pencilled 39–49 are not in the folder at that place; the folder was reordered after pencilling, and page 52 (opening mid-sentence) and pages 61–62 (using a duality triangle defined nowhere in the folder) both continue text that is not here.',
    basis:
      'Pencil numbers agree with the facsimile from 21 to 38 (batch 2 header) and are offset by eleven from 39 through 66 (batch 2, 3 and 4 headers and the \\note under the Tate–Hodge cover); page 52 begins « S^(n) → G … » with no preceding sheet; pages 61–62 use ℓ_G → Δ(G) → ℓ̌_{G*}[1] without definition.',
    ours:
      'The transcriptions record the offset; linking it to the mid-sentence opening of page 52 and the undefined triangle of pages 61–62 is this pass’s inference, not a check that the missing leaves are the ones those pages continue.',
    literature: ['Transcription 6, batches 2–4 (batch-02.fr.tex, batch-03.fr.tex, batch-04.fr.tex), headers and pages 39, 52, 61'],
    status: 'candidate',
    settle:
      'A person checks the pencil numbers at the 38/39 junction on the facsimile, then looks for leaves pencilled 39–49 in the neighbouring folders of the « Cristaux » group (cotes 4–9) and checks whether one of them supplies the start of page 52 or the definition of the triangle of page 61.',
  },
  {
    id: '34-wild-inertia-outer-pi1',
    cote: '34',
    pages: '163–167, 169–180',
    kind: 'mathematical',
    claim:
      'For any X_K of finite type over the fraction field of a henselian trait, an open subgroup of the inertia acts tamely, by outer automorphisms, on the maximal prime-to-p quotient of π₁(X_K̄): the wild inertia has finite image in Out(π₁^(p′)(X_K̄)).',
    basis:
      'Exposé VI, Théorème 1.3 (p. 166), with Lemme 1.2.6 showing that tameness in Aut and in Out agree; the proof is a chain of reductions — to the geometrically normal case by van Kampen descent with P-invariant descent paths (2.1), to a smooth affine curve by generic hyperplane sections (2.2), to a regular model with normal-crossings special fibre (2.3), then to the versal deformation of a nodal curve (Lemme 3.1), where the tame π₁ of the base is abelian by Abhyankar (3.2).',
    ours:
      'The reading adds that the statement, for curves, follows from semistable reduction, and says it does not know whether the general form was published. Two steps are not carried out in the folder: the regular model with normal-crossings fibre is sent to « un exposé ultérieur » (p. 174), and Lemme 3.1 to an exposé VII « à l’aide de la théorie de Schlessinger » (p. 178); the transcription reads « locale » in the theorem’s title with doubt. This pass ran on Opus 5.5, the model that made the reading.',
    literature: [
      'M. Kisin, « Prime to p fundamental groups, and tame Galois actions », Ann. Inst. Fourier 50 (2000), no. 4, 1099–1126 — Introduction and Theorem 2.1: for any variety U over a complete discretely valued field of residue characteristic p, the image of the wild inertia in Out(π₁^(p′)_geom(U)) is finite; proved by de Jong’s alterations and a logarithmic purity theorem, not by reduction to curves',
    ],
    status: 'matched',
    settle:
      'Settled for the tameness clause: it is Kisin’s Theorem 2.1 (the passage from « finite image of P » to « an open I′ acts tamely » is immediate, the kernel being open in P). The finite-generation clause is the classical topological finite generation of π₁^(p′) in characteristic p and was not looked up separately. Kept as a killed candidate, since the reading left open whether the general statement had appeared. Kisin assumes the base field complete; the folder reduces to that case by I 3.13.',
  },
  {
    id: '34-multiparameter-tame-monodromy',
    cote: '34',
    pages: '167, 175–180',
    kind: 'mathematical',
    claim:
      'Over a strictly local base S of any dimension, for X̄ projective and flat with closed fibre having normal crossings outside codimension 2, smooth with relative normal-crossings boundary over an open U ⊂ S, the image of π₁(U) in Out(π₁^(p′)) of a geometric fibre is an abelian group of order prime to p — of rank at most ν, the number of double points, in relative dimension 1.',
    basis:
      'Exposé VI, Théorème 1.4 (p. 167), with the reduction of 2.4 (p. 176) from any relative dimension to relative dimension 1 by a generic hyperplane over the strict localisation of S[t₁,…,t_r], and the relative-dimension-1 case through the versal nodal curve (Lemme 3.1, unproved there) whose base has tame π₁ ≃ Ẑ′(1)^ν; on a trait the generator acts by h₁^{n₁}⋯h_ν^{n_ν}, n_i the thickness of the i-th node (p. 179).',
    ours:
      'The hypotheses rest on uncertain readings: the transcription has an \\ill{} and an uncertain « les composantes des » in (a), an uncertain « schéma » for X̄, and a long struck and overwritten passage between (b) and (d), so the reading « gives only what emerges ». Lemme 3.1 is not proved in the folder. That the h_i are Dehn twists and the local equation xy = t^{n_i} is the reading’s gloss.',
    literature: [
      'M. Kisin, Ann. Inst. Fourier 50 (2000), Corollary 1.16 and Theorem 2.1 — tameness over a discretely valued field (one-parameter base), not the multi-parameter abelian statement; only the introduction and §2 were read',
      'T. Oda, « A note on ramification of the Galois representation on the fundamental group of an algebraic curve II », J. Number Theory 53 (1995), §2.7 — the outer inertia action recovered from edge twists of the reduction graph (cited via Betts–Dogra, not read directly)',
      'M. Asada, M. Matsumoto, T. Oda, « Local monodromy on the fundamental groups of algebraic curves along a degenerate stable curve », J. Pure Appl. Algebra 103 (1995), Theorems 2.1–2.2 — multi-parameter degeneration of a stable curve (cited via Betts–Dogra, not read directly)',
      'L. A. Betts, N. Dogra, « The local theory of unipotent Kummer maps and refined Selmer schemes », arXiv:1909.05734, §3.1 and Theorem 3.1.6 (non-abelian Picard–Lefschetz, edge twists raised to edge lengths)',
    ],
    status: 'unsearched',
    settle:
      'The relative-dimension-1 case, with h = ∏ h_i^{n_i}, appears to be the Oda / Asada–Matsumoto–Oda description; read AMO95 §2 to confirm, and if so the open part is only relative dimension ≥ 2 with fibres normal-crossings off codimension 2. For that part, look in the logarithmic literature (Fujiwara–Kato log purity; Illusie, « An overview of the work of K. Fujiwara, K. Kato and C. Nakayama on logarithmic étale cohomology », Astérisque 279, 2002) and in Kisin 2000 §1. Before any search counts, the hypotheses (a)–(d) must be re-read against the facsimile of p. 167: the status stays unsearched because the statement rests on unread words.',
  },
  {
    id: '34-lci-local-1-asphericity',
    cote: '34',
    pages: '153–155',
    kind: 'mathematical',
    claim:
      'If f : X → S over a strictly local trait is flat, its closed fibre X₀ is a local complete intersection, and the non-smooth locus Z of X₀ has codimension ≥ 2 in X₀, then f is locally 1-aspherical for primes ≠ p; in particular, for f proper, specialisation H¹(X₀, G) → H¹(X_η̄, G) is bijective for every finite group G of order prime to p.',
    basis:
      'Chapter « IV », 5.5–5.6 (pp. 153–154): local 1-acyclicity at the strict generisations reduces 1-asphericity at x to H^i(V(h), G) = 0 for i ≤ 1 on the punctured strict localisations of the finite base changes X(h), which holds when X(h) is a complete intersection of dimension ≥ 3 at x (Grothendieck’s purity, SGA 2 X), i.e. X₀ complete intersection of dimension ≥ 2 at x; the smooth points are handled by local 1-asphericity of smooth morphisms.',
    ours:
      'The page carries the statement; the transcription marks « pour » and « soit » in the hypothesis and « alors » in the conclusion as uncertain, readings of the syntax, not of the mathematics. The word « si » before « les intersections complètes » on p. 154 is struck and re-added in the transcription, so the condition is read rather than written. The induction over generisations is the one set up in 5.1–5.2, whose Lemme 5.3.3 is left unproved (« Donner démonstration ! »), but 5.6 goes through 5.5 and SGA 2 purity rather than through 5.3.3.',
    literature: [
      'L. Illusie, « Grothendieck and vanishing cycles », Ann. Fac. Sci. Toulouse Math. (6) 30 (2021), 83–115 — full text searched for complete intersection, depth and asphericity; not found',
      'Web search (2026-10-10) on specialisation of the prime-to-p fundamental group for lci special fibres with singular locus of codimension ≥ 2; nothing relevant found',
    ],
    status: 'candidate',
    settle:
      'Read SGA 7 I, Exposé I (Deligne’s « Résumé des premiers exposés de A. Grothendieck »), the part on vanishing cycles and depth, and SGA 2 XIII–XIV: if the statement or its 1-asphericity form is there, mark matched. The cohomological shadow for d = 0 is the classical simple-connectedness of the Milnor fibre of an isolated complete-intersection singularity of dimension ≥ 2 (Hamm, over ℂ), which is a reason to expect it is known, not a search.',
  },
  {
    id: '36-h1-invariant-cycle-defect',
    cote: '36',
    pages: '60–70',
    kind: 'mathematical',
    claim:
      'For X projective and regular over a strictly henselian trait, with O_S ≅ f_*O_X, and n prime to p, there is an exact sequence 0 → ₙΓ → H¹(X, μₙ) → H¹(X_η̄, μₙ)^I → Ker(wₙ) → 0, where Γ is the group of divisors supported on the special fibre modulo X₀ and w : Γ → NS(X₀); in the limit, H¹(X, Z_ℓ(1)) → H¹(X_η̄, Z_ℓ(1))^I is injective with cokernel R ⊗ Z_ℓ, R = Ker w cyclic of order dividing gcd(dᵢ), and an isomorphism when X_η has a zero-cycle of degree 1.',
    basis:
      'The typescript of pages 60–63 states a)–d) and Corollaries 9, 10, 15 without proof; the manuscript of pages 64–68 proves the sequence for n prime to p when X_η has a zero-cycle of degree 1 (Kummer, the exact sequence 0 → Γ → Pic X → Pic X_η → 0, the snake lemma, and the injectivity of Pic(X)ₙ → Pic(X₀)ₙ for S complete), and page 70 drops the zero-cycle hypothesis. That Ker w is torsion (assertion b) is referred on page 68 to Raynaud, « Spécialisation du foncteur de Picard », th. 3. The transcription of pages 64–68 carries many \\uncertain{} and \\ill{} words in the linking sentences (batch 4), though none of the displayed sequences rests on one; page 70 says the torsion of R holds « au moins modulo résolution des singularités ».',
    ours:
      'The reading corrects two typed statements: d^t = p^h d with p^h only divisible by gcd(μᵢ), not equal to it, and Br(X_η) for the page’s Br(X_η̄) in Corollary 10; and it gives ₙδ/ₙδ′ as the term after uₙ on page 64, where the page’s run of the sequence is of doubtful reading. The case n divisible by p (flat cohomology), Corollary 15 and the Mittag-Leffler step for ℓ = p are unproved in the folder and are not part of the claim. The pass reads the page-70 boxed formula as assuming R equal to the whole torsion of Γ, as the reading does; the claim keeps the typescript’s cautious « order dividing d ».',
    literature: [],
    status: 'unsearched',
    settle:
      'Read M. Raynaud, « Spécialisation du foncteur de Picard » (Publ. Math. IHÉS 38, 1970), §§ 6–8, and SGA 7 I, exposé IX, §§ 11–12 (component groups and the comparison of H¹ of a regular model with inertia invariants), then Bosch–Lütkebohmert–Raynaud, Néron Models, ch. 9. If the sequence with cokernel Ker wₙ, or the ℓ-adic form with defect R ⊗ Z_ℓ, is stated there, mark matched. Two web searches on 2026-10-10 returned no relevant result, and no source was read, so the status stays unsearched.',
  },
  {
    id: '36-orthogonality-regular-adic-base',
    cote: '36',
    pages: '73–76',
    kind: 'mathematical',
    claim:
      'The orthogonality of a toric part and a part of finite ℓ-power torsion under the Weil pairing holds over a complete regular noetherian J-adic base X = Spec A, not only over a discrete valuation ring: for flat commutative group schemes G, G′ over X restricting to abelian schemes on U = X − V(J), a divisorial correspondence ξ on A_U × A′_U, a flat subgroup H ⊂ G_Y with finite ℓ^ν-torsion and a torus T′ ⊂ G′_Y, φ_ξ(T_ℓ(H̃)|U, T_ℓ(T̃′)|U) = 0 at every point of U.',
    basis:
      'Page 73 states the theorem in this generality; pages 74–75 reduce, when A/J is of finite type over Z, to a complete discrete valuation ring with finite residue field and prove that case by Frobenius weights (q on the toric Tate modules and on T_ℓ(G_m), absolute value q^{1/2} on the abelian part); page 76 removes the finite-type hypothesis by writing V as a filtered union of subrings of finite type over Z. The statement on page 73 is legible except for three \\ill{} words before « en chaque pt »; the reduction steps on pages 73–74 and the linking words of pages 75–76 are read largely through \\uncertain{} and \\ill{}, and page 73’s last lines only « par bribes ».',
    ours:
      'The reading renames the page’s S as H, supplies the Galois-equivariance in the finite-field lemma, which the page states for « tout accouplement » and which is false without it, and reconstructs the reduction to a trait from page 74 where page 73 is illegible. The published orthogonality theorem (SGA 7 IX) gives the exact orthogonal; these pages give only the vanishing, and the claim is limited to it.',
    literature: [],
    status: 'unsearched',
    settle:
      'Read SGA 7 I, exposé IX (Grothendieck, « Modèles de Néron et monodromie »), §§ 2 and 4–5, to see whether the orthogonality theorem or its arithmetic proof is stated there over a regular complete adic base with arbitrary flat group schemes, rather than over a trait; then exposé VIII for the pairing. If the higher-dimensional form is there or in a later paper on degenerating abelian schemes (e.g. Faltings–Chai, Degeneration of Abelian Varieties, ch. III), mark matched. One web search on 2026-10-10 returned nothing relevant and no source was read.',
  },
  {
    id: '36-griffiths-conditional-l-adic',
    cote: '36',
    pages: '9–16',
    kind: 'mathematical',
    claim:
      'In any characteristic, for X smooth projective of dimension 2n and a Lefschetz pencil, if the inclusion of the generic hyperplane section Y satisfies a) a Lefschetz-type splitting by an algebraic correspondence and b) Coker(H^{2n−1}(X) → H^{2n−1}(Y)) contains no piece of coniveau n−1, then a cycle of X whose restriction to Y is algebraically trivial is homologically trivial up to torsion, so that Grif(Y) ⊗ Q has a subquotient mapping onto the primitive algebraic classes of X — an ℓ-adic Abel–Jacobi proof of Griffiths’s theorem conditional on a) and b).',
    basis:
      'The typescript « Le théorème de Griffiths par voie algébrique », nᵒˢ 1–5 (pages 9–15): the class u(x) ∈ H¹(S, R^{2n−1}f_*Z_ℓ(n)) of a primitive class, its functoriality under correspondences, the decomposition of an algebraically trivial cycle under a) and b) (nᵒ 2), its relative form (nᵒ 3), and the injectivity of the Griffiths homomorphism modulo the image of H¹(S, H^{2n−1}(X)) (nᵒ 4). Section 6 proves b) in characteristic 0 only; the author’s own margins say « pas prouvé » of 7.1 and 7.2, by which b) was to be reached in characteristic p.',
    ours:
      'Substantial. The page asserts that Grif(Y) ⊗ Q contains P^{2n}_alg(X) as a subspace; the reading shows the argument gives only a subquotient, and the claim takes the weaker form, which is the edition’s. The proof of nᵒ 4 is referred by the typescript to « calculs explicites essentiellement triviaux »; the argument through the vanishing part and H¹(P¹, j_*E) is the reading’s. The degree formula m = m′ + N − 2d′ (left blank on page 9) and Y_s̄ → X_s̄ (page 13) are the reading’s corrections. Hypothesis a) is a case of the standard conjectures and b) is unproved in characteristic p in the folder, so the claim is conditional twice over.',
    literature: [],
    status: 'unsearched',
    settle:
      'Read N. Katz, SGA 7 II, exposés XX and XXII, and S. Bloch, Lectures on Algebraic Cycles (1980), on Griffiths groups in positive characteristic; then C. Voisin, Hodge Theory and Complex Algebraic Geometry II, ch. 8, for the normal-function proof. If an ℓ-adic proof conditional on a Lefschetz-type correspondence and a coniveau hypothesis on the generic section is in print, mark matched. One web search on 2026-10-10 found only characteristic-0 work (Kahn, « Albanese kernels and Griffiths groups », Tunisian J. Math. 3, 2021, abstract only) and no source was read, so the status stays unsearched.',
  },
  // Folder 57 (Picard: annotated typescript, letters, 1962–[vers 1968]). Pass of 2026-10-10 on
  // claude-opus-5-5, the model of the reading (Opus 5.5, 2026-10-04). Most of the reading's
  // modern names are matches already footnoted there: Mumford's GIT for the theorem of p. 40,
  // Mazur–Messing for pp. 90–93, Raynaud–Gruson for problem A, Ferrand for pinching, Boutot for
  // the local Picard scheme. They are not repeated here. Below: one codicological entry, three
  // killed candidates, and three left open.
  {
    id: '57-csg-letters-transcribed',
    cote: '57',
    pages: '19–22, 72–78, 226–230',
    kind: 'codicological',
    claim:
      'Three letters of this folder are already transcribed and online, from scans of “Cote n° 57”. The Centre for Grothendieckian Studies (Grothendieck Institute, Mondovì) lists them on its transcriptions page: the undated letter to Murre (pp. 19–22, its L24d, dated there “1962 (?)”, draft October 2024), the letter to Murre of 18 July 1962 (pp. 72–78, its L25d), and the letter to Hironaka of 6 July 1962 (pp. 226–230, its L27d, draft April 2024).',
    basis:
      'The L27d and L24d PDFs open with “This transcription is derived from an unpublished scan provided by the Montpellier archive with the reference “Cote n◦ 57””. Their opening text is that of the transcription here: L27d starts “Neuilly July 6 1962 / Dear Hironaka, / I had a little thought over our conversation last tuesday”, and L24d starts “Dear Murre, / I am glad to hear that your are still willing to give the talk on unramified functors”, then states the quotient theorem of p. 19.',
    ours:
      'Neither the reading nor the transcriptions mention these editions. The pass read only the title pages and the opening paragraphs of L24d and L27d. It has not compared the texts line by line. L25d was listed but its URL returned an HTML page, not a PDF, on 2026-10-10, so that letter is identified from the listing alone. The listing labels L25d “French”, but pp. 72–78 here are in English. The pass has not settled whether the listing is wrong or L25d is another document.',
    literature: [
      'Centre for Grothendieckian Studies, Grothendieck Institute, transcriptions page (csg.igrothendieck.org/transcriptions/), entries for letters to J. Murre and H. Hironaka, read 2026-10-10',
      'A. Grothendieck, Letter to H. Hironaka, 6.7.1962, transcription ed. M. Carmona et al., CSG, draft April 2024 (L27d.pdf), title page and pp. 1–2 read',
      'A. Grothendieck, Letter to J. Murre, 1962 (?), transcription ed. M. Carmona et al., CSG, draft October 2024 (L24d.pdf), title page and opening read',
    ],
    status: 'matched',
    settle:
      'Collate L24d and L27d with batch-02 and batch-12, and record any reading where they differ. If L25d can be fetched, collate it with pp. 72–78 as well, and check whether it follows the fair copy (pp. 72–74) or the corrected earlier state (pp. 75–78). Then the reading’s header should name the CSG edition, which is /modernize-grothendieck’s work.',
  },
  {
    id: '57-conic-nonseparated-pic',
    cote: '57',
    pages: '213–218',
    kind: 'mathematical',
    claim:
      'For the family of conics xy = tz² over k[t], which degenerates into two lines at t = 0, the Picard functor is represented by a scheme locally of finite type but not separated. That scheme is ∐ₙ S_{I_n}, the line with its origin repeated once for each bidegree (p, q) with p + q = n.',
    basis:
      'Page 215 computes Pic(X) ≅ Pic(X₀) ≅ ℤ × ℤ through Lemma c) and the two sections (1, t) and (t, 1). Page 218 builds 𝔓 = ∐ S_{I_n} and says it represents the functor. The « Lemme f » of p. 216 claims non-representability, but its proof is struck through.',
    ours:
      'The reading corrects the degree of L_{D₁}|Y₁ to −1 (p. 214). It also keeps p. 218 over the unstruck statement of Lemme f, as the pages’ own later word.',
    literature: [
      'S. L. Kleiman, « The Picard scheme », in Fundamental Algebraic Geometry: Grothendieck’s FGA Explained (AMS, 2005), arXiv:math/0504020, Example 4.14 (Mumford’s example), read on ar5iv 2026-10-10',
    ],
    status: 'matched',
    settle:
      'Kleiman’s Example 4.14 uses x² + y² = t over ℝ[[t]], where the special fibre is a pair of conjugate lines and the Picard scheme does not exist. It notes that over ℂ[[t]] the functor is representable by a disjoint union of non-separated schemes. That is this folder’s split case, over a complete local base instead of k[t]. The match is to the phenomenon and its representing object, not to a word-for-word statement. A reader wanting the k[t] form should check Bosch–Lütkebohmert–Raynaud, Néron Models, ch. 8, before treating the global base as a difference.',
  },
  {
    id: '57-cone-completion-class-group',
    cote: '57',
    pages: '188–192',
    kind: 'mathematical',
    claim:
      'For the local ring S at the vertex of the affine cone over a regular X ⊂ ℙʳ, Pic(S − a) → Pic(Ŝ − â) is bijective if H¹(X, 𝒪_X(n)) = 0 for all n ≥ 1, and only if, when dim X = 1. For plane curves the condition fails exactly when the degree is at least 4.',
    basis:
      'Page 188 reduces the question to injectivity of Pic(Ê) → Pic(X), with Ê the formal completion of 𝕍(𝒪_X(1)) along its zero section. It identifies the successive kernels with H¹(X, 𝒪_X(n)). Page 191 states the criterion.',
    ours:
      'The exact threshold d ≥ 4 is the reading’s. The page gives the coarser sufficient condition deg 𝒪_X(1) < g − 1, which for plane curves means d ≥ 6.',
    literature: [
      'V. I. Danilov, « The group of ideal classes of a completed ring », Mat. Sb. 77(119) (1968), 533–541 (Math. USSR-Sb. 6 (1968)), not read; its theorem is known here only as restated below',
      'J. Manning, « Patching and multiplicity 2^k for Shimura curves », arXiv:1902.06878, Theorem 3.17 (attributed to Danilov 1968): for smooth projective V with very ample L, Cl(S) → Cl(Ŝ) is an isomorphism iff H¹(V, L^{⊗i}) = 0 for all i ≥ 1; read 2026-10-10',
    ],
    status: 'matched',
    settle:
      'As restated by Manning, Danilov’s theorem is the equivalence in every dimension, with Cl(S) in place of Pic(S − a), which is the same group when S is normal. The folder states sufficiency in general and necessity only for dim X = 1. Read Danilov 1968 to confirm the hypotheses: smoothness, projective normality. The page’s further remark, that the henselisation S^h may already have the completion’s local Picard group, is not covered by this match.',
  },
  {
    id: '57-ns-p-divisibility-generization',
    cote: '57',
    pages: '288–289',
    kind: 'mathematical',
    claim:
      'Over a mixed-characteristic discrete valuation ring, there is a product of abelian schemes C = A × B^∨ with a section ū of NS_{C/Y} that is divisible by p on the special fibre but not globally. Divisibility in the Néron–Severi scheme does not pass to generizations.',
    basis:
      'Page 288 takes flat finite subgroups F, G of an abelian scheme X with F₁ ⊄ G₁ and F₀ ⊂ G₀. It sets A = X/F, B = X/G and factors pβ through u : A → B. Then u₀ ∈ p Hom(A₀, B₀) but u ∉ p Hom(A, B). Page 289 transports u into NS_{C/Y} through the correspondence summand Hom(A, B).',
    ours:
      'The reading replaces the page’s condition (iii), pF₁ = G₁, by pF₁ ⊂ G₁, because with (ii) the page’s equality is incompatible with flat subgroups of the same order. It also moves the choice of F, G into one supersingular elliptic factor, where the subgroup of order p of the special fibre is unique. The page claims uniqueness for the whole product, which is false for a product of two supersingular curves. The statement here is therefore the edition’s repair of the realisation. The argument of p. 288 is the page’s.',
    literature: [
      'D. Maulik and B. Poonen, « Néron–Severi groups under specialization », Duke Math. J. 161 (2012), Proposition 3.6 (a), (b) (cokernel of specialization torsion-free, after ⊗ ℤ[1/p] in characteristic p) and Example 3.12, read 2026-10-10 from the author’s PDF',
    ],
    status: 'matched',
    settle:
      'Maulik–Poonen’s Example 3.12 is the same phenomenon by the same mechanism. A p-isogeny of elliptic curves over a finite extension of ℤ_p gives End of conductor p generically and maximal order on the special fibre. This yields p-torsion in coker(NS((E′ × E′)_K) → NS((E′ × E′)_k)). The folder’s version uses a quotient by two subgroups and the summand Hom(A, B) of NS(A × B^∨), not endomorphism orders. That is a different construction of the same counterexample type, not a separate result.',
  },
  {
    id: '57-generic-hyperplane-h1-injective',
    cote: '57',
    pages: '98–99',
    kind: 'mathematical',
    claim:
      'For X ⊂ ℙʳ normal, integral, of dimension ≥ 2 over an algebraically closed field, and Y_K̄ the generic hyperplane section over the algebraic closure of k(t₁, …, t_r), H¹(X, G) → H¹(Y_K̄, G) is injective for G = 𝐆_a and for finite commutative G, μ_p and α_p included. As a corollary, the kernel of Pic^τ_{X_K̄} → Pic^τ_{Y_K̄} is a finite unipotent p-group.',
    basis:
      'Page 98 states the theorem and reduces it to Corollaries 1–4: H¹(𝒪), π₁ via Bertini and Lefschetz–Grauert, α_p, μ_p. Page 99 uses Cartier to embed H¹(X, α_p) and Pic(X)[p] into H⁰(X, Ω̃¹), and then the « presque triviale » injectivity of H⁰(Ω̃¹) under restriction. The description of G on p. 98 (« affine sans composantes conn. (gpe … ou gpe alg. fini) ») is read with \\uncertain{} and \\ill{}, and nearly every word of the p. 99 corollary is \\uncertain{}.',
    ours:
      'The pass notes a tension the reading does not mention. As stated, Corollaries 1 and 4 would give a kernel with no non-trivial points (injectivity on every Pic[n]) and zero Lie algebra (injectivity on H¹(𝒪)). Such a kernel is trivial, which is stronger than the page’s own corollary. Either the page’s corollary undersells the theorem, or Corollary 1 fails in characteristic p, where H¹(X, 𝒪_X(−1)) need not vanish. The reading reproduces both without remark. This is the pass’s own inference, not checked against any source.',
    literature: [
      'S. L. Kleiman, « The Picard scheme », arXiv:math/0504020, Remark 5.8, read on ar5iv 2026-10-10: for a general hyperplane section and r ≥ 2, ker(Pic⁰_X → Pic⁰_Y) is finite and unipotent by Kleiman, SGA 6 XIII, Lemma 3.11 and Remark 3.12 (not read), and trivial in characteristic 0 by Mumford',
    ],
    status: 'unsearched',
    settle:
      'Read SGA 6 XIII, 3.11–3.12, for the Pic^τ and generic-section forms. Then test Corollary 1 (H¹(X, 𝒪_X) → H¹(Y_K̄, 𝒪) injective) against the known characteristic-p failures of Kodaira vanishing, Raynaud’s surfaces with H¹(L⁻¹) ≠ 0 for L ample. If Corollary 1 fails there, the theorem of p. 98 is refuted for 𝐆_a and α_p, and only the finite unipotent kernel of the corollary stands, which is then matched by Kleiman. The status stays unsearched because the statement’s scope rests on uncertain readings and SGA 6 XIII was not read.',
  },
  {
    id: '57-rigid-subgroups-one-fibre',
    cote: '57',
    pages: '42–49',
    kind: 'mathematical',
    claim:
      'Take S locally noetherian and connected, and G a group scheme of finite type over S. Two closed subgroup schemes of G that are “rigid” (commutative, flat, with geometric fibres the schematic closure of their prime-to-residue-characteristic torsion) and that agree on one fibre are equal. Hence two homomorphisms out of a rigid group that agree on one fibre are equal, and rigid subgroups descend uniquely along fppf covers with geometrically connected fibres.',
    basis:
      'Page 44 proves a lemma: finite étale subschemes of an unramified S-scheme that agree at one point agree everywhere. Page 45 states the Théorème de rigidité, and pp. 46–49 give the corollaries. The remark of pp. 50–51 notes that two étale subgroups of degree p of an abelian scheme over a DVR of residue characteristic p can have the same special fibre and still differ.',
    ours:
      'The definition on p. 42 is read with many \\ill{}: condition (ii) is fixed only by its boxed « ${}_{\\ell^k}(\\overline{G}_s)$ », and condition (iii), a finiteness clause, cannot be read. The theorem’s own statement on p. 45 is legible, apart from one \\uncertain{} « soit ». Its proof, which refers to « démonstration donnée plus haut » in the missing author pages 1–3, is not in the folder. The reading treats the notion as “torsion first to p dense”, and so does this entry.',
    literature: [],
    status: 'unsearched',
    settle:
      'Compare with SGA 3, Exp. IX–X (rigidity of groups of multiplicative type) and Exp. XV, and with Mumford, GIT 6.1 (rigidity for abelian schemes). Both theorems cover special cases of the notion: tori and abelian schemes are rigid in this sense. The question is whether the unified “prime-to-p torsion dense” hypothesis, covering for instance non-split extensions of an abelian scheme by 𝐆_a in characteristic 0, appears in print. A general web search on 2026-10-10 found nothing beyond the standard density of prime-to-ℓ torsion in tori and abelian varieties, and that is not a search of the named sources.',
  },
  {
    id: '57-analytic-pic-completion-criterion',
    cote: '57',
    pages: '226–228, 247–271',
    kind: 'mathematical',
    claim:
      'Let f : X → Y be a proper morphism of complex analytic spaces and y ∈ Y. The map from the germ Picard group (R¹f_*𝒪*_X)_y to lim Pic(X_n) is an isomorphism if and only if (R¹f_*𝒪_X)_y has finite length. The system (Pic(X_n)) is Mittag-Leffler. X is projective over a neighbourhood of y iff every X_n is projective. Via GAGA the same holds for X proper over Spec of an analytic algebra.',
    basis:
      'The typed letter to Hironaka (pp. 226–228) states (i)–(iii), (i bis) and Corollary 1, legibly. The draft of pp. 247–271 proves them from Grauert’s comparison theorem, the exponential sequence and the five lemma: w^i is injective, and bijective iff u^i is surjective (Prop. 1.5, Remark 1.7, Cor. 1.8, Th. 2.1, Cor. 2.2).',
    ours: null,
    literature: [],
    status: 'unsearched',
    settle:
      'Look for the “iff finite length” criterion and the projectivity corollary in Bingener’s work on formal and analytic Picard groups, in Artin’s approximation papers (1968–1969), and in SGA 2 XII and EGA III 5.4. The algebraic projectivity statement for X proper over a complete local ring (X projective iff every X_n is) is classical, EGA III 5.4.5. The candidate is the analytic germ version and its necessary-and-sufficient condition (iii). The same letter is online as a CSG transcription (see 57-csg-letters-transcribed); that is the same text, not a literature match.',
  },
// 136: three candidates. Pass: Opus 5.5 (claude-opus-5-5) on an Opus 5.5 reading (% Pass header of 136.modern.tex, 2026-10-10). Dropped as matches the reading already footnotes: Lucas/Kummer (pp. 19–22), the Dirichlet evaluation of the Stokes integral (p. 140, the edition's own), Dold–Puppe/Dold–Kan, Eilenberg–Zilber, the décalage formulas, Serre–Cartan on K(F_p,n), Breen's Ext(G_a,G_a) (pp. 356–375, notes attributed to nobody), the divided-power filtration of Z_2 (p. 240). Dropped as repaired by the edition: the negative-degree proposition of p. 42 (p-divisible for « divisible »), Γ^iΨ and Sym^iΨ « are K(k,i) » (p. 226, false as written).
  {
    id: '136-pd-de-rham-shadows',
    cote: '136',
    pages: '5–10, 226–232',
    kind: 'mathematical',
    claim:
      'For the simplicial k{T}-algebra C^{p,q} = Γ^p Φ ⊗ Λ^q Ψ (divided-power forms on the simplex Σ X_i = T), the cohomology of its sections over any simplicial set X is H^q(X, k) in every complementary degree p ≥ 0, so that, graded by total degree, H^{•,q} is the truncation τ_{≥q}(H^q(X, k) ⊗_k k{T}) — the integral cohomology is recovered only as these « shadows ».',
    basis:
      'Pages 5–7 build C_DRpd over (S, J, t) and specialise to (k{T}, k{T}⁺, T); page 8 argues that each row of fixed total degree is the truncation of an acyclic resolution of k_*, page 9 gives the k{T}-module structure, and pages 226–232 redo the computation through Φ_* ≃ 0 and Λ^iΨ_* = K(k, i). The right-hand end of the row on page 8 and the condition « q ≤ p+q » are \\uncertain{}.',
    ours:
      'The exactness of each row, which page 8 asserts without proof, is supplied by the reading from the divided-power Koszul complex of 0 → k_* → Φ_* → Ψ_* → 0. The comparison with Sullivan forms by T ↦ 1 (p. 11) is restricted by the reading to simplicial sets with finitely many non-degenerate simplices, a restriction the page does not make.',
    literature: [
      'R. Kageyama, « Higher holonomy via a simplicial viewpoint », arXiv:2211.03289 (2022), § 2.1 — builds the same simplicial divided-power de Rham algebra over ℤ⟨ϑ⟩, with ϑ playing the role of the unit (x_0 renamed ϑ), and divided-power integration; full text searched for a cohomology computation, none found',
      'R. Kageyama, « On iterated integral on simplicial sets », arXiv:2405.11570 (2024), § 2.1 — same algebra; full text searched, no computation of its cohomology on a simplicial set found',
    ],
    status: 'candidate',
    settle:
      'The construction itself — the simplex of size ϑ with divided powers over ℤ — is in Kageyama 2022 § 2.1, so only the cohomology statement remains open. Read Cenkl–Porter, « De Rham theorem with cubical forms », Pacific J. Math. 112 (1984) (a web search summary says they work over ℤ[1/2, …, 1/q], not with divided powers; not read), Cenkl, Pacific J. Math. 140 (1989), and the literature on integral models of cochains (Mandell 2006; binomial-ring models, e.g. Horel) for a computation of H of divided-power forms as τ_{≥q}(H^q ⊗ Γ(T)). If found, mark matched; the reading’s Koszul exactness is the step a reader should check first.',
  },
  {
    id: '136-shadow-full-faithfulness',
    cote: '136',
    pages: '19–31, 243–251',
    kind: 'mathematical',
    claim:
      'Over S = k{T}, every truncation τ_{≥N}(M ⊗_k S) determines the k-module M functorially: M ↦ M ⊗_k S^{+(N)} is fully faithful for every N, and more precisely M ⊗_k S → φ_N τ_N(M ⊗_k S) is an isomorphism, φ_N the right adjoint of truncation; the arithmetic core is that a family with binom(j, i)(x_j − x_i) = 0 for all j > i ≥ N in any abelian group is constant from N on.',
    basis:
      'Pages 19–22 prove the binomial lemma by Lucas and a p-adic digit shift (Lemma 2, Theorem 1), page 22–23 derives full faithfulness of ω_N, pages 26–31 prove the general statement through the equivalent form « c_{l,k} ξ_k = c_{l,k−i} ξ_{k+l} ⇒ ξ_k = binom(k, i) ξ », and page 251 restates it as one of four equivalent conditions on τ_N ∘ i. In Theorem 1 (p. 22) the sentence checking that the hypotheses of Lemma 2 hold ends on an \\ill{}.',
    ours:
      'Small: the reading names Lucas and Kummer, which the page does not, and corrects the index slips footnoted in the reading (c_{v,s} for c_{r,s}, ⊗_S for ⊗_k). The derived-category sequel (pp. 262–272: D⁺(Mod k) fully faithful in the derived category of shadows) rests on an Ext-vanishing whose written justification the reading judges insufficient, and is not part of this claim.',
    literature: [
      'One web search (2026-10-10) for the binomial lemma and for full faithfulness of truncated Γ(T)-modules surfaced nothing stating either; it surfaced « The module theory of divided power algebras », arXiv:1606.03431, which was not read',
    ],
    status: 'unsearched',
    settle:
      'Look in Roby (1963) and Berthelot, Cohomologie cristalline (LNM 407), ch. I, on modules over divided-power algebras; in arXiv:1606.03431; and in the literature on graded modules over Γ(T) and on « binomial » sequences (Elliott, binomial rings) for either the lemma or the full-faithfulness statement. The statement is elementary, so a match in passing is likely; if found, mark matched. A separate question, not this entry: whether Ext^n((τ_{N−i}S)[−i], M ⊗ S) = 0 for n > 0 holds at all.',
  },
  {
    id: '136-automorphism-group-scheme',
    cote: '136',
    pages: '161–179, 189–199',
    kind: 'mathematical',
    claim:
      'The simplicial-ring homomorphisms between divided-power de Rham algebras 𝒜(S, S⁺, t)_* — with no grading, filtration or divided powers assumed — are classified by (φ_0, A′_1, (B′_i)) subject to three conditions, the third being (2B′_i)J′ = 0; hence the automorphism functor of the completed algebra over k{T} is an affine group scheme over ℤ, 𝐆_m ⋉ (unipotent) with factors killed by 2, and when 2 is invertible every automorphism preserves the exterior grading and acts on cohomology through 𝐆_m alone.',
    basis:
      'Page 161 states the theorem with conditions 1)–3) and corollaries 1–5 on pages 163–171; pages 173–179 define the « indicateur », prove that φ is an automorphism iff it is invertible, and write Ω as Spec ℤ[(A_jk), (B_ijk)]/(2B_ijk)[A_10⁻¹]. Page 193 carries the earlier, struck corollary with the margin « faux tel quel ; vrai si 2B_i = 0 ». On page 161 the list of structures set aside ends on an \\ill{} and « affinables » is \\uncertain{}; the remark continued on page 162 is largely \\ill{}.',
    ours:
      'The reason for condition 3) — the commutator 2bb′ of the degree-one parts — is the reading’s; the page only asserts it. The reading drops the index ₂ that page 177 writes before the first 𝐆_a factor, following the description by coefficients, and does not fix the exponent of λ by which automorphisms act on H^i (the page’s phrase is largely illegible).',
    literature: [],
    status: 'unsearched',
    settle:
      'Check whether the automorphisms (or simplicial-ring endomorphisms) of the simplicial algebra of polynomial forms — Sullivan’s ∇(•, •), A_PL — have been computed rationally (Bousfield–Gugenheim, Memoirs AMS 179, 1976; Félix–Halperin–Thomas, Rational Homotopy Theory, § 10) or for the divided-power version (Kageyama, arXiv:2211.03289). A rational computation would match only the case 2 invertible; the ₂𝐆_a factors are the part to look for. If found, mark matched.',
  },
  {
    id: '7-catalogue-date-1967',
    cote: '7',
    pages: '2, 20, 35, 56',
    kind: 'codicological',
    claim:
      'The talk notes of pages 20–71 are dated November–December 1966 on the leaves themselves, not « novembre-décembre 1967 » as the catalogue title has it; only pages 2–18, a later write-up bound first, carry 1967.',
    basis:
      'Page 20 reads « Nov. Déc. 1966 » (last digit corrected in red), page 35 « 15.11.66 » (first written « 25 »), page 56 « 6.12.1966 »; the transcription records the three as checked on the facsimile by Michel Hua. Page 2 reads « Juillet-Août 1967 », its third digit barely formed and read 1967 by elimination. The published notes of the talks open: « a rough summary of five talks given at I.H.E.S in November and December 1966 ».',
    ours:
      'The identification of pages 20–71 with the preparatory notes for those IHÉS talks is the reading’s, by agreement of dates and contents; no leaf names the talks. The 1967 on page 2 is an elimination, not a reading.',
    literature: [
      'Transcription 7, batch 1 (batch-01.fr.tex), pages 2 and 20; batch 2, page 35; batch 3, page 56',
      'Catalogue entry for cote 7 in src/content/catalogue.ts, which reads « Notes laïus novembre-décembre 1967 (Cristaux) »',
      'A. Grothendieck, « Crystals and the De Rham cohomology of schemes » (notes by I. Coates and O. Jussila), Dix exposés sur la cohomologie des schémas (1968), Introduction, p. 306 — read in the scan at download.uni-mainz.de (WS23.Padische.1966.Grothendieck.CRCSscan.pdf)',
    ],
    status: 'candidate',
    settle:
      'A person checks the third digit of the date on page 2 against the facsimile, and reports the 1966/1967 discrepancy to the Montpellier inventory. Nothing here dates the mathematics beyond the leaves.',
  },
  {
    id: '7-strat-invariance-problem',
    cote: '7',
    pages: '70–71',
    kind: 'mathematical',
    claim:
      'The folder leaves open whether stratifying cohomology is invariant under a nilpotent immersion X₀ → X (X flat, locally of finite presentation over S), and says this is equivalent to H_inf ≅ H_strat; the published exposé states that this invariance fails, by the case of X₀ = X ×_S S₀ lying over a nilpotent S₀ ⊂ S.',
    basis:
      'Page 70 asks « A-t-on H*(X_cris, F) ≅ H*(X_strat, F) ? » for X « plat » (uncertain reading) of finite presentation; page 71 says « C’est aussi équivalent au pb suivant : … a-t-on H*(X_strat, F) ≅ H*(X₀ strat, F) » and stops. The hypothesis on X₀ sits next to an \\ill{} and an uncertain « Y de prés. finie sur S ». The published text (§5.3, p. 340) notes that every object of the stratifying site of X₀/S lies over S₀ = Spec(A/J), so its cohomology is killed by J, which the cohomology for X in general is not.',
    ours:
      'The reading’s footnote argues that the two forms of the problem are equivalent. This pass reads the folder differently on that point: for X = S and X₀ = S₀ the first form holds trivially (S is formally smooth over itself) and the second fails by the published argument, so the equivalence holds only under some further hypothesis on X₀, perhaps the word on page 71 that cannot be read. Applying p. 340 to the page’s second form is the pass’s own step.',
    literature: [
      'A. Grothendieck, « Crystals and the De Rham cohomology of schemes » (notes by I. Coates and O. Jussila), Dix exposés (1968), §5.3, p. 340, and Conjecture 4.2, p. 335 — read in the scan at download.uni-mainz.de',
    ],
    status: 'matched',
    settle:
      'Read the \\ill{} after « imm. nilp. » on page 71 on the facsimile. If it puts a hypothesis on X₀, such as flatness over S, that excludes X₀ = X ×_S S₀, the published counterexample no longer applies and the second form becomes an open question again. In that case, look for it in Berthelot (LNM 407, 1974) and in Ogus, « The cohomology of the infinitesimal site » (1975). The first form, H_inf ≅ H_strat for singular X, is the published Conjecture 4.2 over ℂ.',
  },
  {
    id: '7-noninfinitesimal-site',
    cote: '7',
    pages: '16–18',
    kind: 'mathematical',
    claim:
      'For X₀ over a perfect field k of characteristic p, the folder proposes as a p-adic cohomology the cohomology of a site whose objects are p-adically complete affine formal W-schemes Spf B with a surjection B → A₀ (A₀ the ring of an affine open U₀ ⊂ X₀) whose kernel is nilpotent mod p. The site has no divided powers and no overconvergence, and it is to pass two tests: Washnitzer–Monsky cohomology for X₀ smooth affine, and H_DR(X/W) modulo torsion for X₀ with a proper smooth lift.',
    basis:
      'Page 17 defines the triples (U₀, 𝒲, i) and the ring condition (« un W-hom. surjectif B → A₀ tel que B/pB → A₀ soit à noyau nilpotent »), with a Zariski-type topology read on the traces in X₀; page 18 states tests a) and b). Several words of the definition are \\ill{} (after « formel complet », « une \\ill{} de W-alg. »), but the parenthesis carrying the ring condition is legible. The tail of page 18 is almost entirely illegible.',
    ours:
      'The reading interprets « isomorphisme nilpotent » as a closed immersion defined by a nilpotent ideal, on the strength of the parenthesis. The comparison with Ogus’s convergent site is the reading’s. The doubt about test a) below is the pass’s own and is cited from memory.',
    literature: [
      'A. Grothendieck, « Crystals and the De Rham cohomology of schemes » (notes by I. Coates and O. Jussila), Dix exposés (1968), §7.1–7.5, pp. 351–356 — read in the scan at download.uni-mainz.de. §7.1 is the folder’s page 16 (the ordinary abelian variety); §7.5 proposes instead a « Monsky–Washnitzer topos » built from Monsky–Washnitzer (weakly complete) algebras A → A₀ with a topologically nilpotent divided-power structure on the augmentation ideal, and notes that p-adically complete liftings give modules of infinite rank',
    ],
    status: 'candidate',
    settle:
      'Compare with A. Ogus, « F-isocrystals and de Rham cohomology II — Convergent isocrystals » (Duke Math. J. 51, 1984), whose enlargements are p-adic formal schemes T with a map from (T₀)_red to X₀. Up to flatness and the closed-immersion condition, these look like the objects of page 17. If they coincide, mark matched. Then decide test a). From memory, convergent cohomology of a smooth affine X₀ is not Washnitzer–Monsky cohomology (for the affine line it is the de Rham cohomology of the closed disc, of infinite rank), which is the obstruction the folder’s own pages 38–40 show for W{t} and the one §7.5 of the published text avoids by passing to weakly complete algebras. If that holds, the site as proposed fails its own test a).',
  },
  {
    id: '37-ind-topos-exercise',
    cote: '37',
    pages: '22',
    kind: 'mathematical',
    claim:
      'For a small category C with Karoubi envelope C′, Ind(C) is a topos if and only if C′ has finite colimits and its canonical functor to sheaves for the finitary topology (covers refined by finite epimorphic families) preserves them — when C has finite limits, iff C has finite colimits and satisfies condition ST) of SGA 4 I 8.8 f) — and that topos is then perfect exactly when C′ has finite limits.',
    basis:
      'Page 22 is a typed « Exercice 2 », pencilled « SGA 4 VI 2 », listing conditions (i), (i bis), (i ter), (ii), (iii), (iv) as equivalent, with ink additions (the Karoubi envelope, « petite ») and the parenthesis meant to define E_PF left blank. It is stated without proof. The transcription found no such exercise, and no « enveloppe de Karoubi », in Exposé VI of the Orgogozo re-edition of SGA 4, t. 2 (consulted 2026-09-27).',
    ours:
      'The page’s (i bis) asks for a RIGHT adjoint that is left exact; the reading corrects it to a left-exact LEFT adjoint (Ind(C) reflective in Ĉ), which is what Giraud’s criterion needs. The reading reads E_PF as the finitely presentable objects, since the page leaves the defining parenthesis empty, and it checked in detail only (i) ⇔ corrected (i bis) and (i) ⇔ (iv); (ii), (iii) and the « parfait » clause were not checked by the edition. (i) ⇔ (iv) is in substance Gabriel–Ulmer (Ind(E_fp) ≃ E for a locally finitely presentable E); the candidate is the intrinsic conditions (ii)/(iii) on C.',
    literature: [
      'Web search (2026-10-10) for a criterion for Ind(C) to be a topos: returned only the nLab page « ind-object », which states no such criterion',
      'Orgogozo re-edition of SGA 4, t. 2, Exposé VI (exercises 1.28, 2.16–2.18, 3.11, 3.12 …): searched by the transcription for the exercise itself, not for the mathematics',
    ],
    status: 'unsearched',
    settle:
      'Read Johnstone, Sketches of an Elephant, D3.3 (locally finitely presentable toposes) and C2.2, Gabriel–Ulmer, Lokal präsentierbare Kategorien (LNM 221, 1971), and Adámek–Rosický, Locally Presentable and Accessible Categories, for a characterisation of the small C with Ind(C) a topos in terms of finite colimits in C (or its Karoubi envelope) and the finitary topology. If (ii) or (iii) is there, mark matched; if not, verify (ii) ⇔ (i) before calling it a candidate, since the edition has not.',
  },
  {
    id: '37-sga4-viii-section-10',
    cote: '37',
    pages: '38–39, 44',
    kind: 'codicological',
    claim:
      'The folder holds a typed § 10 of SGA 4 Exposé VIII, « Compléments : espaces algébriques et étendues algébriques » (10.1–10.4, with 10.5 numbered and empty), which is in neither the published Exposé VIII nor the original IHÉS typescript of VIII, both of which stop at § 9; the folder’s own terminology list cites it as « VIII 10.2 » and « VIII 10.4 ».',
    basis:
      'Pages 38–39 are the typescript, pencilled « SGA 4 VIII », with his ink and pencil marks and a handwritten footnote crediting the term « espace algébrique » to M. Artin. Page 44, the handwritten close of the bilingual terminology list, adds « étendue algébrique VIII 10.2 » and « espace algébrique VIII 10.4 ».',
    ours:
      'The comparison with the published and IHÉS texts is the transcription’s. The mathematical content is not claimed as new: the reading identifies 10.2–10.4 with Deligne–Mumford stacks and the trivial-inertia criterion for algebraic spaces, and 10.1 with M. Hakim, Topos annelés et schémas relatifs (1972) — identifications that are the edition’s and hold up to equivalence of ringed topoi. The typist is not established.',
    literature: [
      'SGA 4, t. 2, Exposé VIII, Orgogozo re-edition (consulted by the transcription 2026-09-27): §§ 1–9 only, no « étendue algébrique »',
      'Original IHÉS typescript of SGA 4 VIII (orgogozo.perso.math.cnrs.fr, SGA4-VIIIo.pdf): ends at 9.4, no « étendue algébrique »',
    ],
    status: 'candidate',
    settle:
      'A person checks pages 38–39 against the facsimile and looks for § 10 in the Springer LNM 270 printing itself (not only the re-edition) and in the IHÉS mimeographed fascicles; if any printing carries it, mark matched.',
  },
  {
    id: '37-ega-i-10-10-5-counterexample',
    cote: '37',
    pages: '92',
    kind: 'mathematical',
    claim:
      'With B = k[X₀, X₁, …], A = B[[T]], A_n = B[T]/(T^{n+1}) and J_n = (X₀, X₁T, …, X_nTⁿ), the modules M_n = A_n/J_n form a compatible system of finitely presented A_n-modules that does not come from any finitely presented A-module, because J_n needs n+1 generators — so condition b) of EGA I 10.10.5 does not imply a) and c) without noetherian hypotheses.',
    basis:
      'The typed letter to Dieudonné dated 27.8.1967 (page 92) gives the construction and a minimality proof by reducing modulo (X_j)_{j≠i}; it proposes stating 10.10.5 as two equivalent conditions implying a third, and printing the counterexample. The missing brackets and signs were inked by hand and are legible; nothing in the statement rests on an \\uncertain{} or \\ill{}.',
    ours:
      'The letter claims the generators are linearly independent over B in J_n/TJ_n; that is false (X₀·X₁T ∈ TJ_n). The reading rewrites the proof: the letter’s reduction shows each aᵢ lies in 𝔪 = (Xᵢ), so the images are independent over k in J_n/(TJ_n + 𝔪J_n), which suffices. It also supplies the Schanuel step (a finitely presented M would bound the number of generators of J_n uniformly), which the letter leaves implicit. The conclusion is the letter’s; that proof is the edition’s.',
    literature: [],
    status: 'unsearched',
    settle:
      'Read EGA I, 2nd ed. (Grundlehren 166, 1971), I 10.10.5 and its remarks: if this counterexample, or another showing b) ⇏ a), is printed there, mark matched. Otherwise check the non-noetherian treatments of adic modules — Fujiwara–Kato, Foundations of Rigid Geometry I, ch. 0 § 8 and ch. I, and the Stacks Project chapters on formal schemes. The question the correspondence leaves open, a) ⇒ c) without noetherian hypotheses, is not part of this entry.',
  },
  {
    id: '37-smooth-base-change-stacks',
    cote: '37',
    pages: '29–30',
    kind: 'mathematical',
    claim:
      'The folder proposes, as « 2.1.1 » of a correspondent’s chapter VII, smooth base change in degrees ≤ 1 with non-commutative coefficients: for f universally locally L-1-aspherical and G an ind-L-stack, G(X) → G′(X′) is an equivalence over strictly local bases, and f*g_*G → g′_*f′*G is an equivalence for g coherent.',
    basis:
      'Page 29 is an undated, unsigned typed letter asking a correspondent addressed as « tu » to restate « 2.1.1 » and to cite SGA 4 XVI; page 30 is the proposed statement, Theorem 2.1.1 and Corollary 2.1.2, with « ind-L- » inked over « champ ».',
    ours:
      'The reading supplies that L consists of primes invertible on S (on k in 2.1.2), without which the statement is false (Artin–Schreier). It interprets « ind-L-champ » from a line struck at the machine. The page does not name the correspondent and the edition does not; the numbering match below is not an identification.',
    literature: [
      'P. Haine, « Nonabelian basechange theorems & étale homotopy theory » (arXiv 2304.00938), introduction and Corollary 2.30: cites J. Giraud, Cohomologie non abélienne (Grundlehren 179, 1971), chapitre VII, Théorème 2.1.2, as smooth base change for sheaves of groupoids',
    ],
    status: 'matched',
    settle:
      'Matched on a secondary citation only: read Giraud, Cohomologie non abélienne, VII § 2.1, check that Théorème 2.1.2 there is this statement (hypotheses on L, ind-L-stacks, the strictly local case a)), and whether the chapter layout fits the letter’s « 2.1.1, 2.1.5, 2.1.7 » and « Chap. VII ». If the statements differ, reopen as unsearched.',
  },
  {
    id: '37-dieudonne-letter-sent-copy',
    cote: '37',
    pages: '96–97',
    kind: 'codicological',
    claim:
      'Pages 96–97, the letter to Dieudonné of 15.9.1967, are an uncompleted copy: a typed top copy of the same letter, with the machine’s blanks filled by hand and signed « Bien cordialement A. Grothendieck », survives elsewhere, and its hand-inked « m = Σ m_i » in the Lemma confirms the reading’s restitution of the blank the folder copy leaves.',
    basis:
      'The transcription records that on pages 96–97 the arrows, ∈, ≤ and the tilde were left blank and never completed, that a blank stands between « m » and « m_i » in the Lemma, and that the second leaf has no signature. The Grothendieck Circle hosts a two-page scan (csg.igrothendieck.org, L88u.pdf) of the same typed text, dated « 15.9.67 », marked « 3H/DIEU I/241 » at the top right, with the blanks inked, « engendré par m = Σ m_i générateurs » and a signature.',
    ours:
      'The comparison is this pass’s own, made on the scan at screen resolution on 2026-10-10; that the scan is the dispatched copy and the folder’s a retained copy is inferred, not established, and the reading of the mark « 3H/DIEU I/241 » (and of « I 10.11.3 » where the folder copy reads « I 10.11 ») is uncertain.',
    literature: [
      'Grothendieck Circle scan csg.igrothendieck.org/wp-content/uploads/2025/01/L88u.pdf, pages 1–2, read directly',
      'Transcription 37, batch 5 (batch-05.fr.tex), pages 96–97',
    ],
    status: 'candidate',
    settle:
      'A person compares the two documents line by line, checks whether the folder’s leaves are a carbon of the scanned sheets, identifies the holding behind « 3H/DIEU I/241 », and records the scan’s Σ and its « 10.11.3 » (if that is what it reads) in the transcription’s apparatus.',
  },
// Folder 58 — find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, over 58.modern.tex (Opus 5.5 reading, 2026-10-04) and batch-01..04.fr.tex.
// SGA 2 was read in the retyped edition (arXiv math/0511279, text extracted from the PDF); nothing else was read in full.
  {
    id: '58-lef-permanence-projective-flat',
    cote: '58',
    pages: '40–43',
    kind: 'mathematical',
    claim:
      'If X is quasi-projective over a noetherian ring and the pair (X, Y) satisfies (LG)_n, that is, H^i(X, F) → H^i(X_{/Y}, F_{/Y}) is bijective for i ≤ n and injective for i = n+1 for every locally free F, then for every W projective and flat over X the pair (W, f⁻¹(Y)) satisfies (LG)_n, and likewise for LG, the condition Lef of SGA 2 X. The hypothesis is put only on the pair (X, Y) and nothing is asked of the fibres of W → X.',
    basis:
      'Page 41 states the Theorem (i)–(iii) for a coherent F on W, with proper support over X and flat. Page 42 draws Corollaire 1, with « ($X$ quasi-projectif) » framed: if (X, Y) satisfies (LG)_n [resp. LG, resp. LG strict], so does (X′, f⁻¹(Y)) for every X′ projective and flat over X. Page 40 carries an earlier, cancelled form. On page 41, « morphisme », « projectif » and « monom. » are \\uncertain{}, but « projectif et plat » is legible in Corollaire 1. The manuscript gives no proof.',
    ours:
      'Every proof is the edition’s. The reading sketches (i) through a perfect complex representing Rf_*F, the comparison theorem (EGA III 4.1) and the five lemma, and passes from (LG)_0 to LG by its own « conclusion pratique ». It does not verify (iii), so the LG-strict (Leff) case of Corollaire 1 is left out of this claim. The page’s « plat sur $Y$ » is read « plat sur $X$ ». « Quasi-projectif » and « à support propre sur $X$ » are the page’s own additions. The sketch was not checked in detail for this entry.',
    literature: [
      'SGA 2 (arXiv math/0511279), Exposé X, § 2: definitions of Lef and Leff, Exemples 2.1–2.2, Proposition 2.3, Corollaires 2.4–2.6 — no permanence under a projective flat morphism',
      'SGA 2, Exposé XII, Corollaires 2.4, 3.4 and 4.9: Lef and Leff for a projective flat f : X → S with Y a relatively ample divisor, proved from depth conditions on the fibres X_s, not inherited from a pair on the base',
      'SGA 2, Exposé XI, § 2 (Pic under Lef and Leff) — no permanence statement',
      'Web search (2026-10-10) for Lef / Leff preserved under projective flat morphisms — nothing found',
    ],
    status: 'candidate',
    settle:
      'Read M. Raynaud, « Théorèmes de Lefschetz en cohomologie des faisceaux cohérents et en cohomologie étale » (Ann. Sci. ÉNS 7, 1974), which SGA 2’s editorial notes cite for improvements of X 2.1 and XII 3.1, and R. Hartshorne, Ample Subvarieties of Algebraic Varieties (LNM 156, 1970), ch. IV and V. If either proves that Lef or (LG)_n passes from (X, Y) to a projective flat W, mark matched. Otherwise, check the reading’s proof sketch of (i) in full, in particular the hypercohomology five-lemma step at degree n+1.',
  },
  {
    id: '58-local-hom-comparison-depth-off-y',
    cote: '58',
    pages: '45–51',
    kind: 'mathematical',
    claim:
      'For A local noetherian, a quotient of a regular ring and t-adically complete, X′ the punctured spectrum and Y′ = V(t) ∩ X′, the folder asserts Hom(F, G) ≅ Hom(F̂, Ĝ) along Y′ for coherent F, G on X′ whenever G has depth ≥ 2 at the closed points of X′ − Y′. No depth is asked at the points of Y′, whereas SGA 2 X, Exemple 2.1 (i) asks depth ≥ 2 at every closed point of X′, so the folder’s hypothesis is weaker.',
    basis:
      'Page 45 states the Theorem and reduces, through H = Hom(F, G), to Γ(X′, H) ≅ Γ(X̂′, Ĥ) for H of depth ≥ 2 « en les pts [fermés] de X′ − Y ». « pts » is \\uncertain{}. The adjective before « de X′ − Y′ » in the first statement is \\ill{}, and the formula Γ F ≃ Γ F̂ is written over other letters. Page 47 sets up a dévissage 0 → P → H → H̄ → Q → 0, with P and Q supported in Y′, and a comparison for the t-power torsion K. It marks the t-regular step with his own « ? » and stops. Pages 49–51 treat the essential image: i_*(F|_U) is coherent by the finiteness criterion, and the page ends « on a gagné ».',
    ours:
      'The t-adic completeness is supplied by the reading; the page’s second line is overwritten. The reading restricts the page’s « ρ pleinement fidèle » to the objects represented by such Modules, and gives a counterexample to the unrestricted statement. The proof is unfinished on the page and in the reading, so the statement is the manuscript’s and is unproved as it stands. The comparison with SGA 2 is made for this entry.',
    literature: [
      'SGA 2 (arXiv math/0511279), Exposé X, Exemple 2.1 and its proof (u_*E coherent by VIII 2.1, then IX 1.5): the same setting with depth ≥ 2 at all closed points of X′, for locally free E. The editorial note there says M. Raynaud (1974), Cor. I.1.4 and I.5, improves (i), and that note was not followed up',
      'SGA 2, Exposé IX, 1.5 and Exposé VIII, 2.1 (finiteness), as cited in X 2.1',
    ],
    status: 'candidate',
    settle:
      'Read Raynaud 1974 (Ann. Sci. ÉNS 7), Corollaires I.1.4 and I.5. If they drop the depth condition along Y′, mark matched. If not, complete or refute the t-regular step that page 47 leaves at « ? ». A test case is a coherent G that is the ideal of a height-two prime containing t, which has depth 1 at a closed point of Y′, in A = k[[x, y, z]] with t = x.',
  },
  {
    id: '58-typed-leaf-sga2-xii-3-1',
    cote: '58',
    pages: '56, 60',
    kind: 'codicological',
    claim:
      'The two copies of one typed leaf on pages 56 and 60 carry the end of the statement and the lead-in « Cet énoncé va résulter du suivant : Corollaire 3.2. » of what is printed as SGA 2, Exposé XII, Théorème 3.1 (existence of a coherent Module with given formal completion along X₀) in a wording that differs from the print. His notes on the blank parts compute with the module ∐_{p,q≥0} F₀(q−p) and the sums Σ_p R^i f_{0*} F₀(q−p), which have the shape of the graded module ⊕_m R^i f_{0*}(F₀(−m)) used in the printed proof of 3.2 (i).',
    basis:
      'Batch 3 describes the typed text on page 56 as the end of a statement whose hypotheses are a) t_s is O_{X_s}- and F_s-regular, b) F and O_X are flat over S, c) F_{0s} and O_{X_{0s}} have depth ≥ 2 at closed points, concluding that a coherent Module on X with the given formal completion exists. It is followed by « Cet énoncé va résulter du suivant : Corollaire 3.2. Sous les conditions de 3.1. ( », with a typed correction at « et O_X ». Page 60 is a second copy of the same leaf, head to tail. The print (XII 3.1–3.2) has a) F flat, b) t_s F_s-regular and c) F_{0s} of depth ≥ 2 at closed points of X_{0s}. There the conditions on O_X are a′), b′), c′), obtained by a reduction, and 3.2 opens « Sous les conditions a), b), c) ci-dessus ».',
    ours:
      'The identification is the edition’s, made for this entry from the transcription’s summary of the typed text against the 2005 retyped edition. No facsimile was read, and the full typed wording is not transcribed. That the handwritten double sums belong to the proof of 3.2 is a resemblance of shape only; the reading had not tied them to any question of the folder. The print says 3.2 was first done « par un expédient un peu pénible » through the punctured projecting cone and replaced by the graded argument, and Exposé XII is said to have been « rédigé en Janvier 1963 ». Neither fact dates the leaf.',
    literature: [
      'Transcription 58, batch 3 (batch-03.fr.tex), header and notes on pages 56 and 60',
      'Modernised reading 58, « Deux brouillons (pages 56 et 60) »',
      'SGA 2 (arXiv math/0511279), Exposé XII, Théorème 3.1, Corollaire 3.2 and the proof of 3.2 (i), Lemme 3.3; footnote (∗) of Exposé XII',
    ],
    status: 'candidate',
    settle:
      'A person transcribes the typed half of page 56 in full from the facsimile and compares it word for word with SGA 2 XII 3.1 in the 1968 North-Holland edition, and if possible with the IHÉS mimeographed fascicles of 1962–63. A match settles which state of Exposé XII the leaf is. The handwritten pages 56 and 60 are then compared with the proof of 3.2 (i) and Lemme 3.3.',
  },
// Folder 63 — find-novelty pass, Opus 5.5 (claude-opus-5-5), 2026-10-10, on the Opus 5.5 reading of 2026-10-03.
// Pool: nearly every footnote of 63.modern.tex names a match (Tate's algorithm, Deligne's formulaire, G_2^* and the Hodge splitting
// [Katz 1973/1976], W[[t]] as universal deformation ring [Lubin–Tate, Serre–Tate], Pic of M_{1,1}, the 72 and 32 twists over Z[1/6],
// class number one and genus theory) and was dropped as a match. The relation 4ρσ = AĀ − 1 and the closed form of (A/|A|)^6 are the
// edition's repairs and answers, not the page's, and were dropped. What remains: one refutation and two codicological entries.
  {
    id: '63-level3-tangents-at-2',
    cote: '63',
    pages: '97–99',
    kind: 'mathematical',
    claim:
      'The folder asserts that the four irreducible components of M_3 ∩ V(c_4) — the j = 0 locus in the full level-3 moduli over μ_3^* — all meet at one point a over F_4 and have the same tangent there; as stated, this fails: in the Hesse model the four branches have four pairwise distinct tangents at a.',
    basis:
      'Page 97 sets up the question « À examiner si les 4 composantes de (M′_3)_2 ont “tangentes distinctes” » and argues by contradiction (« … on aurait une contradiction. Donc les quatre… »); page 99 opens « … aux composantes irréductibles sont égales » and states that the Zariski tangent space at a « splitte canoniquement en V_1 × V_2 » with G′ = SL(2, F_3) acting trivially on V_2 and via F_4^* on V_1. Both pages are palimpsests (226 \\ill{} in the batch, nearly all on pp. 97 and 99): the word « tangentes » before « égales » is not legible, « rigidification » and « Sylow » are \\uncertain{}, and the reading’s orbit argument, which the page does not write, is what yields « same tangent ».',
    ours:
      'The refutation is this pass’s own step, and it disagrees with the reading (same model, Opus 5.5), which endorses the conclusion with its own orbit argument (footnotes on pp. 97–99). Check: over Z[1/3, ζ_3], M_3 is the Hesse line x³ + y³ + z³ = 3t·xyz minus t³ = 1; c_4 is, up to units, t(t³ + 8), so V(c_4) is the four sections t = 0, t = −2, −2ζ, −2ζ², which coincide mod 2 at t = 0 (the point a, over F_4). The local ring there is W(F_4)[[t]], with cotangent space spanned by t and 2; the branches have tangent forms t, t + 2, t + 2ζ, t + 2ζ², pairwise non-proportional. Where the page’s argument breaks: the splitting V_1 × V_2 is not G′-stable — the Hesse involution t ↦ (t + 2)/(t − 1), which comes from Q_8 ⊂ G′, fixes a and acts on the cotangent space by t ↦ t + 2 mod m², a transvection, so the four non-vertical tangent lines form one G′-orbit of size 4, not {0}. The multiplicity 4 and the non-regularity of M′ at p = 2 (p. 95) are unaffected.',
    literature: [
      'M. Artebani and I. Dolgachev, « The Hesse pencil of plane cubic curves » (arXiv math/0611590) — j-numerator ∝ u₀³(u₀³ + 8u₁³)³; seen through a search summary, not read in full',
      'arXiv 2408.04117 (« The dynamics of the Hesse derivative on the j-invariant ») — short Weierstrass form of the Hesse curve with a(t) = −27t(t³ + 8); search summary only',
      'K. Gunji, UTMS preprint 2003-47 — Hesse cubics as the level-3 family, excluded parameters ∞, 1, ω, ω²; search summary only',
      'arXiv 1603.09018 (« On Real and Complex Cubic Curves ») — the order-12 tetrahedral Möbius group on the Hesse parameter; search summary only',
      'Web search for the tangency statement on the level-3 moduli at the supersingular point in characteristic 2: no source found stating it either way',
    ],
    status: 'refuted',
    settle:
      'What still stands: four components, meeting only over 2 and all at a single point a over F_4, M′_3 connected — the page’s statements before the tangent question are consistent with the Hesse model. To close the refutation, a person checks two things: that the minimal-model c_4 of the Hesse family over W(F_4)[[t]] is a unit times t(t³ + 8) (Katz–Mazur, Arithmetic Moduli of Elliptic Curves, ch. 2 and 12, or a direct computation), and, against the facsimile of p. 99, whether « égales » really has « tangentes » as its subject. If the page says something else there, rewrite the claim; the edition’s footnoted orbit argument and the sentence « Les quatre branches ont en a la même tangente » in 63.modern.tex need correcting either way.',
  },
  {
    id: '63-pages-97-99-order',
    cote: '63',
    pages: '97–99',
    kind: 'codicological',
    claim:
      'The level-3 notes do not read in archive order: their logical sequence is 98, 97, 99, yet page 98 ends « TSVP » as if page 99 were its verso, so either page 97 is a sheet inserted between a recto and its verso or page 99 does not continue page 97.',
    basis:
      'Page 98 establishes that M_3[1/6] ∩ V(c_4) is four copies of μ_3^*[1/6] and ends « TSVP »; page 97 begins « Donc il s’ensuit que M_3 ∩ V(c_4) a exactement 4 composantes irréductibles », which presupposes page 98, and breaks off on « Donc les quatre… »; page 99 opens « … aux composantes irréductibles sont égales », which the reading takes as the end of page 97’s sentence. The transcription notes page 99 as « Suite de la page 98 (TSVP) ».',
    ours:
      'The reading orders the section « pages 98, 97 et 99 » and joins 97’s last sentence to 99’s first line; that join rests on words that are \\ill{} at the head of page 99. The transcription keeps archive order, as it should.',
    literature: ['Transcription 63, batch 5 (batch-05.fr.tex), pages 97, 98, 99 and the header note on « TSVP »'],
    status: 'unsearched',
    settle:
      'A person checks on the facsimile whether pages 98 and 99 are recto and verso of one leaf and whether page 97 is a separate leaf (or the verso of the 9 March 1968 letter, page 96), and whether the first legible words of page 99 can complete « Donc les quatre… ».',
  },
  {
    id: '63-level3-notes-after-march-1968',
    cote: '63',
    pages: '96–99',
    kind: 'codicological',
    claim:
      'If the level-3 notes of pages 97 and following are written on the back of the letter at page 96, dated « Wattignies 9/III/68 », those leaves were written no earlier than March 1968 — a terminus post quem for the leaves, not for the mathematics.',
    basis:
      'Page 96 is a letter addressed to him, dated 9/III/68, not transcribed; the transcription of page 97 states the inference conditionally, and the reading keeps the conditional. Pages 95, 97, 98 and 99 are noted as being in the same blue-black ink.',
    ours: null,
    literature: ['Transcription 63, batch 5 (batch-05.fr.tex), notes on pages 96 and 97; 63.modern.tex, section V'],
    status: 'unsearched',
    settle:
      'A person checks on the facsimile which of pages 97–99 is the verso of the letter of page 96. If none is, the entry is withdrawn as a dating and the letter only says when the folder was assembled, not when the notes were written.',
  },
  // Folder 126 — find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, against a reading made on Opus 5.5 (2026-10-03).
  {
    id: '126-fpqc-generated-topology',
    cote: '126',
    pages: '9–14',
    kind: 'mathematical',
    claim:
      'The topology on schemes generated by the Zariski pretopology and, on affine schemes, finite jointly surjective families of flat morphisms has as coverings exactly the families that are refined, over each affine open, by finitely many flat affine maps whose images cover it; and a presheaf is a sheaf for it iff it is a Zariski sheaf satisfying the equaliser condition for every faithfully flat map of affine schemes.',
    basis:
      'Page 9 sets up a pretopology T on C and T′ on a full subcategory C′ under conditions (a), (b), (c); pages 10, 11 and 13 prove Proposition 1 (description of the generated topology) and Corollary 2 (sheaf criterion); pages 11–12 and 14 specialise to schemes as Proposition 2 (i)–(iii).',
    ours:
      'Condition (c) is struck through on page 9 and its reading is very uncertain; the reading reconstructs it from its use on page 13. The page does not verify (a), (b), (c) for schemes; the reading does, in a footnote. The proof of (iii) is announced and does not follow.',
    literature: [
      'The Stacks Project, Definition 34.9.1 (Tag 022B): fpqc coverings, defined as families of flat morphisms such that every affine open of the target is the union of the images of finitely many affine opens of the sources',
      'The Stacks Project, Lemma 59.15.6 (Tag 03O1): a presheaf on Sch/S is an fpqc sheaf iff it is a Zariski sheaf and satisfies the sheaf axiom for every faithfully flat Spec(B) → Spec(A)',
    ],
    status: 'matched',
    settle:
      'Proposition 2 (i) and (ii) are, in substance, the Stacks definition of fpqc coverings and its sheaf criterion; the match is for the schemes case. The general Proposition 1 — the topology generated by a pretopology on C and one on a full subcategory C′ under (a)–(c) — was not searched as such; if anyone pursues it, the place to look is SGA 4 II (topologies engendrées) and Stacks, Sites and Sheaves, but its condition (c) is a reconstruction from a struck passage, so the page cannot carry a separate candidate until the transcription of page 9 is revisited.',
  },
  {
    id: '126-radicial-etale-factorisation',
    cote: '126',
    pages: '17–23',
    kind: 'mathematical',
    claim:
      'A finite, universally open morphism f : X → Y with Y locally noetherian whose fibres all have the same number n of geometric points factors as a finite surjective radicial morphism X → X^ét followed by a finite étale cover X^ét → Y, universal among Y-morphisms from X to étale Y-schemes — under universal openness rather than flatness.',
    basis:
      'Page 17 states the Proposition; pages 18 and 20 build the scheme of numberings Y″ ⊂ X^n; page 19 proves that a section of such an f is open and closed, splitting X = X_(1) ⊔ X^(1); pages 21–22 (Lemmas 2 and 3) descend the trivial cover Y′ × I along a finite surjective Y′ → Y to an étale cover of Y.',
    ours:
      'The proof is only sketched in the folder and the reading says it does not certify the statement in full generality. The reading supplies the justification on page 19 (that a common point would drop the geometric-point count, using universal openness), the closed-immersion criterion of the Lemma of pages 18/20, and the appeal to effective descent of étale covers along finite surjective maps (SGA 1 IX §4, cited from memory). It also shows the page’s remark that « d constant » can be dropped for Y connected is false as it stands (y² = t over k[t]), so constancy stays a hypothesis. On the page, « univ. ouvert » — the hypothesis that would make this weaker than the flat case — is an interlinear addition marked \\uncertain, and « factorisation » in the heading is \\uncertain too; most of the prose of pages 21–23 is \\ill.',
    literature: [],
    status: 'unsearched',
    settle:
      'The statement rests on an uncertain interlinear « univ. ouvert », so the transcription of page 17 should be checked against the facsimile first. Then look for the factorisation (the « étale part » of a finite morphism, π₀ of X/Y) in EGA IV 18.2 and 18.12, SGA 1 IX, and the Stacks Project chapters on étale morphisms and fundamental groups (pione), and see whether it is stated under universal openness or only for finite flat (locally free) morphisms. Two general web searches on 2026-10-10 did not surface the statement in either form; that is not a reading of those sources, hence the status.',
  },
  {
    id: '126-nilpotent-deformation-quotient',
    cote: '126',
    pages: '4–7',
    kind: 'mathematical',
    claim:
      'If R ⇉ X is a flat equivalence relation and its reduction R₀ ⇉ X₀ modulo a nilpotent ideal is effective with fpqc, quasi-separated quotient X₀ → Y₀, then R is effective, with quotient Y a nilpotent thickening of Y₀ and X → Y flat — proved by the vanishing of Ȟ⁰(X₀/Y₀, ℋ¹) for fpqc quasi-separated covers of an affine.',
    basis:
      'Page 4 states the conclusion (« R est M-effective »); pages 5–6 construct 𝒜 = Ker(𝒪_X ⇉ 𝒪_R), use Remark 2 of page 3 to lift sections and Theorem 1 in degree 1 to correct the lift; page 7 concludes flatness and R ≃ X ×_Y X.',
    ours:
      'The hypotheses are largely illegible and are reconstructed by the reading: flatness of p₁, p₂ and R₀ = R ×_X X₀ are not on the page; « (M) » is unresolved. The reading fixes a sign the page leaves uncertain, supplies the reduction to 𝒥² = 0, the fact that a square-zero thickening by a quasi-coherent ideal is a scheme, and the use of the local flatness criterion. So the statement is largely the edition’s; the page carries the strategy (Čech vanishing used to lift and correct invariant functions).',
    literature: [],
    status: 'unsearched',
    settle:
      'Look for deformation of quotients by flat equivalence relations in SGA 3, exposés V and VI_A (quotients by flat groupoids), and in the Stacks Project chapters on groupoids and deformation theory. Given how much of the hypothesis is reconstructed, a match for the reconstructed statement would settle it; if none is found, the transcription of pages 4–5 should be re-read before the entry is promoted to candidate.',
  },
  {
    id: '126-generic-descent',
    cote: '126',
    pages: '26–29',
    kind: 'mathematical',
    claim:
      'For S noetherian, T → S flat of finite type and a fibred category F on finite-type S-schemes for which flat surjective morphisms are of F-descent (full faithfulness only), an isomorphism φ : p₁*X ≅ p₂*X defined over a dense open of T ×_S T and satisfying the cocycle condition over a dense open of T ×_S T ×_S T extends, after shrinking T to a dense open, to a genuine descent datum agreeing with φ where both are defined.',
    basis:
      'Page 26 states the data and the reductions; page 27 defines ψ through a middle point and checks compatibility on the five-point scheme W′; page 28 descends ψ to φ′; pages 28–29 check the cocycle condition on the six-point scheme W‴ and that φ′ extends φ.',
    ours:
      'The reading takes X in F_T where the page writes F_S, takes U, V open from the start, reorders the shrinkings so that V need not be re-shrunk (the page’s own order is circular), corrects « W ×_{T×T} W ≃ T⁴ » to an open subset of T⁴, and exchanges t″ and t‴ in the list defining W‴ to match the computation of page 29. The flatness and surjectivity of W′ → W ×_{T×T} W is asserted by the page « sauf erreur ». The reading relates the method, from memory, to Weil’s theorem on birational group laws and field of definition (1956) and to M. Artin’s exposé in SGA 3 XVIII; the page names neither.',
    literature: [],
    status: 'unsearched',
    settle:
      'Read A. Weil, « The field of definition of a variety » (Amer. J. Math. 78, 1956), and SGA 3, exposé XVIII (M. Artin, birational group laws), for a descent statement for a rational descent datum in this generality — an arbitrary fibred category with flat surjective maps of descent; also EGA IV § 9 and § 20 on generic properties. If the general form is there, mark matched; if only the case of varieties or group laws is, the fibred-category form is the candidate.',
  },
  {
    id: '126-interposed-leaves-13-19',
    cote: '126',
    pages: '10–14, 18–20',
    kind: 'codicological',
    claim:
      'Twice in the folder a text runs across an interposed leaf: the sentence cut off at the foot of page 12 continues in the struck lines at the top of page 14, with page 13 (the resumed proof of Proposition 1 from page 10) in between; and the Lemma of page 18 continues on page 20, with page 19 (the open-and-closed section argument) in between.',
    basis:
      'The transcription notes on page 14 « suite de la phrase interrompue au bas de la page 12 », on page 13 « suite de la démonstration de la page 10 », and on page 20 « suite, semble-t-il, du lemme de la page 18 »; page 18 is struck through with two diagonals.',
    ours:
      'The two continuations are the transcription’s and the reading’s observations, not marks on the leaves; the « semble-t-il » for page 20 is the transcription’s. No explanation (verso numbered in sequence, misbound leaf, insertion) has been checked.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look at the facsimile for whether pages 12/13 and 18/19 are recto and verso of single leaves (in which case the sequence is a reading of the versos, not a binding error) or separate leaves, and compare paper and ink of 13 with 10–12 and 14, and of 19 with 18 and 20.',
  },
// 137: two candidates. Pass: Opus 5.5 (claude-opus-5-5) on an Opus 5.5 reading (% Pass header of 137.modern.tex, 2026-10-10). Dropped as matches the reading already names: the Dold–Kan splitting and rank formula (pp. 6–12), the Smith-normal-form dévissage over a principal ring (pp. 15–21), the additive envelope and additive Yoneda (pp. 27–33), Isbell duality (p. 31), ends and coends (p. 34), Dold–Kan in karoubian categories (pp. 45–46), Quillen exact categories (p. 49), lax symmetric monoidal functors (p. 65), the cup product by acyclic models (p. 71), Roby's theorem and the Friedlander–Suslin definition of strict polynomial functors (pp. 84–85, a match, not a novelty). Dropped as repaired by the edition: Proposition 2 of pp. 9–11 (stability of special modules under Λ, Γ, Sym, false over ℤ), the d)/e) « ssi » of p. 13, the struck weight lemma of p. 75 (struck by him, counterexample in his margin). Not entered: the theorem of p. 3 / p. 72 (u_n an isomorphism), asserted without proof and overlapping 136-pd-de-rham-shadows.
  {
    id: '137-perfect-complexes-universal-sigma-exact',
    cote: '137',
    pages: '39–44, 48–56',
    kind: 'mathematical',
    claim:
      'Let 𝒫 be the k-linear category of bounded chain complexes of finitely generated free k-modules, with Σ the degreewise-split short exact sequences and ℂ^• the cochain complex of discs (k → k in degrees i+1, i). For any k-additive karoubian category ℬ with a class Σ of exact sequences in which every morphism has a Σ-kernel, evaluation F ↦ F(ℂ^•) is an equivalence from the k-linear functors 𝒫 → ℬ that send Σ to left-exact sequences onto all cochain complexes of ℬ, with inverse C^• ↦ (L ↦ Hom^•_k(Hom(L, ℂ^•), C^•)); under it the Σ-exact functors correspond to the Σ-resolutions.',
    basis:
      'Page 40 (Proposition 1) shows that the full subcategory on the discs is the k-additive category freely generated by a cochain complex; page 42 (Proposition 2) gives the perfect pairing Hom(ℂ^n, x) × Hom(x, ℂ^{n+1}) → k; pages 43–44 (Proposition 3) give the reconstruction formula F(x) ≅ Hom^•_k(α^•(x), F(ℂ^•)). Page 50 states the theorem; pages 52–55 build the adjunction ρ ⊣ σ, show σ fully faithful, and prove the unit an isomorphism by induction on length, exhibiting L as the kernel of a Σ-epi (ℂ^p)^r ⊕ L′ → (Ψ^{p+1})^r. The formulas on pp. 52–55 are legible; much of the connecting prose is \\uncertain{} or \\ill{}, including the hypothesis added on p. 50 (« où tout \\uncertain{projecteur} a un noyau ») and the description of the essential image in a).',
    ours:
      'The reading states a) in the form proved on p. 55, not the hesitant form of p. 50 (where « est une équivalence » is struck for « est pleinement fidèle »). It sets aside the margin doubt of p. 52, « Non, il faut condition de platitude ? », judging that the proof uses only the existence of kernels; that judgement is the edition’s, and is the first thing to check. The intrinsic characterisation of 𝒫 by conditions a)–e) on pp. 57–60 is not part of this claim: there the reading itself doubts what the page describes as the essential image.',
    literature: [
      'Two general web searches (2026-10-10) for a universal property of bounded complexes of finitely generated free modules with the degreewise-split exact structure, and for the additive category freely generated by a cochain complex, found no statement of either; they surfaced only background (term-split exact structures on bounded complexes, arXiv:2001.05380; free additive categories on a linear category, arXiv:2402.12251), neither read in full. That is not a search of the sources named in settle',
    ],
    status: 'unsearched',
    settle:
      'Look for the statement that cochain complexes in ℬ are the left-exact functors out of bounded complexes of free modules (or, equivalently through Dold–Kan, out of strictly perfect simplicial modules) in: Mitchell, « Rings with several objects » (Adv. Math. 8, 1972), on complexes as additive functors on a ringoid; Keller, « Chain complexes and stable categories » (Manuscripta Math. 67, 1990) and « Deriving DG categories » (1994); Bühler, « Exact categories » (Expo. Math. 28, 2010); Illusie, Complexe cotangent I, ch. I, on Dold–Puppe in additive categories; and, in ∞-categorical form, Lurie, Higher Algebra 1.3.3 and 1.2.4 (universal property of D⁻ and of the Dold–Kan correspondence). If it is in any of these, even as an exercise, mark matched.',
  },
  {
    id: '137-polynomial-categories-pd-tensor-categories',
    cote: '137',
    pages: '74–83',
    kind: 'mathematical',
    claim:
      'The folder axiomatises « polynomial categories » — a category 𝐏 with finite products, a wide additive subcategory 𝐏₁ of degree-one maps, and a grading 𝐏(X, Y) = ⊕ 𝐏_n(X, Y) by homogeneity under scalars, with composition additive in the outer variable only and degrees multiplying — and asserts that the strict ones are equivalent to « ⊗-pd-categories »: additive symmetric monoidal categories with an exponential graded functor Γ* (Γ*(X ⊕ Y) ≅ Γ*X ⊗ Γ*Y) and maps α_{p,q} : Γ^{pq} → Γ^p Γ^q satisfying associativity and unit conditions, the passage back being 𝐏_p(X, Y) = Hom(Γ^p X, Y).',
    basis:
      'Pages 74–76 give axioms a)–g) and take the degree decomposition as structure after a struck lemma; pages 77–80 define strict tensor products, Γ^n by representability, derive the exponential formula and the α_{p,q} with their associativity square; pages 81–82 build 𝐏 from a ⊗-pd-category with composition g ∘ Γ^q(f) ∘ α_{q,p}; page 83 says « On vérifie alors les axiomes a) à f) » and « Les deux notions sont donc équivalentes ». The phrase on p. 83 saying what is verified about strict tensor products carries \\ill{} and \\uncertain{} words; page 76 has two nearly illegible margin notes, one beginning « Oublié : ».',
    ours:
      'The equivalence is asserted on p. 83 and not proved; the reading says so. The edition corrects id_Y to id_X in the action μ_n (p. 74), the index of the vertical arrow in the associativity square (p. 80), and reads « applications bil. » (p. 82, \\uncertain{}) as linear in the outer variable only. The reading also notes that the page refers to axioms a)–f) while p. 76 lists a)–g). The match of the folder’s final question with the Friedlander–Suslin definition of strict polynomial functors is a match, recorded in the reading, and is not this claim.',
    literature: [
      'Two general web searches (2026-10-10) for categories graded by polynomial degree with composition additive in one variable, and for monoidal categories with an exponential divided-power functor defining polynomial morphisms, found no such axiomatisation; they surfaced the categories Γ^d P of strict polynomial functor theory (Krause, « Koszul, Ringel and Serre duality for strict polynomial functors », arXiv:1203.0311; « Generalized polynomial functors », arXiv:2308.16442) and Roby-style polynomial maps (arXiv:1112.0991), none read for this question',
    ],
    status: 'unsearched',
    settle:
      'Decide whether either notion, or the equivalence, is in print: Roby, « Lois polynomes et lois formelles » (Ann. ENS 80, 1963) and « Lois polynômes multiplicatives » (1980); Friedlander–Suslin (Invent. Math. 127, 1997) § 2; Bousfield, « Operations on derived functors of non-additive functors » (1967); Joyal’s analytic functors and the theory of Γ-rings / Tambara functors for exponential structures; and the literature on categories with polynomial (non-additive) hom-structures, such as Blute–Cockett–Seely differential categories and Ehrhard’s models of differential linear logic, where Hom(!X, Y) plays the role of Hom(Γ X, Y). A match would most likely be a « !-coalgebra / Seely category » formulation; check that its morphisms and composition coincide with 𝐏_p(X, Y) = Hom(Γ^p X, Y) and g ∘ Γ^q(f) ∘ α_{q,p} before marking matched.',
  },
  // Folder 9 — find-novelty pass, Opus 5.5 (claude-opus-5-5), 2026-10-10, on a reading made by Opus 5.5 (pass header 2026-10-03).
  {
    id: '9-det-etale-tate-iso',
    cote: '9',
    pages: '22–28',
    kind: 'mathematical',
    claim:
      'For an ordinary, locally polarisable abelian scheme A over a connected base of characteristic p, α_A = det T_p(φ̃)_ét / √deg φ̃ is independent of the polarisation φ and is an isomorphism of lattices det T_p(A)_ét ≃ det T_p(A*)_ét, compatible with base change; for an isogeny it satisfies only det T_p(u)_ét · det T_p(u*)_ét = deg u, not naturality.',
    basis:
      'Pages 23–24 define β_p(φ) and α_p(φ) on the ℓ-adic model α_ℓ = β_ℓ(φ)/deg φ̃; pages 24 and 26 prove independence by reducing to Δ(u) = δ(u) for symmetric positive u (next entry); pages 26–27 prove the lattice statement from the self-duality of Ker φ̃ and the absence of a local-local part, and box the resulting isomorphism. Pages 27–28 box the automorphism and endomorphism identities. The step Δ(u)Δ(u*) = deg u on page 24 is introduced by « Or par \\ill{} on a »: its justification is illegible, and page 25, which attributed it to a « théorème p-adique ou th. caractéristique de Weil », is cancelled. Pages 27–28 carry several \\ill{} and an \\uncertain{identifiant} in the automorphism paragraph, and the margin extending the boxed identity to isogenies of equal dimension is very uncertain. Points c) (α_{A*} = α_A⁻¹, « signe (?) ») and d) (agreement mod p with the de Rham isomorphism ω_A ≃ ω_{A*} of page 21) are left « à vérifier ».',
    ours:
      'The edition supplies: the hypotheses of local polarisability and a connected base; the proof of Δ(u)Δ(u*) = deg u (étale and multiplicative parts of the Dieudonné module of an ordinary A, determinant of u on the whole being deg u) — the page uses the identity without a legible justification; the restriction of the rationality argument of page 26 to symmetric elements, without which it fails; the reading of ⊗Q_ℓ as ⊗Q_p and of the target of page 23 as det T_p(A*)_ét; the general isogeny form det T_p(f*)_ét ∘ α_B ∘ det T_p(f)_ét = (deg f) α_A and the computation of c) up to sign. The definitions, the statements a) and b), and the arguments for them are the page’s.',
    literature: [
      'Web search, 2026-10-10 (two queries on a canonical isomorphism between determinants of the étale parts of T_p(A) and T_p(A^t) for ordinary abelian schemes): no statement of it surfaced. This is not a reading of any source.',
      'Chai, « Families of ordinary abelian varieties: canonical coordinates, p-adic monodromy, Tate-linear subvarieties and Hecke orbits » — located as the most likely place, not read (download refused, HTTP 403).',
    ],
    status: 'unsearched',
    settle:
      'Read Chai’s « Families of ordinary abelian varieties » (Serre–Tate coordinates and p-adic monodromy sections), Katz « Serre–Tate local moduli » (LNM 868, 1981) and Faltings–Chai, Degeneration of Abelian Varieties, V.1–V.3 (ordinary locus, Igusa tower, det of the étale quotient vs. ω^{p−1}) for an isomorphism det T_p(A)_ét ≃ det T_p(A^t)_ét, or equivalently a trivialisation of det T_p(A)_ét ⊗ det T_p(A^t)_ét^∨ over the ordinary locus. If it is there, or follows in a line from the Weil pairing plus the standard description of the unit-root crystal, mark matched.',
  },
  {
    id: '9-symmetric-positive-det-sqrt-degree',
    cote: '9',
    pages: '24, 26',
    kind: 'mathematical',
    claim:
      'For an ordinary polarised abelian variety A and u ∈ End(A) ⊗ Q symmetric and positive for the Rosati involution, the determinant of u on the étale part of the p-adic Tate module equals +√deg u, the positive root — while for a general endomorphism (e.g. Frobenius over F_q) it does not.',
    basis:
      'Page 24 reduces to Δ(u)² = δ(u)² from Δ(u)Δ(u*) = deg u and u* = φ̃uφ̃⁻¹, and states the sign as the remaining point (« exorciser le signe », \\uncertain{} on that word only); page 26 removes the sign by a positivity argument: Δ is a polynomial with Q-coefficients on the symmetric part, extends to End(A) ⊗ R, and on the positive cone every element is a square v², so Δ(u) = Δ(v)² ≥ 0. The general lemma det T_p(u)_ét = √deg u for every endomorphism, on page 23, is struck through and marked « faux » in the margin.',
    ours:
      'As in 9-det-etale-tate-iso: the input identity Δ(u)Δ(u*) = deg u rests on an illegible citation and its proof is the edition’s; the page asserts rationality of Δ on all of End(A) and the edition restricts it to symmetric elements, where it holds; the Frobenius counterexample to the struck lemma is the edition’s. The positivity step v² ↦ Δ(v)² ≥ 0 is the page’s.',
    literature: [
      'Web search, 2026-10-10 (one query on det of an endomorphism on the étale part of the p-divisible group of an ordinary abelian variety and √deg for Rosati-symmetric positive elements): no statement of it surfaced. This is not a reading of any source.',
    ],
    status: 'unsearched',
    settle:
      'Check Mumford, Abelian Varieties §21 (Rosati involution, positivity, deg u as a norm) together with the unit-root factorisation of the characteristic polynomial for ordinary A (Deligne, « Variétés abéliennes ordinaires sur un corps fini », Invent. Math. 8, 1969; Serre–Tate canonical lift): if the identity follows there from the norm form of the totally real symmetric subalgebra in a line, mark matched; otherwise it is a candidate.',
  },
// Folder 40 — find-novelty pass, Opus 5.5 (claude-opus-5-5) on an Opus 5.5 reading, 2026-10-10.
// Pool from 40.modern.tex: Hopf-algebra dictionary (pp. 1-4), pseudo-torsor criteria (pp. 9-15),
// alpha_p actions as p-nilpotent derivations (pp. 16-18), H^1(A, alpha_p) = A/A^p (pp. 19-23),
// Frobenius sequence (pp. 24-26) — all textbook matches (SGA 3, Demazure–Gabriel, Milne III.4), dropped.
// The k[[X]] list with n <= p-1 (p. 26) is a statement the reading had to repair; dropped.
  {
    id: '40-operator-criterion',
    cote: '40',
    pages: '9, 12–15',
    kind: 'mathematical',
    claim:
      'For B and C free of finite type, Spec C is formally principal homogeneous under Spec B exactly when the map C ⊗ 𝒰 → End_A(C), x ⊗ u ↦ (y ↦ x·(u·y)), with 𝒰 = Hom_A(B, A), is bijective — the operators of the dual Hopf algebra, with coefficients in C, give all A-linear endomorphisms of C.',
    basis:
      'Page 9 announces the equivalence (with a marginal « ? »); pages 12–13 prove the direction φ iso ⇒ ψ iso by two columns of diagrams with an explicit inverse ψ′; pages 14–15 attempt the converse through a map ρ and stop at « Pour ceci, ---- » with « ??? ».',
    ours:
      'The converse (ψ iso ⇒ φ iso) is not on the page: the reading proves it by observing that ψ is the C-transpose of φ, which needs C finite projective. The transposition argument, and the remark that C ≠ 0 is needed for the invariants condition, are the edition’s.',
    literature: [
      'S. Montgomery, Hopf Algebras and Their Actions on Rings (CBMS 82, 1993), §8.3 — located only through the secondary sources below, not read directly',
      'H. F. Kreimer and M. Takeuchi, « Hopf algebras and Galois extensions of an algebra », Indiana Univ. Math. J. 30 (1981) — cited for finite projectivity of H-Galois extensions in arXiv:1903.06358 (survey on subrings of invariants of finite-dimensional Hopf actions); not read directly',
      'arXiv:math/0207187 (Hopf Galois extensions, triangular structures and Frobenius Lie algebras in prime characteristic), which uses A # H ≅ End A for an H-Galois extension',
      'arXiv:0912.0291 (Galois theory of Hopf Galois extensions), definition via the canonical map A ⊗_B A → Hom(H, A), attributed to Kreimer–Takeuchi extending Chase–Sweedler (LNM 97, 1969)',
    ],
    status: 'matched',
    settle:
      'Open Montgomery §8.3 (the theorem characterising H-Galois extensions by A # H* ≅ End(A_{A^coH}) plus finite projectivity) and Chase–Sweedler LNM 97 §9, and record the exact theorem numbers; the match is to that equivalence with A^coH = A, which the page’s setting supplies once C is free and non-zero. If the hypotheses differ in a way that matters, reopen.',
  },
  {
    id: '40-alpha-p-regular-sum',
    cote: '40',
    pages: '26–27',
    kind: 'mathematical',
    claim:
      'Over A = k[[X]], k algebraically closed of characteristic p, the α_p-torsors whose rings are regular are not closed under the group law of H¹(A, α_p) = A/A^p: the torsors of p-th roots of X and of −X + X² are regular, their sum (p-th root of X²) is not, and already their fibre product over A is non-reduced.',
    basis:
      'Page 26 states regularity of A[T]/(T^p − X^n) iff n = 1 and gives the cusp for p = 3, n = 2; page 27 writes that this covering is the sum of the two regular ones and that their fibre product is ≅ C₁[T]/(T^p), which has nilpotents. Page 26’s lead-in to the sum rests on uncertain and illegible words (« \\ill{} point \\ill{} vue des 𝓑-revêtements »); the statement itself on page 27 is clearly read.',
    ours:
      'The page asserts C₁ ⊗_A C₂ ≅ C₁[T]/(T^p) without proof; the computation (−X + X² = (−s + s²)^p in C₁) is the reading’s. That the sum in H¹ is the sum in A/A^p — which page 22 says is not proved — is supplied by the reading through the Frobenius coboundary.',
    literature: [
      'arXiv:1911.02267 (Maximal models of torsors over a local field) — gives, as seen in a search summary only, regularity of R[X]/(X^p − uπ^i) exactly for i = 1; nothing found there about sums',
      'Two web searches (2026-10-10) for regularity of sums of α_p-torsors over k[[x]]: nothing found; no paper read in full',
    ],
    status: 'candidate',
    settle:
      'The single-torsor criterion is in the literature; the question is only whether the failure of regularity under the group law is recorded — look in work on models of α_p-torsors over DVRs (arXiv:1911.02267 §7, and the literature on inseparable covers of surfaces) and in Milne, Étale Cohomology III.4. Given how elementary it is, expect a match or an exercise; if found, mark matched.',
  },
  {
    id: '64-legendre-pinning-moduli',
    cote: '64',
    pages: '74–79, 84–91',
    kind: 'mathematical',
    claim:
      'Over Z[1/2], elliptic curves with an ordered 2-torsion (a Jacobi pinning of level 2) and a « Legendre pinning » — a tangent vector at the origin, twisted by a fixed μ₄-torsor, whose square matches the tangent space of E/±1 at the image of the origin through an identification of μ₄* with the two cyclic orders of the 2-torsion — form a rigid groupoid represented by U_{0,3} × μ₄*, and μ₄ × 𝔖₃ acts on that scheme, 𝔖₃ tautologically on U_{0,3} and through the sign on μ₄*.',
    basis:
      'Pages 74–79 define the Legendre pinning over a field and state the groupoid equivalence with triples (J, t, α); page 84 adds the level-2 Jacobi pinning and says the fibred category becomes rigid, equivalent to pairs (t, α) with t a section of U_{0,3} and α a section of μ₄*; page 85 says it is « représentable par le schéma U₀₃ × μ₄* » and identifies the tangent bundle along the zero section with 𝒪_{U_{0,3}}(1); pages 86–91 give the μ₄ × 𝔖₃ action and the subgroup 𝔖₃ ×_{μ₂} μ₄ acting trivially on μ₄*. No proof of representability is written. The words carrying the statement are read; the uncertain « hexagonale » (p. 84) and the half-read parenthesis « (par Legendre–[ill.]) » (p. 85) do not carry it.',
    ours:
      'The reading supplies an explicit μ₄-torsor Q₀ over Z[1/2] (the roots of x⁴ = −4) for the square the page fixes « une fois pour toutes » without constructing it, and names the order-12 subgroup as the dicyclic group. The comparison with Antieau–Meier below is this pass’s. Written on Opus 5.5 against a reading made on Opus 5.5.',
    literature: [
      'B. Antieau and L. Meier, The Brauer group of the moduli stack of elliptic curves (arXiv 1608.00851), §4: Definition 4.4, Proposition 4.5 and Lemma 4.7, read 2026-10-10. Over Z[1/2] the Legendre parameter space X = A¹ − {0, 1} gives M(2) ≃ B C₂,X; X → M(2) is the C₂-torsor of square roots of p·ω^{⊗2}, p = e₂ − e₁; and the 𝔖₃-action does not lift strictly to X, so it is described by twisting with torsors T_{f,g}. Neither the μ₄*-twisted pinning nor a scheme with a strict μ₄ × 𝔖₃ action appears there.',
      'Web search, 10 October 2026: « Legendre family fine moduli space level 2 structure differential Katz Mazur rigidification sqrt(-1) Z[1/2] » and « Legendre elliptic curve moduli level 2 stack Bμ₂ gerbe lambda line rigidification tangent vector ». These turned up Antieau–Meier and papers on the μ₂-gerbe over the level-2 or j-line, not the pinning.',
    ],
    status: 'candidate',
    settle:
      'Read Katz–Mazur, Arithmetic Moduli of Elliptic Curves (1985), on the Legendre family and level-2 structures, and Deligne–Rapoport (LNM 349) on Γ(2). Look for a rigidification of M(2) over Z[1/2] by a tangent vector at the origin together with a choice of √−1, represented by A¹ − {0, 1} over Z[1/2, i]. If it is there, mark matched. Antieau–Meier’s torsor X → M(2) already kills the generic μ₂ by a square root, without √−1. What the folder adds is the price of i and the strict 𝔖₃-equivariance, and that is the question.',
  },
  {
    id: '64-octahedral-configurations-relative',
    cote: '64',
    pages: '44–52',
    kind: 'mathematical',
    claim:
      'For a projective-line bundle X over a scheme S with residue characteristics ≠ 2, three things correspond bijectively: subgroup schemes of Aut_S(X) locally isomorphic to (Z/2)², subgroup schemes locally isomorphic to 𝔖₄, and regular octahedral configurations (étale degree-6 divisors with antipody). Moreover, pairs (X, Δ) whose orientation torsor is identified with μ₄* are equivalent to finite étale covers of degree 4 of S.',
    basis:
      'Page 46 gives the étale-local normal form σ₁(z) = −z, σ₂(z) = 1/z; pages 48–49 compute the fixer of two non-opposite vertices; the Théorème of page 51 states the three sets and page 52 the four maps between them; Corollaire 2 on page 52 states the equivalence with degree-4 étale covers via faces modulo antipody, with the conic x² + y² + z² = 0 over Z[1/2] as the standard structure. No proof of Corollaire 2 is written. The qualifier that makes it an equivalence, « munis d’un isom. Or_{Δ/S} ≃ μ*_{4S} », is a marginal addition. In it, Or is overwritten and « μ₄*-orientation » is marked uncertain in the transcription.',
    ours:
      'The reading adds the hypothesis « 5 invertible » wherever the page identifies Aut_S(X, Δ) with the octahedral rotation group: over F₅ the configuration is P¹(F₅) and Aut is PGL₂(F₅) ≃ 𝔖₅, as the reading checks. The page’s own margin bounds the computation by « car. ≠ 3 et 5 ». It also reads « icosaédrale » as octaédrale in c), Corollaire 1 and page 59. The bijections a)–b)–c) are claimed here without the char-5 restriction, following the reading’s footnote; that step is the reading’s.',
    literature: [
      'A. Beauville, Finite subgroups of PGL₂(K) (arXiv 0909.3942), Proposition 1.1 and Theorem 4.2 with its proof, read 2026-10-10. It covers a field K with group order prime to the characteristic: 𝔖₄ ⊂ PGL₂(K) iff −1 is a sum of two squares, with a single conjugacy class; Klein subgroups are classified through K*/K*², and the normaliser of a Klein subgroup over K_s is 𝔖₄. That is the field case on a fixed P¹_K, with no base scheme, no forms of P¹, no octahedral divisor and no equivalence with quartic étale covers.',
      'Web search, 10 October 2026: « Beauville Finite subgroups of PGL2(K) octahedral forms conic S4 subgroup classification over a field ».',
    ],
    status: 'candidate',
    settle:
      'Check whether the relative statement, and above all Corollaire 2 ((X, Δ, Or ≃ μ₄*) ↔ quartic étale covers, i.e. H¹(S, 𝔖₄) with 𝔖₄ acting on the conic x² + y² + z² = 0 by signed permutations), is in the literature on forms of P¹ with finite group actions: Serre, Topics in Galois Theory, § 2.5 on embeddings into PGL₂; Klein’s Vorlesungen über das Ikosaeder for the classical field case; work on the relative Brauer–Severi and conic-bundle side. Before any search, a person should settle from the facsimile what the marginal qualifier of page 52 says, since the equivalence depends on it.',
  },
  {
    id: '64-gl2-z4-combinatorial-model',
    cote: '64',
    pages: '25–31',
    kind: 'mathematical',
    claim:
      'Free rank-2 Z/4Z-modules are canonically equivalent, as a groupoid, to triples (I, Q, k): a four-element set I, a combinatorial square Q, and a bijection k from the orientations of I to the codiagonals of Q. Hence GL₂(Z/4Z) ≃ 𝔖₄ ×_{±1} D₄ canonically, as the fibre product of the sign of 𝔖_I and the character of 𝔇_Q on the codiagonals.',
    basis:
      'The Théorème of page 27 (18) gives M ↦ (M₀, I_M, S_M). Corollaire 2 (21) and Corollaire 3 (22) on page 28 give the triples and the cartesian square. Pages 29–31 give the derived subgroups, abelianisations and the lattice of subgroups. The statements read cleanly. The margin of page 27, on the semidirect decomposition, carries five \\ill{} words, but its formulas are legible and the entry does not rest on it.',
    ours:
      'The reading corrects the page’s direct product (GL(M₀)·M₀) × F₂^ω to a semidirect product (page 31). The deduction that the abstract fibre product agrees with the GroupNames description below is this pass’s: the kernel of χ_C is a Klein subgroup of D₄, and D₄ acts on 𝔖_I⁺ ≃ A₄ through D₄/V_S ≃ C₂.',
    literature: [
      'T. Dokchitser, GroupNames, page « A4⋊D4 » (SmallGroup(96,195)), consulted 2026-10-10. It lists GL₂(Z/4Z) as an alias and describes the group as A₄ ⋊ D₄ with D₄ acting through D₄/C₂² ≃ C₂, which is the abstract group of Corollaire 3.',
      'Groupprops, page « General linear group:GL(2,Z4) », found by search 2026-10-10, not read beyond the search summary.',
    ],
    status: 'matched',
    settle:
      'The abstract isomorphism is in GroupNames, so the group-theoretic content is matched. The status would be revisited only if someone finds that the canonical groupoid equivalence (21), with its dictionary C_Q ↔ sg, D_Q ↔ sg·det, ω_Q ↔ det, is itself unpublished and worth listing separately. That is a question about a functorial form, not about the group.',
  },
  {
    id: '64-pages-146-147-reversed',
    cote: '64',
    pages: '145–148',
    kind: 'codicological',
    claim:
      'Pages 146 and 147 are bound in the reverse of the order of the argument: the reading order is 145, 147, 146, 148.',
    basis:
      'The author’s formula numbers run (10) on page 145, (11)–(13) on page 147, (14) on page 146 and (15) on page 148. Page 147 opens by continuing page 145 (« on trouve »), introducing τ_∞ and the action g·τ = (aτ + b)/(cτ + d). Page 146 uses that action in (14), T_g(τ, z) = (gτ, z/(cτ + d)), and page 148 extends it to T_{g,m,n} in (15).',
    ours:
      'The observation is the transcription’s (batch 8 header and its note on page 147), and the reading reads the two pages in the order of the argument. The facsimile was not consulted by this pass.',
    literature: ['Transcription 64, batch 8 (batch-08.fr.tex), header and pages 145–148'],
    status: 'candidate',
    settle:
      'A person checks on the facsimile whether pages 146 and 147 are the two faces of one leaf, in which case the « reversal » is just which face was scanned first, or two separate leaves filed in the wrong order.',
  },
  {
    id: '64-page-156-june-1981-notice',
    cote: '64',
    pages: '154–156',
    kind: 'codicological',
    claim:
      'The jottings on page 156 are written in the blanks of a printed administrative notice stamped « 9 JUIN 1981 » and « 16 JUIN 1981 ». They take up the form T² + 2αT + b of page 154, so at least those jottings were not written before the notice existed.',
    basis:
      'The batch-8 transcription notes that page 156 is a printed convocation carrying both stamps, with only the calculations transcribed: T² + 2αT + b, x² + αxy + βy², T² + απT + βπ² over F₂[T, π], 4T − 1. Page 154 introduces T = S − α and B ≃ A[T]/(T² + 2αT + b) in the study of the normality of A[S]/(S² − a).',
    ours:
      'The link between the jottings and page 154 is drawn by the transcription and the reading. That this bounds the date of the jottings, and of nothing else in the folder, is this pass’s. It is consistent with the inventory’s « [à partir de 1980-1982] » and does not narrow it for pages 1–155.',
    literature: ['Transcription 64, batch 8 (batch-08.fr.tex), header and pages 154, 156'],
    status: 'candidate',
    settle:
      'A person reads the notice on the facsimile: its nature, its sender and whether the stamps are dates of dispatch or of a meeting. They also check whether page 156 is the verso of pages 154–155 or a separate sheet. Note what this dates: the jottings on that sheet, not the appendix they repeat, and not the folder.',
  },
// Folder 123 — find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, over the Opus 5.5 reading of 2026-10-03.
// Three entries, all unsearched: the only search was three general web queries, not a reading of the named books.
  {
    id: '123-steinberg-no-resolution-picard',
    cote: '123',
    pages: '10–13',
    kind: 'mathematical',
    claim:
      'Over a base S, a resolution of the Steinberg map G → T/W that is an isomorphism over G^reg with exceptional locus of codimension ≥ 2 fibre by fibre cannot exist, because its Picard group would be finite modulo Pic(S) while that of the Grothendieck–Springer space G̃ contains the weight lattice with its ample cone. The necessity of the base change T → T/W is obtained here from a Picard-group comparison, not from monodromy.',
    basis:
      'Pages 10–11 prove Pic(Bor) ↪ Pic(G̃) ≅ Pic(G̃^reg) ≅ Pic(G′^reg) by depth and EGA IV 21.4.13. Page 13 d) proves Pic(S) ↪ Pic(G) ↪ Pic(G^reg) with finite cokernel, then concludes « Cela montre qu’on ne peut trouver une résolution X̃ … sans toucher à G^reg ». The words « ne peut » are \\uncertain{} in the transcription, and the sentence breaks off on « … ».',
    ours:
      'The reading adds the hypothesis that S is regular for the finiteness of Coker(Pic(S) → Pic(G^reg)). The page strikes « si S régulier » and infers finiteness from injectivity alone. The reading also writes out the contradiction (rank 0 against the rank-r weight lattice with its ample cone), which the page leaves at « … ». As written, the argument needs X̃ regular, so that Pic(X̃) = Pic(X̃ minus the exceptional locus), and X̃ → G projective, so that it has a relatively ample bundle. Neither assumption is stated on the page.',
    literature: [
      'General web search, 2026-10-10, for a Picard-group proof that the adjoint quotient has no simultaneous resolution without base change: no relevant hit. Slodowy and Brieskorn were not opened.',
    ],
    status: 'unsearched',
    settle:
      'The statement itself, that simultaneous resolution needs the base change by W, is classical (the reading’s footnote cites Brieskorn, Nice 1970, and Slodowy 1980), so only the route is in question. Read Slodowy, Simple Singularities and Simple Algebraic Groups (LNM 815, 1980), ch. 4, and Brieskorn, ICM Nice 1970, for the argument used. If a Picard-group or ample-cone argument appears there, or in Springer’s or Steinberg’s treatment of the group case, mark matched.',
  },
  {
    id: '123-grothendieck-springer-pic-twisted-torus',
    cote: '123',
    pages: '10–12',
    kind: 'mathematical',
    claim:
      'For a reductive group scheme over a normal integral base S whose abstract maximal torus T is not split, Pic(Bor) → Pic(G̃) is injective with cokernel inside H¹(Γ, X*(T)), where Γ is the image of π₁(S) in Aut X*(T). The map is bijective when this H¹ vanishes, and for regular S only then. A line bundle on Bor is ample if and only if its pull-back to G̃ is, with no normality assumption on S.',
    basis:
      'Page 11 proves the lemma Pic(B) = Pic(T) = H¹(Γ, X*(T)) by the torsor B → T, Hochschild–Serre and Hilbert 90, and applies it to the generic fibre of G̃ over Bor. Page 12 a) writes the exact sequence 0 → Pic(Bor) → Pic(G̃) → H¹(Γ, M_ξ̄), and b) extends injectivity and the ampleness criterion to non-normal S. The sufficient condition and « on a une réciproque si S régulier » sit in a margin read with several \\uncertain{} and \\ill{}. On page 12, « flèche » (completing the sequence by → 0 for S regular) is \\uncertain{}, and the reading calls the passage « criblé de mots illisibles ».',
    ours:
      'The page’s theorem states Pic(Bor) ≅ Pic(G̃) without condition. The reading puts the H¹(Γ, X*(T)) = 0 condition into the statement, taking it from the margin and from page 12. It corrects the ample cone from P⁺ to the strictly dominant weights, and reads « T = ∏_{k′/k} T′ » as « T splits over k′ ». The iff for regular S rests on uncertain readings.',
    literature: [
      'General web search, 2026-10-10, for the Picard group of the Grothendieck–Springer space with a non-split torus: hits treat only the split case over a field. No book was opened.',
    ],
    status: 'unsearched',
    settle:
      'Check SGA 3 (Exp. XXII–XXVI) and Demazure’s thesis for Pic of the scheme of Borels over a base in the non-split case. Then check Sansuc, « Groupe de Brauer et arithmétique des groupes algébriques linéaires » (Crelle 327, 1981), §6, where Pic of a torus and of a group is H¹(Γ, X*) by the same route, for whether the comparison with G̃ is stated. Also check whether the iff for regular S is really on page 12 by re-reading the facsimile with /transcribe-grothendieck. If the statement is found, mark matched.',
  },
  {
    id: '123-kostant-rigidifications-count',
    cote: '123',
    pages: '21, 28, 30, 34',
    kind: 'mathematical',
    claim:
      'For a simple adjoint group G with (h, p) = 1, G acts freely on quadruples (T, B, T′, B′) with T, T′ maximal tori in apposition (Kostant) and B ⊃ T, B′ ⊃ T′ Borel subgroups. The quotient RigKos/G is finite étale of rank card(W)²/(h·z·φ(h)), and of rank card(W)²/(h·z) once a generator of T ∩ N(T′) ≅ μ_h is also given.',
    basis:
      'The letter to Kostant (page 21, 22 Oct. 1969) and page 34 assert the count without proof. The letter’s foot-note gives N(T) ∩ N(T′) as an extension of (ℤ/hℤ)* by ℤ/hℤ × 𝔷, of order h·z·φ(h). Page 30 writes T ∩ T′ = 0, and page 28’s grid gives the subgroup lattice. On page 34, « librement » and « rang » are \\uncertain{}.',
    ours:
      'The reading marks the count as asserted, not proved. It checks that the number is an integer for A₁, A₂, B₂ and G₂ (1, 2, 4, 12). This pass’s own step, not on the page: an element fixing (T, B, T′, B′) lies in N(T) ∩ B = T and in T′, so the action is free once T ∩ T′ = 1. The count then reduces to the order of N(T) ∩ N(T′), which the folder asserts and does not prove.',
    literature: [
      'General web search, 2026-10-10, for counts of Borel pairs over tori in apposition: no count found. Kostant 1959 (Amer. J. Math. 81) was not opened.',
    ],
    status: 'unsearched',
    settle:
      'Prove or refute |N(T) ∩ N(T′)| = h·z·φ(h) (the image in W should be W_K ≅ P∨/Q∨ extended by (ℤ/hℤ)*). Then look for the count in Kostant 1959 §§6–9, Springer, « Regular elements of finite reflection groups » (1974), and the literature on Coxeter tori and Kostant–Coxeter pairs. A small-rank computer check (A₂, B₂, G₂) of orbit counts would settle the number independently.',
  },
  // Folder 128 — find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, over the Opus 5.5 reading of 2026-10-03.
  // Web searches (search-engine snippets only, no source read in full) located Ferrand 2003 and Ferrand–Olivier 1970 as the places to check; neither was read, so nothing below is beyond `unsearched`.
  {
    id: '128-nilpotent-conductor-flat-descent',
    cote: '128',
    pages: '4–9',
    kind: 'mathematical',
    claim:
      'If I is a nilpotent ideal of A mapping isomorphically onto an ideal of A′ (a Milnor square A, A′, A/I, A′/I) and Spec A′/IA′ → Spec A/I is an effective descent morphism for flat modules, then Spec A′ → Spec A is an effective descent morphism for flat modules, and stays one after flat base change.',
    basis:
      'Page 1’s exact sequence 0 → I_cst → C•(A′/A) → C•(A′₀/A₀) → 0 gives H^i(A′/A) ≅ H^i(A′₀/A₀) for i ≠ 0 (pp. 2–4); Prop. 2 (pp. 4–7) lifts effectivity from E′₀ to E′ in the square-zero case and inducts on the nilpotency order; Cor. 1–3 (pp. 7–9) globalise it.',
    ours:
      'The last step on page 6 (E ⊗ A′ → E′ an isomorphism, by Nakayama and flatness of E′) is almost wholly illegible and is reconstructed by the reading; the reading also names the local flatness criterion for a nilpotent ideal, which the page uses unnamed, writes out the induction on the nilpotency order, and notes that the hypothesis H¹(A′/A) = 0 is not used. The page’s Cor. 3 says « Y quelconque »; the reading restricts it to flat Y and gives its own counterexample for arbitrary Y.',
    literature: [],
    status: 'unsearched',
    settle:
      'Read D. Ferrand, « Conducteur, descente et pincement », Bull. SMF 131 (2003), §2 (modules over a fibre product of rings, Th. 2.2) and its descent sections: if flat modules over the Milnor square glue as Ferrand shows, the statement may follow formally, without nilpotence — then mark matched. Also check the Stacks Project chapters on descent and on pushouts/pinchings, and Mesablishvili’s results on effective descent for modules (pure morphisms).',
  },
  {
    id: '128-colength-one-equivalence-criterion',
    cote: '128',
    pages: '12–18',
    kind: 'mathematical',
    claim:
      'For A local artinian and A′ a finite A-algebra with trivial residue extensions, if some equivalence ideal J makes A → A′ ⇉ (A′ ⊗_A A′)/J exact and δ(x′) = p₂(x′) − p₁(x′) generates the ideal Δ for every x′ ∉ A, then length(A′/A) ≤ 1; and when A′/A ≅ A/𝔪, Spec A′ carries exactly two equivalence relations over Spec A.',
    basis:
      'Page 12–13 Prop. 1 (A′/A ≅ k gives 𝔪A′ = 𝔪, reduces to a rank-2 k-algebra); pages 14–18 Prop. 2, split into the non-radicial case (reduced to A′₀ ≅ kⁿ, « on trouve n = 2 ») and the radicial case (Ω = Δ/Δ², 𝔪′² ⊂ 𝔪, reduction to A′ = k ⊕ V with V² = 0).',
    ours:
      'Much of the proof is the edition’s: the case k[ε] of Prop. 1 (i) (the page breaks off after « ε² = 0 »), the count 2(n−1) = n² − n behind « n = 2 », the justification that J is nilpotent, and the whole end of page 18 (dim V = 1), where the page stops at « il faut prouver ». The hypothesis on residue extensions is a marginal addition the reading folds into the statement; the case-split word « n’est pas [radiciel] » on page 14 is \\uncertain{} in the transcription.',
    literature: [],
    status: 'unsearched',
    settle:
      'Read D. Ferrand and J.-P. Olivier, « Homomorphismes minimaux d’anneaux », J. Algebra 16 (1970), Th. 2.2–2.3: colength one here is a minimal extension with crucial ideal 𝔪 = conductor, and the two-relation statement may be a reformulation of their decomposed/ramified/inert classification. Then check the later minimal/FCP-extension literature (Dobbs–Shapiro; Picavet and Picavet-L’Hermitte) for a criterion phrased through T ⊗_R T and the diagonal ideal. Page 31, in another hand (the « Notes Murre-Levelt » of the title), treats the same k ⊕ V case; if those notes are identified in print, check them too.',
  },
  {
    id: '128-infinitesimal-descent-theorem',
    cote: '128',
    pages: '19–29',
    kind: 'mathematical',
    claim:
      'For A semi-local noetherian with radical 𝔪 and A′ finite over A, with A_n = A/𝔪^{n+1}, the folder states — but does not establish — that vanishing of H¹(A′_n/A_n) for all n, triviality of H¹(A′_n/A_n, Gl_r) for all n, and effective descent of flat quasi-coherent modules along Spec A′_n → Spec H⁰(A′_n/A_n) for all n are equivalent, and that they imply effective descent for flat modules of finite type along Spec A′ → Spec H⁰(A′/A).',
    basis:
      'The Théorème of page 25 and its proof on pages 26–29, by induction on n through square-zero ideals using Lemme 1 (p. 19–20: Ker H¹(G_m) ≅ Ker H¹(G_a) under B̃₀ = B̃₀* + B̄), its Cor. 2–3 (pp. 21–22) and Lemme 2 (pp. 23–24), then Mittag-Leffler for the limit.',
    ours:
      'The reading finds that the square of page 20 does not commute (the multiplicative coboundary is the logarithmic derivative u⁻¹∂(u), not ∂(u)), so Lemme 1, its corollaries and the steps of a) that use them are unproved in the folder; the Mittag-Leffler condition, the Artin–Rees remark for b)(iii) and the observation that Lemme 2 (i) is implied by (ii) are the edition’s. Large parts of pages 23–27 are illegible, part c) is not proved, and the « qu. cohér. / plats » of (iii) is \\uncertain{}.',
    literature: [],
    status: 'unsearched',
    settle:
      'First decide Lemme 1: either prove Ker(H¹(A′/A, G_m) → H¹(A′₀/A₀, G_m)) ≅ Ker(… G_a …) under the stated hypothesis or find an Amitsur-complex counterexample. Only if it holds, compare the theorem with SGA 1 VIII and IX (descent, formal and infinitesimal), EGA III §5 and EGA IV §18, and Ferrand 2003, where descent along finite non-flat morphisms is decided on infinitesimal neighbourhoods.',
  },
  {
    id: '138-operations-belyi-extending',
    cote: '138',
    pages: '122–124, 127',
    kind: 'mathematical',
    claim:
      'An « operation » on oriented maps given by a subset A of the reference sphere (A pulled back along each map’s cover f : X → S) is, apart from one exceptional case, composition with a cover φ : S → S ramified only over 0, 1, ∞, with φ⁻¹{0, 1, ∞} ⊃ {0, 1, ∞} and ramification 2 over 1, so that A = φ⁻¹([0, 1]) and A_X = (φf)⁻¹([0, 1]): the converse of the construction of operations from Belyi-extending maps.',
    basis:
      'Page 122 identifies the operations for F = 𝔓 with subsets of the reference sphere up to isotopy; page 123 asserts, once vertices, face centres and edge midpoints of A have been chosen by the rules of page 124, that A is deduced from such a φ by taking the inverse image of [0, 1], and page 127 completes the sentence (« φ⁻¹{0, ∞} ⊃ {0, 1, ∞} ») and asks « Que se passe-t-il dans le cas exceptionnel ? ». No proof is written. The word « application » before φ and « non » in « tous distincts non de 0, 1, ∞ » are \\uncertain{} in the transcription; the statement does not turn on them. The exceptional case (rule 3°, s = 1 an end of A) is not resolved on the pages.',
    ours:
      'The reading order 122 → 124 and 123 → 127 is the transcription’s, and the reading follows it; the claim depends on it. The name Belyi-extending map (Wood 2006, after Ellenberg) and the framing as a converse are ours. The page’s condition is written φ⁻¹{0, 1, ∞} ⊃ {0, 1, ∞}, which is Wood’s β({0, 1, ∞}) ⊂ {0, 1, ∞}; the extra requirement of ramification 2 over 1 (clean dessin) is the page’s and is not in Wood’s definition.',
    literature: [
      'M. M. Wood, « Belyi-extending maps and the Galois action on dessins d’enfants », Publ. RIMS 42 (2006), 721–737 (arXiv math/0304489) — §3.1 (definition: β Belyi over ℚ with β({0, 1, ∞}) ⊂ {0, 1, ∞}) and §3.2 (β(Γ) built from the « extending pattern » of β in each diamond of X_Γ), read 2026-10-10 through a fetched HTML rendering, not the printed paper. The construction there goes from β to an operation; no statement that every operation defined by a subset of the sphere arises from such a β was found.',
      'Web search, 2026-10-10, for operations on dessins by composition with Belyi maps: returned papers on compositions of Belyi maps (arXiv 2203.00912, arXiv 1610.08075 Vidunas–He) whose abstracts do not bear; none was read.',
    ],
    status: 'candidate',
    settle:
      'Read J. Ellenberg, « Galois invariants of dessins d’enfants » (in Arithmetic Fundamental Groups and Noncommutative Algebra, Proc. Sympos. Pure Math. 70, 2002), which Wood credits with defining these maps; G. A. Jones and D. Pinto, « Hypermap operations of finite order » (Discrete Math. 155, 1996); and G. A. Jones and J. S. Thornton, « Operations on maps, and outer automorphisms » (J. Combin. Theory B 35, 1983) — all cited from memory. If any of them proves that an operation given by an isotopy class of graphs on the reference sphere, functorial along all ramified covers, is composition with a Belyi-extending map, mark matched. Jones–Thornton treats only invertible operations (Out of the cartographic group), so it is unlikely to bear on subdivision-type operations.',
  },
  {
    id: '138-operations-subset-criterion',
    cote: '138',
    pages: '122, 124',
    kind: 'mathematical',
    claim:
      'The folder states a criterion for a subset A of the reference sphere to define, by pull-back along every map, a new map structure on every surface (X ∖ A_X a union of discs): as read, a) A is connected and b) A contains at most one of the points 0, 1, ∞.',
    basis:
      'Page 124, continuing page 122: « il faut et il suffit que a) A soit connexe … b) A ne peut contenir pas plus qu’un seul des points 0, 1, ∞ ». The passage between a) and b) is a palimpsest — several struck lines with \\ill{}, a box, and a boxed addition (« plus des points 0, 1, ∞ qui sont ∉ A, i.e. définit une carte sur S¹ ») whose place in the sentence is uncertain. The page writes « On prouve » and gives no proof.',
    ours:
      'This pass reads the folder differently from the reading, which reports a)–b) without comment: as read, b) excludes A = [0, 1], which gives the identity operation and plainly defines a map, so either the reading of b) or the page is wrong. What the topology appears to require is that A be connected and that each component of S ∖ A contain at most one of 0, 1, ∞ (a face containing two branch points can pull back to a non-disc). That is the pass’s own step, and it is close to the boxed addition, which may be the intended condition. The statement therefore rests on an unread passage and is not yet a claim the edition can make.',
    literature: [],
    status: 'unsearched',
    settle:
      'First re-read page 124 against the facsimile (/transcribe-grothendieck) to fix where the boxed addition goes and what b) says; if b) concerns the components of S ∖ A rather than A, rewrite the claim accordingly. Then search the same sources as 138-operations-belyi-extending (Wood 2006 §3, Ellenberg 2002, Jones–Pinto 1996) for a criterion on graphs in the reference sphere that define operations on all dessins.',
  },
  {
    id: '138-pages-122-127-order',
    cote: '138',
    pages: '122–127',
    kind: 'codicological',
    claim:
      'The leaves of the « Opérations » section are out of order: the text runs 122 → 124 and 123 → 127, page 123 opens inside a parenthesis whose beginning is in none of the pages, and pages 125 and 126 (a theorem page and a sheet of calculations) interrupt the argument.',
    basis:
      'Page 122 breaks off on « il faut et il suffit » and page 124 opens « que A ∪ [0, 1] soit un 1-complexe »; page 123 breaks off on « car φ⁻¹{0, 1, ∞} ⊃ {0, 1, ∞} et » and page 127 opens « = φ⁻¹{0, ∞} ⊃ {0, 1, ∞}) ». Both joins are recorded in notes of the transcription (batch-07, pages 122, 123, 127).',
    ours:
      'The reading follows this order and says so in a footnote; the observation is the transcription’s.',
    literature: ['Transcription 138, batch 7 (batch-07.fr.tex), pages 122–127 and its header note'],
    status: 'candidate',
    settle:
      'Look at the facsimile of pages 122–127: check the sentence joins and whether 123/124 and 126/127 are the two sides of single leaves, which would explain the order as recto–verso rather than a misbinding. Whether the opening parenthesis of page 123 continues a sheet missing from the folder is not checked.',
  },
// Folder 59 — candidate entries from /find-novelty (Opus 5.5 on an Opus 5.5 reading, 2026-10-10). Not merged into src/content/findings.ts.
  {
    id: '59-surface-even-chi-torsor',
    cote: '59',
    pages: '11–13',
    kind: 'mathematical',
    claim:
      'For an abelian scheme A/S of relative dimension 2 and a section δ of NS_{A/S} with χ(δ) even, the torsor Pic^δ_{A/S} under the dual B is trivial. Over a field, this says the Poonen–Stoll class c_δ vanishes.',
    basis:
      'Page 11 gives the canonical isomorphism (*) Pic^{δ′}_{B/S} ≃ δ̃′_* Pic^δ_{A/S}. Page 13 composes it with its analogue for δ′, uses δ″ = χ(δ)^{n−2}δ and δ̃″δ̃′ = χ(δ)^{n−1}, and deduces that the χ(δ)^{n−2}(χ(δ)−1)-th power of Pic^δ_{A/S} is trivial. The power 2χ(δ)^{n−2} is also trivial. Since χ − 1 is odd when χ is even, the page’s « Exemple » at the foot of page 13 concludes that Pic^δ is trivial for n = 2 and χ(δ) even. That example line rests on an \\uncertain{si} and an \\ill{}. The λ-exponents on page 12 are read without certainty. Page 13 indexes Pic^δ by B/S where A/S is meant.',
    ours:
      'The reading (59.modern.tex, note on page 13) holds that this statement depends on compatibilities of trivialisations that the folder asks for in its margins and never proves, and says the reading could not confirm it. This pass reads it differently, and the step is the pass’s own. Mere triviality needs no compatibility. L ↦ det(L̂)^{±1}, where L̂ is the Fourier–Mukai transform, is a morphism of fppf sheaves Pic^δ_{A/S} → Pic^{φ(δ)}_{B/S} that is equivariant along φ(δ)~ by the square theorem. The same construction on B goes back to Pic^{φφ(δ)}_{A/S}, and for n = 2 one has φφ(δ) = δ (the reading’s own formula (−1)^n χ^{n−2}δ). The composite B → B is δ̃ ∘ φ(δ)~ = −χ(δ). So (χ(δ) ± 1)·[Pic^δ] = 0, with the sign depending on conventions the pages leave open, and 2·[Pic^δ] = 0 by L ↦ L ⊗ [−1]^*L. Both χ + 1 and χ − 1 are odd, so the conclusion does not depend on the signs the pages worry about. Whether the resulting trivialisation is the canonical one is a separate question, and it stays open.',
    literature: [
      'Poonen and Stoll, « The Cassels–Tate pairing on polarized abelian varieties », Ann. of Math. 150 (1999), §4 (definition of c_λ, 2c_λ = 0, Lemma 1, Corollary 2, Proposition 3, Corollary 4), read directly: no criterion in terms of χ(λ) or the dimension',
      'Morgan and Smith, « The Cassels–Tate pairing for finite Galois modules », arXiv:2103.08530, §1.3 and §5 (Theorems 5.10 and 5.17, Remark 5.18), read only through an automated summary: no vanishing criterion in terms of χ(λ), deg λ or the dimension reported',
    ],
    status: 'candidate',
    settle:
      'A person checks the composition argument in the ours field: the equivariance of L ↦ det L̂ along φ(δ)~, and φφ(δ) = δ for surfaces. Then two tests. First, look for an abelian surface over a number field with a polarisation of even χ (type (1,2), say) and c_λ ≠ 0; one such surface refutes the claim. Second, check a sharp consequence. Since c is additive and killed by 2, the claim forces c_θ = 0 for any genus-2 curve C/k whose Jacobian has real multiplication by O_D, D ≡ 1 mod 8, defined over k: θ is then a sum of two classes of even χ, so Pic^1_C would have a k-point. Also read Moret-Bailly, « Pinceaux de variétés abéliennes » (Astérisque 129, 1985), and Polishchuk, « Abelian varieties, theta functions and the Fourier transform » (2003), for the statement.',
  },
  {
    id: '59-determinant-canonical-section',
    cote: '59',
    pages: '1–5, 16–19, 22',
    kind: 'mathematical',
    claim:
      'For X/S proper and flat with Pic^0_{X/S} = B an abelian scheme and A its dual, take a section δ of NS_{X/S}. The determinant of cohomology of the Poincaré sheaf yields a canonical trivialisation of the A-torsor Alb^{χ(δ)}_{X/S} ×^A Pic^{φ(δ)}_{B/S} ×^A (φ(δ)~_* Pic^δ_{X/S})^{(−1)}. Here φ : NS_{X/S} → NS_{B/S} is a polynomial map of degree n − 1, not additive.',
    basis:
      'Pages 1–2 define M_g = det Rf_{P*}(𝓛_g) and its change of section (*_b) with exponent χ. Pages 2–4 define φ by descent and the point ℓ(g) of the twisted torsor. Page 4 factors ℓ_δ through Alb^1 with group homomorphism −χ(δ) and boxes the section. Pages 16–19 recover ℓ_δ from det of a Fourier-type transform on X ×_S B, using (**) on page 18. Page 22 sets the sign convention for Alb^1.',
    ours:
      'The reading inserts the inverse (−1) on the pushed torsor, where the page has none, so that the convention matches (**) and Mukai. It also uses the universal property of Alb^1, which page 22 announces (« on prouve ») but never proves. The descent step is marked « détailler » in the margin. Statement and signs are therefore partly the edition’s.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check whether this trivialisation, or the map φ with its degree-(n−1) polynomiality, appears in Moret-Bailly (« Pinceaux de variétés abéliennes », Astérisque 129, and his work on the key formula), in Faltings–Chai, « Degeneration of abelian varieties », I.5, or in Polishchuk’s book on the determinant bundle and the Fourier transform. The abelian-scheme case (φ(δ)~ ∘ δ̃ = −χ(δ)) is in substance Mukai 1981 and the dual polarisation of Birkenhake–Lange §14.4. If the general form is there too, mark matched.',
  },
  // Folder 120 — find-novelty pass, Opus 5.5 (claude-opus-5-5), 2026-10-10, on a reading made by Opus 5.5 (pass header 2026-10-03).
  {
    id: '120-axiomatic-pushouts-along-embeddings',
    cote: '120',
    pages: '8–13',
    kind: 'mathematical',
    claim:
      'In a purely set-theoretic axiomatic setting — families 𝓜_n of subsets of Rⁿ stable under coordinate maps and projections, diagonal preimages, intersections, products and finite unions, with no complements, topology or order — the folder proves that pushouts X₁ ⊔_Z X₂ along tame embeddings exist and are computed as in sets once two axioms hold: every tame subset of a tame set is a fibre over a tame point of finitely many tame functions that separate the points off it (M6), and tame functions extend from tame subsets (M7); it also gives a criterion for such a pushout by finite families of compatible separating tame functions.',
    basis:
      'Page 9 adds stability under finite unions; page 10 states the criterion a)–c) and a NB generalising it to finite diagrams; page 11 proves that a set-theoretic colimit carrying a structure making the canonical maps tame is the colimit in Σ; page 12 states (M6), (M7) and the Proposition; page 13 builds the embedding of X₁ and X₂ in R^I × R^{A₁} × R^{A₂} on two levels {e₂} and {e₁} (diagram (*)). On p. 10 « paires de » is \\uncertain{}, and the NB carries an \\ill{} and three \\uncertain{} words; on p. 13 the direction of two arrows of diagram (*) is uncertain.',
    ours:
      'The page does not prove the criterion of p. 10; the proof in the reading is the edition’s. The reading adds « modérées » to the functions of the criterion (absent from the page’s statement, present in the NB), reads the page’s « M5 » there as stability under finite unions (M5′), which the page introduces after stating the colimit principle it needs, and restores the conclusion of p. 13 (the two images meet exactly along Z, their union is tame), where the page stops after the diagram. The pass takes no position on whether the reading’s restored conclusion is the one the page intended; it agrees that the construction as drawn yields it.',
    literature: [
      'van den Dries, Tame Topology and o-Minimal Structures (1998), ch. 10 « Definable spaces and quotients » — only the chapter summary on cambridge.org was read (2026-10-10): § 1 glues finitely many affine definable patches and proves the Robson-type affine embedding for regular definable spaces; § 2 treats quotients X/E by definably proper equivalence relations; no axiomatic, topology-free treatment of pushouts along embeddings is mentioned there',
      'One general web search (2026-10-10) on gluing / pushouts / quotients of definable spaces surfaced only Nowak’s non-Archimedean definable spaces (arXiv:2103.01836) and Fujita’s definable quotients by definably compact groups (arXiv:2303.01644), neither read for this question',
    ],
    status: 'unsearched',
    settle:
      'Read van den Dries ch. 10 (and ch. 6 on the zero-set and Tietze results the folder takes as axioms) to see whether pushouts along closed definable embeddings are derived there from zero-set + extension properties alone; then check axiomatic frameworks that drop complements and topology: Shiota, Geometry of Subanalytic and Semialgebraic Sets (1997), ch. II on 𝔛-sets; categorical treatments of definable sets as regular categories (Makkai–Reyes, First Order Categorical Logic, 1977; Johnstone, Elephant D1–A1.3) for pushouts along monomorphisms; and the Esquisse d’un programme § 5 and its commentators. A derivation of this pushout statement from (M6)+(M7)-type hypotheses in any of these marks the entry matched.',
  },
  {
    id: '120-collapse-separation-over-a-field',
    cote: '120',
    pages: '22–23',
    kind: 'mathematical',
    claim:
      'When R is a field with tame ring operations and tame inverses (M11), the second half of axiom (M6) follows from the first: if Y is the common zero set of tame functions f_α on a tame X embedded by tame g_β, the functions f_α and f_α·g_β still have Y as common zero set and separate the points of X ∖ Y, so X/Y exists in the strict sense.',
    basis:
      'Page 22 reduces to e_α = 0 by translation and introduces the f_α g_β; page 23 checks separation (λ = f_α(x) ≠ 0, g_β(x) ≠ g_β(y)) and states the Proposition « Si on a M1 : M7 et M11 … ». The statement line on p. 23 carries two \\ill{} words, one before « $X/Y$ »; the « Dém : » is empty, the argument standing above it.',
    ours:
      'The edition corrects « e_α ∈ R » (p. 22) to e_α ∈ R₀, which the translation needs, and « sépare les pts de X » (p. 23) to X ∖ Y, the only reading under which the statement is true; the closing gloss « X/Y est un espace modéré » is read through an \\ill{} word.',
    literature: [
      'Ferrand, « Conducteur, descente et pincement », Bull. SMF 131 (2003), 553–585 — located by web search (2026-10-10), not read: affine pinching of X′ along a closed subscheme Y′ → Y, with ring A′ ×_{B′} B, whose case Y = point is the ring k + I(Y′) generated by elements of the form f and f·g with f ∈ I(Y′)',
    ],
    status: 'unsearched',
    settle:
      'The argument is, on its face, the elementary fact that collapsing a closed affine Y to a point is realised by the subring k + I(Y) and that its elements separate points off Y; check whether this appears as such in Ferrand 2003 § 5 or in standard treatments of pinching/conductor squares (e.g. the Stacks Project chapter on pushouts of schemes), and, for the definable setting, van den Dries ch. 10 § 2 on collapsing. If so, mark matched; it is likely to be.',
  },
// Folder 127, /find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, on a reading made by Opus 5.5 (header of 127.modern.tex). Web searches only, no source read by section.
  {
    id: '127-closure-flatness-artinian-or-trait',
    cote: '127',
    pages: '2–4, 15, 19',
    kind: 'mathematical',
    claim:
      'For X → Y locally noetherian, F coherent on X, and a coherent quotient G_U of F|_U on a retrocompact open U, flat over Y: if the local rings of X at the points of X − U have geometrically normal formal fibres, then G = Im(F → i_*G_U) is flat over Y with U universally G-dense relative to Y if and only if this holds after every base change Y′ → Y with Y′ artinian or a trait. This is a valuative criterion for the flatness of a schematic closure over a base that need not be reduced.',
    basis:
      'Page 15 states this as the « Vrai théorème » / « Énoncé final », combining Remarque 1.4.2 (conditions (b)+(c) of Th. 1.4 ⟺ solutions after every artinian base change) and Remarque 1.4.3 (condition (a) follows from solutions after every base change to a trait). Pages 3–4 give Th. 1.4 and the outline of its proof (localisation, henselisation, completion, limit over the Spec Ô/m^n). Page 19 gives the Chevalley-type finite subfamily used in the limit step. No complete proof is written: page 4 is largely illegible, and the « Vrai théorème » is stated without proof. On page 15, « tout » and « artinien » in 1.4.2 are \\uncertain{} and « inutile » in the circled marginal note (« inutile si les O_{Y,y} réduits ») is \\uncertain{}. The statement turns on « artinien ».',
    ours:
      'The edition supplies a good deal. It writes condition (a) in a density form and asserts that this form is equivalent to the page’s specialisation form. It phrases universal injectivity by base change, in EGA IV 11.10 vocabulary. It takes the alternative in condition (c) from the fair copy in another hand (page 16) rather than from the overwritten page 3. It works out how page 19, Lemma 1.3 and (c) chain together in the limit step. The density-form restatement is ours.',
    literature: [
      'Web search, 10 October 2026: « valuative criterion flatness schematic closure universally schematically dense artinian base change traits non-reduced base ». It found the usual valuative criterion of flatness, stated for a reduced noetherian base (lecture notes of D. Bejleri, Math 259x, lecture 4; A. Fernández Herrero, « My favorite flatness results », citing Raynaud–Gruson), and Timofeeva, arXiv 1209.6279 (Hilbert-polynomial criterion over a non-reduced base). None of them bears on schematic closures or universal density. This was an orienting search, not a reading of the sources.',
    ],
    status: 'unsearched',
    settle:
      'Read EGA IV §11.8 (valuative criterion of flatness, reduced base) and §11.10 (universally schematically dense opens, the Ass criterion 11.10.9–10), and Raynaud–Gruson, « Critères de platitude et de projectivité » (Invent. Math. 13, 1971), Part I §§4–5 (pure modules, flattening, valuative criteria). Ask whether the two-sided criterion — artinian base changes and traits together — for the flatness and universal density of Im(F → i_*G_U) appears there, with or without the formal-fibre hypothesis. Before any search, settle « artinien » on page 15 against the facsimile; that is /transcribe-grothendieck’s work.',
  },
  {
    id: '127-non-flat-descent-artinian-epimorphism',
    cote: '127',
    pages: '2–3',
    kind: 'mathematical',
    claim:
      'Over an artinian base Y, the problem of a flat quotient G of F extending G_U, with G → i_*G_U universally injective relative to Y, descends along any epimorphism of schemes Y′ → Y, flat or not, provided Y′ → Y is finite or f and the solution are of finite presentation. The flat quotients in question are those of a sheaf already given, and the solution is unique when it exists.',
    basis:
      'Lemma 1.3 is stated at the foot of page 2 (« Suppo… ») and resumed at the top of page 3. The alternative hypothesis (finite, or of finite presentation) comes from a pencil note on page 2. The sentence introducing the lemma defines « descente non plate » as the descent of flat quotients of a given sheaf. The lemma is not proved in the folder.',
    ours:
      'The reading adds two things. It argues that, over a local artinian base, an epimorphism is the same as a surjective morphism with A → Γ(Y′, O) injective. It gives the example of two copies of Spec k[ε] mapped onto the axes of Spec k[x,y]/(x,y)², an epimorphism that is not flat. Neither is on the page. The lemma’s statement is the page’s, pieced together across a page break.',
    literature: [],
    status: 'unsearched',
    settle:
      'Decide first whether the lemma is true as stated; no proof is given. Then look for descent of flatness of a determined quotient along non-flat (universally injective or epimorphic) morphisms: Raynaud–Gruson 1971, Part I; Ferrand, « Conducteur, descente et pincement » (Bull. SMF 131, 2003); Mesablishvili on pure morphisms and effective descent for modules. Also look at the Stacks Project chapter on descent along non-flat morphisms. If the statement there is the same, with the uniqueness of Im(F → i_*G_U) doing the work, mark matched.',
  },
  {
    id: '127-hironaka-reduced-base-openness',
    cote: '127',
    pages: '7, 9, 10, 12',
    kind: 'mathematical',
    claim:
      'Let f : X → Y be of finite type, with Y noetherian and O_{Y,y} reduced with geometrically normal formal fibres. Suppose f is universally open at x and the fibres are equidimensional of the same dimension near x. Suppose further that X_y is reduced at the maximal generisations of x and (X_y)_red is geometrically normal. Then x has an open neighbourhood U such that U_red → Y is flat with geometrically normal fibres. This is Hironaka’s flatness-and-normality statement over a reduced, not necessarily regular, base.',
    basis:
      'Th. 1.8 is stated on page 7, and its conclusion there is struck and only partly read. Page 10 restates it, with the conclusion « plat à fibres géom. normales ». The proof is a sketch. Page 9 and page 10 show the separable locus open (EGA IV 12) and dense in the fibres (EGA IV 15.2.3, by equidimensionality). Page 12 gets normal fibres by Hironaka’s lemma after base change to a trait, and flatness from the folder’s own « critère valuatif de platitude d’une adhérence schématique » (Cor. 1.6–1.7). Page 9 carries a « Lemme à dégager » that is never written out. On page 12, the indices y′₀ and several words of the normality step (« remarqué », « appliquons », « plat ») are \\uncertain{}.',
    ours:
      'The statement follows the restatement on page 10, because the conclusion on page 7 is struck. The reading names Hironaka’s lemma in its EGA IV 5.12.8 form, cited from memory; the folder does not state it. The link to Cor. 1.6–1.7 with F = O_X and G_U = O_U is the page’s. Filling in the sketch is not.',
    literature: [
      'Web search, 10 October 2026: « universally open morphism reduced base fibre generically reduced normal reduction implies flat normal Hironaka lemma », then « Kollár "Simultaneous normalization and algebra husks" Hironaka ». The abstract of Kollár, « Simultaneous normalization and algebra husks » (Asian J. Math. 15, 2011; arXiv 0910.1076), attributes to Hironaka the case S regular: fibres generically reduced with normal reductions ⇒ red X → S flat with normal fibres. The paper itself was not read.',
    ],
    status: 'unsearched',
    settle:
      'Read Kollár 2011 (arXiv 0910.1076), §1 and the statement attributed to Hironaka with its reference. Read also EGA IV 5.12.8, 15.2.2–15.2.3 and 12.1–12.2, and Kollár, Families of varieties of general type (2023), on Hironaka-type flatness. The question is whether the version over a reduced base — universally open and equidimensional in place of regular, with geometrically normal formal fibres — is in print. If it is, mark matched. If only the regular-base case is, the status becomes candidate, but the sketch on page 12 rests on uncertain readings and on the unproved Cor. 1.6–1.7.',
  },
  {
    id: '127-ega-iv-typescript-leaf',
    cote: '127',
    pages: '8–9',
    kind: 'codicological',
    claim:
      'Page 8 is not a draft of this folder. It is a leaf of the EGA IV typescript (§21, n° 21.10 « Factorialité des anneaux locaux réguliers », typed page number read IV-1131 with doubt), carrying autograph corrections: « Créditer Kaplansky de la démonstration ici », « (Auslander-Buchsbaum) », the reference « (5.11.6) » changed to « I 9.4.5 », a struck clause, and the label (21.10.1.1) added by hand. The renumbering of page 9 (« 7 » over « 8 ») is consistent with the leaf having been slipped into the sequence.',
    basis:
      'The transcription’s header and its page-8 note identify the typed text and list the hand interventions. The page-9 note records the overwritten number.',
    ours:
      'The reading that the leaf was « glissé là », inferred from the page numbers, is the edition’s. The typed page number is read with doubt.',
    literature: [],
    status: 'unsearched',
    settle:
      'Compare the leaf with the published EGA IV 21.10–21.11 (Publ. Math. IHÉS 32, 1967). Check whether the credit to Kaplansky, the attribution to Auslander–Buchsbaum and the reference I 9.4.5 reached print as corrected. Check the typed page number against the facsimile.',
  },
  // Folder 129 — find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, over the Opus 5.5 reading of 2026-10-03 (same model; no exception invoked).
  // Read in full for this pass: E. Peterson’s English translation of Grothendieck, « Groupes de Barsotti–Tate et cristaux de Dieudonné » (Montréal 1974), matematicas.unex.es/~navarro/res/cristaux-eng.pdf, which prints the French section numbers in its margin; and L. Illusie, « Revisiting deformations of truncated Barsotti–Tate groups » (Chicago, 6 March 2023), imo.universite-paris-saclay.fr/~illusie/Illusie-Chicago-2023-1.pdf. The French original, Illusie’s Astérisque 127 (1985) and the 1970 Nice Actes were NOT read.
  // Most of the folder turned out to be drafts of the Montréal volume itself, so the mathematical candidates are matches; they are kept as killed candidates.
  {
    id: '129-tate-object-one-index',
    cote: '129',
    pages: '97, 99, 101–103',
    kind: 'mathematical',
    claim:
      'For an endomorphism f with fⁿ = 0 of an object of an abelian category, the conditions Ker fʲ = Im fⁿ⁻ʲ for all j, for one j, and the bijectivity of gr⁰[t] → gr•_f are equivalent; for a flat, finitely presented commutative group scheme the condition can be checked fibre by fibre. This is in the published literature for f = p.',
    basis:
      'Page 97 states the proposition (i)–(iv) and proves it with a chain of implications; pages 101–103 give the group-scheme version, (i) Ker fʲ flat and fⁿ⁻ʲ : G → Ker fʲ faithfully flat ⇔ (ii) every fibre is a Tate object, by the fibrewise flatness criterion.',
    ours:
      'The reading supplies the chain (i bis) ⇔ (ii) and the remark that the inclusion Ker fʲ ⊂ Im fⁿ⁻ʲ for one j suffices, which is equivalent to equality because the opposite inclusion always holds. It also supplies “non-negative” for the rank function (page: « à valeurs entières », \\uncertain{}), and treats the one-index condition (iv) of page 97 as the page’s own. « plat » in the hypothesis of page 101 is \\uncertain{}. Identifying these objects with truncated BT groups for f = p and n ≥ 2 is the reading’s link.',
    literature: [
      'Grothendieck, Groupes de Barsotti–Tate et cristaux de Dieudonné (Montréal 1974), ch. III Prop. 2.2 and 2.4, read in Peterson’s translation (Prop. 3.1.4 items (3), (4) “for some i”, (6) the graded map; Prop. 3.1.5, whose proof uses the fibre-by-fibre flatness criterion)',
      'Illusie, « Revisiting deformations of truncated Barsotti–Tate groups » (Chicago 2023), Def. 1.1 and the comment after it (flatness over ℤ/pⁿ ⇔ exactness of G → G → G for pⁿ⁻¹, p; “these conditions can be checked on the fibers”)',
    ],
    status: 'matched',
    settle:
      'Matched for f = p in the Montréal volume, ch. III 2.2. What is left is the abstract form for an arbitrary nilpotent endomorphism in an abelian category. Its proof is formally the same, so it is not a candidate. To close the entry, read the French original of III 2.2 and confirm that the translation’s numbering is accurate.',
  },
  {
    id: '129-colie-truncated-bt-package',
    cote: '129',
    pages: '92, 94–95',
    kind: 'mathematical',
    claim:
      'The folder’s results on the co-Lie complex of a truncated BT group are published. These are the « formule remarquable » R𝐻𝑜𝑚(ℓ^G, 𝒥) ≅ τ≤1 R𝐻𝑜𝑚(G*, 𝒥), the proposition on ω and n of G(n) under inclusion and under multiplication by p^{n−n′} (with pᴺ = 0, n ≥ N), and Ext²_{ℤ/pⁿ}(G, M) ≅ Ext²_ℤ(G, M) with Ext¹_{ℤ/pⁿ}(G, M) = 0.',
    basis:
      'Page 92 has the boxed formula, page 94 (D) the proposition with its bounds, and page 95 the theorem. The page proves none of them.',
    ours:
      'For the formula, the reading supplies the hypothesis “G finite locally free”. It also corrects the marginal t_{G*} to t_G and reads the page’s H_i(L^{G(n)}) as H_i(ℓ^{G(n)}). The reading’s footnote attributes the formula to Illusie, Complexe cotangent et déformations II, ch. VII, from memory, and Illusie 2023 attributes it to Grothendieck via Mazur–Messing, LNM 370, 14.1. The two citations differ, and the reading’s footnote should be checked.',
    literature: [
      'Illusie, « Revisiting deformations of truncated Barsotti–Tate groups » (Chicago 2023), (1.7.1) and Lemma 1.8 (1)–(5), with the remark that only pᴺ𝒪_S = 0 and n ≥ N are needed (citing Astérisque 127, §2)',
      'Grothendieck, Groupes de Barsotti–Tate et cristaux de Dieudonné (Montréal 1974), ch. VI §5 « Complexe cotangent relatif », in Peterson’s translation (§6.6)',
    ],
    status: 'matched',
    settle:
      'Matched. Check Illusie, Astérisque 127 (1985), §2, for the exact form of the bounds of page 94, which the reading did not verify. Check Mazur–Messing LNM 370 §14 against the reading’s footnote attributing the formula to Illusie CC II.',
  },
  {
    id: '129-ext2-vanishing-p-odd',
    cote: '129',
    pages: '95',
    kind: 'mathematical',
    claim:
      'The folder asserts that 𝐸𝑥𝑡²_ℤ(G, M) = 0 for every finite locally free commutative group scheme G and quasi-coherent M as soon as 2 is invertible, and remarks that this simplifies the deformation theory of BT groups for p ≠ 2.',
    basis:
      'Page 95 has a parenthetical NB after the theorem on Ext over Λₙ: « Ext²_ℤ(G, M) = 0 si 2 \\uncertain{inv.}, pour tt G fini loc. libre ». The word carrying the hypothesis is uncertain in the transcription, and the page gives no proof.',
    ours:
      'The reading leaves the statement as the page’s own and does not verify it. This pass adds one observation, which is its own step and not a source. Illusie 2023 places the obstruction to deforming a BTₙ in Ext²_ℤ(G₀, t_{G₀} ⊗ J), and says that proving directly that it vanishes is “out of reach”. On S₀ = Spec k the NB as read would make that obstruction vanish at once for p odd. So the NB, read this way, is in tension with Illusie’s account. This is not a refutation.',
    literature: [
      'Illusie, « Revisiting deformations of truncated Barsotti–Tate groups » (Chicago 2023), §1, pp. 2 and 6. The NB is not stated there.',
    ],
    status: 'unsearched',
    settle:
      'First have the transcription re-read the word « inv. » on page 95 against the facsimile. Then compute 𝐸𝑥𝑡²_ℤ(α_p, 𝔾_a) over a perfect field of odd characteristic. The tools are Breen, « Extensions du groupe additif » (Publ. IHÉS 48, 1978) and Illusie, Astérisque 127 §2–4. If it is non-zero, the NB as read is refuted. If not, look for the vanishing in Astérisque 127.',
  },
  {
    id: '129-drafts-of-montreal-volume',
    cote: '129',
    pages: '1–75, 77, 79–95',
    kind: 'codicological',
    claim:
      'The folder holds the working material of the 1974 Montréal volume « Groupes de Barsotti–Tate et cristaux de Dieudonné ». Pages 1–75 are typescripts of its chapters I–III. His typed and handwritten drafts at pages 83–87 and 89–95 correspond to its ch. III §§6–7 and ch. VI §§2, 4 and 5 (Théorème (4.1) on page 90 bears the volume’s own number).',
    basis:
      'The typescript titles and numbering recorded in the transcription match the French marginal numbering of the published volume. They are « Préliminaires sur Witt », ch. II Théorème 4.2 and the Annexe on a quasi-inverse, and ch. III « Platitude et critère de représentabilité » 2.2/2.4, Définitions 3.2, 4.1, 4.2, « Sorites » 5.2, « Exemples » §6, « Suite de composition » Prop. 7.4. Page 90’s « 4. Déformations de groupes de BT : énoncés », Théorème 4.1 a)–d), matches the volume’s ch. VI §4 « (énoncé) », Théorème (4.1) (1)–(4). Page 90 announces « 5. Rapport sur le complexe cotangent relatif », which is the volume’s ch. VI §5. Labute’s Avertissement credits Hakim and Delale with drafting most chapters, and says the F-crystal chapter was left out. This agrees with the pencilled « DELALE » on page 1 and with chapter VI of page 77’s plan, « F-cristaux », which has no pages in the folder.',
    ours:
      'The identification is this pass’s, made on the published volume. Only the chapter titles and numbers were compared, not the text. It corrects the reading on one point. The reading assigns pages 89 and following « vraisemblablement » to chapters IV–V of the plan, but the published volume puts that material in its chapter VI, « Propriétés infinitésimales des groupes de Barsotti–Tate ». It says nothing about who wrote which typescript.',
    literature: [
      'Grothendieck, Groupes de Barsotti–Tate et cristaux de Dieudonné (Montréal 1974), read in Peterson’s translation with its French marginal section numbers: Avertissement (Labute, October 1973), contents, ch. I–III, ch. VI §§2–6',
      'Transcription 129, batches 1–5, headers and notes on pages 1, 28–75, 77, 89–90',
    ],
    status: 'candidate',
    settle:
      'A person compares the typescript leaves of pages 1–75 with the printed French volume, section by section, and checks pages 89–95 against its ch. VI. The rights question (RIGHTS.md) is separate: naming the published volume does not restate the typescripts.',
  },
  {
    id: '129-page-101-continues-99',
    cote: '129',
    pages: '97–101',
    kind: 'codicological',
    claim:
      'Page 101 continues page 99 across a foreign leaf. Pages 98 and 100 are the fronts of duplicator sheets (« n° 380 », pp. 48 and 51) whose backs carry pages 97 and 99. The argument on morphisms of Tate objects runs from the foot of page 99 to the head of page 101.',
    basis:
      'Page 99 ends with a list of equivalent conditions on u : A → B (u isomorphism, gr⁰(u) …), largely illegible. Page 101 opens « en cours de démonstration » with « \\ill{} que c’est un isom. » and then proves exactly those implications: u mono ⇒ gr⁰(u) mono, u épi ⇒ gr⁰(u) épi, gr⁰(u) isom ⇒ u isom.',
    ours:
      'The join is the reading’s. Batch 6’s note says only that the preceding page of the argument « n’est pas dans ce lot ».',
    literature: ['Transcription 129, batch-05.fr.tex header and pages 97, 99; batch-06.fr.tex page 101'],
    status: 'candidate',
    settle:
      'A person checks against the facsimile that the leaf of page 101 follows the sheet carrying page 99, and that page 101 is not the back of page 100.',
  },
  {
    id: '129-leaves-81-82-missing',
    cote: '129',
    pages: '80–81',
    kind: 'codicological',
    claim:
      'Two leaves may be missing after page 80. The archivists’ pencil numbers jump from 80 to 83 between consecutive leaves of the scan, page 80 stops mid-sentence, and page 81 begins in mid-exposition with a « ceci » that points to nothing in the folder.',
    basis:
      'Batch 5 records « 80 » on PDF page 80 and « 83 » on PDF page 81, with 82 + k on every later leaf checked. Page 80 breaks off at « On va introduire sur W_k une structure de schéma en groupes avec ». Page 81 is a handwritten leaf whose « ceci » refers back to text not in the folder.',
    ours: null,
    literature: ['Transcription 129, batch-05.fr.tex header (numbering) and page 81 note; batch-04.fr.tex page 80'],
    status: 'candidate',
    settle:
      'A person checks the original folder at Montpellier, or the archive’s own scan, for leaves pencilled 81 and 82. The alternative is that the archivist skipped two numbers. The volume’s ch. I 1.2 (ind-schemes Ŵ) and ch. II 2.3–2.4 show what the missing text should cover.',
  },
  {
    id: '129-nice-outline',
    cote: '129',
    pages: '112–114',
    kind: 'codicological',
    claim:
      'Pages 112–114, headed « Conférence à Nice » in his hand, are the outline of his address to the 1970 Nice International Congress, « Groupes de Barsotti–Tate et cristaux » (Actes du Congrès international des mathématiciens 1970, t. 1, pp. 431–436).',
    basis:
      'The heading, the inventory’s date [1970], and the content: BT groups, Serre–Tate, divided powers, the crystalline site, crystals, and a programme I)–V) on the crystalline Dieudonné functor.',
    ours:
      'The identification is the reading’s, and it was not compared with the printed text. This pass found only the bibliographic reference (pp. 431–436), not the text.',
    literature: [],
    status: 'unsearched',
    settle:
      'Compare pages 112–114, point by point, with the printed address in the Nice Actes (Gauthier-Villars 1971, t. 1, 431–436). Check in particular whether the printed text keeps the restriction on page 114 to G₀ with toroidal or connected fibres, and the « il se pourrait » of point II).',
  },
  // Folder 132, find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, on the Opus 5.5 reading of 2026-10-03.
  // Dropped, not written up: the base-change sequence of page 15 (an elementary consequence of the two homotopy sequences); the corrected statement of page 21 (the page marks its own claim « faux »; the proposition is the reading’s); the closing answer to page 13’s question (entirely the reading’s); the Ladegaillerie offprints (another author’s published Notes).
  {
    id: '132-nonconnected-extension-classification',
    cote: '132',
    pages: '16–20',
    kind: 'mathematical',
    claim:
      'For a topological group H with discrete π₀(H) = 𝔊, given a chosen extension H̃ of H by π = π₁(H⁰) prolonging the universal cover of H⁰, the category of extensions of H by an arbitrary (not necessarily abelian) discrete group N is equivalent to the category of pairs (G̃₀, φ): an extension G̃₀ of 𝔊 by N and a 𝔊-equivariant morphism φ : π → 𝔷(N), with G recovered as a contracted product and π₀(G) ≅ G̃₀/φ(π).',
    basis:
      'Page 19 states the equivalence under α) H̃₀ connected and simply connected, β) π ⊂ H̃₀, γ) π, N, 𝔊 discrete; pages 16–17 set up the general frame (A) with strict trivialisations; page 20 gives the explicit construction by G_! and the push-out of H̃ along φ, and the formula for π₀(G). No proof beyond these reductions is written. In the transcription, the « 𝔊- » of « 𝔊-hom. » on page 19 is written over an overwrite, and the slanted NB that identifies G̃₀ with π₀G̃ is a partial reading (\\uncertain{} throughout); the statement itself is legible.',
    ours:
      'The reading supplies the standing hypotheses (groups locally path-connected and semi-locally simply connected, quotient maps Serre fibrations), without which the page’s homotopy sequences do not hold, and gives « trivialisation stricte » a definition (equivariant splitting centralising N) where the page’s gloss on page 16 is illegible. It also notes that page 17’s product Ext(𝔊, N) × Hom_𝔊(π, 𝔷(N)) is a product only once the outer action 𝔊 → Out(N) is fixed. The page-19 statement does not depend on these repairs beyond the standing hypotheses.',
    literature: [
      'R. Brown and O. Mucuk, « Covering groups of non-connected topological groups revisited », Math. Proc. Camb. Phil. Soc. 115 (1994), 97–110, read 2026-10-10 in the arXiv version math/0009021v2 (2006): Theorems 5.2, 5.4 and 6.3 classify covering morphisms X̃ → X of topological groups via crossed modules π₁(X, e) → X and extensions of type a crossed module, by data θ : Φ → π₀X, a π₀X-invariant N ⊂ π₁(X, e), an obstruction in H³_θ(Φ, π₁X) and a torsor under H²_θ(Φ, A). Not found there: a classification, for a fixed H̃, of the extensions of H by a given non-abelian discrete kernel by the pair (G̃₀, φ : π → 𝔷(N)).',
      'D. Rumynin, D. Vakhrameev, M. Westaway, « Covering groups of nonconnected topological groups and 2-groups », arXiv 1709.09728 — abstract only (Taylor and Sinh cocycles); the body was not read.',
    ],
    status: 'candidate',
    settle:
      'Read R. L. Taylor, « Compound group extensions I », Trans. AMS 75 (1953), 106–135, and « Covering groups of nonconnected topological groups », Proc. AMS 5 (1954), 753–768 (cited from Brown–Mucuk’s bibliography and from memory), and K. Mackenzie’s account for Lie groupoids that Brown–Mucuk cite: Brown–Mucuk say results of this type were known to Taylor. If either gives the (G̃₀, φ) description, or if it is a direct translation of Brown–Mucuk 6.3 via the crossed module π → H̃, mark matched.',
  },
  {
    id: '132-taylor-obstruction',
    cote: '132',
    pages: '19',
    kind: 'mathematical',
    claim:
      'An extension H̃ of a non-connected topological group H by π = π₁(H⁰) prolonging the universal cover of H⁰ need not exist nor be unique; such extensions form a homogeneous space under H²(π₀H, π), the obstruction to existence lies in H³(π₀H, π), and one exists when H is a semi-direct product π₀H ⋉ H⁰.',
    basis:
      'The NB of page 19, which says « sauf erreur » of the H³ obstruction and « unique (i.e. mod. action de H²(𝔊, π)) comme extension de 𝔊 par π ». The words « à isom. près » are \\uncertain{} in the transcription; a struck \\ill{} sits before the parenthesis.',
    ours:
      'The reading writes « homogeneous space under H²(𝔊, π) » where the page says « unique … mod. action de H² »; the semi-direct product case is the page’s.',
    literature: [
      'R. Brown and O. Mucuk, Math. Proc. Camb. Phil. Soc. 115 (1994), arXiv math/0009021v2, read 2026-10-10: Theorem 5.4 and Corollary 5.5 (obstruction class in H³(π₀X, π₁(X, e)), coverings classified by H²), crediting R. L. Taylor, Proc. AMS 5 (1954).',
    ],
    status: 'matched',
    settle:
      'Settled: this is Taylor’s obstruction, restated by Brown–Mucuk 1994, Corollary 5.5. Kept as a killed candidate; the reading’s footnote already names both.',
  },
  {
    id: '132-peripheral-gr-category',
    cote: '132',
    pages: '5–8',
    kind: 'mathematical',
    claim:
      'For a compact orientable surface with n ≥ 1 boundary components, the 2-group of self-equivalences of the model (π₁, boundary loops ℓᵢ, tethers α(i)) has π₀ the mapping class group with free boundary and π₁ zero except for the disc (ℤ, canonically) and the cylinder (ℤ, not canonically), and its boundary-fixed version has π₀ the mapping class group relative to the boundary and π₁ always zero: an algebraic, groupoid-theoretic Dehn–Nielsen–Baer statement for several boundary components.',
    basis:
      'Pages 5–7 define the 2-category of triples (𝒞, 𝒟, φ), reduce to the normal form (G, (ℓᵢ)), compute π₀ as the subgroup of Out(G) preserving the boundary conjugacy classes and π₁ case by case (disc, cylinder, general), and define TS from the pairs (v, α) with v(ℓᵢ) = α(i) ℓᵢ α(i)⁻¹. The page computes only these groups; it never states the topological identification. « Aut(,) » on page 6 is \\uncertain{}.',
    ours:
      'Substantial. The page does not define « groupoïde 2-spécial » or « foncteur spécial »; the reading takes them to be the fundamental groupoids of a compact orientable surface and its boundary. The identification of T and TS with mapping class groups (free boundary, relative to the boundary) is the reading’s, as is the justification that each ℓᵢ is not a proper power, and the correction of page 7’s last term v₁(ℓᵢ) to ℓᵢ. As read in this pass, the boundary-fixed TS for n = 1 is the stabiliser of ℓ₁ in Aut(F), which agrees with the classical description of the mapping class group of a surface with one boundary component; for n ≥ 2 the identification was not checked.',
    literature: [],
    status: 'unsearched',
    settle:
      'Compare with Zieschang–Vogt–Coldewey, Surfaces and Planar Discontinuous Groups (LNM 835, 1980), ch. 5, and Farb–Margalit, A Primer on Mapping Class Groups, ch. 8 (Dehn–Nielsen–Baer with boundary, cited from memory), and with any treatment of the mapping class group rel boundary as automorphisms of the fundamental groupoid with one base point on each boundary component. If the multi-boundary, rel-boundary statement is there in groupoid form, mark matched; the computation of π₁ (disc, cylinder) is the algebraic shadow of the known homotopy types of their homeomorphism groups and is not itself a candidate.',
  },
  {
    id: '132-teichmuller-boundary-sequence',
    cote: '132',
    pages: '8',
    kind: 'mathematical',
    claim:
      'There is a sequence 0 → ℤ^I → TS → T → 𝔖_I → 1, exact except at ℤ^I for the disc (TS = 0) and the cylinder (kernel ℤ via the sum): in mapping-class terms, the boundary Dehn twists generate a free abelian kernel of rank n between the group relative to the boundary and the group with boundary free and permutable.',
    basis:
      'Page 8 writes the sequence and computes Ker Ψ, with the margin « exacte sauf pour la sphère à 1 ou 2 trous », whose first word is \\uncertain{}. Surjectivity onto 𝔖_I is not argued on the page.',
    ours:
      'The mapping-class reading, the identification of ℤ^I with boundary twists, and the topological justification of surjectivity onto 𝔖_I are the reading’s.',
    literature: [
      'Web search, 2026-10-10: Farb–Margalit, A Primer on Mapping Class Groups, §3.6 « Cutting, capping, and including » — the capping homomorphism with kernel generated by the boundary twists, quoted as Theorem 3.18 or Proposition 3.19 by secondary sources (e.g. arXiv 1410.5531); only the search snippets were read, not the book.',
    ],
    status: 'matched',
    settle:
      'Open Farb–Margalit §3.6 and confirm the numbering and the exceptions (disc, annulus); the sequence is standard and the entry is kept as a killed candidate.',
  },
  {
    id: '132-fibre-product-pi2-defect',
    cote: '132',
    pages: '1–3',
    kind: 'mathematical',
    claim:
      'For a Serre fibration f : X → S and any g : Y → S, the functor Π₁(X ×_S Y) → Π₁(X) ×²_{Π₁(S)} Π₁(Y) is bijective on π₀ and surjective on π₁, with kernel at the base component Coker(π₂X × π₂Y → π₂S); hence an equivalence for aspherical X, Y, S.',
    basis:
      'Pages 1–3 (his pagination (1)–(3)) compare the homotopy sequences of Z → Y and of the groupoid fibre Φ. On page 3 the word « id. » in « ext. de id. par » is \\uncertain{}, the F̃ of the second diagram may be a Φ, and the closing word (« X, Y, S sont des … ») is \\ill{}.',
    ours:
      'The reading reads « connexes » as path-connected (otherwise « f surjectif » fails), restricts the π₂ criterion to the component of z₀ (the page states it without restriction), and restores the illegible last word as « asphériques ».',
    literature: [
      'Web search, 2026-10-10, for the fundamental groupoid of a fibre product and Brown’s « Fibrations of groupoids »: returned Jacqmin–Mantovani–Metere–Vitale (arXiv 1707.00868) and Brown–Heath–Kamps (J. Pure Appl. Algebra 1983) on Mayer–Vietoris sequences for pullbacks of groupoid fibrations; only the search summaries were read.',
    ],
    status: 'unsearched',
    settle:
      'Read R. Brown, « Fibrations of groupoids », J. Algebra 15 (1970), and Topology and Groupoids (ch. 7 and 10), and Brown–Heath–Kamps 1983. The statement is almost certainly the low-degree part of the Mayer–Vietoris sequence of a homotopy pullback; if it is stated there, mark matched.',
  },
  {
    id: '132-page-18-interleaved',
    cote: '132',
    pages: '18',
    kind: 'codicological',
    claim:
      'Page 18, bound between paragraphs (A) and (B) of the run on extensions of topological groups (pages 13–23), belongs by its content to the run on surfaces and 1-complexes (pages 5–11).',
    basis:
      'Page 18 treats embeddings of 1-complexes in surfaces (PLO, TUBO, SOB, CO, Teichmüller groups T_{g,n}, « Le calcul des g_i n_i est donné par Yves »), with no reference to the notation of (A)–(C); page 17 and page 19 continue each other ((A) closes, (B) opens). Most annotations around page 18’s diagram are \\uncertain{}.',
    ours:
      'The assignment to pages 5–11 is the reading’s, by content only.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look at the facsimile for page 18: paper, ink, fold and any pagination, against pages 10–11 and 17–19. If the leaf matches 10–11 physically, the interleaving is a binding accident; if it matches 17–19, it was written in the course of the extensions run.',
  },
// Candidate findings for folder 4, written by /find-novelty on Opus 5.5 (claude-opus-5-5), 2026-10-10,
// on a reading made by Opus 5.5 (4.modern.tex, 2026-10-03) and a transcription made by Opus 5 (batch-01.fr.tex, 2026-09-14).
// Not merged into src/content/findings.ts: other agents edit that file in parallel.
  {
    id: '4-vanishing-unit-root-bound',
    cote: '4',
    pages: '1, 4–7',
    kind: 'mathematical',
    claim:
      'Granting crystalline weak Lefschetz with torsion, for a smooth hypersurface section Y of a smooth projective X of dimension n over a perfect field of characteristic p there is an exact sequence 0 → Ker v → (ₚTorsⁿ(X))_ss → (E(Y) ⊗ k)_ss → E(Y, O_Y)_ss → 0, so the number of p-adic unit Frobenius eigenvalues on the vanishing crystalline cohomology is at least the F-semisimple rank of the coherent vanishing cohomology Coker(H^{n−1}(X, O_X) → H^{n−1}(Y, O_Y)), with the defect measured by the p-torsion of H^n_cris(X).',
    basis:
      'Page 5 states « Théorème » 8.5 under admitted crystalline hypotheses; page 6 carries (8.5.1) as rewritten by hand, with the second term replaced by (ₚTorsⁿ(X))_ss boxed, and (8.5.5)–(8.5.6); page 4’s margin gives (Ker u₂)_ss = (ₚTorsⁿ(X))_ss and (Coker u₂)_ss = 0 « en vertu de 8.4.4 », which rests on the nilpotence of F above the dimension stated on page 1 (8.4.4 a). The title calls the whole estimate « heuristique ».',
    ours:
      'The reading supplies the proof of 8.4.4 (a), which page 1 states without argument, and the description of w as the restriction of H^{n−1}_DR(X)_ss → (ₚTorsⁿ(X))_ss: the page labels the arrow w but its only typed definition of w, (8.5.3), is struck. The reading also notes that Poincaré duality, listed among the theorem’s hypotheses, is not used by the revised argument. The terms of (*) on page 1 are flagged uncertain in the transcription (read over an erased first attempt), as is « Tor » in line a); the theorem does not rest on (*) but on line a) itself. The statement is conditional on crystalline weak Lefschetz with torsion, which the folder admits and whose current status the reading does not assert.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check whether this exact sequence, or the inequality (8.5.6) for the vanishing part, follows from or appears in the de Rham–Witt treatment of slopes and unit-root parts (Illusie, « Complexe de de Rham–Witt et cohomologie cristalline », 1979, II.7; Bloch, Illusie), in Katz, SGA 7 exposé XXII, or in Illusie, « Ordinarité des intersections complètes générales » (1990); and whether crystalline weak Lefschetz with torsion is established (Berthelot, LNM 407), since without it the statement is conditional. If it is there, mark matched.',
  },
  {
    id: '4-revision-reverses-surjectivity',
    cote: '4',
    pages: '1, 4–6, 9–10',
    kind: 'codicological',
    claim:
      'The manuscript leaf bound as page 1 is the « feuille jointe (marquée 8.4.4) » that the margin of page 5 cites, and the hand revision it supports contradicts the typescript it annotates: the typed text derives conditions for φ to be non-surjective and builds examples of it (pages 9–10), while the revision makes φ always surjective and those passages are struck.',
    basis:
      'Page 5’s margin reads « Cor. 8.4.4 ter (utilisé dans 8.1.?) les résultats de la feuille jointe (marquée 8.4.4) » and page 4’s margin « en vertu de 8.4.4 »; page 1 is headed « 8.4.4 » and carries the nilpotence statements those margins use; on page 6 the end of the typed (8.5.1) is blacked out up to « → 0 »; on pages 9–10 the « resp. » surjectivity clauses, the three-condition equivalence and the X × Z example are struck.',
    ours:
      'The identification of page 1 with the « feuille jointe » is the transcription’s, by its heading and content; « ter » and the reference « 8.1.? » in the page 5 margin are uncertain or illegible. Whether the strike on page 10 covers condition c) is not certain. The reason given for the reversal — that Poincaré duality transposes F, so the F-semisimple part of a dual is semisimple for V, not F — is the reading’s, not the page’s; the page says only that duality is « malcommode » (underlined word uncertain).',
    literature: ['Transcription 4, batch 1 (batch-01.fr.tex), pages 1, 4, 5, 6, 9, 10'],
    status: 'candidate',
    settle:
      'Look at the facsimile of pages 1, 5 and 10: confirm the « 8.4.4 » heading and the margin reference on page 5, and the extent of the strike on page 10 (whether condition c) is included).',
  },
  // Folder 5 — find-novelty pass, Opus 5.5 (claude-opus-5-5), 2026-10-10, on a reading made by Opus 5.5 (pass header 2026-10-03); transcriptions by Fable 5.1 (2026-09-19), batch 3 revised by Opus 5.5. No literature was read in this pass: every mathematical entry is unsearched.
  // Dropped as matches (they are in the reading's footnotes, where they belong): Roby's Γ(M) (p. 22); the PD envelope and its presentation (pp. 23, 31; Berthelot–Ogus 3.19); e ≤ p − 1 for the maximal ideal of a DVR (pp. 12, 46); the PD criterion on a principal ideal (p. 44, which as written is wrong — the repaired condition is the edition's); Legendre (p. 10); the Čech–Alexander complex (pp. 28–30); the inserter/co-inserter topos Q(α, β) (pp. 15–17), a lax colimit of topoi; the Poincaré-lemma list (p. 36), quasi-homogeneous cases (Reiffen 1967, K. Saito 1971); κ′_n ≡ (∏ a_i!)⁻¹ mod p (p. 40), the edition's answer, from the classical congruence for n!/p^{v_p(n!)}. Not proposed: the questions the pages leave open (p. 40, extending γ_p; pp. 18–19, derived functors), since the folder establishes nothing there.
  {
    id: '5-universal-artinian-pd-normal-form',
    cote: '5',
    pages: '4–8',
    kind: 'mathematical',
    claim:
      'The universal artinian local W(k)-algebra whose maximal ideal carries divided powers killed in degrees ≥ p^{ν+1} is W[Λ_0,…,Λ_ν]/(Λ_i^p − q_iΛ_{i+1}, Λ_ν^p, Λ_0 − p), with q_i = (p^{i+1})!/((p^i)!)^p, and in the coordinates Θ_i = Λ_i − p^{p^i}/(p^i)! it has an explicit normal form: coefficient of Θ^a taken mod p^i where a_i is the first non-zero exponent, constant term mod p^{c(ν)}, c(ν) = ν + p[p^ν − (p^{ν−1}+…+1)]; and likewise for the quotients W^{(ν,r)} with p^{i−r} and p^{c(ν)−r}.',
    basis:
      'Page 4 writes the presentation and asserts universality between brackets, without proof; page 5 states the lemma a)–b) on the ideal (Θ_0), page 6 proves sufficiency (p^iΘ_i ∈ I by induction, p^{c(ν)} ∈ I) and leaves necessity « facile et laissée au lecteur », with a « ! » in the margin; page 6 states the corollary, page 7 the lemma and normal form for W^{(ν,r)}, page 8 the independent bound Λ^a = 0 for Σ a_i p^i ≥ p^{ν+1}. The induction start reads « si i = ν » (sic, for i = 0) next to an \\ill{}; « sont » and « Cohen » on page 4 are \\uncertain{} but do not carry the statement.',
    ours:
      'The edition supplies: the meaning of « ν-nilpotentes » (the page does not define it); the proof that W^{(ν)} carries the divided powers and is initial (as the PD envelope of pW modulo γ_n(p), n ≥ p^{ν+1}); the necessity half of both lemmas, checked by machine only for (p, ν) ∈ {(2,1),(2,2),(2,3),(3,1),(3,2),(5,1)} and not by hand; the « no condition if i ≤ r » clause of page 7; and the length formula c(ν) + Σ_{i=1}^{ν} i(p−1)p^{ν−i}, which is not on the page. The general statement therefore rests on a step neither the page nor the edition proves. This pass also reads one footnote of the reading differently: the reading says the weaker condition γ_{p^ν}(x)^p = 0 would give the same initial object, but γ_{p^ν}(x)^p = q_ν γ_{p^{ν+1}}(x) with v_p(q_ν) = 1, so in the presence of p-torsion that condition does not obviously force γ_{p^{ν+1}}(p) = 0; the pass has not settled this and does not override the reading.',
    literature: [],
    status: 'unsearched',
    settle:
      'First prove necessity (that the set I′ cut out by a)–b) is stable under multiplication by each Θ_i) for all p and ν. Then look for an explicit W-module description of the PD envelope D_{W}(pW) = W⟨X⟩/(X − p) and its truncations in Berthelot, Cohomologie cristalline (LNM 407, 1974) ch. I, Berthelot–Ogus, Notes on crystalline cohomology §3, and the Stacks Project chapter « Divided Power Algebra »; if a normal form or the length formula is there, mark matched.',
  },
  {
    id: '5-deligne-letter-ringed-duality',
    cote: '5',
    pages: '49–50',
    kind: 'mathematical',
    claim:
      'The letter of 10.12.1965 states étale duality for a smooth compactifiable morphism f : (X, B) → (Y, A) of ringed sites, A any sheaf of rings on Y killed by an integer n prime to the residue characteristics and B any sheaf of rings with f⁻¹(A) → B, with f^!(K) = RHom_{f⁻¹(A)}(B, f⁻¹(K) ⊗ T_{X/Y}[2d]), reduced to the cases f⁻¹(A) ≅ B and f = id.',
    basis:
      'Page 49, a typed carbon dated by hand: the definition of f^!, the decomposition into two cases, the recommendation to include « cette forme générale du théorème de dualité » in the write-up, and the doubt that it follows from A = (Z/nZ)_Y « comme simple corollaire »; page 50 extends the remark to global duality. The same paragraph proposes the simplification of the proof avoiding relative purity (reduction to relative dimension 1, induction on dimension, Y strictly local). The statement is a sketch: no proof is written. The shift [2d] is supplied (\\supplied{}), the carbon having no brackets.',
    ours:
      'Pass’s own remark, not in the reading: the B-half of the reduction looks formal (Hom–tensor adjunction along f⁻¹(A) → B), so the substance lies in allowing a non-constant A; this is offered as a reading, not checked. The reading supplies the remark that it is the dimension of Y − y, not of X, that drops.',
    literature: [],
    status: 'unsearched',
    settle:
      'Read SGA 4 XVIII (Deligne, « La formule de dualité globale »), §§ 3.1–3.2: whether duality is stated there for a sheaf of rings A on Y and B on X as in the letter, and whether its proof avoids relative purity by the induction the letter proposes. If either is there, mark matched (the letter is addressed to the author of that exposé).',
  },
  {
    id: '5-ega-iv-typescript-versos',
    cote: '5',
    pages: '44–47',
    kind: 'codicological',
    claim:
      'The versos of the two « Cristaux » leaves (44, 46) are pages IV-977-23 and IV-977-22 of a typescript of EGA IV § 18.13, read in reverse of the binding (47 then 45), annotated in his hand — including a marginal query on the « semi-local noethérien » hypothesis of 18.13.4 and the striking of « déterminés de façon uniques » in Proposition 18.13.5(iii).',
    basis:
      'Page 47 ends « co- » and page 45 opens « ïncide »; the typescript numbers 977, 22 and 23 are in hand. The marginal query reads « à quoi sert \\uncertain{l’hypothèse} \\ill{} ? Prendre \\ill{} topologie plus \\uncertain{générale} ? »; a second marginal note by the struck words is only half read.',
    ours:
      'The reading order and the identification are the transcription’s; neither the transcription nor the reading compared the typescript with the printed EGA IV.',
    literature: ['Transcription 5, batch 3 (batch-03.fr.tex), header and pages 45, 47'],
    status: 'candidate',
    settle:
      'A person checks the hand and the page numbers on the facsimile, then compares with printed EGA IV, Publ. Math. IHÉS 32 (1967), 18.13.4–18.13.5: whether the semi-local noetherian hypothesis and the words « déterminés de façon unique » survive in print. That would show whether these annotations reached the published text.',
  },
  {
    id: '5-berthelot-correspondence-absent',
    cote: '5',
    pages: '1–52',
    kind: 'codicological',
    claim:
      'The inventory title announces « correspondances Deligne et Berthelot », but among the 52 pages only the letter to Deligne is correspondence; no transcribed leaf is a letter to or from Berthelot or names him.',
    basis:
      'The three batch headers describe every leaf in his hand and the letter of pages 49–52; Berthelot’s name occurs only in the copied folder title. Pages 3, 9, 11, 33 (typescripts) and 13 (a list of corrections to a typescript, in his hand) are skipped without description, so their content is not recorded.',
    ours:
      'The observation is the reading’s header note; the transcriptions do not make it.',
    literature: [
      'Transcription 5, batches 1–3 (batch-01.fr.tex, batch-02.fr.tex, batch-03.fr.tex), headers',
    ],
    status: 'candidate',
    settle:
      'A person checks the skipped leaves 3, 9, 11, 13 and 33 on the facsimile — in particular whether page 13’s list of corrections is addressed to a Berthelot typescript — and whether Montpellier’s PDF of folder 5 has any leaf beyond 52.',
  },
  // Folder 32 — find-novelty pass, Opus 5.5 (claude-opus-5-5), 2026-10-10, on a reading made by Opus 5.5 (pass header 2026-10-09).
  // The rest of the candidate pool was dropped as matches already named in the reading's footnotes: Dold–Puppe bounds (p. 4), SGA 4 XVIII 1.2 drafts (pp. 15–27), the SL_2 lift and theta characteristics (p. 28), the Deligne pairing (p. 32), the tame symbol (p. 33), the induction formula and sheafified/local duality (pp. 38–47), or as repairs made by the edition (pp. 4, 9, 12–13, 41, 46, 47).
  {
    id: '32-pullback-kernel-index',
    cote: '32',
    pages: '10–11',
    kind: 'mathematical',
    claim:
      'For f : X → Y proper over a field k, Y irreducible (and smooth, as the paragraph assumes) with generic point η and X_η non-empty, and N the gcd of the degrees of the 0-cycles of X_η, there is a map H*(X, G_X) → H*(Y, G), functorial in the étale coefficient complex G, whose composite with f* is N·id — so Ker f* is killed by the index of the generic fibre, with no hypothesis on the relative dimension.',
    basis:
      'Page 11 states it in brackets, in his hand, with « d et d′ quelconques » added in ink; page 10 is the pencil computation: closed points x_i of X_η of degrees n_i, Bézout coefficients with Σ d_i n_i = N, closures Z_i with u_i : Z_i → X and f_i = f u_i, and (Σ d_i f_{i*} u_i*) f* = Σ d_i f_{i*} f_i* = Σ d_i n_i id, using Tr_f(1_X) = N·1_Y for proper f of virtual dimension 0. No \\ill{} under it; the label of the arrow H^r(Y) → H^r(X) is overwritten and read as f*, and the last equality is written « Σ d_i (f_{i*}f_i*) n_i id ».',
    ours:
      'The reading supplies the smoothness of Y (from q smooth in the surrounding § 4, not restated in the bracket), the identification of N as the gcd of the n_i over closed points, and the corrected last equality. The step f_{i*}f_i* = n_i rests on the Gysin formalism of § 4 for f_i : Z_i → Y with Z_i possibly singular, which the folder lists and does not prove; the statement depends on that formalism existing as proposed.',
    literature: [
      'Web search, 2026-10-10 (one query on the kernel of pullback in étale cohomology killed by the index of the generic fibre): surfaced only the Brauer-group analogue via restriction–corestriction (arXiv 2012.01324, « On the Brauer groups of fibrations »; arXiv 2410.15125), no statement for arbitrary étale cohomology. This is not a reading of any source.',
    ],
    status: 'unsearched',
    settle:
      'Look for the statement for étale cohomology with arbitrary torsion coefficients in SGA 4½ « Cycle » (§ 2, Gysin and degree) and SGA 4 XVIII 2–3, Fulton, Intersection Theory § 1.4 and Ex. 19.1 (cycle-class compatibility of proper push-forward), and Colliot-Thélène–Skorobogatov, The Brauer–Grothendieck Group (index arguments). The mechanism is the standard restriction–corestriction one; if any of these states it, or it follows in a line from the trace formula f_*f* = deg for generically finite proper maps to a smooth target, mark matched.',
  },
  {
    id: '119-foliation-quotient-topos-equivalence',
    cote: '119',
    pages: '144–145',
    kind: 'mathematical',
    claim:
      'The folder states, without proof, an equivalence between the category of pairs (X, R) — X a topological space, R a local equivalence relation on X, locally open with locally connected fibres — and the category of triples (X, 𝒴, f) with f : Top(X) → 𝒴 a locally open geometric morphism with locally connected fibres to a « multiplicité topologique », the latter a 2-category whose Hom-categories are discrete.',
    basis:
      'Page 145, under « Th », dated « Mars 1986 » on page 144: « On a C ⇄ C′ » with both arrows marked ≈. No proof is written. The statement rests on unread words: a third condition on f (« à fibres loc. connexes et \\ill{} ») and struck \\ill{} words in the conditions on R are not read, and « mult. top. » and « flèches » are \\uncertain{} in the transcription (batch-08.fr.tex, page 145). The variants for C^(r) foliated manifolds and the question « Quelles variétés obtient-on comme quotients des feuilletages ??? » are the page’s and are not part of the claim.',
    ours:
      'The reading (119.modern.tex) spells out the functor C → C′ (send (X, R) to the quotient morphism to the quotient topos) and the inverse (read R on f as « same local connected component of a fibre »); neither is on the page. It also identifies the quotient with the classifying topos of the holonomy groupoid; this pass notes that Kock–Moerdijk 1996 distinguish the topos of R-invariant sheaves (equivalent to sheaves on a monodromy groupoid) from the holonomy quotient, so which topos the page means by « topos quotient » is not settled by the page, and the reading’s identification with holonomy may be the wrong one. The condition the page leaves illegible is not restored.',
    literature: [
      'A. Kock and I. Moerdijk, « Every étendue comes from a local equivalence relation », J. Pure Appl. Algebra 82 (1992), 155–174 — pp. 155–156 read (abstract, introduction, §1 opening), from a scan fetched 2026-10-10. They cite Grothendieck–Verdier, SGA 4 IV, p. 478 ff., for local equivalence relations and étendues in the context of foliations, and say that every locally connected geometric morphism from sheaves on a locale M into an étendue gives rise to a canonical local equivalence relation on M — one direction of the page’s correspondence. No equivalence of categories between pairs (X, R) and morphisms Top(X) → 𝒴 was seen in the pages read; the rest of the paper was not read.',
      'A. Kock and I. Moerdijk, « Spaces with local equivalence relations, and their monodromy », Topology Appl. 72 (1996), 47–78 — pp. 47–48 read (abstract, introduction), same date. Elaborates « a suggestion of Grothendieck » from SGA 4; proves sh(M, r) ≃ sheaves on an étale groupoid under connectedness assumptions, and that every étale groupoid arises this way. No statement of the page’s equivalence seen in the pages read.',
      'Web search, 2026-10-10, for SGA 4 exposé IV on local equivalence relations and quotient toposes of foliations: returned tables of contents only; SGA 4 IV p. 478 ff. was not read.',
    ],
    status: 'unsearched',
    settle:
      'Read SGA 4 IV around p. 478 (the Grothendieck–Verdier passage on local equivalence relations), and the full texts of Kock–Moerdijk 1992 (§§2–7) and 1996, for a 2-categorical or categorical equivalence between spaces with (locally open, locally connected) local equivalence relations and locally open, locally connected geometric morphisms out of Top(X); if found, mark matched. Before that, the illegible third condition on page 145 must be re-read against the facsimile (/transcribe-grothendieck), since the statement may be false or trivial without it — which is why the status stays unsearched although sources were read.',
  },
  {
    id: '119-page-157-interleaved-leaf',
    cote: '119',
    pages: '157',
    kind: 'codicological',
    claim:
      'Page 157, inside the photocopied « Digressions combinatoires (pour Réflexions t. 4) » (pp. 154–160), is a leaf of another text: a typed list of complementary pairs (« Avenir — Passé », « Espace — temps », …) under renumbered headings V″₄ « Devenir » and V″₅ « Espace-temps », followed by handwritten drafts of footnotes numbered 98–107 that refer to « note n° 162 » and « p. 779 « conviction et connaissance » ».',
    basis:
      'The transcription (batch-08.fr.tex, header and note to page 157) records the leaf’s nature and the archivists’ number written upside down; the headings IV″₅ → V″₄ and IV″₆ → V″₅ are corrections in his hand. Several words of the footnote drafts are \\ill{}. The sketches of tetrahedra and octahedra with vertex lists at the foot of the page may belong to the combinatorial plan, so the leaf may not be wholly foreign to it.',
    ours:
      'The observation is the transcription’s, which disagrees on this point with the survey map of issue #45; the reading repeats it. Nothing has been checked against the facsimile by this pass, and the text the footnotes belong to is not identified.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look at the facsimile of pages 156–158 to see whether page 157 is a separate sheet photocopied with the set or the verso of a combinatorial sheet. Then look for the list of pairs and a « note n° 162 » with a « p. 779 » cross-reference in his texts of 1984–1987 that carry long numbered note apparatus — Récoltes et Semailles (its yin–yang part) and La Clef des songes are the obvious places, named from memory and not consulted.',
  },
// Folder 130 — find-novelty pass, Opus 5.5 (claude-opus-5-5) on an Opus 5.5 reading (130.modern.tex, 2026-10-03).
// Dropped as matches already footnoted in the reading: p. 6 (Raynaud, closure of Pic^0 as Néron model), pp. 9-13
// (Shioda-Tate shape), p. 14 (Shioda's height formula, asked not proved), pp. 16-18 (Beilinson-Bloch local pairing,
// programme only), pp. 25-29 (Albanese reduction, standard functoriality of Néron functions).
  {
    id: '130-neron-symbol-component-correction',
    cote: '130',
    pages: '3–5',
    kind: 'mathematical',
    claim:
      'For an abelian variety A over the fraction field of a DVR, the folder splits Néron’s local symbol (X, a)_v into an intersection number on the Néron model plus a correction v(X, a) characterised by four axioms (bilinearity, translation invariance, a normalisation by the vertical part of div f̄, boundedness), with m·v(X, a) ∈ ℤ for m the order of the component group, giving a pairing A^∨(K) × A(K) → ℤ/mℤ that factors through A(K)/A^0(K).',
    basis:
      'Page 3 lists the four properties of v(X, a); page 4 states (iv bis)–(vi) without proof and boxes (X, a)_v = v(X, a) + i(X̄, ā); a margin says v vanishes when m = 1 and asks, circled, « À examiner : cas d’une polarisation principale, jacobienne ».',
    ours:
      'The reading takes the 0-cycles to be of degree 0 and reads Z_ℓ as the kernel of the sum map (the page writes Z_0^*(A)_K with a doubtful exponent); (iv bis) carries an \\ill{} in the transcription (batch-01, l. 150) and the m = 1 margin is partly illegible. The existence of v satisfying the four axioms is not proved on the page, and the identification of the ℤ/mℤ pairing with SGA 7 IX’s pairing is explicitly not established by the reading.',
    literature: [],
    status: 'unsearched',
    settle:
      'Read Bosch–Lorenzini, « Grothendieck’s pairing on component groups of Jacobians » (Invent. Math. 2002), §4, and Néron, « Quasi-fonctions et hauteurs sur les variétés abéliennes » (Ann. of Math. 1965), for the decomposition of the local symbol as intersection on the Néron model plus a component-group term with denominator dividing m; if either has it for abelian varieties (not only Jacobians via regular models of curves), mark matched. An orienting web search surfaced Bosch–Lorenzini and Pépin, « Néron’s pairing and relative algebraic equivalence » (arXiv 1103.0570), as the neighbourhood; no section was read, so the status stays unsearched.',
  },
  {
    id: '130-quasi-function-sheaf',
    cote: '130',
    pages: '39–48',
    kind: 'mathematical',
    claim:
      'The folder organises Weil functions as a Zariski sheaf QF_X, the pushout of the sheaf of admissible functions Φ_X and of ℛ*_X over 𝒪*_X, in an exact sequence 0 → Φ_X → QF_X → Div_X → 0 whose other kernel is the constant sheaf U_X of M_K-units, and states that for quasi-projective X the maps to H^1(X, Φ_X) vanish, so that every Cartier divisor is the divisor of a global quasi-function.',
    basis:
      'Pages 41–44 define QF_X by θ(f) = (−φ_f, f), prove Φ_X → QF_X injective and compute the kernel of ℛ*_X → QF_X; pages 44, 46, 48 take global sections and reduce the surjectivity to O(1) on P^r.',
    ours:
      'The sign in θ is the edition’s (the exponent of f on p. 42 is illegible); the sheaf property of Φ_X is « admis » on p. 41 and proved only in a footnote of the reading; the P^r case is the reading’s, the page stops before it; the prose of p. 43 computing the kernel is partly illegible. In substance the global statement is the existence of Weil functions for Cartier divisors (Lang); what may not be in print is only the sheaf extension and its H^1 formulation, which is close to a matter of presentation.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check Lang, Fundamentals of Diophantine Geometry (1983) ch. 10, and Vojta’s CIME notes « Diophantine approximation and Nevanlinna theory » (2011) §8, for Weil functions presented as a sheaf extension of Div_X by locally M_K-bounded functions. If it is there, or if the sheaf form adds nothing beyond Lang’s existence theorem, mark matched. An orienting web search found no such sequence stated, which is not a search of those texts.',
  },
  {
    id: '130-interleaved-44-48',
    cote: '130',
    pages: '44–48',
    kind: 'codicological',
    claim:
      'The last leaves of the « Quasi-fonctions » run are two interleaved threads: the reading order is 44 → 46 → 48, while the cancelled pages 45 and 47 form a separate thread 45 → 47.',
    basis:
      'The last sentence of p. 44 continues at the head of p. 46 with the global-sections diagram, and that of p. 46 at the head of p. 48; pp. 45 and 47 are struck through with long diagonal strokes and p. 45’s last sentence continues on p. 47, on another formulation of admissibility on rational points.',
    ours:
      'The observation is the transcription’s (batch-03.fr.tex, header and notes to pp. 44–48); the reading keeps the threads apart. Nothing on the page says which thread was written first.',
    literature: ['Transcription 130, batch 3 (batch-03.fr.tex), header and pages 44–48'],
    status: 'candidate',
    settle:
      'A person checks against the facsimile whether 44/45, 46/47 are rectos and versos of the same sheets (an accident of scanning) or separate leaves filed out of order.',
  },
  // /find-novelty 134-8 — Opus 5.5 (claude-opus-5-5) on an Opus 5.5 reading, 2026-10-10. Only p. 63 is transcribed; it carries no mathematics, so both entries are codicological.
  {
    id: '134-8-copying-leaf-misfiled',
    cote: '134-8',
    pages: '63',
    kind: 'codicological',
    claim:
      'The folder catalogued as the typescript of chapter VII of Pursuing Stacks (typescript pp. 555–593) contains a typed, signed leaf of copying instructions for a different slice of the typescript, pp. 259–381 (« Modelizing Story »), so at least this leaf does not belong to the chapter the folder title names.',
    basis:
      'Page 63 asks for three copies of « Modelizing Story », pages 259 to 381 plus three pages of table of contents; the inventory title reproduced in the transcription is « [Chapitre VII (pages 555 à 593) : Linearization of homotopy types] ». The leaf is scanned upside down. Nothing in the claim rests on an \\ill{} or \\uncertain{} (the only \\uncertain{} is « aoùt » in the PS; the \\ill{} are struck words replaced by additions).',
    ours:
      'The reading states the mismatch and declines to explain it (wrapper, reused sheet, later filing are all left open); this entry claims only the mismatch. The other pages of batch 4 and the rest of the folder were not transcribed, so whether other leaves of the folder are also foreign to chapter VII is not known.',
    literature: [
      'Transcription 134-8, batch 4 (batch-04.fr.tex), header and page 63',
      'Modernised reading 134-8.modern.tex, section « Ce que couvre cette lecture » and its footnotes',
    ],
    status: 'unsearched',
    settle:
      'A person checks page 63 against the facsimile (and its verso), and checks whether the Montpellier inventory or G. Maltsiniotis’s edition of Pursuing Stacks says where the typescript pp. 259–381 and its covering papers are filed. If the edition or the inventory already records the leaf, mark matched.',
  },
  {
    id: '134-8-modelizing-story-distribution',
    cote: '134-8',
    pages: '63',
    kind: 'codicological',
    claim:
      'The leaf records one distribution of the typescript slice pp. 259–381 of Pursuing Stacks: three copies, one posted to Ronnie Brown (Bangor), one to Zoghman Mebkhout (Paris), one handed to Contou-Carrère, the original returned to the author; and it records that typescript pages 274 and 275 were typed on the two sides of a single sheet by mistake.',
    basis:
      'Page 63, typed with an autograph closing and signature: items 2) and 3), the two addresses, « Remettre la troisième copie à Monsieur Contou-Carrère », and the PS about returning the original « vers le quatre ou le cinq » August. The leaf carries no year; the reading’s « été 1983 » is an inference and is not part of this claim.',
    ours:
      'The reading adds, from memory and unchecked, that Brown was among the correspondents through whom Pursuing Stacks circulated and that Mebkhout is the mathematician of the Riemann–Hilbert correspondence; neither is part of this entry. The identification of « Contou-Carrère » with a Montpellier colleague is also the reading’s, not the page’s.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check G. Maltsiniotis’s edition of Pursuing Stacks (introduction and editorial notes on the typescript and its circulation) and R. Brown’s published accounts of the Grothendieck correspondence for this distribution list and for the recto-verso pages 274–275; if either records them, mark matched. The recto-verso claim can also be settled by looking at the typescript leaf carrying pp. 274–275 wherever it is filed.',
  },
  {
    id: '156-1-segment-biorder',
    cote: '156-1',
    pages: '10–13',
    kind: 'mathematical',
    claim:
      'A model of a one-dimensional form that is a single segment (axioms F1–F5, with F′3) is the same thing as a poset with distinct least and greatest elements that is dense and locally directed in both directions, segments being the intervals [x, y], x < y; the order need not be total.',
    basis:
      'Page 12 builds the order from the sub-segments issued from one extremity, lists « infiniment divisible » and « localement filtrante décroissante » with a filtrante croissante clause added between the lines, and states the converse; page 13 concludes that a segment structure is a biorder, the conditions being autodual.',
    ours:
      'Neither direction is proved on the page; the proofs sketched in the reading are the edition’s, and the filtering condition F′3 that the forward direction (property b) needs is the reading’s reconstruction of a mostly illegible note at the foot of page 6. The converse rests on a line of page 12 carrying several \\ill{} words and a struck word, and the « filtrante croissante » clause is read only in part; the marginal note keyed to it by an asterisk is fragmentary. That the order is not total in general is the reading’s emphasis, drawn from Cor. 3 c) on page 5.',
    literature: [
      'B. Courcelle, Betweenness of partial orders, RAIRO ITA 54 (2020) — abstract and introduction only, via a web search; characterises betweenness relations of posets, not this bounded, dense, locally directed class',
      'Directed Transit Functions, arXiv:2407.07741 (2024) — abstract only, via a web search; first-order axioms for directed betweenness in posets',
      'arXiv:1609.07519, On the strength of some topological lattices — abstract only; bounded dense betweenness, total-order case',
    ],
    status: 'unsearched',
    settle:
      'First settle the page: re-read the converse on page 12 against the facsimile (/transcribe-grothendieck), since it is carried by illegible words. Then read Courcelle 2020 and the betweenness literature it cites (Pitcher–Smiley 1942; Sholander 1952), and Prenowitz–Jantosciak, Join Geometries (1979), for an axiomatics of segments as intervals of a non-total, bounded, dense, locally directed order. The search so far went only to abstracts, so the status stays unsearched.',
  },
  {
    id: '156-1-branching-without-branch-point',
    cote: '156-1',
    pages: '20–22',
    kind: 'mathematical',
    claim:
      'The local axioms F1–F5 admit a regular connected model in which every lieu has exactly two branches and yet the form bifurcates — a trunk order with two or more upper branches glued above it — so a sixth axiom F6, saying that same-branch segments at a lieu are contained in a common segment, is needed to exclude it.',
    basis:
      'Page 20 states that a connected order, locally strictly directed both ways and with no extreme element, satisfies F1–F5 but need not be directed; page 21 gives the example L₀ ⨿ ∐ Lᵢ with every element of L₀ below every element of each Lᵢ (a first example on ℚ cut at an irrational, times a set E of cardinal ≥ 2, is struck); page 22 states F6 and compares it with F3.',
    ours:
      'The reading supplies card I ≥ 2, which the page does not state, reads « ∃ x′ < a < a″ » as « for every a there exist a′ < a < a″ », and shows that F6 excludes the example. The identification with the branching line of non-Hausdorff one-manifolds is this pass’s, not the reading’s. The phenomenon matched is topological; the page’s statement is about its own combinatorial axioms, and only the phenomenon is in the literature.',
    literature: [
      'A. Haefliger, G. Reeb, Variétés (non séparées) à une dimension et structures feuilletées du plan, Enseign. Math. 3 (1957) — known here through secondary sources only, not read',
      'M. Baillif, A. Gabard, Manifolds: Hausdorffness versus homogeneity, arXiv:math/0609098 — the branching line (two copies of ℝ identified along the negative reals) as a standard non-Hausdorff one-manifold',
      'Wikipedia, Non-Hausdorff manifold — the branching line',
    ],
    status: 'matched',
    settle:
      'Read Haefliger–Reeb 1957 to confirm that a one-dimensional space branching with no branch point is treated there. If so, this stays matched as a phenomenon. What remains open is narrower: whether F6, as a combinatorial « Hausdorff-type » condition on segments, appears in a published axiomatics of graphs or one-dimensional spaces — a separate search, not a reason to reopen this entry.',
  },
  {
    id: '156-1-written-alongside-156-2',
    cote: '156-1',
    pages: '3, 23',
    kind: 'codicological',
    claim:
      'Chapter I (folder 156-1) was still being written after chapter II (folder 156-2) had begun: a margin note on page 3 is dated « 7.6. » and page 23 opens « (7 juin) », one day after the « (6 Juin) » heading of 156-2, and the dated note on page 3 decides an identification that the corollary on page 6 justifies.',
    basis:
      'Page 1 carries « (5 juin) » and « (Juin 86) »; the transcription reads « 7.6. » at the head of the slanted note in the left margin of page 3 and « (7 juin) » at the start of page 23; folder 156-2’s transcription reads « (6 Juin) » in its margin. The author’s own pagination restarts at page 3 (his p. 2), so pages 1–2 are a separate first start.',
    ours:
      'The inference that the two chapters were written concurrently is the reading’s, from the three dates; the pages do not cross-refer on this point.',
    literature: [
      'Transcription 156-1, batch-01.fr.tex, pages 1, 3 and header; batch-02.fr.tex, page 23 and header',
      'Transcription 156-2, batch-01.fr.tex, the « (6 Juin) » margin date',
    ],
    status: 'candidate',
    settle:
      'A person checks the three dates against the facsimiles — « 7.6. » on page 3 of 156-1, « (7 juin) » on page 23 of 156-1, « (6 Juin) » in 156-2 — and whether the page 3 note is in the same ink as the page 23 additions rather than the main text of page 3.',
  },
// Candidate entries for folder 156-3 (find-novelty, Opus 5.5 on an Opus 5.5 reading, 2026-10-10). Not merged into src/content/findings.ts.
  {
    id: '156-3-order-from-betweenness',
    cote: '156-3',
    pages: '11–13',
    kind: 'mathematical',
    claim:
      'The order of a "tronçon ordonné" — a partially ordered set that is dense, directed upwards and downwards, has at least two elements, and whose strict up- and down-sets are filtered — is determined up to reversal by its strict betweenness relation (b strictly between a and c iff a < b < c or c < b < a).',
    basis:
      'Page 11 recovers the comparable pairs from betweenness by density, chooses a comparable pair a < b, and expresses L≥b, L≤a and ]a,b[ by betweenness; page 12 writes u ≤ v as the existence of x ≤ a, y ≥ b with x ≤ u ≤ v ≤ y, using directedness; page 13 proves the lemma that turns this into betweenness conditions, and its NB lists exactly the two hypotheses used (density, two-sided directedness). The step « a et b disjoints ssi ∃ c strictement entre a et b » rests on words read with doubt (\\uncertain{soit strictement entre}), though the mathematics it needs is unambiguous.',
    ours:
      'The reading corrects the lemma\'s « trois éléments » to four and replaces the margin\'s « or {a,b,c} of cardinal ≤ 2 » (false for a = c ≠ b) by the exact relation; it also supplies the observation that the result fails for an arbitrary poset. The reading\'s footnote credits the characterisation of poset betweenness to Altwegg (1950); Courcelle 2020 credits the axiomatisation to Lihová (2000). Altwegg was not opened by this pass, so that attribution is unchecked here.',
    literature: [
      'B. Courcelle, « Betweenness of partial orders », arXiv:2004.09777 (2020), §1(a)–(b) and Theorem 7 with its Lemma on B-minimality',
      'J. Lihová, « Strict-order betweenness », Acta Univ. M. Belii Ser. Math. 8 (2000) — cited by Courcelle for the axiomatisation; not opened',
    ],
    status: 'matched',
    settle:
      'Settled as a special case: Courcelle 2020, Theorem 7, shows a poset is reconstructible up to reversal from its betweenness relation iff it is B-minimal (every comparable pair lies in a 3-chain) and connected (with one infinite exception). Density gives B-minimality and two-sided directedness gives connectedness, so every tronçon qualifies. Kept as a killed candidate; the page\'s explicit formula for ≤ via an anchor pair (a, b) is a direct route, not a different result.',
  },
  {
    id: '156-3-betweenness-from-cuts',
    cote: '156-3',
    pages: '14–15',
    kind: 'mathematical',
    claim:
      'For a tronçon ordonné, the comparability relation together with, for each comparable pair ε, only the partition (unlabelled) of the elements comparable to both members of ε into its connected pieces determines the strict betweenness relation, hence the order up to reversal: in a 3-chain J, the middle element is the unique one for which the pieces of C(ε) and C(ε′) containing the third element, ε and ε′ the two pairs through it, are disjoint.',
    basis:
      'Page 14 sets the problem (Drap₂ and the decompositions of C(ε) determine 𝓡); page 15 computes the three pieces X_{a,b} = L>b, X_{b,c} = L<b, X_{c,a} = ]a,c[ for a < b < c, finds X_{a,b} ∩ X_{b,c} = ∅ and the other two intersections non-empty by density, and concludes « On gagne ! »; combined with the lemma of pages 11–13 this recovers the order up to reversal. Comparability alone would not suffice for a totally ordered tronçon, where the comparability graph is complete.',
    ours:
      'The reading normalises the page-14 formula for C(ε), which the page writes with an indexed L and {ε, t} (read as t ∉ ε and ε ∪ {t}), and reads the page-10 pieces between consecutive cuts as open intervals where the brackets read closed. The pass adds the remark that comparability alone does not determine the order; the construction itself is the page\'s.',
    literature: [
      'B. Courcelle, « Betweenness of partial orders », arXiv:2004.09777 (2020), §1–2 — treats reconstruction from betweenness and (Remark 12, via modular decomposition) from the comparability graph, not from cut or component data',
    ],
    status: 'candidate',
    settle:
      'Only one source was read, and the statement is elementary once posed, so the search is thin. Check the cut-point characterisations of linear order (L. E. Ward 1936; Kok, Connected orderable spaces, 1973), M. Altwegg 1950 and J. Lihová 2000 on poset betweenness, and Gallai 1967 on unique transitive orientation, for a version taking as data the partitions of the common-comparability sets. If any of them states it for posets, mark matched; if it appears only for total orders, say so here, since the partial-order case is the one the page is about.',
  },
// Candidate entries for folder 156-4 (find-novelty, Opus 5.5 on an Opus 5.5 reading, 2026-10-10). Not merged into src/content/findings.ts.
  {
    id: '156-4-figures-as-configurations',
    cote: '156-4',
    pages: '53–61',
    kind: 'mathematical',
    claim:
      'A poset of "figures" (𝔉, ≤) in which every bounded family has a supremum, every figure is the supremum of the sup-irreducible figures below it, and figures whose strata are pairwise compatible are compatible (C 1–C 3), with all figures finite, is the same thing as a poset (𝓜, ≤) with finite down-sets and a reflexive, symmetric relation R inherited downwards; the figures are then the finite down-closed subsets whose elements are pairwise R-related.',
    basis:
      'Page 53 poses C 1, page 54 C 2 (with the sup-primeness the reading supplies), page 57 the description by down-closed subsets, page 58 C 3, pages 59–60 the equivalence for figures of finite type, and page 61 the finite form: « les 𝓜_{≤X} finis », R « réfl. et sym. » inherited by X′ ≤ X, Y′ ≤ Y, the figures being « les parties fermées, finies » with (X, Y) ∈ R for all their elements. The conditions themselves are legible; illegible words on pages 59 and 61 sit in the wording around them, and « évident » in page 58’s NB is uncertain.',
    ours:
      'The reading supplies the sup-primeness hypothesis (strata of Sup F_i lie under some F_i) without which page 54’s « Sup ↦ ∪ » fails, and compares the result with Birkhoff (1937) and Raney (1952). The identification with event structures is this pass’s: taking # as the complement of R, R inherited downwards is the principle of conflict heredity (e # e′ ≤ e″ ⇒ e # e″), finite down-sets are the principle of finite causes, and the figures are the finite configurations (left-closed, conflict-free sets). The reading does not name this match.',
    literature: [
      'F. W. Vaandrager, « A simple definition for parallel composition of prime event structures », CWI report CS-R8903 (1989), Definitions 2.1 (prime event structure with binary conflict: finite causes, conflict heredity) and 2.3 (configuration: left-closed and conflict-free); §1 attributes prime event structures to Nielsen, Plotkin and Winskel and their relation to finitary prime algebraic domains',
      'M. Nielsen, G. Plotkin, G. Winskel, « Petri nets, event structures and domains, Part I », Theoret. Comput. Sci. 13 (1981) 85–108: cited for the representation theorem, not opened',
      'G. Winskel, « Event structures », LNCS 255 (1987) 325–392: fetched as a scanned PDF and not readable by this pass',
    ],
    status: 'matched',
    settle:
      'Matched on the (𝓜, ≤, R) side: page 61’s figures are exactly the finite configurations of a prime event structure with binary conflict (Vaandrager 1989, Defs 2.1, 2.3). For the other direction, open Nielsen–Plotkin–Winskel 1981 and check that its representation theorem (finitary prime algebraic coherent domains ↔ prime event structures) has the same hypotheses as C 1–C 3 with sup-primeness; if it does, the whole equivalence of pages 59–61 is matched. Kept as a killed candidate.',
  },
  {
    id: '156-4-supports-boolean-presumption',
    cote: '156-4',
    pages: '65–68',
    kind: 'mathematical',
    claim:
      'The folder presumes that the saturated sets of multistrates (fixed points of cosupp ∘ cosupp, where cosupp is « disjoint from every element ») form a Boolean algebra; as stated, under the axioms C 1–C 4 posed up to page 64 (and C 5–C 7 with ≼ the identity), this fails: the lattice of saturated sets can be a non-distributive hexagon.',
    basis:
      'Page 68: « Je présume qu’on a en fait une algèbre de Boole (« ultra-stonienne », à cause des Sup quelc.) » — « présume » is an insertion over a struck « dis », legible; the lines that follow on page 68 are mostly \\ill{}. Pages 66–67 define cosupp, supp, saturated sets and Σ, with arbitrary Inf and Sup. Page 74 itself notes that disjunction is not controlled by C 1–C 4.',
    ours:
      'The counterexample is this pass’s own, checked by exhaustive computation: 𝓜 has four minimal elements a, b, c, d and three elements v_ab, v_bc, v_cd above the pairs ab, bc, cd; R is the reflexive symmetric relation generated by all pairs inside each 𝓜_{≤v} (hence inherited downwards, and making each 𝓜_{≤v} a figure); 𝓜 is connected, so C 4 is vacuous. Disjoint pairs are exactly ab, bc, cd, and the saturated sets are ∅, {b}, {c}, {a,c}, {b,d}, 𝓜 — two chains between ∅ and 𝓜, where {b,d} ∧ ({b} ∨ {c}) = {b,d} but ({b,d} ∧ {b}) ∨ ({b,d} ∧ {c}) = {b}. The reading already notes that Σ is a complete orthocomplemented lattice, not distributive « en général pour une relation symétrique quelconque », and Boolean when R is total (regular open algebra of (𝓜, ≤)); it does not say whether the folder’s axioms exclude the general case. They do not.',
    literature: [],
    status: 'refuted',
    settle:
      'What still stands: Σ is a complete ortholattice for any such (𝓜, ≤, R), and a complete Boolean algebra when R is total. Open questions: whether the later disjunction axioms (C 5 of page 69, the « paquet d’axiomes de disjonction » of page 85, or those of folders 156-6 to 156-8) restore distributivity; and, in the literature on orthogonality spaces (Dacey 1968; Birkhoff, Lattice Theory, polarities), which condition on a symmetric irreflexive relation makes its lattice of closed sets Boolean. A person should re-run the hexagon check before relying on it.',
  },
// Candidate entries for folder 156-5 (find-novelty, Opus 5.5 on an Opus 5.5 reading, 2026-10-10). Not merged into src/content/findings.ts.
// No mathematical entry: every candidate in the pool was a match the reading already footnotes (Alexandrov 1937 for figures as Alexandrov topologies, refinement as continuous inclusion; SGA 4 IV §9 recollement for the lemma of pp. 40-44 and its closing characterisation on p. 48; Quillen's Theorem A for the corollary of p. 46; Stone 1937 for regular opens), or a statement the reading had to repair or refute (connectedness of M, pp. 12-14; the corollary of p. 31; e) of p. 41), which the skill excludes.
  {
    id: '156-5-gf-viii-rereading',
    cote: '156-5',
    pages: '1, 3',
    kind: 'codicological',
    claim:
      'Chapter V (folder 156-5, dated 14-18 June 1986) was reread and annotated after chapter VIII (folder 156-8, begun 26 June 1986) had reached its pages 37 and 44-45: two margins of 156-5 send the reader forward to « GF VIII p. 37 » and « GF VIII pp. 44, 45 », and 156-8 page 45 of the archivists opens « Je vais reprendre ici la prop. 1 p. 1 de [GF] V ».',
    basis:
      'Margin of page 1 (« voir variante in extenso, formellement plus forte, voir GF VIII p. 37 ») and margin of page 3 (« Exemple idiot — mais voir contre-exemple correct avec I infini, GF VIII pp. 44, 45 »), both checked against the facsimile by Michel Hua on 27 September 2026 per the apparatus of batch-01; the page-3 note is in a different ink from the page, the page-1 note in the same ink, so ink alone does not separate the layers. On the 156-8 side, the archivists\' page 45 is the start of « Figures indexées » and pages 52-53 carry an example « où on a 1\' et 2\' … sans avoir 3\') », which fits the page-3 margin. « avec I » (p. 3) and the « CF V » of 156-8 p. 45 are read with doubt.',
    ours:
      'The concordance of Grothendieck\'s chapter-VIII pagination (his 37, 44-45) with the archivists\' 45 and 52-53 is the reading\'s, taken from the offset of 156-8\'s own numbering; it was checked here against the 156-8 transcription only, not against the facsimile. The lower bound « not before 26 June » is the catalogue date of 156-8, not a date on these leaves.',
    literature: [
      'Transcription 156-5, batch 1 (batch-01.fr.tex), pages 1 and 3 and their \\note apparatus',
      'Transcription 156-8, batch 3 (batch-03.fr.tex), pages 45, 52 and 53',
      'Inventory title of 156-8 (src/content/catalogue.ts): « notes manuscrites (26/06-04/07/1986) »',
    ],
    status: 'candidate',
    settle:
      'A person reads Grothendieck\'s own page numbers on 156-8 facsimile pages 45 and 52-53 to confirm they are his 37 and 44-45, and checks whether any other margin of 156-5 (pp. 4, 7, 10, 11, 16-18, 20) is in the page-3 ink, which would delimit the rereading layer.',
  },
// Candidate entries for folder 156-6 (find-novelty, Opus 5.5 on an Opus 5.5 reading, 2026-10-10). Not merged into src/content/findings.ts.
// No mathematical entry: the candidate pool is matches the reading already footnotes (Birkhoff 1937 for the representation by down-sets of irreducibles, pp. 14-18 and 41; Alexandrov 1937 for the generic-point remark, p. 30; Raney 1952 for the Lemma of p. 49; the sheaf condition for At 11, p. 67), definitions and axioms internal to his framework (At 1-At 14, the definition of subdivision p. 85), or statements the reading had to repair (pp. 11, 18, 56, 58, 62-63, 90, 93), which the skill excludes.
  {
    id: '156-6-dates-past-catalogue',
    cote: '156-6',
    pages: '1, 10, 20, 34, 64, 87',
    kind: 'codicological',
    claim:
      'The folder was written from 18 to 22 June 1986, not 18-20 June as the inventory title has it: his own dates run « 18 juin 86 » (p. 1), « 19 juin » (p. 20), « 20 juin » (p. 34, and the additions of pp. 10 and 13), « 21. juin » (p. 64) and « 22. Juin » (p. 87), which closes the gap with chapter VII (156-7), whose page 1 is dated « 23 juin ».',
    basis:
      'Dates in his hand, each transcribed as a \\marginal with a \\note: batch-01 p. 1 (« 18 juin 86 », slanted, left margin), p. 10 (« (20 juin) » heading an addition), p. 13 (« le 20 », in a mostly illegible margin, read as a reference to 20 June), p. 20 (« 19 juin », underlined); batch-02 p. 34 (« 20 juin », underlined); batch-04 p. 64 (« 21. juin », underlined); batch-05 p. 87 (« 22. Juin », underlined). None is marked \\uncertain{}; only the « le 20 » of p. 13 sits in an \\ill{}-ridden note and is not needed for the claim. The 20 June additions on pp. 10 and 13 are later than the 19 June of p. 20, so the first pages carry a rereading layer.',
    ours:
      'The comparison with the inventory title and with the 156-7 date is the edition\'s; the transcription headers of batches 4 and 5 already note the discrepancy. Reading the 18-22 June span as the writing period assumes the dates mark the day of writing, which the pages do not say.',
    literature: [
      'Transcription 156-6, batches 1, 2, 4, 5 (batch-0N.fr.tex), the \\marginal dates and their \\note apparatus at pp. 1, 10, 13, 20, 34, 64, 87',
      'Inventory titles of 156-6 (« notes manuscrites (18-20/06/1986) ») and 156-7 (« (23-26/06/1986) ») in src/content/catalogue.ts',
      'Transcription 156-7, batch 1 (batch-01.fr.tex), page 1: « 23 juin »',
    ],
    status: 'candidate',
    settle:
      'A person reads « 21. juin » on facsimile page 64 and « 22. Juin » on page 87 of 156-6, confirming the day numerals; if they stand, the inventory range should read 18-22/06/1986.',
  },
// Candidate entries for folder 156-7 (find-novelty, Opus 5.5 on an Opus 5.5 reading, 2026-10-10). Not merged into src/content/findings.ts.
// No mathematical entry: the candidate pool is matches the reading already footnotes (Birkhoff 1937 for the join-irreducible representation, p. 5; Nielsen-Plotkin-Winskel 1981 prime event structures, p. 5; Björner 1984 simplicial posets, p. 13; Birkhoff 1940 polarities and Dacey 1968 orthogonality spaces for the support lattice, pp. 61-63; Husimi 1937 orthomodular law for the graph counter-example of p. 98, and the non-distributivity of pp. 81-83, which is a standard property of orthocomplemented lattices of this kind; complete atomic Boolean algebras for the Proposition of p. 80), axiomatics internal to his framework (At, ML, MΛ, Prat, Mag), statements the reading had to repair (pp. 5, 13, 25-26, 29, 54-58, 91, 103), or statements the folder announces without proof (p. 22 b)-d), p. 42, p. 93 (b)-(c), p. 100, p. 104), which the skill excludes. Nothing was looked up in the literature for this pass beyond those footnotes.
  {
    id: '156-7-page1-index-later-layer',
    cote: '156-7',
    pages: '1, 86, 99, 110–113',
    kind: 'codicological',
    claim:
      'The cross-reference on page 1, « cf. … p. 23, 50-58, 59, 110-113 », points to pages of this same folder up to its last leaf, so it was written after pages 110-113 existed: page 1 carries a rereading layer added at or after the end of the folder, like the « 26.6 » margin note of page 86, which sits beside text that precedes the « 26 juin » heading of page 99.',
    basis:
      'Batch 1, page 1 \\note: under « GF VII », a slanted reference in his hand « cf. \\ill{} p. 23, 50-58, 59, 110-113 », the last numbers circled and the « 50 » overwritten; the pages it names are the recapitulation of axioms (p. 23), the préateliers and ensemblistes (pp. 50-58), the Définition of p. 59 and the magasins / atelier spécial (pp. 110-113). Batch 5, page 86 \\marginal opens « 26.6 » (« read so »), page 99 opens its second paragraph with « 26 juin »; page 69 is dated « 25 juin ». The one \\ill{} on page 1 is the word before « p. » and does not carry the claim; the page numbers are not marked \\uncertain{}.',
    ours:
      'That the numbers on page 1 are pages of this folder rather than of another chapter is the edition\'s inference (the \\ill{} word before « p. » could in principle name another text), supported by the match of each number with a recapitulation or definition here. That pages 84-98 were written before 26 June is likewise inferred from the order of the dates, not stated.',
    literature: [
      'Transcription 156-7, batch 1 (batch-01.fr.tex), header and page 1 \\note',
      'Transcription 156-7, batch 5 (batch-05.fr.tex), header, page 86 \\marginal and \\note, page 99 \\subsection{26 juin}',
      'Transcription 156-7, batch 4 (batch-04.fr.tex), page 69 « (25 juin) »',
      'Modernised reading 156-7.modern.tex, sections on pp. 50-60 and 101-113',
    ],
    status: 'candidate',
    settle:
      'A person reads the cross-reference on facsimile page 1 of 156-7: the illegible word before « p. » (« ici », « infra », or a chapter siglum such as « GF VIII ») and the numbers « 110-113 »; if the word names this folder and the numbers stand, the reference was added after the folder was finished.',
  },
// Candidate entries for folder 156-8 (find-novelty, Opus 5.5 on an Opus 5.5 reading, 2026-10-10). Not merged into src/content/findings.ts.
// No mathematical entry: the candidate pool is matches the reading already footnotes (Serre 1977 graphs, pp. 3-5; the diamond property, p. 3; order ideals, p. 18; Birkhoff 1937 join-irreducibles, p. 19; polyhedral vs regular CW complexes, p. 26; Birkhoff 1940 polarities and Dacey 1968 orthogonality spaces for Σ_M, pp. 73-75; Chevalley constructible sets, p. 84; SGA 4 projection formula, p. 56; Fishburn 1970 interval orders, p. 106; order complex, p. 95), axiomatics internal to his framework (Mag, Mag', Mag L, Mag div, Mag quens, Magens, At, At M, Mag pol, supp 1, the theorem of p. 69, the Proposition of p. 39, the Scholie of pp. 86-87, which follows formally from injectivity of A ↦ |A|° under full faithfulness), elementary combinatorics of finite unions of intervals in an ordered set (pp. 94-126), statements the reading had to repair or verify itself (pp. 9, 10, 23, 30, 76-77, 88, 102, 126), or statements announced without proof (Prop. 4 and 5, pp. 12-13; p. 117 2)), which the skill excludes. Nothing was looked up in the literature for this pass beyond those footnotes.
  {
    id: '156-8-page2-table-later-layer',
    cote: '156-8',
    pages: '2, 30, 39, 75, 77, 86–87',
    kind: 'codicological',
    claim:
      'The table of kinds of magasins on page 2 was written after page 77 at the earliest: it states results about the set of supports Σ_M, a notation the folder introduces only on page 75, and the identification Σ_M ≃ 𝔓(L) proved as the corollary of page 77, so the leaf placed second in the folder is a later recapitulation rather than an opening plan.',
    basis:
      'Batch 1, page 2: each box carries a Σ_M statement (« Σ_M ⊂ 𝔓(M) », « Σ_M ≃ 𝔓(L) » for the ponctuaires, « A ∩ B = ∅ ⇔ A |∘| B » for the fidèles) and cites his pages 9 to 31 (our 17 to 39, e.g. « Mag 1 -- Mag 4 (p. 22) » = our p. 30). Batch 4, page 75 introduces the notation: « Je désigne par Σ_M (notation standard) l\'ens. des supports ». The box names (locaux, ponctuaires, fidèles, maquettes, modérés) do not occur as such in the body. The \\uncertain{} and \\ill{} on page 2 sit in the qualifications of the « locaux » box and in the margin notes, not in the Σ_M statements or page numbers the claim rests on.',
    ours:
      'The correspondence between the table\'s page numbers and ours (his n = our n + 8) and between its box names and the body\'s notions is the reading\'s, established from the cited page numbers. That the « fidèles » box\'s « A ∩ B = ∅ ⇔ A |∘| B » echoes the Scholie of pp. 86-87 (which states it only for admissible families) is our observation and would push the date later still; it is not needed for the claim.',
    literature: [
      'Transcription 156-8, batch 1 (batch-01.fr.tex), page 2',
      'Transcription 156-8, batch 4 (batch-04.fr.tex), page 75',
      'Transcription 156-8, batch 5 (batch-05.fr.tex), pages 86-87',
      'Modernised reading 156-8.modern.tex, header and section « La table de la page 2 »',
    ],
    status: 'candidate',
    settle:
      'A person compares ink and hand of page 2 with pages 73-88 and with page 7 (26 June) on the facsimile, and checks whether page 2 is a separate leaf or the verso of a later sheet; if its ink matches the late pages, the table is a recapitulation written at or after the end of the supports section (about 1 July 1986).',
  },
  {
    id: '156-9-disposition-correspondences',
    cote: '156-9',
    pages: '87–99',
    kind: 'mathematical',
    claim:
      'For sets with a symmetric relation (orthogonality spaces), the correspondences that admit a transpose — equivalently, relations whose rows and columns are all closed for the polarity — correspond bijectively to Sup-preserving maps between the complete ortholattices of closed sets, giving a category that is self-dual by transposition, identity on objects.',
    basis:
      'Proposition 3 (p. 89), Proposition 4 (p. 94) and the scholie of pp. 96–98 set up the bijections Corr(Σ, Σ′) ≅ Corr(E, E′) ≅ Corr*(E, E′); page 98 composes correspondences and page 99 states the equivalence with complete ortholattices and Sup-maps and its self-duality, with the Hilbert-space analogy written by the author. The words « complètes » and « systèmes » in that statement, and the date « 11.7 » above it, are \\uncertain{} in the transcription; the mathematics does not rest on them.',
    ours:
      'The reading supplies a direct proof that (iv) ⇔ (v) in Proposition 4 without the clause the page « dû ajouter après coup », and the remark that every Sup-map between complete ortholattices has a transpose (∁ ∘ g ∘ ∁, g its right adjoint). It also corrects the « Lemme » of p. 71, which as written claims a bijection where only an injection holds. The modern names (orthogonality space, complete ortholattice, dagger category) are the edition’s.',
    literature: [
      'S. Tull et al., « Monoidal Categories for Formal Concept Analysis », arXiv:2012.08268, abstract: the category of bonds / Chu correspondences between formal contexts is equivalent to the *-autonomous category of complete sup-lattices (read in the abstract only, not in full)',
      'J. Paseka and T. Vetterlein, « Categories of orthosets and adjointable maps », arXiv:2501.04482v3 (Int. J. Theor. Phys. 2025): Definition 3.1 (adjointable maps of orthosets), Lemma 3.6 (adjointable maps between complete ortholattices are Sup-preserving), Section 6 (dagger category of complete ortholattices, dagger = adjoint) — read through a web summary, not the PDF',
      'B. Jacobs, « Orthomodular lattices, Foulis semigroups and dagger kernel categories » (2010), as cited in the reading’s footnote — not consulted in this pass',
    ],
    status: 'matched',
    settle:
      'Matched in substance: Corr*(E, E′) for symmetric contexts is the notion of a bond between the contexts (E, E, non-|o|) and (E′, E′, non-|o|), and the bond–Sup-map correspondence is standard in formal concept analysis. A person should confirm against Ganter and Wille, Formal Concept Analysis (1999), the section on bonds (§7.1), which this pass did not open, and check that the transposition on Corr* is the bond-transpose there. Nothing here dates the folder relative to those sources, and no precedence follows either way.',
  },
  {
    id: '156-9-crossref-156-8',
    cote: '156-9',
    pages: '13',
    kind: 'codicological',
    claim:
      'The cross-reference « cf. p. 110, 111 » on page 13, for a classification of the vertices of a prefigure into five types, points to the author’s pages 110–111 of chapter VIII, which are pages 118–119 of folder 156-8 — not to pages missing from the fonds.',
    basis:
      'Page 13 of 156-9 announces a « petite digression » on the vertices of a prefigure, « cinq types : sommets-bord propres et impropres, sommets isolés, sommets intérieurs propres et impropres », cf. p. 110, 111. In folder 156-8, page 118 (author’s p. 110) defines ord(a, Φ), isolated vertices and sommets-bord propres/impropres, and page 119 (author’s p. 111) adds the internal vertices, redundant (« de morcellement ») and lacunary, and says « il y a un sommet de chacun des cinq types combinatoires ». In 156-9 the words « cinq », « impropres » and « ceux-là seront les redondants » are \\uncertain{}, but 156-8 states the count explicitly.',
    ours:
      'The identification is this pass’s, made from the two transcriptions. The 156-9 transcription calls the pages « extérieures à ce lot » and the modernised reading says they « ne sont pas dans ce dossier »; both are right, and neither names where the pages are.',
    literature: [
      'Transcription 156-9, batch 1 (batch-01.fr.tex), page 13',
      'Transcription 156-8, batch 6 (batch-06.fr.tex), pages 118–119, with their « p. 110 / p. 111 de l’auteur » notes',
    ],
    status: 'candidate',
    settle:
      'A person checks the « 110, 111 » on the facsimile of 156-9 page 13 and the author’s page numbers on 156-8 pages 118–119. If they hold, the modernised reading of 156-9 (section on pages 7–15) can name folder 156-8 pages 118–119 instead of saying the pages are outside the folder.',
  },
  // Folder 25 — find-novelty pass, Opus 5.5 (claude-opus-5-5), 2026-10-10, on a reading made by Opus 5.5 (pass header 2026-10-03). Only pp. 134-135 (a typed letter to Dieudonné) are transcribed; the rest of the folder is the EGA V typescript covered by another edition and was not read.
  // Mathematical pool dropped: the struck paragraph of p. 135 is the standard limit argument of EGA IV § 8 applied to a fibre locus EGA IV § 12 proves open, which the reading names as a match; its statement as written (« prof ≥ n ») is false and was repaired by the edition, so neither version is a novelty. The plan of §§ 22-27 (p. 134) is a document about the treatise, not a mathematical statement.
  // Kind of the second entry: it is a claim about what the letter refers to and about a published paper's origin; filed as codicological because it is not a mathematical statement, though it does make a claim about the literature and is held to that standard.
  {
    id: '25-letter-1965-before-folder-range',
    cote: '25',
    pages: '134–135',
    kind: 'codicological',
    claim:
      'The two leaves 134–135 are a typed letter to Dieudonné dated in Grothendieck’s hand 29.9.1965, earlier than the lower bound of the folder’s inventory dating « [à partir de 1967-1987] », and they carry a second pencil numbering 37–38 showing the letter was filed inside a run of notes rather than added to the folder as a loose piece.',
    basis:
      'Transcription 25, batch 7: the date « 29.9.1965 » at the head of p. 134 and the signature on p. 135 are marked as his ink (\\add{}); the header records the pencil numbers 37–38 on the two leaves. The letter speaks of the 4th fascicule of EGA IV as still in preparation, which agrees with a 1965 date. No \\ill{} or \\uncertain{} touches the date.',
    ours:
      'The observation that the date falls outside the inventory range, and that this does not contradict the inventory (a folder assembled from 1967 can hold an older piece), is the reading’s. Whether the pencil 37–38 is the typist’s or his is left open by the transcription.',
    literature: [
      'Transcription 25, batch 7 (batch-07.fr.tex), header and pages 134–135',
      'Modernised reading 25.modern.tex, section « Une date hors de l’intervalle du dossier » and its footnote on the pencil numbering',
    ],
    status: 'candidate',
    settle:
      'A person checks the handwritten date and the pencil numbers 37–38 on the facsimile, and finds which leaves of the folder carry 36 and 39 — that locates the run of notes the letter was filed in.',
  },
  {
    id: '25-appendix-18-joint-paper',
    cote: '25',
    pages: '134–135',
    kind: 'codicological',
    claim:
      'The letter records Grothendieck refusing to publish under his sole name a text Dieudonné had drafted as an « ex-Appendice au par. 18 » of EGA IV, on the ground that he had only said « il n’y a qu’à faire pareil que pour les anneaux complets », and asking that it become a joint paper; the edition proposes, without evidence in the folder, that this text became Dieudonné–Grothendieck, « Critères différentiels de régularité pour les localisés des algèbres analytiques », J. Algebra 5 (1967), 305–324.',
    basis:
      'Pages 134–135 of the transcription carry the refusal and the request in typescript; « manuscriptes » and « papar » are typing slips, the latter marked \\uncertain{} and read as « paper ». Nothing on the two pages names the subject of the appendix beyond the comparison with complete rings.',
    ours:
      'The identification with the 1967 J. Algebra paper is entirely the reading’s, from subject (differential criteria of regularity, done for complete rings in EGA 0_IV, « faire pareil » for analytic algebras), date and double signature; the reading itself calls it a plausible conjecture. The page carries only the refusal and the request.',
    literature: [
      'Web search, 2026-10-10 (two queries on the paper’s title and on its relation to EGA IV): confirmed the citation J. Algebra 5 (1967) 305–324 from reference lists only; found no abstract, full text or statement of the paper’s origin. This is not a reading of the paper.',
    ],
    status: 'unsearched',
    settle:
      'Read the introduction of the J. Algebra 5 (1967) paper and EGA IV § 18 (IHÉS 32) for any mention of an appendix or of the paper’s origin; if either says the paper was the former appendix to § 18, mark matched (the identification is then in print) — if the paper treats something other than what EGA IV § 18 would have needed, mark refuted.',
  },
// 141: no entry. Pass: Opus 5.5 (claude-opus-5-5) on an Opus 5 reading (% Pass header of 141.modern.tex, 2026-09-13), under the 2026-09-23 exception; no disagreement with the reading. Every statement is a match or rests on the edition's repair. Kummer theory on a henselian DVR, tame π₁ and the Kummer sequence (pp. 1–5): textbook; the reading had to supply henselian, n invertible and the tame quotient. Thm 1/2 on Bπ = K(π,1) and the Borel construction (pp. 7–8): Milnor 1956, Eilenberg–MacLane; the 1)⇔2) equivalence is cut off and never proved. Cartographic groups Γ_{p,q}, PSL(2,ℤ) ≅ ℤ/2*ℤ/3 (p. 9): Grothendieck's own Esquisse (1984) and the modular group; p. 10's « carte trouée » stops at its first line. Schreier index formula, free cocompletion, Ens(π)-equivalences = bitorsors, π₀Bit(π',π) = Isomext(π',π) (pp. 11–15): Schreier; Morita theory for groups; Giraud 1971 and Breen, « Bitorseurs et cohomologie non abélienne » (1990), cited from memory, not read. Bit.invol(π) ≃ Invol(Ens(π)) ≃ Ext(ℤ/2,π) (p. 13): stated, not proved; it is the case G = ℤ/2 of the classification of extensions by 2-group maps G → AUT(π) (Breen 1990), from memory; a web search on 2026-10-10 found Aldrovandi–Noohi, « Butterflies II » (arXiv 0909.3350), on extensions via bitorsors, but not this case, and nothing was read. π₁(X,Γ,a) with (γ',ℓ')(γ,ℓ) = (γ'γ, ℓ'∘γ'(ℓ)) (p. 14): Rhodes's fundamental group of a transformation group (1966), an extension of Γ by π₁(X,a), found by a 2026-10-10 web search through secondary papers (arXiv 0712.3039; Korean Math. Soc. papers by Park, Han and Woo on koreascience.kr); Rhodes's own paper was not read.
// 143: no entry. Pass: Opus 5.5 (claude-opus-5-5) on an Opus 5.5 reading (% Pass header of 143.modern.tex, 2026-10-10); no disagreement with the reading. The folder establishes nothing that survives as a candidate: it is an inventory, a programme, formalism and conjectures. Σ_X as extension of the absolute automorphism group G-script by π₁, and the point-germ φ_ξ as a section of the fundamental exact sequence (pp. 1–4): SGA 1, equivariant π₁; injectivity of points → sections under a semi-abelian embedding (p. 4) is asserted on the page and proved by the edition (Kummer map, Mordell–Weil), and is the known injectivity half of the section conjecture (Stix, LNM 2054, from memory, not read). Inertia/cusp data Φ and the Kummer structure (pp. 4–7): textbook tame inertia. Reformulation α/β, extension-with-free-Σ-set ↔ connected groupoid with universal cover and G-action (pp. 16–18): the gauge groupoid and covering/orbit-groupoid theory; a 2026-10-10 web search found Brown–Higgins 1985 and Brown, Topology and Groupoids (1988), via arXiv math/0212271 and math/0412230 (Luo), none read, no exact statement of the equivalence found — classical by every indication, the page checks it object by object only. Pseudo-partition = unique path lifting, covering of the groupoid ⟨π⟩ (pp. 23–24): Gabriel–Zisman, Brown. T-groupoid = gerbe banded by T (p. 21): Giraud 1971; the page stops (« Arrêtons »). Conjecture π₁(M_{g,ν}) ≅ Out°_lac(π̂_{g,ν}) (pp. 28–30): Grothendieck's own later Esquisse (1984); Belyi 1979 for injectivity at (0,3); Γ = GT^ open (Drinfeld 1990, Ihara 1991). Question Γ → Out(T̂_{g,ν}) injective? (p. 30): the same 2026-10-10 search found Iijima (2015, Hiroshima Math. J., projecteuclid hmj/1439219709) on faithfulness of the outer Galois action on profinite mapping class groups, and Harbater–Schneps notes (genus 0, via Belyi), abstracts only; bijectivity fails at (0,4) by the edition's own example, the page already expecting an extra condition. Out(T_g) = 1? (p. 31): answered no by Ivanov/McCarthy. Pp. 26–27 (genus-0 modular stacks) and p. 32 (Birman sequence, profinite) are matches. No codicological entry: nothing was checked against the facsimile.
// Candidate entries for folder 150 (find-novelty, Opus 5.5 on an Opus 5.5 reading, 2026-10-10). Not merged into src/content/findings.ts. No literature was searched in this pass: every mathematical entry is unsearched.
  {
    id: '150-unfolding-as-ordered-space',
    cote: '150',
    pages: '47–63, 64–66, 70',
    kind: 'mathematical',
    claim:
      'The unfolded data of an equisingular stratification indexed by a finite poset I (unfolded strata Σ_i, connecting tubes Σ_ij with a fibration to Σ_i and a closed collared embedding into Σ_j) are equivalent to a single ordered topological space Σ, whose order graph is the union of the tubes, satisfying: target map proper and locally a collared immersion, each Σ_{<x} finite and totally ordered, the collared germs at each point mutually transverse, the source transverse to the target and a proper fibration, together with a strictly increasing map π₀(Σ) → I that need not be surjective.',
    basis:
      'Pages 55–60 restate the conditions on an ordered space Σ after the author abandons pages 47–54 (« Je reprends »), separating the order-theoretic part (Σ_{<x} totally ordered, chains of length d over x ↔ d-subsets) from the topological one; pages 57–59 recover the order from a source map s and a cartesian square Σ*(2) → Σ*(1); pages 60–62 give the scholie and the hexagon; pages 64–66 recapitulate the indexed data; page 70 states the equivalence as « Conséquence » and proves the disjointness condition b) from the total order on Σ_{<x}. Page 70 carries five \\ill{} and an illegible marginal note on finite dimensionality facing condition (a); the equivalence itself is legible. Pages 55–58 carry 13 \\uncertain{} and 27 \\ill{} in all, mostly in struck or marginal matter.',
    ours:
      'The reading supplies the hypotheses of the dimension argument on pages 67–69 that the equivalence of page 70 rests on (local triviality of the source fibration, Σ_i of pure dimension and manifold-like, so that a rare closed subset has strictly lower dimension); the page assumes only finite-dimensional components. It also corrects « b fibrant » to s on page 67, N(x) = card Σ_{≤x} to card Σ_{<x} on page 56, and b_ij⁻¹ to s_jk⁻¹ in condition c) of page 65. No proof of the equivalence is written out on the pages beyond the order-recovery step and condition b).',
    literature: [],
    status: 'unsearched',
    settle:
      'Check whether the unfolding (resolution) of a Thom–Mather or conically smooth stratified space into manifolds with corners is anywhere presented as one ordered space with proper collared target map and fibred source, with the index poset recovered as a quotient of π₀ rather than given. Sources to try: Albin–Leichtnam–Mazzeo–Piazza, The signature package on Witt spaces (Ann. Sci. ÉNS 2012), on resolution to manifolds with iterated fibration structure; Ayala–Francis–Tanaka, Local structures on stratified spaces (Adv. Math. 2017), the « unzip » construction; Verona, Stratified mappings — structure and triangulability (LNM 1102, 1984); Mather, Notes on topological stability (1970; Bull. AMS 2012). If the index-free ordered-space form is there, mark matched; the indexed form alone is almost certainly matched by ALMP and AFT and is not the claim.',
  },
  {
    id: '150-flag-fibration-smoothness',
    cote: '150',
    pages: '1, 45–47',
    kind: 'mathematical',
    claim:
      'In the unfolding of a non-singular equisingular stratification presented as a functor on the flags of I, the boundary of the fibres of Σ_{d′} → Σ_d (d = (i_1,…,i_p) an initial segment of d′ = (i_1,…,i_n)) is cylindrically stratified by the non-empty flags of the ordinal sum I_{]i_p,i_{p+1}[} ⊔ … ⊔ I_{]i_{n−1},i_n[}, so the fibration has boundaryless fibres exactly when each of i_p, i_{p+1}, …, i_n covers the preceding one in I, the condition not involving i_1, …, i_{p−1}.',
    basis:
      'Page 1 announces the statement as part b) of the programme; pages 45–46 derive it from the conditions (a)–(f) of paragraph 10, first for Σ_ij → Σ_i (boundary stratified by Drap(I_{]i,j[}), empty iff j is a successor of i), then for general initial segments; page 47 states the criterion with the author\'s emphasis « à partir de i_p, pas de i_1 ! ». The word qualifying « successeur » on page 47 is an \\uncertain{} addition (« le plus proche, au sens de I »), and the parenthesis after « lissité » is three \\ill{}; the criterion is fixed by page 46, which is legible. A struck first version on page 46 also required j maximal in I; it is not the page\'s final statement.',
    ours:
      'Nothing of the statement; the reading restores the page-1 orientation of the fibration (to Σ_i, not Σ_k), which the rest of the folder uses.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check whether the boundary-face combinatorics of the fibres of the iterated boundary fibrations of a resolved stratified space — faces indexed by flags of the open intervals of the stratum poset, smooth fibres iff consecutive strata are adjacent — is stated in Albin–Leichtnam–Mazzeo–Piazza (2012, §2 on iterated fibration structures), Ayala–Francis–Tanaka (2017) on links of unzipped strata, or Debord–Lescure–Rochon (2015) on manifolds with fibred corners. If stated there, mark matched; this is the more likely outcome, since the link of stratum i in stratum j is classically stratified by the strata between them.',
  },
  {
    id: '150-leaves-swapped',
    cote: '150',
    pages: '28–31, 91–93',
    kind: 'codicological',
    claim:
      'Two pairs of leaves are bound out of reading order: pages 29 and 30 are interchanged (the reading order is 28, 30, 29, 31), and so are pages 92 and 93 (the reading order is 91, 93, 92).',
    basis:
      'Page 30 bears the author\'s sheet number « 10 » and opens on the end of condition c) of paragraph 6, which page 28 leaves unfinished; page 29, unnumbered, opens paragraph 7 (« Stratifications et voisinages côniques »), and page 31, numbered « 11 », continues it. Page 92 bears « 43 » and opens on (94) after a struck line « X*_J = X_{J̄} », while page 93, unnumbered, carries (92) and (93), the definition of X*_J that page 92 uses, and continues the « si i, j ∈ J » on which page 91 stops.',
    ours: null,
    literature: ['Transcription 150, batch 2 (batch-02.fr.tex), notes to pages 28–31; batch 5 (batch-05.fr.tex), notes to pages 91–93'],
    status: 'candidate',
    settle:
      'A person checks the four leaves against the facsimile: the author\'s sheet numbers on pages 30, 31 and 92, and whether 29/30 and 92/93 are rectos and versos of single leaves (scanning order) or separate leaves (binding order).',
  },
// Folder 152: no entry — every statement the folder establishes is a match (rotation systems, Heffter 1891 / Edmonds 1960; the darts-involution-rotation description of combinatorial maps with faces as cycles of the product, Jacques 1968 / Cori 1975; plane trees as one-face genus-0 maps, i.e. a polygon with a non-crossing side-pairing, with the dual tree of a chord dissection), all already footnoted in 152.modern.tex as modern names; the only statement beyond these, the page 2 equivalence for « types de mots », leaves its terms (type de mot, S_0) undefined and rests on \uncertain/\ill readings, and the page 9 criterion's closing words are illegible, so neither can be written as a checkable claim. Pass on Opus 5.5 over an Opus 5 reading (2026-09-23 exception); no disagreement with the reading's dictionary rho_C = rho_Gamma sigma_Gamma, sigma_C = sigma_Gamma; no literature searched in this pass.
  {
    id: '153-relative-int-coproducts',
    cote: '153',
    pages: '3, 9',
    kind: 'mathematical',
    claim:
      'For an inclusion of commutative rings k₀ ⊂ K₀, not assumed to be a domain and its fraction field, the ring Int(k₀) = {F ∈ K₀[T] | F(k₀) ⊂ k₀} carries well-determined co-addition and co-multiplication in Int(k₀) ⊗_{k₀} Int(k₀), and so the composition rules of an analyseur (a plethory), once Int(k₀) is a free k₀-module and K₀[X,Y] = K₀[X] ⊗_{k₀} K₀[Y].',
    basis:
      'Page 3 strikes out « k₀ anneau intègre, K₀ son corps des fractions », replaces it by an inclusion of commutative rings (itself read with doubt), states a lemma identifying the K₀[T] ⊗ M-polynomials with values in a free M as Int ⊗ M, writes F(X+Y) and F(XY) as elements of Ω ⊗ Ω with a « ? » over each equals sign, and adds in the margin « OK si Ω est un k₀-module libre »; page 9 lists the relative Int as Example 2 of an analyseur.',
    ours:
      'The freeness hypothesis is the page’s own (margin); the hypothesis K₀ ⊗_{k₀} K₀ = K₀ (e.g. K₀ a localisation of k₀), without which K₀[X,Y] = K₀[X] ⊗ K₀[Y] fails, is the reading’s (Opus 5). The word « Lemme » and « d’anneaux commutatifs » are \\uncertain{} in the transcription. This pass (Opus 5.5, on an Opus 5 reading) adds a step the reading also leaves implicit: to apply the lemma with M = Ω one needs F(X+Y) to lie in K₀[X] ⊗ Ω, i.e. K₀ ⊗_{k₀} Ω = K₀[T]; this holds when K₀ is a localisation S⁻¹k₀ (each F ∈ K₀[T] has sF ∈ k₀[T] ⊂ Ω), and then the coordinates in a k₀-basis of Ω are in Ω by evaluation. That check is the pass’s, not the page’s. The page states only co-operations; plethory axioms beyond them are not verified there.',
    literature: [
      'J. Elliott, « Birings and plethories of integer-valued polynomials », arXiv:1109.3848v3 (2014; v1 2011 « Biring and plethory structure on integer-valued polynomial rings »), abstract and §1 (Proposition 3, Theorem 4, Corollary 5, Proposition 7, Theorem 8), read by text extraction: works throughout with an integral domain D and its quotient field K, under flatness of Int(D) or D-torsion-freeness of Int(D)^{⊗n}, n ≤ 4 — the non-domain pair k₀ ⊂ K₀ is not treated there',
    ],
    status: 'candidate',
    settle:
      'Search the literature on integer-valued polynomials over rings with zero divisors (Cahen–Chabert, Integer-Valued Polynomials, 1997, and its sequels; Frisch; Elliott’s later papers and the CIRM 2010 note, acirm.34) and Borger–Wieland 2005 for a biring/plethory structure on Int(k₀) relative to a non-domain extension; and decide whether the generalisation is more than routine, since for a domain the freeness hypothesis is stronger than Elliott’s flatness. If found, mark matched.',
  },
// Folder 142 — find-novelty pass, Opus 5.5 (claude-opus-5-5) on an Opus 5.5 reading, 2026-10-10.
// Dropped as matches already footnoted in the reading: the « relation des lacets » (Drinfeld 1990 / Ihara 1991, GT),
// tangential base points (Deligne 1989), injectivity of the Kummer map (Mordell–Weil, Lang–Néron), Brown's groupoid
// van Kampen, Belyi reduction, Prop. 2 (finite-order homeomorphism isotopic to id on a hyperbolic surface), the
// covering-groupoid lifting lemma (standard covering theory), PGL_2(Z) presentation. Pages 99 and 102–103 are too
// illegible to carry a claim.
  {
    id: '142-galois-image-conditions-single-curve',
    cote: '142',
    pages: '94–95, 98–101',
    kind: 'mathematical',
    claim:
      'The folder lists necessary conditions for a vertex-fixing automorphism Θ of the profinite fundamental groupoid Π̂₁(X, I) of one curve X over K to come from Gal(K̄/K) — lifting to Π̂₁(X′, I′) for every finite étale cover X′ of X defined over K, stability of kernels of π̂₁(X′, x′) → π̂₁(Y, f(x′)) for every K-morphism f : X′ → Y, compatibility along morphisms between covers, and the loop (inertia) condition with one multiplier — and conjectures them sufficient when X is an anabelian curve and K is of finite type over Q; a characterisation of the Galois image in this form, attached to a single curve and its covers, was not found in the sources read, which state it for the category of all varieties.',
    basis:
      'Page 94 states a) and b) as « conditions nécessaires »; page 95 conjectures them sufficient « lorsque X est (disons) une courbe algébrique anabélienne, avec K extension de type fini de Q » and expects uniqueness of u for K algebraic over Q; pages 98–101 restate them as 1)–4), calling 1) the loop condition « sûrement la plus importante de toutes, et de très loin ! ». In the transcription « exagère » (p. 95) is \\uncertain{} and several words of the conjecture sentence are \\ill{}, but « conjecturant », « nécessaires », « suffisantes », « provienne bien d’un u ∈ Γ », « courbe algébrique anabélienne » and « extension de type fini de Q » are read; the conjecture is stated for a) and b), and 1)–4) are a later restatement whose relation to it the page does not spell out. Condition 1) is written out only in the reading’s summary of pages 98–99, which are largely illegible.',
    ours:
      'The reading’s footnote says that a characterisation of the Galois image by conditions of this kind is, to its knowledge, open. This pass reads it differently: Ihara’s question / Oda–Matsumoto conjecture (I/OM), which characterises Gal_{k₀} as the automorphisms of the geometric fundamental group functor on k₀-varieties compatible with all morphisms, is stated as proved by Pop for 𝒱 = all varieties; the folder’s statement differs in being attached to one curve X, its finite étale covers and morphisms out of them, with explicit base points and the inertia condition, so whether it is implied by or equivalent to a published variant is the open point, not the characterisation in general. The grouping of a), b) and 1)–4) into one statement is the reading’s.',
    literature: [
      'A. Topaz, « The Galois action on geometric lattices and the mod-ℓ I/OM » (arXiv 1510.08836), §1–§1.2, read 2026-10-10 through a fetched HTML rendering (first part only): statement of I/OM as ρ_{k₀,𝒱} : Gal_{k₀} → Out(π̄₁|_𝒱) for subcategories 𝒱 of varieties, and attribution of the absolute I/OM for 𝒱 = Var_{k₀} to Pop (unpublished 1999 manuscript, later released); no inertia condition and no single-curve version stated there.',
      'F. Pop, « Finite tripod variants of I/OM: On Ihara’s question/Oda–Matsumoto conjecture », Invent. Math. (2019), 745–797, DOI 10.1007/s00222-019-00855-8 — abstract only, via a newsletter page, 2026-10-10; the theorem was not read.',
    ],
    status: 'candidate',
    settle:
      'Read Pop 2019 (tripod variants), whose subcategories are built from finite étale covers of P¹ ∖ {0, 1, ∞}: if it proves that automorphisms of the geometric fundamental groups of the covers of one hyperbolic curve (or of U_{0,3}), compatible with the morphisms among them, come from Galois, mark matched with the section number. Also check H. Nakamura’s and Y. Ihara’s surveys of the GT/I/OM programme and Mochizuki’s Hom-form of the anabelian conjecture for a single-curve formulation with inertia. Nothing here is a priority claim; the folder is dated only « [à partir de 1978] » and, by its mention of Belyi, after 1979.',
  },
  {
    id: '142-teichmuller-galois-category-etale',
    cote: '142',
    pages: '2–16',
    kind: 'mathematical',
    claim:
      'The folder builds a single category whose objects are anabelian curves of all types (g, ν) and whose arrows are the profinite completions of isotopy classes of finite étale maps, by a general profinite completion of categories whose automorphism groups satisfy the finiteness condition (*) (the image H_u of the stabiliser of every arrow u has finite index in Aut(Y)); in it every automorphism group is the profinite Teichmüller group, the construction is algebraic and invariant under extension of algebraically closed fields of characteristic 0, and Aut(k) acts on it — a Galois–Teichmüller object linking different types by étale maps rather than by the subsurface and fusion maps of the Teichmüller tower; no published construction of this category was found, but no source was read.',
    basis:
      'Pages 2–7 prove that isotopy classes of finite étale maps between anabelian surfaces are A°_X-torsors with finitely many T_X-orbits and finite stabilisers; pages 8–13 state condition (*) (16), the completion (17) and the factorisation (19)–(22); pages 12, 14–16 make it algebraic, functorial in k, and call it the « catégorie de Teichmüller–Galois ». Page 11 (\\uncertain{} « sans », « pb ») and pages 12 and 14 (\\uncertain{} « anabéliennes », « modulaire », several \\ill{}) carry the passage; the end of page 15 is barely legible.',
    ours:
      'The identification of (17) with Hom ×^{Aut X} Âut(X), on which the composition rests, is asserted by the page and not proved; the reading notes that it needs a compatibility of profinite topologies along u that (*) alone does not give, and declines to take it over. The interpretation of a class of homeomorphisms as a path in the profinite fundamental groupoid of the moduli stack, and the characteristic-0 restriction (the page says « pas besoin qu’il soit de car. 0 ! »), are the reading’s. The contrast with the Teichmüller tower is this pass’s framing.',
    literature: [
      'Web search, 2026-10-10, for a profinite completion of a category of surfaces with finite étale maps and its Galois action: returned G. Horel, « Profinite completion of operads and the Grothendieck–Teichmüller group » (arXiv 1504.01605), M. Robertson and collaborators on GT symmetries of cyclic operads (arXiv 2511.05911), and lecture notes on modular ∞-operads and GT theory (arXiv 2210.13640); abstracts only, none read, none on étale maps between surfaces of different types.',
    ],
    status: 'unsearched',
    settle:
      'Read the Teichmüller-tower literature where categories rather than groupoids appear: P. Lochak and L. Schneps (eds.), Geometric Galois Actions 1 (LMS LN 242, 1997), in particular Hatcher–Lochak–Schneps and Lochak–Nakamura–Schneps; Nakamura–Schneps on the profinite Teichmüller modular groups; and any construction of a « profinite completion of a category with profinite Aut groups » (e.g. in the profinite-groupoid literature). If a category of hyperbolic curves with finite étale maps, completed profinitely and carrying a Galois action, appears, mark matched; independently, a proof or counterexample for the identification (17) under (*) decides whether the general completion holds as stated.',
  },
  {
    id: '142-run-I-leaf-order',
    cote: '142',
    pages: '2–6, 10–14',
    kind: 'codicological',
    claim:
      'In the first run (« Catégories de Galois–Teichmüller », his pp. 1–10) the text does not follow the scan order: it runs 3 → 5 → 4 → 6 and, further on, 11 → 13 and 12 → 14, the pages he numbered (2, 4, 8, 10, 12, 14, 16, 18, 20 bear his 1, 2, 4, 5, 6, 7, 8, 9, 10) alternating with unnumbered ones that carry continuations.',
    basis:
      'Transcription batch-01: page 3 breaks off on « peut-on la » and page 5 opens « factoriser canoniquement », with notes saying the sentence continues on page 5, not 4, and that page 4 (his p. 2) follows page 5; page 11 ends « Par construction, tout Ĉ₀-morphisme » and page 13 opens « (18) f̂ : X → Y »; page 12 (his p. 6) ends « Pour la » and page 14 (his p. 7) opens « voir ». The reading follows this order and says so.',
    ours: 'The observation is the transcription’s; the reading adopts it. The pattern of numbered and unnumbered pages is this pass’s collation of the transcription’s « p. n de sa main » notes.',
    literature: ['Transcription 142, batch 1 (batch-01.fr.tex), header and notes on pages 2–14'],
    status: 'candidate',
    settle:
      'Look at the facsimile of pages 2–14: whether 4/5 and 12/13 are the two sides of single leaves scanned verso-first, or whether he wrote continuations on the versos of the preceding leaves; the second would make the order a habit of writing rather than a misbinding. Why his p. 3 (page 6) carries no number in the transcription is not checked.',
  },
  {
    id: '142-run-II-missing-opening',
    cote: '142',
    pages: '21–23',
    kind: 'codicological',
    claim:
      'The run « Opérations de Γ_{Q̄/Q} sur π₁ M_{0,3} » begins at his page 5 behind its own cover, and his pages 1–4 are not in the folder; the formula numbering nevertheless starts at (1) on his page 5.',
    basis:
      'Page 21 is a cover in his hand with the title; page 22 carries only a pencilled count; page 23 is numbered 5 in his hand and opens with formula (1) (transcription batch-02, header and note on the title). The reading reports the computations of the run as dependent on conventions fixed in the missing pages.',
    ours:
      'That pages 1–4 fixed the conventions is the reading’s inference from the run’s undefined notation; the restart of the numbering at (1) leaves open that pages 1–4 were a separate preamble without numbered formulas. No other folder was searched for them in this pass (a grep of the transcriptions of folders 143, 144, 146 and 148 for M_{0,3} turned up no matching run, which is not a search of the fonds).',
    literature: [],
    status: 'unsearched',
    settle:
      'Search the transcriptions and inventory entries of the neighbouring folders (141, 143–148), especially folder 145’s drafts on the same relations, for four pages numbered 1–4 on the thrice-punctured sphere with base points R_i^ω, and check the facsimile of pages 21–23 for traces of removed leaves.',
  },
  // Folder 144, find-novelty pass on Opus 5.5 (claude-opus-5-5) over the Opus 5.5 reading of 2026-10-10.
  // The rest of the pool was matches already footnoted in the reading (Belyi, real Belyi theory, Hecke-type
  // groups, Deligne–Mumford strata, B3) or statements announced but never established on the pages
  // (pp. 13, 17, 24, 26–27, 153). Those were dropped without entries.
  {
    id: '144-triangulation-weighting-obstruction',
    cote: '144',
    pages: '73–76',
    kind: 'mathematical',
    claim:
      'For an oriented triangulated closed surface whose vertices all have even degree and whose faces are 2-coloured (adjacent faces differently), a class cl(X) ∈ H¹(X, ℤ/3) vanishes exactly when the triangulation admits a weighting, i.e. a proper vertex 3-colouring by {0, 1, ∞}; the weightings with the + faces direct correspond to the sections of the associated ℤ/3-torsor.',
    basis:
      'Page 76 states the obstruction and the correspondence with sections cleanly. The construction behind it, on pages 74–75, builds the principal 𝔖₃-cover X′ → X from the colours of the flags, notes that it ramifies only at vertices of odd order, and reduces the group to 𝔖₃⁺ ≅ ℤ/3 by the face colouring. Those two pages carry many \\ill{} and \\uncertain{} readings, among them the word « ramifiée » in the odd-order claim. No proof is given.',
    ours:
      'The reading states the result as the page gives it and supplies no proof. The match with Fisk and Izmestiev is this pass’s. The reading has no footnote on it.',
    literature: [
      'S. Fisk, Geometric coloring theory, Advances in Math. 24 (1977) 298–340, the « even obstruction map »',
      'M. Joswig, Projectivities in simplicial complexes and colorings of simple polytopes, Math. Z. 240 (2002), the group of projectivities, with vertex-colourability equivalent to its triviality',
      'I. Izmestiev, Color or cover, arXiv:1503.00605 (2015), Definition 2.1 (coloring monodromy π₁ → Sym₃; colourable iff trivial) and the statement after Theorem 5 that an even triangulation of an orientable surface is face-colourable iff the monodromy image is trivial or generated by a 3-cycle',
    ],
    status: 'matched',
    settle:
      'Matched. The monodromy into Sym₃, which drops to the 3-cycle group ℤ/3 once faces are 2-coloured, is the page’s 𝔖₃-cover and its 𝔖₃⁺-reduction. Its triviality is the vanishing of cl(X). The only open check is codicological: whether pages 74–75 really say that X′ is ramified only at odd-order vertices. That turns on the transcription, not the literature.',
  },
// 145: two entries. Pass: Opus 5.5 (claude-opus-5-5) on an Opus 5.5 reading (% Pass header of 145.modern.tex, 2026-09-24); no disagreement with the reading. Dropped as matches already footnoted in the reading: the S_3-commutation equations of pp. 6–11 and β = γ (forms of relations (I)–(II) of Drinfeld's GT^, 1990), E⁺ ≃ PSL₂(ℤ) and E ≃ PGL₂(ℤ) (pp. 19, 30), the cartographic group ℤ/2*ℤ/2*ℤ/2 (p. 22), the commensurator of p. 1, the non-lifting of the 2-Sylows to SE (p. 36: cusp stabilisers of PSL₂(ℤ) are torsion-free). Dropped as not established by the folder: whether Out_lac^!(π^) equals the centraliser of S_3 (p. 23, « j'ignore »).
{
  id: '145-unit-exponent-exercise',
  cote: '145',
  pages: '34–35',
  kind: 'mathematical',
  claim:
    'In the free profinite group on l₀, l₁ with l_∞ l₁ l₀ = 1, a unit p ∈ Ẑ* satisfies l_∞^p l₁^p l₀^p = 1 only for p = 1; hence the « rectifier-free » systems (p, σ, 1, 1, 1) of SÊ^ are exactly the six (sg σ, σ) of Γ_P, as in the discrete SE.',
  basis:
    'Page 35 proves the discrete case (p = ±1: (13) holds iff (σ, p) ∈ Γ_P), conjectures the profinite one (« Sans doute il est vrai que le même résultat est valable dans SÊ^ »), reduces it to (14) l_∞^p l₁^p l₀^p = 1 ⇒ p = 1, and leaves it as « Exercice ! ». The sentence carrying the reduction is read with difficulty (\\uncertain{même}, \\uncertain{pense}, \\uncertain{quitte}, batch-02.fr.tex, page 35); the statement of (14) itself is read clearly.',
  ours:
    'The proof is entirely the edition’s: send l₀, l₁ to two reflections of a dihedral group of order 2N whose product has order N, with N ≥ 3 and p ≢ 1 mod N; p odd gives l₁^p l₀^p ↦ r and (l₁l₀)^p ↦ r^p ≠ r. The reading also corrects the order of the product in the page’s (13), which as written (l_σ(0)^p l_σ(1)^p l_σ(∞)^p = 1) is false for σ = 1, p = 1 under the relation l_∞ l₁ l₀ = 1. The page carries only the question and the reduction.',
  literature: [
    'Web search, 2026-10-10, « free profinite group x^λ y^λ z^λ = 1 xyz=1 implies λ = 1 Grothendieck-Teichmüller »: returned Schneps, notes on GT (math.arizona.edu, 05SchnepsNotes.pdf), arXiv 1407.3112, 1504.01605, 1604.04415, read only as search summaries; none stated the implication. Not a search of the literature in the sense of the skill.',
  ],
  status: 'unsearched',
  settle:
    'Read Drinfeld 1990 (§4), Ihara’s 1991 ICM address and Lochak–Schneps’ expositions of GT^ for the statement that (λ, 1) satisfies relation (II) only for λ = 1, i.e. that z^m y^m x^m = 1 with xyz = 1 forces m = 0 in F̂₂ — the same fact with a different exponent. If it is stated there, or as a standard exercise on F̂₂, mark matched; the elementary dihedral argument makes that the likely outcome.',
},
{
  id: '145-page-20-after-21',
  cote: '145',
  pages: '19–22',
  kind: 'codicological',
  claim:
    'Page 20 is out of the order of the argument: it carries formulas (13)–(16), which continue (11)–(12) of page 21, so the reading order is 19, 21, 20, 22.',
  basis:
    'The author’s numbering puts « 8 » on page 19 and « 9 » on page 21; page 20 has no number. Page 21 introduces the section φ (11) and its canonical lift σ ↦ σ̃ (12); page 20 opens « Donc aussi les relations (13) » on the σ̃_i, then (14) and τ_i = σ_i σ̃_i (15)–(16), and page 22 (his « 10 ») goes on to E_τ with (17).',
  ours:
    'The observation is the reading’s (header and the subsection « pages 21 et 20 »); the transcription records the author’s page numbers in its batch headers. The facsimile was not consulted by this pass.',
  literature: [
    'Transcription 145, batch 1 (batch-01.fr.tex), header and page 20',
    'Transcription 145, batch 2 (batch-02.fr.tex), header and page 21',
    'Modernised reading 145.modern.tex, header and subsection on pages 21 and 20',
  ],
  status: 'candidate',
  settle:
    'A person checks on the facsimile whether page 20 is the verso of the leaf whose recto is page 21 (his p. 9), scanned before it, or a separate leaf filed one place early.',
},
  // Folder 146, find-novelty pass on Opus 5.5 (claude-opus-5-5) over the Opus 5.5 reading of 2026-10-10 (% Pass header of 146.modern.tex); same model, no exception needed.
  // Dropped as matches already footnoted in the reading: tangential base points (p. 62; Deligne 1989), plumbing / opening of nodes (pp. 105–111),
  // the Lego–Teichmüller programme (p. 111; Hatcher–Lochak–Schneps 2000), the presentation of a group extension (p. 80; classical),
  // π-fibrations as gerbes (pp. 88–94), the cartographic groups C₂, C₂⁰ (p. 66), Belyi maps of the monogon and bigon (p. 64), \bar M_{0,5}
  // as the universal curve over \bar M_{0,4} (p. 67), ψ_i of degree 1 on \bar M_{0,4} (pp. 16–17), icosahedral and dodecahedral counts (pp. 61, 65, 76),
  // stable-graph contraction (pp. 127–130). Dropped as the edition's: the 2-skeleton argument that relation (2) of p. 116 follows from (1);
  // the pointed form of the correspondence (17) of p. 94 (the page's unpointed statement needed repair). Dropped as announced, never established:
  // the groupoid-over-groupoid presentation of pp. 82–86 (stated without proof), the filtered colimit of p. 99, the relations of p. 123.
  {
    id: '146-variant-pi1-trinion',
    cote: '146',
    pages: '8–10',
    kind: 'mathematical',
    claim:
      'For card I = 3, the « variant » fundamental group π₁(S₀𝒯_{0,I}, 𝔖_I; x) is an extension G(I) of 𝔖_I by ℤ^I, obtained from 0 → ℤ →(2) ℤ → μ₂ → 0 by pulling back along the signature and pushing out along the diagonal ℤ → ℤ^I; it does not depend on x, is not split (already over the subgroup generated by one transposition), and splits canonically over 𝔖_I⁺.',
    basis:
      'Page 8 writes (17) and (18) and identifies the group with pairs (α, n), the n_i of the parity fixed by sgn(α); page 9 states the Proposition, the non-splitting by projection onto one coordinate, and the canonical splitting (19) over 𝔖_I⁺; page 10 notes that the group does not depend on x. The statement itself is legible; only « variants » (p. 8) is uncertain, and several connecting words on p. 8 are \\ill{}.',
    ours:
      'The reading supplies the explicit surjection from the semidirect product with its kernel, and the squaring argument for non-splitting; the page projects onto one coordinate instead. The identification of G(I) with the mapping class group of the three-holed sphere, boundary components permutable, is this pass’s and was checked only at the level of the relations: rotation of order 3 against the canonical splitting over 𝔖_I⁺, braiding squared equal to a product of boundary twists against (σ, n)² = (1, n + σn).',
    literature: [
      'B. Bakalov, A. Kirillov Jr., « On the Lego–Teichmüller game », Transform. Groups 5 (2000), arXiv math/9809057: Proposition 6.6 (presentation of Γ_{0,n} = Γ(S_{0,n}), boundary components permutable, by braidings b_i, twists t_i and the rotation z with z^n = 1), Example 4.18 (T_α = T_β T_γ B_{γ,β} B_{β,γ} on a sphere with three holes), relation (4.11)',
    ],
    status: 'matched',
    settle:
      'Matched in substance. For n = 3, Bakalov–Kirillov’s Γ_{0,3} is an extension of 𝔖₃ by the boundary twists ℤ³, the rotation z of order 3 splits it over the 3-cycles, and Example 4.18 makes the square of a braiding a product of twists with the fixed hole’s twist to the power ±1, so no lift of a transposition has order 2: the page’s G(I), in other words. What is not in that paper is the page’s route, the half-turn parity description of the arrows between the two real base points ω(I). The one remaining check is to write the isomorphism G(I) ≅ Γ_{0,3} explicitly, with the sign of the braiding fixed, rather than comparing relations. A web search on 2026-10-10 found nothing else on this extension. Folder 145, p. 31, leaves the same extension SΓ to be made explicit, according to the reading’s footnote.',
  },
  {
    id: '146-equivariant-trivialising-exponents',
    cote: '146',
    pages: '70, 72–73',
    kind: 'mathematical',
    claim:
      'The folder tabulates, for n = card I = 4, 5, 6, the smallest exponent that makes the tangent line bundles L_i, and L = ⊗ L_i, trivial compatibly with the symmetric group on M_{0,I}: 3 for L and 6 for L_i when n = 4, and only queried values (« 12 ? », « 20 ? », « 60 ? ») for n = 5, 6.',
    basis:
      'Page 70 is a table with these entries, the n = 5, 6 columns followed by question marks and the last two rows left empty; page 72 builds sections ξ_A indexed by the 3-element subsets A, takes their product as a section of L^{⊗ν}, ν = (n−1)(n−2)/2, and writes « L^{⊗6} ≃ 1 » for both n = 4 and n = 5, with « on trouve » uncertain, which disagrees with the « 12 ? » of the table for n = 5; page 73 sets up the exact sequence through H¹(𝔖_K, H⁰(M_{0,K}, 𝔾_m)). No value is proved on the pages, and several exponents are overwritten or \\ill{}.',
    ours:
      'The reading supplies the reason the sequence of p. 73 is exact on the left (the units modulo constants carry no 𝔖_K-invariants) and says it does not verify the table. The question, as a claim about the literature, is this pass’s framing.',
    literature: [],
    status: 'unsearched',
    settle:
      'Compute the class of L and of L_i in H¹(M_{0,I}, 𝔖_I; 𝔾_m), respectively H¹(M_{0,I}, 𝔖_{I∖{i}}; 𝔾_m), for n = 4 by hand (M_{0,4} = ℙ¹ ∖ {0, 1, ∞}, units λ^a(1−λ)^b up to constants) and see whether the page’s 3 and 6 come out; then look for these 𝔖_n-equivariant orders in the literature on equivariant Picard groups and linearisations on M_{0,n} and \bar M_{0,n} (Hassett–Tschinkel–Zhang on 𝔖_n-actions, the S_n-invariant F-conjecture literature). Two web searches on 2026-10-10 found no paper on these orders; nothing was read, so the status stays unsearched. The entry rests on overwritten and uncertain figures and drops if the n = 4 values do not check.',
  },
  {
    id: '146-pages-62-64-outside-numbering',
    cote: '146',
    pages: '62, 64, 74',
    kind: 'codicological',
    claim:
      'Pages 62 and 64 (and probably 74) continue two different runs of formula numbers that begin outside the folder: page 62 numbers (53)–(55) with no (1)–(52) anywhere in 146, and page 64 opens mid-argument, refers back to a formula (25) that the folder does not hold, and numbers the monogon and bigon maps (26) and (27).',
    basis:
      'The transcription of batch 04 notes on p. 62 that (53)–(55) extend a numbering begun before the batch, and on p. 64 that the opening words (« les étaient 0, ∞ au lieu de 0, 1 ») and the reference to (25) assume an earlier argument; among the neighbouring leaves (55–77), the only other numbered formulas are the boxed (41) and (42) of p. 74, which also opens mid-statement (« dont la deuxième… ») and could belong to the same outside run as p. 62.',
    ours:
      'The comparison with folder 144 is this pass’s: 144 writes the same monogon map g(z) = −(z−1)²/4z as its formula (23) (batch 04) and reuses it on its p. 86 « (cf. (23)) », while its (25) is « U′^τ = ∅ » and its (53)–(55) concern the dihedral group and λ_a. Neither run of 146 therefore matches 144’s numbering as transcribed.',
    literature: [],
    status: 'unsearched',
    settle:
      'A person checks on the facsimile that pages 62 and 64 are single leaves with nothing numbered on their versos. Then the other Teichmüller folders (143–145, 147–148) are searched for a manuscript whose formulas run to (52) before « points base à l’infini », or to (25) just before the monogon. That decides whether these are stray leaves of another redaction or drafts of 144’s pp. 7 ff.',
  },
// 147: two entries. Pass: Opus 5.5 (claude-opus-5-5) on an Opus 5.5 reading (% Pass header of 147.modern.tex, 2026-10-10); no disagreement with the reading. Dropped as matches already named in the reading: the Deligne–Mumford–Knudsen compactification and its stratification by stable graphs (pp. 21–30), codimension = number of edges (p. 27), the orbifold Euler characteristics χ(M_{0,4}) = −1, χ(M_{1,1}) = −1/12 (pp. 61–63), the Petersen graph as dual graph of the boundary of M̄_{0,5} (p. 67, the ten lines of the quintic del Pezzo surface), the « two-level » impression of p. 59 (Hatcher–Lochak–Schneps 2000), the Lego–Teichmüller Programme of p. 103 (Esquisse, 1984), Dehn twists as the ℤ^C of (101)–(103). Dropped as repairs or as not established: (37) as a closed immersion (false, the reading repairs it), the claim that every subgroup of S_4 is an image Γ_G → S_4 (p. 57, « sauf erreur », unverified by page and pass), the connectedness of the boundary for dim ≥ 2 (pp. 71–74: page 74 read with much uncertainty, and the statement is very probably standard via the connectedness of the curve complex; not searched), the structure of M̄_{1,2} at infinity (p. 71, « J'y renonce »), the Scholie of p. 176 (posed « heuristiquement »).
{
  id: '147-m11-stratified-class-over-z',
  cote: '147',
  pages: '62–64',
  kind: 'mathematical',
  claim:
    'In the additive invariant that counts each locally closed piece of a Deligne–Mumford stack with constant automorphism group H as the class of its coarse space divided by card H, the stack of elliptic curves over Spec ℤ has class ½(L − 1) − 1/12 + ⅛ζ₂ + ⅙ζ₃, with ζ_p = [Spec 𝔽_p], and its compactification ½L − 1/12 + ⅛ζ₂ + ⅙ζ₃; over ℤ[1/6] these reduce to ½(L − 1) − 1/12 and ½(L − 1) + 5/12.',
  basis:
    'Pages 63–64 cut the j-line 𝔸¹_ℤ by the sections S₀ (automorphisms ℤ/4) and S₁ (ℤ/6), meeting only at a₂ and a₃ in characteristics 2 and 3 (automorphisms of order 24 and 12), write [M_{1,1}] = ½[U] + ¼[S′₀] + ⅙[S′₁] + (1/24)ζ₂ + (1/12)ζ₃ and arrive at (80); page 63 gives (79) over ℤ[1/2] by the Legendre gerbe over [U_{0,3}/S₃]. The computation of pages 63–64 is read clearly (the words « harmonique », « équianharmonique » are \\uncertain{} in batch-04.fr.tex, page 63, and an \\ill{} sits beside « groupes d’automorphismes d’ordre 24, et 12 »); the margin of page 62 that limits the formulas to ℤ[1/6] is largely \\ill{}.',
  ours:
    'The page says only « dans un groupe de Grothendieck convenable » and never defines the invariant; the rule stated in the claim (coarse class over constant-stabiliser strata, divided by card H) is the reading’s reconstruction, chosen because it makes all the page’s computations come out right (footnote to the « Classes » paragraph, p. 62). The reading also notes that this is neither the weighted point count (q for M_{1,1}) nor the class in Ekedahl’s Grothendieck group of stacks, corrects « ½[M_{0,4}] » to 2[M_{0,[4]}], and moves the validity of (79) from ℤ[1/2] to ℤ[1/6]. This pass re-did the arithmetic of (80) (constant −7/12, coefficient of ζ₂ ½ − 5/12 + 1/24 = ⅛, of ζ₃ ½ − 5/12 + 1/12 = ⅙) and found it right.',
  literature: [
    'Web search, 2026-10-10, « Ekedahl Grothendieck group of algebraic stacks class of M_{1,1} »: returned Ekedahl, « The Grothendieck group of algebraic stacks » (arXiv 0903.3143) and « A geometric invariant of a finite group » (arXiv 0903.3148), Bergh, « Motivic classes of some classifying stacks » (arXiv 1409.5404), read only as search summaries; none stated a class of M_{1,1} over Spec ℤ with ζ₂, ζ₃ terms. Not a search of the literature in the sense of the skill.',
  ],
  status: 'unsearched',
  settle:
    'Decide first whether the invariant is in print: look in the literature on orbifold / stringy Euler characteristics and « motivic » or inertia-weighted classes of Deligne–Mumford stacks (e.g. Ekedahl 2009, Bergh, and treatments of [M_{1,1}] over ℤ in K₀ of stacks) for a class defined by coarse spaces of constant-stabiliser strata divided by card H, and for its value on M_{1,1} over Spec ℤ. If the invariant appears with this value, mark matched; if the invariant itself is not in print, the entry is about the edition’s reconstruction as much as the page and should say so in its claim.',
},
{
  id: '147-deleted-neighbourhood-codim-two',
  cote: '147',
  pages: '148–151',
  kind: 'mathematical',
  claim:
    'For a smooth complex analytic space (or « multiplicité ») X with a normal-crossings divisor Θ, the folder states, without proof, that the deleted tubular neighbourhood V*_{Θ,X} is the homotopy colimit of the semi-simplicial system of deleted tubular neighbourhoods of the unfolded strata D_{d₀…d_r}, and deduces that its fundamental groupoid is the amalgamated sum Π̃₁ ← Π̃_{2,1} → Π̃₂ of the groupoids of the multinormal torus bundles over the open strata of codimension 1 and 2 (Corollary 2), hence the same for Π₁(X ∖ Θ) whenever X ∖ Θ and its end have equivalent fundamental groupoids (Corollary 3).',
  basis:
    'Page 149 states the « Th. de recollement » as an equivalence of topos and corrects it at once (« en fait, c’est une équivalence d’homotopie »); page 150 extends it to a stratum (Corollary 1); page 151 states Corollary 2 as (2.46) and Corollary 3 as (2.47), with a bracketed justification that Θ^{(3)} can be neglected by a purity argument. That justification rests on several \\uncertain{} words (« dans un voisinage », « voisins », « changement ») and an \\ill{} (batch-08.fr.tex, page 151); the « bijection » on π₀ and « rev. » on page 149 are \\uncertain{}; a left-margin note on page 151 about Π̃_i for i ≥ 3 is largely \\ill{}. Corollary 4 and a « Cor. Main 2 » are struck out. No proof is given anywhere in the folder.',
  ours:
    'The reading reads the theorem as a statement about the homotopy colimit (the page says « limite inductive » of topos), supplies the purity argument in the form « removing real codimension ≥ 3 does not change π₁ », renumbers (2.46)–(2.47) as (246)–(247), and corrects Corollary 3’s Π₁X to Π₁X* (the hypothesis is about X*; the page writes Π₁ X). The application to moduli — X* = M_{g,ν}, so that the mapping class group would be expressed through the strata of codimension 1 and 2, a form of the two-level principle — is the reading’s rapprochement; the page only remarks, on p. 178, that the open strata are K(π, 1) « dans la situation de Teichmüller ».',
  literature: [
    'Web search, 2026-10-10, « homotopy type deleted neighbourhood normal crossings divisor homotopy colimit strata tubular neighbourhoods fundamental group van Kampen codimension two »: returned Libgober, « Complements to ample divisors and singularities » (arXiv 2108.02812), Dimca’s survey on fundamental groups of divisor complements on surfaces, Ding–Saito on local fundamental groups near normal crossings, Zakharov on rational models of complements of submanifold arrangements (arXiv 2211.05033), read only as search summaries; none stated the gluing theorem or Corollary 2 in this form. Not a search of the literature in the sense of the skill.',
    'Modernised reading 147.modern.tex, footnote on the two-level principle (Hatcher–Lochak–Schneps, J. reine angew. Math. 521, 2000) — cited by the reading for p. 59, not checked by this pass against Corollaries 2–3.',
  ],
  status: 'unsearched',
  settle:
    'Look for the statement that the boundary of the real oriented blow-up (equivalently the Kato–Nakayama space of the log structure, or the deleted neighbourhood) of a normal-crossings divisor is the homotopy colimit of torus bundles over the open strata, and for the resulting van Kampen presentation by codimension 1 and 2 — in the literature on real oriented blow-ups and Kato–Nakayama spaces, in Looijenga’s and Boggi’s work on the boundary of M̄_{g,n} and its fundamental groups, and in Hatcher–Lochak–Schneps 2000; and check whether, for M_{g,n}, the hypothesis of Corollary 3 (end and interior with the same Π₁) is the simple connectivity of the curve complex (Harer). If the general statement is in print, mark matched.',
},
  // Folder 148 (Teichmüller, 1983), find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, on a reading made by Opus 5.5.
  // Dropped as matches already footnoted in the reading: stable graphs (p. 47), Hatcher–Thurston pants complex (pp. 30–32),
  // modular operads (pp. 51–59), Dehn–Thurston arc coordinates in a pair of pants (p. 65), Belyi / trivalent maps (p. 25),
  // the classification of 5-point configurations with symmetry (pp. 33–35), and the p. 19 diagram, which is the edition's repair.
  {
    id: '148-multimarked-teichmuller-groupoid',
    cote: '148',
    pages: '40, 49–60',
    kind: 'mathematical',
    claim:
      'The folder defines a Teichmüller groupoid of cut surfaces in which each cutting or boundary circle carries any number r(a) ≥ 0 of marked points, forming a torsor under the twisted group ℤ_a/r(a), and takes as elementary operations, beside cutting and gluing, the uniform partial erasure (restriction to the subgroup of order r′ dividing r) and the uniform over-marking (extension along ℤ/r → ℤ/dr) of those points; gluing two circles is defined up to unique isomorphism once they carry the same number of points and an anti-isomorphism of their torsors is given.',
    basis:
      'Page 40 (dated Oct. 1983) gives the data (RR, A⃗, S, g) with a D_∞-action on the « repères » and RR/D_∞ ≃ A; pages 49–50 make R_a a torsor under ℤ_a/r(a), ℤ_a = ℤ twisted by the orientations ω(a); pages 55–58 define surmarquage, the uniform operations and recollement via an element of R_a ∧_{ℤ/r} R_{a′}; page 60 recapitulates operations 0°–7° with their reversibility.',
    ours:
      'The reading supplies the realisation of the D_∞-set of repères as the flags of the polygons P_a, with ε(σ₀) = ε(σ₁) = −1; the justification that gluing is unique (orientation-reversing homeomorphisms realising a given anti-isomorphism form a contractible space); and the correction of « restriction de ℤ_a/r à ℤ_a/r′ » to restriction to the subgroup of order r′. The transcription has \\ill{} words inside the definition of uniform over-marking (batch 3, « surmarquage uniforme, \\ill{} de multiplic. par d(a) ») and in the sentence reducing gluing to r(a) = r(a′) (« uniformes \\ill{} \\ill{} »); the operations themselves are legible.',
    literature: [],
    status: 'unsearched',
    settle:
      'Read Bakalov–Kirillov, « On the Lego-Teichmüller game » (Transform. Groups 5, 2000; arXiv math/9809057), Hatcher–Lochak–Schneps, « On the Teichmüller tower of mapping class groups » (Crelle 521, 2000), and Funar–Kapoudjian on the universal mapping class groups, for whether a groupoid with r(a) marked points per circle and the uniform erasure / over-marking operations appears there; the versions this pass knows use one marked point per boundary circle. Also compare with surfaces with marked points on the boundary in Fomin–Shapiro–Thurston (Acta Math. 201, 2008), which carry several boundary points but not these operations. A web search of 2026-10-10 returned only the Bakalov–Kirillov abstract and was not a reading of any source, so it is not listed as searched.',
  },
  {
    id: '148-m05-special-structures-chart',
    cote: '148',
    pages: '30–32, 35',
    kind: 'mathematical',
    claim:
      'The folder proposes, as base points and generators for a presentation of the Teichmüller groupoid of five points on the sphere built from pieces of modular dimension ≤ 1, a chart of 542 « special » structures in nine 𝔖₅-orbits on three levels (12 pentagonal, 20 bitetrahedral, 30 pyramidal; 60 + 60 + 120; 60 + 120 + 60) joined by 1620 arrows in fourteen orbits (gommages, fractional twists and level-2 arrows f).',
    basis:
      'Page 30 is the chart of the nine types with their automorphism groups G and G̃ and the counts 120/|G|; page 32 counts the arrows by type, 5 × 60 + 11 × 120 = 1620, and sets the « Programme de travail »: find the fundamental relations, write every arrow as a composite of arrows coming from modular dimension ≤ 1, then eliminate level-0 vertices and the tetrahedral pieces II₁. Page 35 gives the counts 12, 60 + 120, 60 by stratum. The relations are announced and never written.',
    ours:
      'The edition places the three levels on the strata of the compactified M_{0,5} and over its 10 curves and 15 pants decompositions, and the comparison with the Hatcher–Thurston complex is the reading\'s. The line of γ^{1′}_r is read on the page as « 3 × 120 = 3 × 40 » over a blackened equality; 360 is restored by the edition from the total. For γ⁰_r, γ²_r and γ^{2′}_r the reading reports that the sources and targets drawn on the chart do not match the factors of the tally, so the page\'s count is reproduced, not verified. « 1620 » is written over a struck « 1580 ». The arrow sources and targets on page 30 are flagged by the transcription as the reading to check first.',
    literature: [],
    status: 'unsearched',
    settle:
      'First recount the 1620 arrows from the chart on the facsimile of page 30, since the reading could not reconcile three arrow types. Then compare with presentations of the genus-0, five-point Teichmüller groupoid on special or tangential base points: Lochak–Schneps, « The universal Ptolemy–Teichmüller groupoid » (1997), Hatcher–Lochak–Schneps (Crelle 521, 2000), and Bakalov–Kirillov (2000). If one of them uses this set of 542 base points or an equivalent one, mark the entry matched. A web search of 2026-10-10 for « 542 » with M_{0,5} and tangential base points found nothing; that is not a reading of those papers.',
  },
  {
    id: '148-pages-36-37-reversed',
    cote: '148',
    pages: '36–38',
    kind: 'codicological',
    claim:
      'Pages 36 and 37 are filed in the reverse of the order of the argument: the reading order is 37, 36, 38.',
    basis:
      'Page 37 opens with the title « Autom d\'ordre deux d\'une sphère holomorphe », introduces T₁ = L₁*, T₂, e = ξ ∧ η ∈ T₄ and ξ + η, and stops in mid-sentence (« donc (ξ + η)² », struck). Page 36 begins with the invariant λ = (ξ + η)²/ξ ∧ η and introduces the base e₁ with e₁^{⊗4} = e; page 38 opens by changing e₁ into ζe₁. None of the three leaves carries a page number in his hand.',
    ours:
      'The observation is the transcription\'s (batch 2 header and the notes on pages 36–38), and the reading reads the pages in the order 37, 36, 38. The first words of page 36 are « \\uncertain{le} \\ill{} est », so the join with the end of page 37 rests on content, not on a sentence read across the break. The facsimile was not consulted by this pass.',
    literature: ['Transcription 148, batch 2 (batch-02.fr.tex), header and pages 36–38'],
    status: 'candidate',
    settle:
      'A person checks on the facsimile whether pages 36 and 37 are the two faces of one listing sheet, in which case the « reversal » is just which face was scanned first, or two separate sheets filed in the wrong order.',
  },
// 149: three entries. Pass: Opus 5.5 (claude-opus-5-5) on an Opus 5.5 reading (% Pass header of 149.modern.tex, 2026-10-10); no disagreement with the reading. Dropped as matches already named in the reading: Thm 1 (trivial centralisers of open subgroups of G_K), Thm 2 (faithfulness of K ↦ G_K over G_Q), Thm 3 (injectivity of points into section classes for subvarieties of semi-abelian varieties), the cuspidal splittings as a torsor under K*^ (tangential base points), the Zariski–Riemann proposition, the dual complex, the « dominant » Hom form (Mochizuki 1999), Oda's good-reduction criterion. Dropped as not established by the folder: every conjecture of §§2–4, the injectivity of G_k → Out(Δ_K) (p. 20), the conormal identification of c_i (p. 80, sign undecided), presumptions 1°) and 2°) of p. 129. Dropped as repairs: the Lemma of p. 36 as stated (false for types (1,1), (1,2)), d) ⇒ a) of p. 100, p. 121, p. 123, p. 129 2°).
{
  id: '149-dominant-faithfulness-curves',
  cote: '149',
  pages: '21–26, 36–39',
  kind: 'mathematical',
  claim:
    'Over an algebraically closed field of characteristic 0, if X is normal and connected, Y a hyperbolic curve, and f, g : X → Y with f dominant induce the same outer homomorphism of profinite étale fundamental groups, then f = g — proved geometrically, through the generalised Jacobian of Y, a Lefschetz fixed-point count in genus ≥ 2 and the loop subgroups of the cusps, without passing to a field of finite type over Q.',
  basis:
    'Pages 21–26 state Corollary 1 b) and reduce it, via Corollary 1 a) (maps to a semi-abelian variety are fixed by H_1 up to translation), to (∗): an open V ⊂ Y and u in the Jacobian with V + u ⊂ Y and π_1 of the inclusion and of the translate agreeing extérieurement on an open subgroup force u = 0; pages 27–33 prove it arithmetically (Kummer, Mordell–Weil), and the « Complément » of pages 36–39 proves the Lemma behind (∗) geometrically (« Ouf ! »). The sentences carrying the argument have a few \\uncertain{} and \\ill{} words (pages 23, 26, 36, 37), none on the statements themselves.',
  ours:
    'Substantial. The page’s Lemma (p. 36) drops the π_1 hypothesis of (∗) and is then false for types (1,1) and (1,2); the edition gives the counterexamples, corrects J \\ f(I) to J \\ f^{-1}(I) (p. 38), notes that shrinking V does not remove the exceptional case card I = 1, and writes the paragraph closing types (1,1) and (1,2) from the hypothesis of (∗) — that paragraph is the edition’s. The page also asserts the argument for hyperbolic polycurves of any dimension, resting on an embedding into a semi-abelian variety that fails in dimension ≥ 2 (universal elliptic curve minus zero section over Y(N)); the claim is therefore restricted to curves. Characteristic 0 is the page’s own restriction (pp. 33–35 leave characteristic p open).',
  literature: [
    'Web search, 2026-10-10, « dominant morphisms to hyperbolic curve determined by induced outer homomorphism of étale fundamental group algebraically closed field faithfulness »: returned Mochizuki, The Grothendieck Conjecture on the Fundamental Groups of Algebraic Curves (kurims), arXiv 1902.02058, arXiv 1211.4963, arXiv 2603.05968, read only as search summaries; none stated the faithfulness over an algebraically closed field. Not a search of the literature in the sense of the skill.',
  ],
  status: 'unsearched',
  settle:
    'Over ℂ the statement for the discrete fundamental group follows from the classical rigidity of non-constant holomorphic maps into hyperbolic Riemann surfaces (homotopic ⇒ equal; cf. the de Franchis–Severi circle, Imayoshi’s generalisations, harmonic-map uniqueness); check those sources, and Stix’s Rational Points and Arithmetic of Fundamental Groups (LNM 2054) and Mochizuki 1999 (§ on « Hom » forms), for the profinite form, i.e. for whether equality of outer maps into the profinite completion — a weaker hypothesis than homotopy — is already known to suffice. If either is stated, mark matched.',
},
{
  id: '149-cusp-specialisation-index',
  cote: '149',
  pages: '72–77, 84–93',
  kind: 'mathematical',
  claim:
    'For a relative hyperbolic curve U = X \\ T over a trait (or at a codimension-1 point s of a base, residue characteristic 0) and a rational section f meeting the cusp section g_{i_0} in the special fibre with intersection multiplicity n, the inertia at s maps to n times the cuspidal loop subgroup L_{i_0}, so that the section of the generic fibre specialises to a cuspidal (« second kind ») section of U_s whose decomposition group is an index-n subgroup of the normaliser of L_{i_0}; and inertia acts trivially exactly when f extends.',
  basis:
    'Page 73 states the local criterion (f extends ⇔ the section comes from π_1(U) over π_1(S) ⇔ it kills inertia); pages 76–77 define n = long V/g_{i_0}^*(J_f) = long A/(J_{i_0} + J_f) and « présume » that H_1 of the punctured trait maps to n times the canonical injection of index i_0 (« Il faudrait que je demande à Carlos de me le confirmer »), and that for ν = 1 the same holds on π_1 (« je vais admettre »); pages 84–93 draw the equivalences a)–f) and identify μ with the multiplicity of f^*T at s. The presumption and the definition of n are read clearly; the sentence on p. 77 saying n is intrinsic is mostly \\uncertain{}.',
  ours:
    'The proof of the presumption — f^*t = unit · ϖ^n for a local equation t of g_{i_0}(S), whence the loop around s goes to n times the loop around the cusp in the tame fundamental group of the punctured neighbourhood, on π_1 and not only on H_1 — is the edition’s footnote (p. 77). The page carries the statement, the definition of n and the equivalences, not their verification.',
  literature: [
    'Web search, 2026-10-10, « section conjecture rational point specializes to cusp inertia maps to multiple of cuspidal inertia intersection multiplicity good reduction relative curve »: returned Saïdi arXiv 1010.1313 and 1010.1314, Borne–Emsalem–Stix (lifting, preprint 2015), Porowski (RIMS preprints), arXiv 1301.4429, read only as search summaries; Nakamura’s characterisation of cuspidal sections as those cyclotomically normalising an inertia subgroup was cited there, the specialisation with index n was not. Not a search of the literature in the sense of the skill.',
  ],
  status: 'unsearched',
  settle:
    'Read Stix, LNM 2054 (chapters on cuspidal sections and on the specialisation of sections / good reduction), Nakamura’s papers on cuspidal sections and tangential base points, and Saïdi’s « Good sections » for the statement that the specialisation of a point-section at a place where the point meets a cusp is a cuspidal section through an index-(intersection multiplicity) subgroup of the cusp’s decomposition group. It is a local computation in tame ramification and is likely stated; if so, mark matched.',
},
{
  id: '149-leaf-82-83-misplaced',
  cote: '149',
  pages: '69–72, 82–84',
  kind: 'codicological',
  claim:
    'The leaf of pages 82–83, which bears his number 41, belongs by its text and its formula numbers between pages 71 and 72 (his 35 and 36): page 71 ends the genus ≥ 1 case « OK. », page 82 opens « Si le genre est zéro », page 83 ends on U_{O_x} and page 72 opens on diagram (9) built on U_{O_x}; its formulas (7), (8) fall between (6) of page 66 and (9) of page 72; while page 84 (his 42) continues page 81 directly.',
  basis:
    'The transcription records « p. 41 de l’auteur » on page 82, « p. 35 » on 70, « p. 36 » on 72, « p. 40 » on 80, « p. 42 » on 84; formulas (7) and (8) on page 83, (6) on page 66, (9) on page 72, (20)–(21) on page 81 and (22) on page 84; and at the foot of page 83 notes that the argument continues « sur un autre sujet » in page 84 and that a page may be missing. His continuous numbering 35, 36 across pages 70–72 leaves no gap for the leaf, so either the number 41 is not what it seems or the leaf was numbered where it was later filed.',
  ours:
    'The placement between 71 and 72 is the modernised reading’s, from the formula numbers; the join 83 → 72 through U_{O_x}, and the tension with his own numbering, are this pass’s observations from the transcription. The facsimile was not consulted.',
  literature: [
    'Transcription 149, batches 4 and 5 (batch-04.fr.tex, batch-05.fr.tex), pages 66, 69–72, 80–84',
    'Modernised reading 149.modern.tex, header and « L’ordre des feuillets »',
  ],
  status: 'candidate',
  settle:
    'A person checks on the facsimile the number written on page 82 (41, or something read as 41), whether pages 82–83 are the recto and verso of one leaf, and whether the last two lines of page 83 (not read with assurance) lead into diagram (9) of page 72.',
},
  {
    id: '154-dihedral-monodromy-half-turn',
    cote: '154',
    pages: '55–63, 85–86',
    kind: 'mathematical',
    claim:
      'For a system Σ of n pseudolines in a real projective plane, the 2n-gons Pol(D) cut on the double cover of an added pseudoline D form a local system on the cellular surface of relative positions, the transport along a half-turn around a position D = D_i of Σ is the rotation t ↦ t − (n − 1) of ℤ/2nℤ, and the monodromy π₁ → 𝔻_{2n} (dihedral, of order 4n) is surjective on the surface where crossing the positions D_i is allowed.',
    basis:
      'Page 55 writes the transport across an edge as a reflection t ↦ l_i − t and the alternating sum χ_{2n} = Σ(ν(s) − 1) = n − 1 for the chain of 2n faces around D_i; page 57 boxes λ(t) = t − (n − 1) and draws the gcd(n − 1, 2n) consequence; page 63 b) obtains every symmetry from half-circuits around a point of X and writes « u_D : π₁(𝒳, F_D) → Aut(F_D) est surjectif ouf ! », the word underlined twice. The further claim that π₁(𝒳̃) → 𝔻_{2n} is surjective even when crossing the D_i is forbidden (pages 85–86) rests on prose the transcription marks densely with \\uncertain{} and \\ill{}, including the n even / n odd distinction, and is not part of this claim.',
    ours:
      'The reading corrects two slips on the page (the rotation subgroup is ℤ/2nℤ, not ℤ/nℤ, on pages 57 and 85) and supplies the remark that pages 59–60 give surjectivity by themselves only for n even, a side reflection being needed for n odd; it did not redo the identification of the chain of 2n faces on page 55. The framing as a local system on a cellular model of the extension space of the rank-3 oriented matroid of Σ is the reading’s; nothing in the folder refers to oriented matroids. Page 63’s companion statement that the parity character χ_c is trivial (« Il semble que ») is contradicted by the cancelled table of page 81, and is left out.',
    literature: [
      'Web search, 2026-10-10, for monodromy / dihedral group / local system on extension spaces of rank-3 oriented matroids and pseudoline arrangements: returned work on extension spaces (Sturmfels–Ziegler 1993; G. Liu, arXiv 1606.05033; arXiv 2211.14083; arXiv 2303.04079) whose result snippets do not mention monodromy, a dihedral group or a local system of polygons; none was read.',
      'B. Sturmfels and G. M. Ziegler, « Extension spaces of oriented matroids », Discrete Comput. Geom. 10 (1993), 23–45 — only the abstract as reported by the search (extension spaces of rank-3 oriented matroids are spherical); the ZIB preprint SC-91-11 was fetched but is a scan with no extractable text, and was not read.',
    ],
    status: 'unsearched',
    settle:
      'Read Sturmfels–Ziegler 1993 and Björner, Las Vergnas, Sturmfels, White, Ziegler, Oriented Matroids (2nd ed.), ch. 7 (single-element extensions, Las Vergnas’s localisation theorem), together with Goodman–Pollack on allowable sequences (« Semispaces of configurations, cell complexes of arrangements », JCTA 37, 1984), for any statement about the cyclic order of the elements along a moving extension and its monodromy. Independently, check the half-turn value n − 1 in the realisable case, where positions are points of the dual plane off the lines δ_iδ_j and Pol(D) is the doubled cyclic order of the lines from that point to the δ_j. Until a source is read the status stays unsearched.',
  },
  {
    id: '154-generisation-cube',
    cote: '154',
    pages: '153',
    kind: 'mathematical',
    claim:
      'For a position D of an added pseudoline passing through ν ≥ 2 vertices of Σ, the stable generisations of D are the 2^ν vertices of a ν-cube whose ν·2^(ν−1) edges are the generisations through exactly one vertex, incidence being specialisation — whereas a straight line through ν vertices of a line arrangement has only 2ν stable perturbations.',
    basis:
      'Page 153 states it in words (« Les générisations stables de D correspondent aux sommets d’un cube de dimension ν, dont les arêtes sont les générisations sous-stables ») and gives the two counts 2^ν and ν2^(ν−1). The exponent of the first 2 is overwritten in the transcription; the counts fix it.',
    ours:
      'The justification — the side on which D is unstuck at each vertex can be chosen independently, two vertices of D never lying on a common pseudoline of Σ — is the reading’s; the page gives none. The contrast with straight lines (2ν sectors around a point of the dual plane on ν dual lines) is this pass’s, and so is the observation that the cube is in tension with page 150, which gives a vertex ρ of the surface X* of positions the order 2·card S_ρ: the two counts of incident sub-stable positions, 2ν and ν·2^(ν−1), agree only for ν = 2, so for ν ≥ 3 the positions near D do not form a surface vertex if all of them are kept. Neither the reading nor the page draws that consequence.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check against Las Vergnas’s characterisation of single-element extensions by signatures on cocircuits (Björner et al., Oriented Matroids, §7.1): if the independence of the signs at the cocircuits on the new element is stated or immediate there, mark matched. Then decide, from Sturmfels–Ziegler 1993, how the extension poset is made into a cell complex near a non-generic extension, which settles whether page 150’s surface can contain the positions of specialty ≥ 3.',
  },
  {
    id: '154-cyclic-order-determines-position',
    cote: '154',
    pages: '18',
    kind: 'mathematical',
    claim:
      'The folder asserts, without proof, that a relative position of an added pseudoline, other than the D_i themselves, is determined by the antipody-compatible cyclic order in which its double cover meets the oriented pseudolines of Σ.',
    basis:
      'Page 18 defines the map from P ∖ Σ to the antipody-compatible polygonal structures on Ĩ and says « il ne devrait pas être difficile de montrer que cette application est l’injection »; nothing in the folder proves it.',
    ours:
      'The reading says it does not know whether the order determines the position. This pass reads it differently and records why, as its own unchecked step: the cyclic order of i, j, −i, −j on the double cover decides on which side of D the vertex D_i ∩ D_j lies (for an orientation of D), and a single-element extension is determined by its signature on the cocircuits, i.e. by those sides. The double cover Ĩ in place of the page’s I ∖ {i₀} on the same page is a correction of the reading, not used here.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check the pass’s sketch against Björner et al., Oriented Matroids, §7.1 (extensions determined by their localisations) and the topological representation theorem (§5.2), keeping track of the passage from the sphere to the projective plane. If it holds as sketched, mark matched: the statement is then a standard consequence, and the entry stays only to correct the reading’s footnote.',
  },
  {
    id: '154-rectification-b-page-159',
    cote: '154',
    pages: '117, 159',
    kind: 'codicological',
    claim:
      'The « rectification b) » invoked on page 117, which the reading says is on no page of the folder, may be alinea b) of page 159: both leaves are cancelled by a large green cross, both complete the exceptional facets of the déploiement (𝒳, K), and page 159’s b) gives an exceptional facet multiple vertices of L, which is what page 117’s f) says the rectification now allows.',
    basis:
      'Page 117 (batch 6) opens in the middle of a sentence, has alineas read d)? e) f), and f) says that « à cause de la rectification b) » exceptional lines of K can no longer be characterised as containing no vertex of L′, « c’est plutôt qu’elles peuvent en contenir plusieurs »; it stops on « d’- ». Page 159 (batch 8), dated 1.1.84 and headed « Complément … sur les facettes exceptionnelles de (𝒳, K) », has alineas a)–d), and its b) describes « branches principales » of L through a « sommet multiple » on an exceptional facet. Much of 159 b) is \\uncertain{} or \\ill{}, and page 117’s first letter reads c) or d), so page 117 does not simply follow 159’s d).',
    ours:
      'The link between the two leaves is this pass’s; neither the transcriptions nor the reading draws it, and the reading states the opposite. That page 117 is a fragment of a longer redaction — its opening sentence and its earlier alineas on another leaf — is the transcription’s.',
    literature: [
      'Transcription 154, batch 6 (batch-06.fr.tex), header and page 117',
      'Transcription 154, batch 8 (batch-08.fr.tex), page 159',
    ],
    status: 'unsearched',
    settle:
      'A person compares pages 117 and 159 on the facsimile: ink (both green crosses), paper, and whether 159 b) can be read as a correction of an earlier characterisation of exceptional lines. If it can, the reading’s « ne figure sur aucune page du dossier » should be revised; if not, the missing leaf carrying page 117’s a)–c) is still to be looked for.',
  },
  // Folder 155 — find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, over a reading made by Opus 5 (claude-opus-5), under the 2026-09-23 exception; a commit adding this must name both models.
  // Dropped as matches: the Tannakian dictionary over k' (Deligne, Catégories tannakiennes, 1990, §1); rigidity ⇒ antipode for Hopf algebroids (the classical finite-dimensional Hopf-algebra statement and its groupoid form in Deligne 1990); the descent example U = k' ⊗_k k', A = End_k(k') (Galois descent / Morita); the « ? ? ? » question (Deligne 1990, §7). Searched: nothing beyond what the reading cites.
  // Disagreement with the reading, recorded and not acted on: section IV and IX say the positive-characteristic case « reste ouverte » / « n'est pas connue ». Coulembier, Etingof and Ostrik have since given positive-characteristic criteria (moderate growth, Verlinde categories) — cited from memory, not checked; the reading's footnote may need a person to revise it. Not a finding of the folder.
  {
    id: '155-takeuchi-idealiser',
    cote: '155',
    pages: '1',
    kind: 'mathematical',
    claim:
      'The ring in which the comultiplication of a Hopf algebroid over a non-central base k′ takes its values is presented as the idealiser quotient 𝒥̃/𝒥 of the right ideal 𝒥 = J·(A ⊗̂_k A), J = Ker(k′ ⊗_k k′ → k′) — a presentation of the Takeuchi product that the sources searched do not give.',
    basis:
      'Page 1, condition (ii): the map A → A ⊗̂_{k′} A is written, then said to take its values in 𝒥̃/𝒥 with 𝒥̃ = {λ | λ𝒥 ⊂ 𝒥}, and to be a ring homomorphism A → 𝒥̃/𝒥. The formulas are read; the connective words around them are not (« \\ill{} dont \\uncertain{comp.} par », « \\ill{} hom. d’anneaux »), and the article’s structure word is \\uncertain{} under a strike.',
    ours:
      'The identification with the Takeuchi product is the reading’s, « au dual près ». That 𝒥̃/𝒥 coincides with Takeuchi’s balanced subspace — λ𝒥 ⊂ 𝒥 unwinds to Σ aᵢr ⊗ bᵢ = Σ aᵢ ⊗ bᵢr in A ⊗_{k′} A, by the standard isomorphism I(L)/L ≅ End(S/L) for a one-sided ideal L — is this pass’s own check (Opus 5.5), not on the page. The page writes the object and never names it or says why the first formula fails; that explanation is the reading’s.',
    literature: [
      'nLab, « Takeuchi product » (read 2026-10-10): gives the balanced-subspace definition and the end-of-coend description, no idealiser or endomorphism-ring presentation. It cites Takeuchi 1977, Sweedler 1974, Brzeziński–Militaru 2002 and Schauenburg 1998, none of which were read.',
    ],
    status: 'candidate',
    settle:
      'Read M. Takeuchi, « Groups of algebras over A ⊗ Ā », J. Math. Soc. Japan 29 (1977), §§1–3, and M. E. Sweedler, « Groups of simple algebras », Publ. IHÉS 44 (1974), where ×_R was introduced: if either presents A ×_R A as an idealiser quotient or as End(A ⊗_R A) of a cyclic module, mark matched. Because I(L)/L ≅ End(S/L) is textbook ring theory, the presentation is likely folklore even if unprinted; the entry should be dropped to matched on any explicit statement of it.',
  },
// Candidate entries for folder 156-2 (find-novelty, Opus 5.5 on an Opus 5 reading — the 2026-09-23 exception; 2026-10-10). Not merged into src/content/findings.ts.
// Dropped as matches already footnoted in the reading: conical neighbourhoods (Whitehead, Siebenmann), faille composition as topological cobordism (Thom), the arc characterisation by non-cut points (R. L. Moore), bicollared lieux (M. Brown), Godement II.3.3.1, the maille's node as a two-sided non-separating hypersurface. The dated « (6 Juin) » / « 7 Juin » headings are already covered by 156-1-written-alongside-156-2.
  {
    id: '156-2-rives-cut-along-closed-set',
    cote: '156-2',
    pages: '14–17',
    kind: 'mathematical',
    claim:
      'For a closed subset A of an arbitrary space X, the folder defines the « rives » (sides) of A as the Boolean algebra Riv(A,X) = colim over neighbourhoods V of A of the clopen subsets of V ∖ A, the space Ã of local sides over A as the spectrum of the sheaf of Boolean rings j_*F_2 (j : X ∖ A → X), a canonical map Riv(A,X) → Comp(Ã) that is injective and, for X paracompact, bijective, and the space X̄ cut along A by a two-element partition {ρ, ρ′} of the sides — a general-topological, sheaf-theoretic construction of « cutting X along A » requiring no manifold or polyhedral structure.',
    basis:
      'Page 14 writes Rives(A,X) = lim→_V Comp(V ∖ A) = lim→_V Γ(V, i_*F_{2,U}), Riv(A,X) ≃ Comp(S_{A,X}) for A regularly immersed, the paracompact formula Γ(A, F|A) = lim→ F(V), and Ã = Spec(i_*F_{2,U}) with Comp(Ã) ≃ Γ(A, i_*F_{2,U}); page 15 gives (*) Riv(A,X) → Comp(Ã), « injective, et » added above « bijective si X paracompact », and defines bi-rives ρ + ρ′ = 1; pages 16–17 define X̄ = Dec_β(A,X) and the maille. The words « d\'où » (p. 15) and « A fermé » (p. 14) are \\uncertain{}, the page-14 paragraph ends on struck and \\ill{} words, and the page-15 NB describing the algebra of rives is largely \\ill{}.',
    ours:
      'The reading (Opus 5) supplies the interpretation of Spec(i_*F_{2,U}) as the relative Stone spectrum of (j_*F_2)|_A, which is what makes Comp(Ã) ≃ Γ(A, (j_*F_2)|_A) true; the page does not restrict to A nor say which spectrum. The reading also supplies the proof of injectivity, the correction « A non ouvert » for the page\'s « A ≠ ∅ », and the Möbius-band example; the space X̃ (X cut along A before contracting the halves) is used on page 16 without definition, and neither the page nor the reading defines its topology, so the construction of X̄ is incomplete as it stands. This pass (Opus 5.5) agrees with the reading\'s statements and adds one caution: the bijection Comp(Ã) ≃ Γ(A, (j_*F_2)|_A) depends on the topology put on the relative spectrum, which the reading names but does not specify. The comparison with Freudenthal-type ends of X ∖ A at A, and with local separation in Wilder\'s sense, is this pass\'s, not the page\'s.',
    literature: [
      'Web search, 2026-10-10: « ends of the complement of a closed subset, germs of clopen sets, sides, local separation, Stone space, cutting a space along a closed subset » — no source stating the construction; nothing opened beyond result titles',
      'Web search, 2026-10-10: « cutting along closed subset, two-sided, locally separates, sheaf j_* Z/2 » — surfaced arXiv:2308.12365 (two-sided closed sets via components of S ∖ B, bicollared closed sets) and arXiv:2007.02158 (separation by quasicomponents); neither read beyond the search summary, neither seen to define the sheaf j_*F_2 or a cut space',
    ],
    status: 'unsearched',
    settle:
      'No monograph was opened, so this stays unsearched. Check H. Freudenthal 1931 and later relative-end constructions (ends of X ∖ A converging to A, e.g. B. Hughes and A. Ranicki, Ends of Complexes, 1996), R. L. Wilder, Topology of Manifolds (1949), on local separation and ulc properties, G. E. Bredon, Sheaf Theory, on j_* and stalks of complements, and P. T. Johnstone, Stone Spaces (1982), V, on Stone spaces of sheaves of Boolean algebras: if any defines the sides of a closed subset as germs of clopens of its deleted neighbourhoods together with a space of local sides over it and a cut space, mark matched with the reference; if only the pointwise or compact-A version exists, say so and keep the sheaf-over-A form as the candidate.',
  },
  // Folder 158 — find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, over a reading made by Opus 5 (claude-opus-5), under the 2026-09-23 exception; a commit adding this must name both models.
  // Dropped as matches (named from memory, not consulted): the π₁ presentation of a pseudo-cofiltrant category with least object via fractions of End(e) (pp. 17–20; calculus of fractions, Gabriel–Zisman 1967, ch. I); Ep(E) and Mon(E), E infinite, have trivial group completion (pp. 55–56; an Eilenberg-swindle argument); cofiltered ⇒ every connected presheaf ∞-connected (p. 52, the easy direction). Conditional or abandoned, not entered: the Lemme (?) of p. 10, Prop. 2 (??) of p. 46, the repudiated corollary of p. 49, and the T ≠ ∅ / S² argument of pp. 61–83, which the folder leaves open.
  // Disagreements with the reading, recorded and not acted on: (1) the résumé says the answer is « oui dans le cas fini, non en général » and calls pp. 21–41 a counterexample to « (H) ⇒ cofiltrant »; on the pages the Ep(E)/Mon(E) construction refutes only « B_M 1-connexe (+ pseudo-cofiltrant) ⇒ cofiltrant » — it exhibits an F violating (H) — and p. 39 proves (H) ⇒ cofiltrant for monoids with a minimal element. (2) p. 52's corollary reads « X^0 tot. W-asphérique … i.e. X^0 est filtrante »; the second X^0 can only be the opposite category X°, so the first is X° too (cf. p. 70), not the open X_0 of least objects as §5.3 of the reading has it. (3) The reading repeats p. 39's « ou même seulement si leur H¹(−,Q) est nul » without flag; this pass finds it false (see the first entry).
  {
    id: '158-minimal-monoid-cofiltered',
    cote: '158',
    pages: '21–41',
    kind: 'mathematical',
    claim:
      'A monoid M having an element ψ with ψ ∈ uM for every u is cofiltered as soon as every connected right M-set has a simply connected category of elements; when M is not cofiltered the folder produces such an M-set explicitly — M/R_φ, whose category of elements has π₁ mapping onto Z, or the point, when the image of M in the maps of its minimal elements is a non-trivial group.',
    basis:
      'Proposition 2 (pp. 31–33) with hypotheses (A)–(D) and the degree δ: M₀ → Z of pp. 22–30; the quotient M̄ ⊂ Ep(M₀) and the two-case alternative of pp. 35–37; the Corollaire of p. 39, and case b) completed on p. 41. P. 37 carries several \\ill{} around « u λ = λ » and « Y_{/F} est 0-connexe (tous ses objets sont \\uncertain{équivalents}) »; p. 39’s Théorème breaks off and p. 41, numbered « 7 », does not continue its pagination.',
    ours:
      'The existential quantifier of p. 22, the additive reading of δ (p. 23) and the corrected relation of p. 28 are the reading’s repairs. The p. 39 Corollaire adds « ou simplement, que leur H¹(X,Q) = 0 »: this pass (Opus 5.5, own step) finds that variant false — for M = Z/2, every ψ is minimal, the connected M-sets are Z/2 and the point, with categories of elements contractible and BZ/2, both with H¹(−,Q) = 0, and M is not cofiltered. The loss is in case b) (p. 41), where Γ may be finite; the claim above keeps only the simply-connected form, which survives that example.',
    literature: [
      'Web search (2026-10-10) for a characterisation of filtered/cofiltered monoids by the categories of elements X//M of their connected M-sets: hits on Rogers, « Toposes of monoid actions » (arXiv 2112.10198) and « Monoid properties as invariants of toposes of monoid actions » (arXiv 2004.10513), not read. No source was read; the status stays unsearched.',
    ],
    status: 'unsearched',
    settle:
      'Read Rogers’ two papers (arXiv 2004.10513, 2112.10198) for a statement linking cofilteredness of M (flatness of the terminal M-set) to the homotopy of X//M for connected X, and McDuff, « On the classifying spaces of discrete monoids », Topology 18 (1979); check also that p. 41’s case b), applied with the minimal-element hypothesis alone, gives Γ = 1 ⇒ uφ = φ for all u — the step under the \\ill{} of p. 41.',
  },
  {
    id: '158-finite-category-cofiltered',
    cote: '158',
    pages: '50–53',
    kind: 'mathematical',
    claim:
      'A finite category X such that every connected presheaf on X has a simply connected category of elements is cofiltered — so for finite categories the homotopical condition, which p. 70 relates to total asphericity of X°, is equivalent to cofilteredness.',
    basis:
      'Proposition 1 (pp. 50–51): for X pseudo-cofiltrant with least object e and the minimal condition on sub-M-sets of Hom(e,x), the H_x = ⋂ fM form a local system, constant when X is 1-connected, giving fu = gu for u ∈ H_e. Proposition 2 and Corollaire (p. 52), and p. 53’s three lines. The step « (H) ⇒ X pseudo-cofiltrante » is asserted on p. 53 with an \\ill{} and no argument; « localisateur fondamental » and « W(δ) » on p. 52 are \\uncertain{}; 3°–4° on p. 51 carry \\uncertain{} on « aussi », « forment », « constante ».',
    ours:
      'The page’s Prop. 2 assumes X_0 (least objects) 1-connected while p. 51 4° uses X 1-connected; passing through X_0, where e is least and greatest, and back to X is not written and is the reading’s gloss. That (H) implies pseudo-cofilteredness is not proved on the page. The identification of p. 52’s X^0 with X° rather than with X_0 is this pass’s (Opus 5.5), against the reading. A sanity check by this pass: for M = {1,e,f} with e, f left zeros of {e,f} (not pseudo-cofiltrant), the M-set {x,y,i,j} with x·e = i, x·f = j, y·e = j, y·f = i has a category of elements equivalent (Quillen A) to a 4-cycle, π₁ = Z, so (H) fails there, as the claim requires.',
    literature: [
      'Web search (2026-10-10) for « cofiltered iff every connected presheaf aspheric / totalement asphérique / Maltsiniotis »: hits on Maltsiniotis, « Structures d’asphéricité, foncteurs lisses et fibrations » (arXiv 0912.2432), not read. No source was read; the status stays unsearched.',
    ],
    status: 'unsearched',
    settle:
      'Look in Maltsiniotis, La théorie de l’homotopie de Grothendieck (Astérisque 301, 2005), and Cisinski, Les préfaisceaux comme modèles des types d’homotopie (Astérisque 308, 2006), at the sections on totally aspheric categories for any statement that a finite totally (1-)aspheric category is filtered, or a finite counterexample. Independently, a person supplies the missing step (H) ⇒ pseudo-cofiltrant for finite X: the p. 61 lemma (products B × C = ∅ and β × γ = ∅ ⇒ not 1-connected) is the likely route, but its last eight lines are the least certain of the transcription.',
  },
  {
    id: '158-finite-monoid-right-zero',
    cote: '158',
    pages: '44–46',
    kind: 'mathematical',
    claim:
      'A finite monoid in which any u, v admit u′, v′ with uu′ = vv′ and whose group completion is trivial has an element p with up = p for all u, hence is cofiltered (p need not be unique).',
    basis:
      'Proposition 1 of p. 44 with its proof on pp. 44–46: a common p = u v(u) for all u, the faithful action on a finite E, E₀ = Im p stable under every u, and M → Aut(E₀) trivial by hypothesis a). « automorphisme » is \\uncertain{} twice on p. 45; « fini » before E is struck on p. 45, and finiteness of E comes from the regular representation of the finite M.',
    ours:
      'The non-uniqueness example {1, a, b} and the Lean formalisation (lean/Grothendieck/Folder158.lean) are the edition’s, from the reading’s correction of 2026-09-26; the page’s own uniqueness paragraph is struck.',
    literature: [],
    status: 'unsearched',
    settle:
      'Likely a short consequence of the Rees–Suschkewitsch structure of the kernel of a finite semigroup with the right-reversibility (Ore) condition: look in Clifford–Preston, The Algebraic Theory of Semigroups I (1961), §§1.10 and 3.1–3.3, and in Rhodes–Steinberg, The q-theory of Finite Semigroups (2009), for a finite right-reversible monoid with trivial maximal group image having a right zero; mark matched on any explicit statement.',
  },
// Folder 159 — find-novelty pass, Opus 5.5 (claude-opus-5-5), 2026-10-10, on a reading made by Opus 5 (claude-opus-5, 2026-09-19).
// Searches were web searches; every source below was seen through a search summary, not read in full.
  {
    id: '159-no-reduction-monodromy-dense',
    cote: '159',
    pages: '20–22',
    kind: 'mathematical',
    claim:
      'On a smooth projective curve of genus ≥ 2 in characteristic 0, no projective connection lets the PGL₂ structure group reduce to a Borel subgroup or to the normaliser of a maximal torus; over ℂ the monodromy therefore has Zariski-dense image.',
    basis:
      'Page 21 computes deg L = g − 1 from det E ≃ det F ⊗ L^⊗2 and kills the composite ω → E → L as a section of a negative-degree bundle; it then treats the torus normaliser by passing to the double cover, and page 22 draws the Zariski-density conclusion in three lines.',
    ours:
      'The reading supplies the third case the page omits — the finite subgroups A₄, S₄, A₅, by an étale cover and Riemann–Hurwitz — and links the result to the non-degeneracy criterion of page 14, which the folder never does. On the page, « lorsque », « normalisateur » and « passage au revêtement double » are uncertain readings, the adjective in « Le [...] argument montre » and the symbol before « fibrés » are illegible, and the group name PGL(1)_S is uncertain.',
    literature: [
      'R. C. Gunning, « Special coordinate coverings of Riemann surfaces », Math. Ann. 170 (1967), 67–86 — located as a reference only, contents not seen',
      'D. Gallo, M. Kapovich, A. Marden, « The monodromy groups of Schwarzian equations on closed Riemann surfaces » (arXiv math/9511213) — non-elementary monodromy of projective structures',
      'T. Serandour, slides (COFECUB, Rennes), attributing irreducibility of the monodromy for g ≥ 2 to Hejhal, Earle and Hubbard — secondary',
    ],
    status: 'matched',
    settle:
      'Nothing to settle as a novelty: irreducibility and non-elementary monodromy for projective structures in genus ≥ 2 are in the cited literature, and the reading itself calls the result standard. A person may still check Gunning 1967 for the degree argument in the algebraic form the page gives it.',
  },
  {
    id: '159-formal-rigidity-quadratic-torsor',
    cote: '159',
    pages: '24–33',
    kind: 'mathematical',
    claim:
      'A complete augmented algebra with invertible J/J² and a connection whose symbol Ω → Ω¹_{X/S} is an isomorphism is, in characteristic 0, isomorphic to the formal completion of a P¹-bundle along a section with its canonical connection, uniquely once the isomorphism is fixed to order 3; the order-3 ambiguity is a torsor under Γ(X, Ω^⊗2), so projective connections on a curve form an affine space under quadratic differentials.',
    basis:
      'Pages 25–26 state the theorem with items a) (order 2 determines the extension) and b) (order 3 determines the rest), pages 27, 28 and 30 compute that a change of parameter contributes (n+1)α_n ω₀ⁿ ϖ₀, page 29 proves G₀ × G(c) → G bijective, page 31 abstracts it to a lemma on a group acting on a set, and pages 32–33 define regularity and close on G(c) ≃ G/G₀ ≃ Γ(X, Ω^⊗2).',
    ours:
      'The reading supplies the computation G/G₀ ≃ Hom(Ω, Ω^⊗3) ≃ Γ(Ω^⊗2) by the q_i, which the page asserts without proof, and rewrites the page-31 proof with distinct letters. Item b) of page 25 breaks off and ends on page 26; item c) of page 26 is almost entirely illegible; « régulière » on page 33 is an uncertain reading settled by the gloss below it. This pass (Opus 5.5) adds one observation the reading does not make: the existence part can only hold locally on S (page 32 says « Loc. (sur X, affine) »), since for a family of curves of genus ≥ 2 the projective connections form an f_*(ω^⊗2)-torsor over S that need not have a global section; the reading states existence without that qualification.',
    literature: [
      'D. Dumas, « Complex projective structures » (arXiv 0902.1951) — projective structures on a fixed surface as an affine space over holomorphic quadratic differentials',
      'Projective structures and projective bundles over compact Riemann surfaces (arXiv 0706.3608) — Gunning’s parametrisation by the 3g−3-dimensional space of quadratic differentials',
      'E. Frenkel, D. Ben-Zvi, Vertex Algebras and Algebraic Curves — named as the place for the formal-coordinate (Aut 𝒪-torsor) formulation; not found by the search and not consulted',
    ],
    status: 'matched',
    settle:
      'The conclusion is matched. What remains unsearched is the route — rigidity of a complete augmented algebra with a regular connection over an arbitrary X/S, with the abstract lemma of page 31 — against Frenkel–Ben-Zvi (projective connections and Aut 𝒪), Deligne, LNM 163, and Mochizuki’s indigenous bundles; if the route gives nothing beyond the classical statement, leave this entry matched.',
  },
  {
    id: '159-monodromy-injectivity-question',
    cote: '159',
    pages: '17',
    kind: 'mathematical',
    claim:
      'The folder defines the space M_ann(X) of projective structures on a fixed compact Riemann surface, maps it to the PGL₂ character variety of π₁(X), and asks whether that monodromy map is injective, without answering.',
    basis:
      'Page 17 writes the morphism M_ann(X) → M_g^𝔷(X) and the question « est-il injectif ? »; the same page introduces the description of the Teichmüller locus by « on suppose ».',
    ours:
      'The reading names the map as the monodromy map of projective structures. The sentence describing M_ann(X) is mutilated on the page; only the module H⁰(X, ω^⊗2) is certain. The symbol written here as 𝔷 is an editorial placeholder for an unidentified glyph.',
    literature: [
      'D. Dumas, « Complex projective structures » (arXiv 0902.1951) — on a fixed Riemann surface the holonomy map is a proper holomorphic embedding; injectivity attributed to Poincaré, image analytic to Gallo–Kapovich–Marden',
      'K. Matsuzaki (Ann. Acad. Sci. Fenn. 32, 2007) — injectivity on each Bers fibre attributed to Kra, properness to Kapovich and Tanigawa',
    ],
    status: 'matched',
    settle:
      'Nothing to settle as a novelty: the question has a positive answer in the cited literature. A person may check whether the mutilated sentence on page 17 states anything beyond the question.',
  },
  {
    id: '159-filed-under-derivateurs',
    cote: '159',
    pages: '1–33',
    kind: 'codicological',
    claim:
      'Folder 159 is filed in the group 157-1 to 160 that the inventory titles « Dérivateurs » and dates 1990-[1991], yet none of its thirty-three pages concerns derivators, derived categories or homotopical algebra: the content is projective connections on curves in EGA/SGA vocabulary.',
    basis:
      'Both transcriptions note it independently on their own batches, and the reading checks it across the whole folder. Pages 30, 32 and 33 are reported on printed music-staff paper and other leaves on fan-fold computer listing.',
    ours:
      'The observation is about content only and dates nothing; the reading says so and keeps Montpellier’s dating. The paper observations were made on a digital facsimile and are fragile.',
    literature: [
      'Transcription 159, batch 1 (batch-01.fr.tex) and batch 2 (batch-02.fr.tex), headers',
      'Modernised reading 159 (159.modern.tex), section « Ce que le contenu montre, et ce qu’il ne date pas »',
    ],
    status: 'unsearched',
    settle:
      'A person checks the Montpellier inventory for how folder 159 came into the « Dérivateurs » group (a chemise, a box, the archivists’ grouping), and checks the music-staff and listing paper on the original leaves against other folders on the same paper.',
  },
  {
    id: '160-ga-subgroups-additive-kernels',
    cote: '160',
    pages: '2–6',
    kind: 'mathematical',
    claim:
      'Over any base S of characteristic p, every finite locally free subgroup of rank pⁿ of 𝔾_{a,S} is the kernel of a unique monic additive polynomial xᵖⁿ + aₙ₋₁xᵖⁿ⁻¹ + … + a₀x, so that the scheme Xₙ of such subgroups is 𝔸ⁿ, and the subgroup is étale exactly when a₀ is invertible.',
    basis:
      'Page 6 states the theorem; pages 2–4 prove surjectivity on algebraically closed fields, monomorphy by deformation over square-zero extensions and properness by the valuative criterion, whence 𝔸ⁿ ≅ Xₙ,réd only. Page 5 asks whether Xₙ is reduced and answers only for n = 1 at the origin, through a tangent-space computation whose six lines are mostly \\ill{} in the transcription.',
    ours:
      'The folder establishes the isomorphism only onto Xₙ,réd. The full statement is completed in the reading’s footnote (characteristic polynomial of x, then additivity), not on the page; the final dimension count of the tangent space at n = 1 is also the reading’s. This pass checked the footnote’s step in the row: P(x+y) − P(x) − P(y) has degree < pⁿ in each variable, so membership in (P(x), P(y)) forces it to vanish.',
    literature: [
      'M. Brion, « Homogeneous varieties under split solvable algebraic groups », arXiv 2101.12452v2 (2021), Lemmas 4.1–4.2 — read 2026-10-10: for X locally noetherian, a finite flat subgroup H ⊂ 𝔾_{a,X} is Ker(P, id) for a unique monic additive P ∈ O(X)[t], by exactly the characteristic-polynomial-then-additivity argument; the proof is said to adapt Demazure–Gabriel IV §2 1.1.',
      'M. Brion, « Some structure theorems for algebraic groups », arXiv 1509.03059v3, Example 2.1.7 — read 2026-10-10: the field case, every subgroup scheme of 𝔾_a is the kernel of an additive polynomial.',
      'M. Demazure, P. Gabriel, Groupes algébriques I (1970), IV §2 1.1 and II §3 4.4 — cited through Brion, not read.',
    ],
    status: 'matched',
    settle:
      'Settled as a match: Brion 2021, Lemma 4.2 (locally noetherian base, which the uniqueness lets one remove by the same local argument). Kept so that the next reader does not search again; the étale criterion f′ = a₀ is immediate. Reading Demazure–Gabriel IV §2 would give the earlier printed source.',
  },
  {
    id: '160-dickson-geometric-route',
    cote: '160',
    pages: '7–12',
    kind: 'mathematical',
    claim:
      'The folder proves Dickson’s theorem 𝔽ₚ[X₁,…,Xₙ]^{GL(n,𝔽ₚ)} = 𝔽ₚ[A₀,…,Aₙ₋₁] (and the SL variant with Δₙ in place of A₀) geometrically: 𝔸ⁿ/GL(n,𝔽ₚ) → 𝔸ⁿ is birational, quasi-finite and surjective onto a normal target, hence an isomorphism by Zariski’s Main Theorem — a route whose ingredients are those of the Galois-theoretic proof.',
    basis:
      'Page 7 factors the Moore determinant (« reste à déterminer c »), page 8 gives the Aᵢ by Cramer, page 9 sets Δᵢ = AᵢΔₙ and A₀ = ±Δₙ^{p−1}, pages 9–11 argue birationality, finite fibres and surjectivity (via étale subgroups and a restriction lemma for Xₙ = 0), and pages 11–12 deduce the SL case.',
    ours:
      'The reading supplies the constant c = 1, the exact sign (−1)ⁿ, the reason Δₙ divides Δᵢ, and the Frobenius twist in the restriction lemma Aᵢ(X₁,…,Xₙ₋₁,0) = Aᵢ₋₁(X₁,…,Xₙ₋₁)ᵖ, which the page writes without the p-th power.',
    literature: [
      'L. E. Dickson, « A fundamental system of invariants of the general modular linear group with a solution of the form problem », Trans. AMS 12 (1911) — the theorem, including the SL case; cited, not read.',
      'S. V. Sam, « Dickson invariants », notes (2011), following C. Wilkerson, « A primer on the Dickson invariants » (1983) — read 2026-10-10: Moore-determinant definition of the invariants, integrality over 𝔽_q[c_{n,i}], Galois group of the splitting field equal to GL(V), and normality of the polynomial ring. These are the algebraic counterparts of the folder’s finiteness, birationality and normality.',
      'R. Steinberg, « On Dickson’s theorem on invariants », J. Fac. Sci. Univ. Tokyo 34 (1987) — known from a web search result only, not read.',
    ],
    status: 'matched',
    settle:
      'Settled as a match for the theorem and, in substance, for the route: the folder replaces integrality by quasi-finiteness plus surjectivity and the Galois equality by birationality, which yields nothing the Wilkerson proof does not. The one feature not seen in the sources read is that surjectivity is obtained from the classification of subgroups of 𝔾_a (160-ga-subgroups-additive-kernels); a reader who thinks that worth recording can check Steinberg 1987 and Wilkerson 1983 for it.',
  },
  {
    id: '160-special-linear-structures-sign',
    cote: '160',
    pages: '9, 13',
    kind: 'mathematical',
    claim:
      'Page 13 asserts that for an étale M = Ker f_a ⊂ 𝔾_{a,S} of rank pⁿ the trivialisations of Λⁿ_{𝔽ₚ}M correspond bijectively to the (p−1)-th roots of a₀; as stated this fails for p and n odd, and what holds is the correspondence with the (p−1)-th roots of (−1)ⁿa₀.',
    basis:
      'Page 13, Corollaire, written right after page 9’s A₀ = ±Δₙ^{p−1} with the sign left floating; « aura » and « l’image inverse » are \\uncertain{} in the transcription, but the statement does not turn on them.',
    ours:
      'The refutation is this pass’s own step, and it disagrees with the reading (made on Opus 5), which keeps « racines (p−1)-ièmes de a₀ » and glosses a root of a₀ as « au signe près, une valeur de Δₙ ». Counterexample: S = Spec 𝔽₃, n = 1, M = 𝔽₃ = Ker(x³ − x), so a₀ = −1; Λ¹M = M has two trivialisations over 𝔽₃, while −1 has no square root in 𝔽₃. In general, with A₀ = (−1)ⁿΔₙ^{p−1}, a (p−1)-th root y of a₀ satisfies (y/Δₙ)^{p−1} = (−1)ⁿ, and −1 is not a (p−1)-th power in 𝔽ₚ for p odd; the two μ_{p−1}-torsors differ by the torsor of (p−1)-th roots of −1.',
    literature: [
      'Over a field the identity “constant coefficient = (−1)ⁿ Δₙ^{q−1}” for the subspace polynomial is standard (Moore determinant literature; a web search of 2026-10-10 returned it in an EMS Press article and in Wikipedia, « Moore matrix »). The relative torsor form of page 13 was not searched.',
    ],
    status: 'refuted',
    settle:
      'What still stands is the corrected statement: (Λⁿ_{𝔽ₚ}M)^× is the μ_{p−1}-torsor of (p−1)-th roots of (−1)ⁿa₀. A person confirms the counterexample and the reading’s Corollary on page 13 is amended accordingly (/modernize-grothendieck). Whether the corrected relative form is in print is the open question of 160-relative-moore-determinant.',
  },
  {
    id: '160-relative-moore-determinant',
    cote: '160',
    pages: '13–16',
    kind: 'mathematical',
    claim:
      'For a locally free E of rank n with u : E⁽ᵖ⁾ ⥲ E (an étale 𝔽ₚ-local system), the folder defines a Moore determinant Δₙᴱ : V(E) → V(ΛⁿE), homogeneous of degree (pⁿ−1)/(p−1), and Dickson-type coefficients Aᵢᴱ that extend from the complement of its zero divisor to all of V(E), with A₀ᴱ = ±(Δₙᴱ)^{p−1} made meaningful by the trivialisation (ΛⁿĚ)^{⊗(p−1)} ≅ 𝒪_S coming from Λⁿǔ.',
    basis:
      'Pages 13–15 set up the dictionary M ↔ (E, u), define ξ⁽ᵖ⁾ and the wedge ξ ∧ ξ⁽ᵖ⁾ ∧ … ∧ ξ⁽ᵖⁿ⁻¹⁾, state that the Aᵢᴱ are sections of Sym(E) (« on trouve que », no proof), and give the trivialisation in a bracket; page 15–16 write ǔ in the basis ξ⁽ᵖⁱ⁾ as a companion matrix. Several words (« ouvert », « déterminés », « tout entier ») are \\uncertain{} and the last column of the companion matrix is partly under erasures.',
    ours:
      'The reading fixes the variance (sections of Ě, structure ǔ), where the page writes u(ξ⁽ᶠ⁾). The extension of the Aᵢᴱ to V(E) is asserted on the page without proof; it follows by reducing étale-locally to the trivial local system, where the Aᵢᴱ are the absolute Dickson invariants — that reduction is this pass’s remark, not the page’s. The sign in A₀ᴱ is left as ± by both page and reading.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look for Dickson invariants or the Moore determinant attached to an 𝔽_q-local system / unit-root F-crystal over a base, with the trivialisation of (det)^{⊗(q−1)}: first « Modular characteristic classes for representations over finite fields » (arXiv 1607.01052), which a web search of 2026-10-10 returned but which was not read; then Katz, « p-adic properties of modular schemes and modular forms » (1973) §4 for unit-root F-crystals, and the Drinfeld-module literature (Goss, Basic Structures, ch. 1). If any of them builds Δₙᴱ and the Aᵢᴱ for a sheaf with Frobenius, mark matched.',
  },
  {
    id: '160-content-not-derivators',
    cote: '160',
    pages: '1–22',
    kind: 'codicological',
    claim:
      'The folder is filed in the group the inventory titles « Dérivateurs » and dates 1990-[1991], but none of its twenty-one written pages concerns derivators, derived categories or homotopical algebra: pages 2–22 are on finite subgroup schemes of 𝔾_a in characteristic p and page 1 on algebraisation along a closed subset.',
    basis:
      'Both batch transcriptions (batch-01.fr.tex, batch-02.fr.tex) and the reading’s section « Ce que le contenu montre, et ce qu’il ne date pas »; no leaf carries a date, a heading or a reused verso.',
    ours:
      'The observation on content is checkable from the transcription. Nothing here dates the leaves: a remark by one transcriber on the hand (fountain pen, EGA-era abbreviations) was made on a digital facsimile and is not relied on, and the archivists’ dating stands.',
    literature: [],
    status: 'unsearched',
    settle:
      'A person examines the physical folder at Montpellier — paper, ink, any watermark, and how the leaves sit within the « Dérivateurs » group 157-1 to 160 — to say whether the folder belongs with that group or was filed there by position only. Until then this records a mismatch of subject, not a date.',
  },
// Folder 2 — /find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, over a modernised reading made by Opus 5 (header: « Pass: Opus 5 (claude-opus-5), 2026-09-19 »). Disagreements with the reading are stated in `ours`.
  {
    id: '2-chern-ring-gamma-comparison',
    cote: '2',
    pages: '20–21, 28–29',
    kind: 'mathematical',
    claim:
      'For a special λ-ring K with a family of geometric elements, the ring CK presented by generators c^i(x) and the Whitney, product and geometric relations maps onto the γ-graded ring GK, with a map ψ back such that φψ is multiplication by (−1)^{i−1}(i−1)! in degree i; hence φ is surjective and bijective after ⊗ℚ.',
    basis:
      'Page 28 presents CK by generators and relations, page 29 constructs ψ : GK → G(Ã) from any Chern homomorphism respecting the E_s, and the top of page 21 proves γ^i(P − ε(P)) − (−1)^{i−1}(i−1)! P ∈ B^{(i+1)} on the universal ring B, ending « cqfd ». The statement of the proposition itself (page 20) is lost; page 20 writes the sign (−1)^i, page 21 proves (−1)^{i−1}.',
    ours:
      'The reading reconstructs the proposition from its proof and states the ⊗ℚ bijectivity, which the page does not write (it states only surjectivity, as a corollary, with an \\ill{} in the sentence). The pass agrees with the reading on the sign.',
    literature: [
      'E. Mackall, « Universal additive Chern classes and a GRR-type theorem », arXiv:2006.14664 (2020), Prop. 2.1 and Theorem 4.1 — a universal graded receptor B(X) of Chern classes for schemes, with B^i(X) → gr^i_γ K(X) and c^B_i back, both composites multiplication by (−1)^{i−1}(i−1)!',
      'SGA 6 (LNM 225), Exposé XIV, and Fulton–Lang, Riemann–Roch Algebra (1985) — cited by Mackall §4 for the same factor between gr and the Chow ring (Riemann–Roch without denominators); not read directly in this pass',
    ],
    status: 'matched',
    settle:
      'Mackall’s B(X) is built from schemes and projective bundles, the page’s CK from an abstract special λ-ring with a chosen geometric family; check whether Mackall §3 (« Chern classes and λ-rings ») or Fulton–Lang Ch. III states the λ-ring form, and whether the two presentations agree when K = K(X) with all vector-bundle classes as the geometric family. The composite formula itself is in Mackall Theorem 4.1.',
  },
  {
    id: '2-chern-ring-not-injective-pn',
    cote: '2',
    pages: '21',
    kind: 'mathematical',
    claim:
      'The comparison φ_K : CK → GK fails to be injective for the λ-ring K = ℤ[L]/(L−1)^n = K(P^{n−1}) when L alone is taken as geometric element, because the relation (L−1)^n = 0 imposes only (n−1)!·ζ^n + (higher terms) = 0 on CK while GK = ℤ[ζ]/(ζ^n) is torsion-free.',
    basis:
      'Page 21 asks « Est-ce que φ_K est toujours bijectif ??? », answers « Non » (boxed), and gives this example with the margin « c’est-à-dire K = K(P^{n−1}) »; it asserts « CK a de la torsion ». The generator of the ideal and the exponent of (1+ξ) are \\ill{}, and a diagonal marginal note reads « Mais si … l’idéal était … CK = ℤ[ξ]/ξ^n », i.e. with a larger ideal the torsion disappears.',
    ours:
      'The pass’s own observations, not on the page and not in the reading: (a) the example needs n ≥ 3, since for n ≤ 2 the factor (n−1)! is 1 and no torsion arises; (b) the page does not show that ζ^n ≠ 0 in CK, which needs a Chern homomorphism into a ring where ζ^n ≠ 0 and (n−1)!ζ^n = 0; (c) the example depends on the geometric family — if the rank-(n−1) class n − L^{−1} (the tautological quotient) is also declared geometric, its axiom forces ζ^n = 0 and CK = GK, which is what the marginal note appears to say, and is consistent with Mackall’s B(Gr) having level 1 (Example 3.8). The reading presents the example as unconditional.',
    literature: [
      'E. Mackall, arXiv:2006.14664 (2020), §4 after Corollary 4.2 — gives non-injectivity of b^3_γ for a finite approximation of BO⁺(2n+1), citing SGA 6 XIV §4, 4.5; the P^{n−1} λ-ring example with a restricted geometric family is not there',
    ],
    status: 'candidate',
    settle:
      'First decide whether the claim holds: construct (or rule out) a Chern homomorphism ℤ[L]/(L−1)^n → Ã with c(L) = 1 + h and h^n ≠ 0, (n−1)!h^n = 0, for n ≥ 3. Then search Fulton–Lang Ch. III and SGA 6 Exposés 0 App. and V for the dependence of the universal Chern ring on the geometric family.',
  },
  {
    id: '2-trivial-total-chern-class',
    cote: '2',
    pages: '9, 11, 13',
    kind: 'mathematical',
    claim:
      'If i : X → X × P^r is a constant section and Y ⊂ X a divisor whose class x′ ∈ A^1(X) is nonzero but killed by (r−1)!, then i_!(O_Y) is a nonzero class of K(X × P^r) whose total Chern class is 1 (possible only for r ≥ 3).',
    basis:
      'Page 9 computes c(ξ^r) = 1 + (−1)^{r−1}(r−1)! η^r for the class of a point of P^r; page 11 writes c(i_!x) as 1 + (−1)^{r−1}(r−1)! η^r [ε(x) + Σ Q^{(r)}_i]; page 13 applies it to O_Y with c(O_Y) = Σ x′^n and concludes « Si donc (r−1)! x′ = 0, … = 0 ». On page 13 « hyperplan » (for Y) and the final « 0 » are \\uncertain{}, and the words around the conclusion are \\ill{}; the statement rests on them.',
    ours:
      'The reading reads the last member as 1 (total class) rather than 0, supplies the elliptic-curve torsion point as an instance, and supplies the general leading coefficient of Q^{(r)}_i. The pass disagrees with the reading on one point: the reading (and the page) call the class [O_{Y×P^r}], but i_!(O_Y) = [O_Y] ⊗ ξ^r is the class of Y × {point}; Y × P^r would be the pull-back of O_Y, whose total Chern class (1 − x′)^{−1} is not trivial. The r ≥ 3 restriction is the pass’s.',
    literature: [],
    status: 'unsearched',
    settle:
      'Search Fulton, Intersection Theory §15.3 and its examples (Riemann–Roch without denominators, c_r of the structure sheaf of a point), SGA 6 Exposé XIV and Jouanolou’s Riemann–Roch sans dénominateurs (1970) for an explicit nonzero K-class with trivial total Chern class built from torsion in Pic; it is likely there in some form, in which case mark matched.',
  },
  {
    id: '2-mixed-campaigns',
    cote: '2',
    pages: '2–3, 4, 15, 32–37',
    kind: 'codicological',
    claim:
      'Folder 2, inventoried as « Notes Antiques (antérieures à 1958) » under the date [1957], contains leaves using vocabulary that the published record dates later — « Topos annelé » (p. 15), D_parf(f) and complexes « parfaits relativement à f » (p. 32), « préschéma » (pp. 4, 34) — beside leaves (pp. 2–3) that use none of it; the seam runs inside the first wrapper, « Classique pour les Courbes ».',
    basis:
      'The transcription reads « Topos annelé » on page 15 and D_parf(f), K_parf(f) on page 32 without \\uncertain{}; « préschéma » is struck on page 4. Pages 2–3 write E, not K, for the ring of classes and use only c^1; the five wrappers (pp. 1, 8, 19, 31, 39) carry the run titles and none carries the inventory’s words. This dates leaves, not mathematics, and fixes no date for any leaf.',
    ours:
      'The campaign analysis and the observation that the seam falls inside the first wrapper are the reading’s; the dates attached to the words (topos: SGA 4, 1963–64; perfect complexes relative to a morphism: SGA 6, 1966–67; préschéma: EGA I, 1960) are general knowledge, not checked against a source in this pass.',
    literature: ['Transcription 2, batch-01.fr.tex (pages 4, 15) and batch-02.fr.tex (page 32)'],
    status: 'unsearched',
    settle:
      'A person checks pages 4, 15 and 32 against the facsimile for these words and records the paper of each run (white, blue-grey, typescript versos) to see whether the material seams coincide with the vocabulary seams; separately, confirm the first attested dates of « topos » and of relative perfect complexes in SGA 4 and SGA 6.',
  },
  {
    id: '18-real-frobenius-trivial-converse',
    cote: '18',
    pages: '35, 37',
    kind: 'mathematical',
    claim:
      'The folder asserts that a motive over ℝ has trivial real Frobenius exactly when it is generated by the even Tate twists ℚ(−2n), equivalently when its group is G_m or trivial (p. 35), and that f_∞ = id_M forces M to be a sum of tensor powers of ℚ(2) (p. 37); as stated this fails: H² of P¹_ℂ viewed as an ℝ-scheme contains the summand ℚ(−1) ⊗ ε (ε the sign Artin motive of ℂ/ℝ), on which F_∞ acts by (−1)(−1) = +1, which is not a sum of even Tate twists, and ℚ(1) has group G_m with F_∞ = −1.',
    basis:
      'Page 35 boxes the chain (f_∞ = 1) ⟺ (ℝ(α) = ℝ) ⟺ « M est engendré par ℚ(−2n) » ⟺ G ≃ G_m ou {e}; page 37 states the Remarque on ℚ(2) in clean ink (only « directe » is uncertain). The surrounding prose of p. 35 is dense with \\ill{} and \\uncertain{}, and a margin note reads « engendré par ℚ \\uncertain{tordu} et par ℚ(2) », which may be reaching for a twisted Artin factor; the boxed chain itself is legible.',
    ours:
      'The counterexample is this pass’s own step, not the page’s and not the reading’s: X = P¹_ℂ as an ℝ-scheme has X(ℂ) = two copies of P¹(ℂ) swapped antiholomorphically by conjugation, so F_∞ on H² = ℚ[1] ⊕ ℚ[2] is [1] ↦ −[2], with +1-eigenvector [1] − [2] of Hodge type (1,1) and real period ±2π. The first equivalence (f_∞ = 1 ⟺ all periods real) and the implication f_∞ = 1 ⟹ G ∈ {G_m, e} (granting the Hodge conjecture the page invokes) are not contested. This disagrees with the modernised reading (Opus 5), which repeats the chain and concludes that « les seuls motifs sur ℝ dont toutes les périodes sont réelles sont les sommes de twists pairs du motif de Tate »; this pass is Opus 5.5.',
    literature: [],
    status: 'refuted',
    settle:
      'A person checks the eigenvalue computation for F_∞ on H²((P¹_ℂ)_ℝ) and whether « ℚ tordu » in the p. 35 margin is the sign-twisted object, which would mean the page saw the correction in the margin and boxed the uncorrected form. What still stands: f_∞ = 1 iff the periods are real, and the corrected class is the motives generated by the ℚ(−n) ⊗ εⁿ (with ε² = 1), whose group is G_m or trivial; the reading’s p. 35 and p. 37 paragraphs need the correction.',
  },
  {
    id: '18-archimedean-lattice-cocycle',
    cote: '18',
    pages: '46–61',
    kind: 'mathematical',
    claim:
      'For a motive M over a field k ≃ ℂ defined over a finitely generated k₀, comparing the integral Betti lattices M^ℤ_v ⊂ ∏_{ℓ ≤ ∞} M(ℓ) attached to different archimedean places v of k gives an element of G(𝔸_ℂ)/G(Ẑ) whose archimedean component is well defined in G(k); σ ↦ φ_{v,∞}(σ) is a 1-cocycle Gal(k/k₀) → G(k) whose class, hence a G-torsor over k₀, does not depend on v; and the transcendence degree of the configuration attached to n places is bounded by (n − 1)·dim G.',
    basis:
      'Pages 46–48 set up the torsors Isom(ξ, ξ_{v_i}) and the bound (n−1)d; pages 52–58 define φ_v, mark the archimedean component « bien déterminé dans G(k) !!! » and write the cocycle identity; page 61 computes the change of place. Almost every connecting sentence on pp. 52–60 carries \\ill{}, including the hypotheses on k₀ (p. 52) and the Zariski-density statement (p. 58, « à vérifier / ok »); the formulas are legible, the argument between them is not.',
    ours:
      'The reading states the result with the hypotheses it could reconstruct, reads « place » as an archimedean topology on k, and replaces the boxed conjugation of p. 61 by the coboundary formula φ_w(σ) = ˢg_∞ φ_v(σ) g_∞⁻¹ (the struck first version on the page). The independence of the class from v is the reading’s formulation of the page’s boxed formula. The generic-element lemma of p. 48, on which the sharpness of the bound rests, is stated and not proved.',
    literature: [],
    status: 'unsearched',
    settle:
      'Search the literature on conjugate varieties and their Betti lattices inside adelic cohomology — Serre 1964 (non-homeomorphic conjugate varieties), Deligne–Milne–Ogus–Shih LNM 900 I §2 (absolute Hodge cycles, the 𝔸_f-comparison of H_B(σX)), and André, Une introduction aux motifs §7.5 and ch. 23 (period torsors, several embeddings) — for a cocycle Gal(k/k₀) → G(k) built from the archimedean component of the lattice comparison, and for a transcendence bound in the number of embeddings. Until then it is a list item, not a candidate.',
  },
  {
    id: '18-p6-foreign-typescript',
    cote: '18',
    pages: '6',
    kind: 'codicological',
    claim:
      'Page 6 is a typed leaf from another text — its own pagination « 18 », numbered paragraphs 7.13.10–7.13.12 on the specialisation of cycle classes, citing « SGA 5 IV » and « XIV 4.1 » — corrected by hand and cut mid-sentence (« où Z est »), and its source is not identified in the folder.',
    basis:
      'Transcription batch-01, page 6 and the batch header (« Page 6 is typed, not handwritten »); the reading’s footnote says nothing on the leaf names the work it comes from.',
    ours: null,
    literature: ['Transcription 18, batch 1 (batch-01.fr.tex), header and page 6'],
    status: 'unsearched',
    settle:
      'A person compares the paragraph numbering and the cross-references with the typescripts of SGA 6 and SGA 7 and with the EGA/SGA drafts in the fonds, and checks against the facsimile whether the corrections are in Grothendieck’s hand.',
  },
  {
    id: '22-power-series-discrete-obstruction',
    cote: '22',
    pages: '22, 24',
    kind: 'mathematical',
    claim:
      'For k = ℚ(x_i : i ∈ I) with I infinite, A = k[[t]] is formally smooth over k for its t-adic topology but not for the discrete topology: no derivation D : A → Ω¹_k ⊗_k A ≅ A^{(I)} induces d_k, because D(Σ x_{i_n} tⁿ) would have infinitely many non-zero components.',
    basis:
      'Page 22 sets up k = ℚ((x_i)), A = k[[t]], writes Ω_k ⊗_k A ≅ A^{(I)} ⊊ ∏ A dx_i and looks for D : A → Ω_k ⊗_k A; page 24 writes D(Σ a_λ t^λ) = Σ d(a_λ) t^λ, chooses indices i_0, i_1, … and starts f = Σ a_n tⁿ, then stops. Page 22 also states the general expectation (« Je présume que … A n’est jamais formellement lisse sur k pour la topologie discrète ») in a line half \\ill{}, with « formellement lisse » and « pessimiste » \\uncertain{}.',
    ours:
      'The page stops at the construction of f; the conclusion, the continuity argument (D(tⁿA) ⊂ tⁿ(Ω_k ⊗ A) once D(t) = 0) and the choice a_n = x_{i_n} are the reading’s (Opus 5). The reduction to D(t) = 0, which pages 22–23 carry in illegible prose through a finitely generated subfield k_0, is not needed: this pass (Opus 5.5) notes that D − D(t)·∂/∂t already kills t and still induces d_k, so the claim does not rest on the illegible step. The pass checked the argument: the projection onto the dx_{i_n} component is A-linear and gives tⁿ mod tⁿ⁺¹, hence non-zero for every n. Whether « ℚ((x_i)) » means the rational-function field or a Laurent-series field does not matter, the x_i being algebraically independent over ℚ in both. The same argument applies to any k of characteristic 0 with Ω_k of infinite dimension; the folder states only the case above.',
    literature: [
      'Stacks Project, Example 15.41.2 (Tag 07EM) and Theorem 15.41.1 (Tag 07EL) — formal smoothness of K[[x]] for the (x)-adic topology only; read 2026-10-10',
      'Stacks Project, Lemma 10.158.5 (formally smooth field extensions are separable), seen through a search summary only',
      'Two web searches (2026-10-10) for formal smoothness of k[[t]] over k for the discrete topology in characteristic 0: no source found stating it either way',
    ],
    status: 'candidate',
    settle:
      'Read EGA 0_IV §§19–22 (formal smoothness for the discrete versus adic topologies, and the remarks on power series over a field) and Matsumura, Commutative Ring Theory §§25–28, for an example of k[[t]] not formally smooth over k for the discrete topology when Ω_k is infinite-dimensional. This is a short argument and is likely to be stated or set as an exercise somewhere; the search so far is too thin to rule that out, and if it is found the status becomes matched.',
  },
  {
    id: '22-p23-proposition-reconstruction',
    cote: '22',
    pages: '22–24',
    kind: 'mathematical',
    claim:
      'The modernised reading completes page 23’s Proposition as « if Ω_{K/k} is finite-dimensional over K then A = K[[t_1,…,t_n]] is formally smooth over k for the discrete topology »; as completed it fails, by the folder’s own example on pages 22 and 24 (K = k = ℚ(x_i : i ∈ I), I infinite, n = 1, where Ω_{K/k} = 0).',
    basis:
      'Page 23 states the hypothesis (Ω_{K/k} of finite dimension over K, A = K[[t_1,…,t_n]]) and its conclusion is \\ill{} apart from an \\uncertain{discret} and « sur K rel. ; k »; the bottom of the page looks for D : A → Ω_{K/k} ⊗_K A inducing d_{K/k} and ends on an \\uncertain{l’hypothèse !}.',
    ours:
      'The conclusion is the reading’s (Opus 5), flagged there as « nôtre ». The refutation is this pass’s own step (Opus 5.5) and disagrees with the reading: with K = k, Ω_{K/k} = 0 satisfies the hypothesis, yet pages 22 and 24 show k[[t]] is not formally smooth over k for the discrete topology. The reading conflates the relative Ω_{K/k}, which the page 23 derivation targets, with the absolute Ω_k, which page 22’s obstruction lives in. The same conflation is in the reading’s statement that « the dividing line is the dimension of Ω_{K/k} » (spine and end of section IV). A derivation A → Ω_{K/k} ⊗_K A extending d_{K/k} is necessary for something, but by itself it does not give formal smoothness over k.',
    literature: [],
    status: 'refuted',
    settle:
      'What stands is the page’s hypothesis and its search for D : A → Ω_{K/k} ⊗_K A. Re-read page 23 on the facsimile (/transcribe-grothendieck) to recover the conclusion: plausibly a relative statement (formal smoothness relative to K, or a condition on the absolute Ω_K or on a finitely generated subfield, as the k_0 of page 22 suggests). Then correct the reading’s footnote on p. 23 and its « Ω_{K/k} » invariant.',
  },
  {
    id: '22-differentials-kernel-counterexample',
    cote: '22',
    pages: '26, 28',
    kind: 'mathematical',
    claim:
      'For a field extension K/k in characteristic p > 0, the map Ω¹_{k/(k∩K^p)} ⊗_k K → Ω¹_K need not be injective. Equivalently, the kernel of Ω¹_k ⊗_k K → Ω¹_K need not be generated by the differentials of k ∩ K^p. The counterexample is k = 𝔽(x, y) ⊂ K = 𝔽(x, a_0^{1/p}, …, a_{p−1}^{1/p}) with y = Σ a_i x^i and x, y, a_1, …, a_{p−1} algebraically independent.',
    basis:
      'Page 26 draws the square k, K, k ∩ K^p, K^p, writes the map and the sequence through Ω_{k∩K^p}, announces « Voici un contre-exemple » and sets a_0 = y − Σ a_i x^i, a = x^p, K^p = 𝔽(x^p, a_1, …, a_{p−1}, a_0). Page 28 argues by contradiction that (x, y) is p-free over K^p ∩ k (« … donc a_i ∈ k = 𝔽(x,y), absurde ») and offers the specialisation a_i = 0 for 2 ≤ i ≤ p − 1. The last generator of K on page 26 is \\ill{}, and most connecting prose on both pages is \\ill{}, including two mentions of a norm N_{K/k} whose role is unknown.',
    ours:
      'The reading (Opus 5) assembles the example from the coherent fragments: it supplies a_0^{1/p} as the \\ill{} generator of K, identifies the base field as 𝔽_0, and writes out the final step (dy proportional to dx in Ω¹_K, linearly independent in Ω¹_{k/k′}). This pass (Opus 5.5) checked that step: [k : k′] = p² follows from the page’s contradiction argument, since x ∉ K^p gives a unique K^p-basis expansion of y. What the page asserts beyond the counterexample, including the positive statement it was testing, is not legible.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look in EGA 0_IV §21 (differentials in characteristic p, the imperfection module and the Cartier equality) and Matsumura, Commutative Ring Theory §26, for a description of the kernel of Ω_k ⊗_k K → Ω_K in terms of k ∩ K^p, and for this or a simpler counterexample. If the kernel is described there, or the failure is noted, mark matched. A small example such as this may well be standard exercise material.',
  },
  // Folder 28. Pass: Opus 5.5 (claude-opus-5-5), 2026-10-10, on a reading made by Opus 5 (2026-09-12), under the one-way exception of /find-novelty.
  {
    id: '28-enriques-systems-classification',
    cote: '28',
    pages: '4–10',
    kind: 'mathematical',
    claim:
      'The connected algebraic subgroups of Cr_{n,k} containing a split n-dimensional torus are classified up to conjugacy by « systèmes d’Enriques » (R ⊂ M, ρ : R → M*) under five axioms, the fifth carrying the condition binom(n,i) ≠ 0 in k; this is matched by Demazure 1970, which uses the same name and the same axioms.',
    basis:
      'Page 5 sets the three axioms on the pseudo-projector f; pages 6–9 extract (x_α, ρ_α) with ⟨ρ_α, α⟩ = 1, the reduction to PGL(2), the GL(2) homomorphism and coroot ρ_α − ρ_{−α}, the commutation proposition with its corollaries and the case (c) chain; page 10 lists axioms 1)–5) and states the existence theorem in one line.',
    ours:
      'The reading supplies n = −⟨ρ_α, β⟩ in axiom 5) from page 9; Demazure’s (Sat′) and (p-Sat) state it with that n, so the supply agrees with print. Demazure’s Définition 1 has only (SE 1)–(SE 3) plus the cycle condition (S); the page’s axiom 4) is his weaker (S′), and his Prop. 1 and 2 show (S′) with (Sat′) or (p-Sat) gives a saturated or p-saturated system — the page’s axiom 5) with i = n already implies his (S″), so the page’s five axioms define the same class. This equivalence is the pass’s own check against the printed text, not a statement of the folder. The reading’s sentence that the chain « se troue » in characteristic p concerns the root set of the group, which Demazure’s (p-Sat) confirms.',
    literature: [
      'M. Demazure, « Sous-groupes algébriques de rang maximum du groupe de Cremona », Ann. Sci. ÉNS (4) 3 (1970), 507–588: introduction pp. 507–509; §2 n° 3 Déf. 2 (système d’Enriques associé à (G, T, f)), n° 4 Prop. 3 (commutation of U_α, U_β), n° 5 (théorème d’isomorphisme); §3 n° 1 Déf. 1–3, (S′), (Sat′), (p-Sat), Prop. 1–2 and corollaries (pp. 544–547); §4 n° 7 for existence',
      'H. Umemura, « Sur les sous-groupes algébriques primitifs du groupe de Cremona à trois variables », Nagoya Math. J. 79 (1980): description of Demazure’s bijection with Enriques systems (search-result summary only, not read)',
    ],
    status: 'matched',
    settle:
      'Nothing left to settle on the mathematics: the classification, the name, the axioms and the characteristic-p condition are in Demazure 1970 §§2–3, and the existence theorem the page states without proof is proved there in §4 n° 7. A reader may compare the page’s axiom 5) with (p-Sat) line by line.',
  },
  {
    id: '28-torus-extension-stable-rationality',
    cote: '28',
    pages: '4',
    kind: 'mathematical',
    claim:
      'Every split torus of a given dimension in Cr_{n,k} lies in an n-dimensional one if and only if every field K whose purely transcendental extension of total transcendence degree n is pure over k is itself pure over k; this is matched by Demazure 1970, §1 n° 6, Cor. 1 to Prop. 11.',
    basis:
      'Page 4, Cor. 1 after the proposition X ⇢ T × Y, with the bracketed NB « OK si d = 0, d = 1, d = 2 (Castelnuovo) [car. nulle], d = n [k alg. clos]. Marche si n ≤ 3 ». Both members of the equivalence are partly illegible (\\ill{} in a) and b)).',
    ours:
      'Demazure’s print indexes d as the torus dimension and writes L(t_1, …, t_d) pure of transcendence degree n; the page writes « K/k de deg. tr. d » with K[t_1, …, t_{n−d}], so its d is the transcendence degree of the quotient, while its a) says G_m^d. The reading keeps both « G_m^d » and « degré de transcendance d », which is inconsistent with its own gloss (K the function field of Y, of dimension n − d); the pass reads the page’s d in b) and in the NB as the dimension of the quotient. On that reading the NB’s d = 2 case (Castelnuovo) goes one step beyond Demazure’s printed remark, which names only d = 0, d = n and the Lüroth case; the pass notes, as its own step, that over an algebraically closed field q and P_2 are stable birational invariants, so the Castelnuovo–Zariski criterion settles that case in every characteristic and the page’s « car. nulle » is a precaution, not a necessity — this contradicts the reading’s footnote, which says the restriction is not precautionary. The reading’s footnote that the first counterexample is a 3-dimensional torus in Cr_n for n ≥ 4 does not follow either: Popov reports (n−3)-dimensional maximal tori in Cr_n for every n ≥ 5.',
    literature: [
      'M. Demazure, Ann. Sci. ÉNS (4) 3 (1970), introduction p. 508 (condition (C), Lüroth, Zariski’s conjecture) and §1 n° 6, Cor. 1 and Cor. 2 to Prop. 11 with the Remarque (pp. 524–525)',
      'V. L. Popov, « Some subgroups of the Cremona groups », arXiv:1110.2410, abstract and version comments only (maximal tori of dimension n − 3 in Cr_n for n > 4); the body was not read',
      'A. Beauville, J.-L. Colliot-Thélène, J.-J. Sansuc, P. Swinnerton-Dyer, « Variétés stablement rationnelles non rationnelles », Ann. of Math. 121 (1985), cited by the reading, not opened in this pass',
    ],
    status: 'matched',
    settle:
      'The equivalence is printed in Demazure 1970. What remains is the edition’s: a person checks on the facsimile which index the page’s b) carries, corrects the reading’s footnotes on « car. nulle » and on the dimension of the first non-extendable torus against Popov’s theorem, and decides whether the NB’s « marche si n ≤ 3 » needs Castelnuovo at all in the printed indexing.',
  },
  {
    id: '28-demazure-ihes-1970-notes',
    cote: '28',
    pages: '1–10',
    kind: 'codicological',
    claim:
      'The folder’s two runs, headed « Demazure 5.1.1970 » and « Demazure 12.2.70 », follow the order and content of Demazure 1970 §§1–3 and fall within the dates Demazure gives for his exposés at the IHÉS, « janvier-février 1970 ».',
    basis:
      'The two headings are in his hand; the sequence pseudo-morphisms, Psaut/Baut, pseudo-operations, rigidification, tori, Cor. 1 on stable rationality, pseudo-projector f with three axioms, rank one, PGL(2), GL(2), commutation, conjugacy, Enriques systems matches Demazure’s §1 n° 1–6, §2 n° 1–5 and §3 n° 1 in that order.',
    ours:
      'The identification with the IHÉS exposés is the pass’s, from Demazure’s introduction (p. 509); nothing on the leaves names the occasion. It corrects the reading’s résumé, which says the theory is seen « au moment où elle est exposée pour la première fois »: Demazure says the main results were announced at Nancy in June 1969.',
    literature: [
      'M. Demazure, Ann. Sci. ÉNS (4) 3 (1970), p. 509 (« annoncés au colloque organisé à Nancy en juin 1969 […] et exposés à l’I. H. E. S. en janvier-février 1970 »), and the section headings of §§1–3',
    ],
    status: 'candidate',
    settle:
      'An IHÉS seminar listing or Demazure’s own record for January–February 1970 giving the dates 5 January and 12 February would settle it; the facsimile is not needed, the two headings being read without \\uncertain{}.',
  },
  {
    id: '41-irreducible-components-etale-criterion',
    cote: '41',
    pages: '3, 8–10',
    kind: 'mathematical',
    claim:
      'For f : X → Y of finite type which, at each generic point of a component of a fibre, is locally universally open and quasi-finite over an affine space Y[t₁, …, t_{n−1}] (no flatness and no geometric reducedness of fibres assumed), the folder states that an étale separated Y-scheme M whose geometric points over y index the geometrically irreducible components of X_ȳ exists if and only if, over every trait, no component of the generic fibre specialises to two distinct components of the special fibre and distinct components do not meet in one specialisation; and that M is moreover finite if and only if every generic component specialises to some special component.',
    basis:
      'Page 3 defines monogène sections and the functor F they form, and gives the bijection M(Ω) → Irr(X ⊗_Y Ω) as the criterion for (M, φ_M) to represent it; page 8 states the Théorème with its hypothesis and conditions (ii) and (iii); page 9 adds the finiteness condition under a word read « Cor. » with doubt; page 10 says the first condition alone gives a non-separated étale M. The statement rests on \\ill{}: the theorem’s first condition is illegible, condition (iii) of page 8 is fragments only, the hypotheses on the trait (« fini et plat », « V° fini ») are fragments, and no proof is on the leaves.',
    ours:
      'The sense of page 8’s condition (iii) is the reading’s, built from scattered legible words; the index n − 1 is undefined on the leaf; the explanation of the conditions as the three valuative criteria (étaleness, separation, existence) is the reading’s, as is the reinterpretation of page 9’s « ouvert étale » as finite étale. This pass (Opus 5.5, on a reading made by Opus 5) reads the folder as the reading does, with one emphasis of its own: once an étale M exists, the separation and finiteness conditions are the valuative criteria applied to M and are standard; what would not be standard is the existence statement under this hypothesis, which is also the part the leaves leave least legible.',
    literature: [
      'M. Romagny, « Composantes connexes et irréductibles en familles », Manuscripta Math. 136 (2011), arXiv:0912.2605 — §1 (introduction), 2.1.1–2.1.2, 2.2.4, Théorème 2.5.2, Remarques 2.5.3, 3.2.1, 3.3 (Irr(X/S)^f étale et séparé): Irr(X/S) is shown representable by an étale quasi-compact algebraic space for X flat, of finite presentation, with geometrically reduced fibres; Remark 2.5.3(2) shows π₀(X/S) non-separated over a strictly henselian trait. No valuative criterion for separation or finiteness of Irr(X/S) in terms of specialisation of components was found in the parts read, and nothing under universal openness without reducedness.',
      'Stacks Project, Section 37.27 (Tag 0553, irreducible components of fibres) and Lemmas 37.74.1–2 (Tags 0F30, 0F32, universally open morphisms), via search results only — not read in full.',
    ],
    status: 'unsearched',
    settle:
      'First make the statement legible: re-read pages 8–10 against the facsimile with /transcribe-grothendieck, especially the theorem’s first condition and condition (iii). Then read Romagny 2011 §2–3 in full, and EGA IV 15.5–15.6 and 14.5, for an existence result for the topological functor of components (generic-point sections, as on page 3) under universal openness without geometrically reduced fibres, and for a trait criterion for its separation. The status stays unsearched because the statement rests on illegible words, not because nothing was read.',
  },
  {
    id: '41-chapter-number',
    cote: '41',
    pages: '1',
    kind: 'codicological',
    claim:
      'The title leaf of folder 41 reads « Chap. VI », not the « Chap. V » of the archivists’ title, and its first line places the section in a paragraph on descent and its applications.',
    basis:
      'Page 1 of the transcription: « Chap. VI. Dans le § de la descente, …, applications », then two struck words « Construction », « Étude », and the underlined title « Morphismes étales associés à l’étude des composantes irréductibles d’un morphisme ouvert ». « descente » is \\uncertain{} and the word after it is \\ill{}.',
    ours: null,
    literature: [
      'Inventory title of cote 41: « Construction de morphismes étales (Chap. V) : notes manuscrites (s.d.) »',
      'Transcription transcripts/41/batch-01.fr.tex, page 1 (an Opus 5 pass from the facsimile, unchecked by a human)',
    ],
    status: 'unsearched',
    settle:
      'Read the chapter numeral on the facsimile of page 1 directly. If it is VI, compare with the plan of the Éléments announced in EGA I (Introduction), where a chapter VI on descent was planned, before saying anything about which work the section was drafted for — the folder itself does not say.',
  },
// Folder 43 — candidate entries from /find-novelty (Opus 5.5, claude-opus-5-5, on an Opus 5.5 reading of 2026-10-03).
// Most of the folder's statements are matches already footnoted in 43.modern.tex (Rosenlicht–Serre, Parshin–Beilinson adeles,
// Grothendieck pairing, Lichtenbaum's Brauer description of the Tate pairing, SGA 2 VI, Gabriel, Poitou–Tate) and are not listed.
  {
    id: '43-ext-ga-zp-perfection',
    cote: '43',
    pages: '165–169',
    kind: 'mathematical',
    claim:
      'Over an arbitrary base S of characteristic p, Ext¹_{S-gr}(𝔾_a, ℤ/pℤ) ≅ Γ(S, 𝒪^{p^{-∞}}), the global sections of the perfection colim(𝒪 → 𝒪 → …, x ↦ x^p), so the functor Ext¹(𝔾_a, ℤ/pℤ) is representable among perfect pro-schemes over S; this follows from a lemma identifying Ext¹_{S-gr}(G, Γ) with primitive classes in H¹(G, Γ) and from its invariance under universal homeomorphisms S_0 → S when Γ is étale and G has geometrically connected fibres.',
    basis:
      'Pages 166–168 state and prove the lemma (Ext¹ → H¹(G, Γ) injective, image the primitive classes, with the hypotheses in the margin as « 1° » and « 2° », citing « le livre de Serre, p. 183 »); page 168 states the invariance under S_red and under universal homeomorphisms; page 169 writes the formula for Ext¹(𝔾_a, ℤ/pℤ) and the representability. The formula and the invariance are legibly read. The word « parfaits » in « pro-schémas parfaits » is \\uncertain{}, and the parenthesis just before the formula, which seems to mention « l’hypothèse noethérienne », is mostly \\ill{}.',
    ours:
      'The reading supplies the explanation of why the perfection appears: modulo (F − 1), an additive polynomial Σ aᵢt^{pⁱ} reduces to a single term a·t with a in the perfection. Neither the page nor the reading writes out the proof of the formula itself, and the page does not say whether a noetherian hypothesis is needed.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check over a non-perfect field and over a general base: Serre, Groupes algébriques et corps de classes VII (the field case, and the p. 183 the page cites); Oort, Commutative group schemes (LNM 15, 1966); Demazure–Gabriel, Groupes algébriques III.6 and V; SGA 7 VII–VIII. Over a perfect field the formula reduces to the known Ext¹(𝔾_a, ℤ/pℤ) ≅ k, so the only possibly unrecorded part is the arbitrary base. One web query (2026-10-10) returned nothing that states the base-S form, but no source was read in full, so it does not count as a search.',
  },
  {
    id: '43-local-cohomology-concentration',
    cote: '43',
    pages: '70–74',
    kind: 'mathematical',
    claim:
      'For a regular local ring A of dimension d containing an algebraically closed field k, and a commutative algebraic group G over k, the Zariski local cohomology H^i_a(Spec A, G) at the closed point vanishes for i ≠ d, is G(K)/G(A) for d = 1, and is H^{d−1}(Spec A − a, U) for d ≥ 2, where U is the unipotent part of G. The functor G ↦ H^d_a(G) is therefore exact on locally trivial sequences, which is the input for the « local Jacobian » J_{A/k} defined on page 74.',
    basis:
      'Pages 70, 72 and 73 argue the result in full: the abelian quotient gives a constant, hence flasque, sheaf on Spec A − a; 𝔾_m drops out because A is factorial; the unipotent part is dévissé to 𝔾_a; and H^i(Spec A − a, 𝔾_a) = H^{i+1}_𝔪(A) vanishes outside i = d − 1. Page 71 is an earlier draft of a)–c). Page 73 adds that nothing changes on passing to Â. The formulas are legible, but nearly every word of the prose is \\uncertain{} and several clauses are \\ill{}.',
    ours:
      'The reading adds the hypothesis that k is algebraically closed, which the dévissage needs (split tori and a composition series of the unipotent part by 𝔾_a); the page only says « partie linéaire ». The page gives « factoriel » as the only reason for H^i(Spec A − a, 𝔾_m) = 0 for every i ≥ 1. The reading states this vanishing without giving the step for i ≥ 2, which the Zariski Gersten resolution of 𝔾_m supplies. The three conjectures of page 74 about J_{A/k} (« Je soupçonne ») are not part of this claim.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look for Zariski local cohomology with coefficients in a commutative algebraic group, and for a « local Jacobian » or « local Albanese » representing H^d_a(−) at a point of dimension d ≥ 2. Search in Serre, Groupes proalgébriques (1960) and Corps locaux; in Kato–Russell on Albanese varieties with modulus; and in the literature on higher local class field theory (Parshin, Kato). If H^d_a(G) or its representing pro-group appears there, mark matched.',
  },
  {
    id: '43-leaves-59-60-reversed',
    cote: '43',
    pages: '59–60',
    kind: 'codicological',
    claim:
      'Pages 59 and 60 are bound in reverse: page 60, which sets up ordered sets satisfying the chain condition and the rings A_c of saturated chains, comes first in the text, and page 59, which begins mid-sentence on « une multiplication », continues it with the graded ring A* and the element Θ.',
    basis:
      'Page 60 ends on « et satisfont les », after announcing pairings A_{c′} × A_c → A_{c′c}. Page 59 opens on an interlinear, partly struck passage and then on « une multiplication », and goes on to Θ² and the quotient by the two-sided ideal it generates. The transcription’s note at the head of page 59 already proposes the inversion.',
    ours:
      'The reading reads page 60 before page 59 and says so in a footnote. The transcription keeps the binding order.',
    literature: ['Transcription 43, batch 3 (batch-03.fr.tex), pages 59 and 60, and the note at the head of page 59'],
    status: 'candidate',
    settle:
      'A person checks the facsimile to see whether 59 and 60 are recto and verso of one leaf (the order would then be an accident of which side was numbered first) or two separate leaves bound in the wrong order.',
  },
  {
    id: '45-h1-surjectivity-dim-one',
    cote: '45',
    pages: '3–10',
    kind: 'mathematical',
    claim:
      'Over a field k with Br(k′) = 0 for every finite separable k′/k, H¹(k, G) → H¹(k, G′) is surjective (flat cohomology) for every epimorphism G → G′ of algebraic group schemes, not necessarily smooth, linear or with commutative kernel, by reduction to H² of commutative groups through normalisers of maximal tori and of Cartan subalgebras of radicial kernels.',
    basis:
      'Lemmas 1–5 (pp. 3–9) reduce the smooth case to tori, finite étale groups, abelian varieties and p-torsion unipotent groups, and the radicial case (Lemma 4) to commutative radicial kernels; Lemma 3 assembles them and the Théorème on p. 9 states the result. The statement line of p. 9 is itself partly unread (« Soit k un \\uncertain{corps} \\ill{} \\ill{} cd(k) ≤ 1 … \\ill{} épim. G → G′ de \\ill{} k »), and the argument of Lemma 4 on p. 8 is mostly \\ill{} and \\uncertain{}.',
    ours:
      'Much of the statement is the reading’s. It replaces the page’s « cd(k) ≤ 1 » by Serre’s « dimension ≤ 1 » and the page’s « extension radicielle » in Lemma 5 by « séparable »; it drops the page’s H^i(k, α_p) = 0 for all i (false for i = 1); it adds the commutativity and smoothness the corollary of Lemma 2 needs and the twisted forms Lemma 1 needs. And it records that the proof is incomplete: Lemma 4 invokes a conjugacy of Cartan subalgebras under the infinitesimal kernel that the page does not establish and that fails in general in characteristic p. As it stands the folder carries a reduction scheme, not a proof.',
    literature: [],
    status: 'unsearched',
    settle:
      'First decide whether Lemma 4 can be repaired (a conjugacy statement for Cartan subalgebras of a restricted Lie algebra under the infinitesimal group acting on it, or another way to reduce a non-commutative height-one kernel to commutative ones). Then check whether the statement for non-smooth G over imperfect fields is in Serre, Cohomologie galoisienne III.2 (Steinberg’s theorem and its corollaries), Borel–Springer 1968 (imperfect fields), or later work on fppf cohomology of non-smooth groups. For smooth connected linear G it is the matched case (Serre’s Conjecture I, Steinberg 1965; Borel–Springer 1968).',
  },
  {
    id: '45-bands-tsen-field',
    cote: '45',
    pages: '10–14',
    kind: 'mathematical',
    claim:
      'Over a C₁ (Tsen) field every algebraic band (lien), smooth or not, comes from a k-group scheme, and H²(k, L) then reduces to its neutral class — sketched by two « reduction principles » for gerbes of realisations (through the normaliser of a canonical class of subgroups, and through an embedding into a band already realised).',
    basis:
      'Pages 11–12 set up the gerbe of realisations of a band on a site, the sheaf of conjugacy classes of subgroups, and the two reduction principles; pages 13–14 apply them over a Tsen field, by cases (finite étale, radicial of height one with [K,K] = K, then positive dimension via maximal tori). Page 10 states the neutrality of H²(k, lien(K′)) for a form K′ of an algebraic group, with its proof almost entirely \\ill{}. On pp. 13–14 the cases are carried by many \\uncertain{} words, the case (ii) hypothesis reads « [K,K] = 1 » on the line and « [K,K] = K » in the margin, and the third case of b) is not read.',
    ours:
      'The reading calls pp. 13–14 a sketch, not a proof: case (ii) needs the infinitesimal Cartan subgroups to form a single conjugacy class defined over k (the same unproved conjugacy as Lemma 4, p. 8), and the third case of b) is not restored. It also declines to identify the page’s Π(K) with the band of inner automorphisms, so the exact sequence of the second principle is the page’s, unchecked. The reading’s own remark that it does not check whether published results cover non-smooth bands is what this entry turns into a question.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check Giraud, Cohomologie non abélienne (1971), ch. IV and VI, and Douai’s work on H² of bands over fields of dimension ≤ 1 (Douai 1976 and later; also Borovoi on bands over such fields) for the scope of the neutrality theorem: if they cover only smooth (or connected reductive) bands, the non-smooth case — finite radicial and non-reduced bands — is the candidate, and it stands or falls with the conjugacy step of case (ii).',
  },
  {
    id: '45-delzant-referee-letter-1961',
    cote: '45',
    pages: '71–74',
    kind: 'codicological',
    claim:
      'Pages 71–74 are a typed four-page commentary in Grothendieck’s voice, dated in ink 22.7.61, on an article by A. Delzant on quadratic forms — a referee-style letter, not the article — setting out a programme for the Grothendieck–Witt ring via H¹ and H² with ℤ/2 coefficients and their cup product, and for Stiefel–Whitney classes of quadratic modules over local rings, preschemes and in characteristic 2.',
    basis:
      'Typed title « Commentaires sur l’article de A. Delzant sur les formes quadratiques »; date « 22.7.61 » in ink top right of p. 71, the 6 written over another digit; first-person « mon séminaire » for the fundamental group of Spec(A) (SGA 1, 1960–61); Delzant addressed as « tu »; Greek letters and corrections inked into the typist’s blanks in the same blue ink as the date.',
    ours:
      'The attribution to Grothendieck rests on internal evidence (first person, the seminar, the hand of the ink corrections), argued in the transcription header. The identification of the article commented on with Delzant’s 1962 Comptes rendus note on Stiefel–Whitney classes of quadratic modules is the reading’s and is not stated in the letter, which names no title.',
    literature: [
      'Transcription 45, batch 4 (batch-04.fr.tex), header and pages 71–74',
      'Facsimile of page 71, date checked by Michel Hua on 27 September 2026 (as recorded in batch-04.fr.tex)',
    ],
    status: 'candidate',
    settle:
      'A person compares the letter’s content (λ-structures, the treatment of characteristic 2, the « programme minimum ») with Delzant’s 1962 CRAS note to confirm which text is being refereed, and checks whether this commentary is recorded or cited anywhere (Serre’s or Delzant’s papers, the Grothendieck–Serre correspondence).',
  },
// Folder 47: no pass run. transcripts/47/47.modern.tex header reads "% Pass: Fable 5.1 (claude-fable-5-1)"; find-novelty forbids any model running on a Fable reading (folders 1 and 47) until someone decides what should. Nothing searched, no entries.
// Folder 50 — find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, over a reading made by Opus 5 (claude-opus-5, 2026-09-02), under the skill's one-way exception.
// The pool is mostly matches and was dropped: the four conditions of p. 2 (Barsotti–Weil, theorem of the cube), Matsusaka's theorem (p. 4), the dim A ≤ dim Pic ≤ dim H¹ ≤ dim A sandwich (also folder 49), NS(A×B) ≅ NS(A) ⊕ NS(B) ⊕ Hom(A, B^∨), and the trace formula itself, which is Lang, Abelian Varieties (1959) V §3 Thm 1, Weil 1948 Thm 38, Mumford §21.
  {
    id: '50-axiomatic-trace-formula',
    cote: '50',
    pages: '6–10',
    kind: 'mathematical',
    claim:
      'The folder sets out an axiomatic frame for the endomorphism theory of abelian varieties — an additive category with a duality D, a subgroup N(A) of antisymmetric elements of Hom(A, D(A)), two cones N⁺ ⊂ N and N^> generating N, and a ℤ-valued r-linear intersection form I positive on N^> — in which the degree ν(α), the coefficients σᵢ(α) of ν(α + n), and the trace formula tr(α) = r·I(ξ^{r−1}, D_ξ(α)) / I(ξ^r) are stated as consequences without points, base field or divisors.',
    basis:
      'Pages 10, 9, 8 (from (d)) and 7 state the axioms (a)–(e) and the identities (1)–(3) for D_ξ(α, β) = (α+β)*ξ − α*ξ − β*ξ = φ_ξ(α′β + β′α); the head of page 8 and page 6 state the trace formula and its form for tr(αα′). The derivations are not written: the sentence in 7, 3) that justifies ν is mostly \\ill{}, the trace formula on page 8 follows « en particulier, \\ill{} », « r = dim(A) » and « str. pos. » are \\uncertain{}, and the Corollaire on page 6 is the bare word.',
    ours:
      'The reading supplies the compatibility condition D(κ_A)∘κ_{D(A)} = id, the leaf order 10, 9, 8, 7, 8-head, 6, and the Rosati positivity as the Corollaire. This pass reads three points differently from the reading. (1) The trace formula with D_ξ(α) in one slot follows from the axioms only if I is symmetric, which (e) does not say (it says r-linear); with that added, expanding I(((n+α)*ξ)^r), (n+α)*ξ = n²ξ + n·D_ξ(α) + α*ξ, gives it at once — this step is the pass’s own. (2) The reading’s proof of the Corollaire says α*ξ lies in the positive cone and (e) 2) makes I(ξ^{r−1}, α*ξ) > 0; but for α not an isogeny α*ξ is not in N^> (φ_{α*ξ} = ᵗα φ_ξ α is not a ℚ-isomorphism), and (e) 2) as the reading fixes it covers only N^>, so Rosati positivity does not follow from (a)–(e) as read; the page’s own « i.e. » with N⁺ would be what is needed in the last slot, at the cost of the E × E example the reading cites. (3) Propriété fondamentale 1 is « purement formel » only if N(A × B) contains every antisymmetric matrix, i.e. N is all antisymmetric elements; (c) says only « un sous-groupe ». None of this is on the page; it is the edition’s and this pass’s.',
    literature: [
      'Lang, Abelian Varieties (1959), Ch. V §3 Thm 1 — the trace formula, as cited in the survey below; not read directly',
      'Milne, « The Riemann Hypothesis over finite fields: from Weil to the present day », arXiv:1509.00797 — states the formula and Rosati positivity, citing Weil 1948 Thm 38; search snippet only',
      'Milne, « Polarizations and Grothendieck’s standard conjectures », Ann. of Math. 155 (2002) 599–610 — abstract only; polarizations on Tannakian quotient categories, not this additive frame',
    ],
    status: 'unsearched',
    settle:
      'The formula is matched; the question is the frame. Read Quebbemann–Scharlau–Schulte, « Quadratic and hermitian forms in additive and abelian categories » (J. Algebra 1979), Knus, Quadratic and Hermitian Forms over Rings, Ch. II, Kleiman, « Algebraic cycles and the Weil conjectures » (1968) §§1–3, and Saavedra Rivano, Catégories tannakiennes VI, for an additive category with duality plus cone and integer intersection form from which ν, σᵢ and the trace formula are derived; if found, mark matched. Separately, decide whether the Corollaire can be got from (a)–(e) at all, or needs I(ξ^{r−1}, η) > 0 for ξ ∈ N^>, η ∈ N⁺ ∖ {0}.',
  },
  {
    id: '50-leaf-order',
    cote: '50',
    pages: '6–10',
    kind: 'codicological',
    claim:
      'The blue-ink run on pages 6–10 lies in the folder essentially reversed: its reading order is 10, 9, 8 from (d), 7, the head of 8, then 6.',
    basis:
      'Three facts recorded in the transcription: « après d) » in his hand on page 7, the sheet lettered (d) being page 8; page 9 opens on the relative « qui d’ailleurs s’annule sur Im N(A) + Im N(B) », continuing the boxed map that closes page 10; and the paragraph at the head of page 8 continues the σᵢ of the foot of page 7, with (d) beginning lower on the same sheet.',
    ours:
      'The order is the reading’s reconstruction; the transcription records the three facts and explicitly leaves the order unresolved. The account of how page 8 was filled (top left blank, then returned to) is the edition’s inference.',
    literature: [],
    status: 'unsearched',
    settle:
      'Check on the facsimile (archives/batches/50/batch-01.pdf) whether pages 6–10 are separate sheets or recto/verso pairs, and whether the head of page 8 is in a visibly later stint of the same ink; a recto/verso pairing would constrain or overturn the order.',
  },
  {
    id: '53-geometric-irreducibility-criterion',
    cote: '53',
    pages: '9',
    kind: 'mathematical',
    claim:
      'An irreducible scheme X over a field k is geometrically irreducible as soon as some geometrically irreducible k-scheme Z maps to X with image not contained in the set of points through which several irreducible components of X_k̄ pass; a geometrically normal point of X_red in the image is one way to meet that condition.',
    basis:
      'Page 9, headed « Rectificatif sur critère d’irréductibilité géom. », states hypotheses a) and b), proves the result by a Galois-conjugation argument over a finite Galois extension, and gives x² + y² = 0 over ℝ, with Z the origin, as the counterexample when b) is dropped. In b) a struck word is \\ill{}, and « univ. » is an interlinear addition before a second struck \\ill{}. The statement does not rest on either.',
    ours:
      'The page does not write « X irréductible ». The proof uses it (« p(X′ᵢ) = X »), and the modernised reading supplies it, since without it the statement is false: two disjoint lines and a point on one of them. The hypothesis that makes the claim true is therefore the edition’s. This pass, run on Opus 5.5 over a reading also made on Opus 5.5, reads the page the same way the reading does.',
    literature: [
      'Orienting web search (2026-10-10) for EGA IV₂ §4.5 and geometric unibranchedness. It surfaced only M. Haiman’s synopsis of EGA IV §§4.1–4.6 and Poonen’s use of EGA IV 4.5.14 in a regular setting. Neither text was read with the page open.',
    ],
    status: 'unsearched',
    settle:
      'Read EGA IV₂ §4.5, where 4.5.13 is the connected analogue with a geometrically connected Z, together with the Stacks Project chapter « Varieties », sections on geometrically irreducible schemes and on geometrically unibranch points. Look for the irreducible analogue with a geometrically irreducible source Z and the condition on the image. If it is there, even only in the case where Z is a point, mark the entry matched.',
  },
  {
    id: '53-cancellative-monoid-is-group',
    cote: '53',
    pages: '21',
    kind: 'mathematical',
    claim:
      'A monoid scheme of finite presentation over a ring whose left and right translations are monomorphisms (for example one admitting a monomorphism into a group) is a group scheme; this is the folder’s reason why an affine monoid of finite type over a field embeds in M_n and not in GL_n.',
    basis:
      'Page 21 opens with the rectification called for by the June 1973 letter. The sentence giving the reason reads « tel que les translations à g (à dr.) \\uncertain{sont} \\ill{} \\ill{} … alors G est un objet \\uncertain{gr.-pr.} ». The word that qualifies the translations is illegible, and the conclusion is uncertain.',
    ours:
      'The modernised reading supplies both « monomorphismes », the illegible word, and the proof by Ax–Grothendieck (EGA IV 10.4.11, surjectivity of radicial endomorphisms). The statement is therefore the edition’s reconstruction around two unread words, not a sentence on the page. Quasi-compactness is essential: the constant monoid scheme ℕ has injective translations and is not a group.',
    literature: [
      'Orienting web search (2026-10-10) on algebraic monoids with injective translations. It surfaced M. Brion, « On algebraic semigroups and monoids » (arXiv 1208.0675), which states that an algebraic monoid without non-trivial idempotents is a group. The search did not show whether that text states the cancellative form; it was not read in full.',
    ],
    status: 'unsearched',
    settle:
      'First a person reads the illegible words of page 21 on the facsimile, since the claim rests on them. Then check Brion’s survey (arXiv 1208.0675, §2) and Putcha, Linear Algebraic Monoids (1988), ch. 3, for « a cancellative algebraic monoid is a group ». The classical form over an algebraically closed field is expected there. If only that form is found, what remains open is the form over an arbitrary ring with scheme-theoretic monomorphisms.',
  },
// Folder 56 — /find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, over a modernised reading made by Opus 5.5 (header: « Pass: Opus 5.5 (claude-opus-5-5), 2026-10-03 »). No mathematical candidate survived: the vanishing cycles of a quadric degeneration (pages 2–6) are the quadratic case of the Picard–Lefschetz formula (SGA 7 XV, as the reading footnotes), the cohomology and Chow rings of smooth quadrics (pages 19–34) are classical, and the boxed question of page 16 is answered by the contraction lemma; every departure the reading records is a repair of the page, not a statement beyond the literature. The one entry is codicological.
  {
    id: '56-sga3-xii-corrected-typescript',
    cote: '56',
    pages: '3, 5, 7, 11, 13, 15, 17, 20, 22, 24, 26, 28, 30, 32',
    kind: 'codicological',
    claim:
      'The folder keeps fourteen leaves of a typed state of SGA 3 Exposé XII (« Tores maximaux, groupe de Weyl, sous-groupes de Cartan, centre réductif… »), corrected in his hand, whose additions include a paragraph announcing that numbers 6 to 8 remove the affine hypothesis by a simpler method avoiding the representability theorems of Exp. XI n° 4, a replacement of Remarque 1.11’s typed ending by « il est possible (et sans doute avantageux) d’éliminer totalement les résultats de représentabilité de Exp XI N° 4 », and the marginal remark « Il est évident que le contenu des exposés XI, XII, XV, XVI devrait être complètement refondu »; whether these hand additions passed into the published Exposé XII has not been checked.',
    basis:
      'Batch 1 transcribes the title leaf (page 7, typescript p. 0) with the added paragraph in a quote block, one struck \\ill{} inside it, and the « refondu » remark as a \\marginal{} written bottom-to-top in the left margin, tied by a reference sign; page 11 carries the boxed, struck typed ending of 1.11 and its handwritten replacement. The legible typed page numbers are 0, 1, 11, 12, 21, 23, 26, 31, and the leaves are not filed in typescript order; the folder’s manuscript notes on quadrics are written on their versos.',
    ours:
      'The identification with the published SGA 3 Exposé XII is the reading’s, « à notre connaissance », without a number-by-number comparison. The inference that the verso notes postdate the typing, and the placing of the typescript in the 1962–64 seminar, are the reading’s, not the page’s. No facsimile was consulted.',
    literature: [
      'Transcription 56, batch 1 (batch-01.fr.tex), pages 5, 7 and 11',
      'Modernised reading 56 (56.modern.tex), « Les feuillets du tapuscrit de l’exposé XII de SGA 3 »',
    ],
    status: 'unsearched',
    settle:
      'Compare the leaves with SGA 3, Exposé XII as published (LNM 152, 1970, and the 2011 Gille–Polo re-edition): whether its introduction carries the paragraph on numbers 6 to 8 and the « refondu » remark, whether Remarques 1.11 ends with the handwritten sentence, and whether the numbering 1.5–1.17, 2.2–2.3, 4.3–4.4 matches. If all are there, the leaves are a fair-copy state of the published text and the entry is matched; if not, it records an unpublished state. Nothing here dates the mathematics.',
  },
// Folder 89 (Opus 5.5 pass on an Opus 5 reading): no entry qualifies — every statement the folder establishes is a match to textbook material (D6 ≅ S3×Z2, Coxeter presentation of S3, AGL/affine plane over F3 with its four parallel classes, dihedral group of the square vs monomial GL2(F3), u∧v=v∧w=w∧u ⇔ u+v+w=0 by elementary linear algebra, two orientations of a connected cycle graph); the G ≅ S3×S3 answer, the I↔II link and the (13) check are the edition's own, not the page's; the rank-2 reconstruction of pp. 15–18 is announced but not established (only property a) written), and no codicological anomaly beyond pages 8 and 20 breaking off, already recorded in the transcription. Nothing searched externally; the pass's own check of G = N × M on the Z/3 × {1,2} model agrees with the reading.
  {
    id: '105-interval-anodyne-generators',
    cote: '105',
    pages: '11–17',
    kind: 'mathematical',
    claim:
      'In a topos with the monomorphisms as cofibrations, the folder generates the trivial cofibrations from the pushout-products h(i₀, I, ε) = i₀ ⊠ (ε : e → I) of monomorphisms with the section of W-aspheric intervals, shows the resulting classes are stable under pushout-product, and reduces TF ⊂ W to the single axiom that Ω → e (the Lawvere object, a separating injective interval) is universally in W — a construction that is in the published literature.',
    basis:
      'Pages 11 and 13 define (TC)₀ as the h(i₀, I, ε) for a « bunch » of intervals and compute the pushout-product on generators (« donc OK »); page 15 states that TF ⊂ W amounts to « (L → e) ∈ UW » for the Lawvere object, with the marginal « but this is always so, because the [Lawvere] object is injective !!! »; pages 15–17 list the axioms (1)–(5) under which W̃ ⊂ W.',
    ours:
      'The reading supplies the passage from generators to TC (saturation argument, pp. 11–13), the proof of both directions of the equivalence on page 15, and the requirement that the factorisation used on page 17 be the cellular one; the page states these without argument. « Vérifier », « OK », « really » and « Lawvere element » are \\uncertain{} in batch-01/02. This pass agrees with the reading.',
    literature: [
      'nLab, « Cisinski model structure » (read 2026-10-10, first two-thirds of the page): reports, after D.-C. Cisinski, Les préfaisceaux comme modèles des types d’homotopie, Astérisque 308 (2006), the Lawvere segment Ω with endpoints ⊤, ⊥ as a separating segment (Example 1.3.8 there), classes of anodyne extensions generated from a small set of monomorphisms and required to contain the pushout-products (I ⊗ K) ∪ ({e} ⊗ L) → I ⊗ L for monomorphisms K ↪ L (§1.3, Prop. 1.3.11), and cofibrantly generated model structures on a topos whose cofibrations are the monomorphisms. Astérisque 308 itself was not opened.',
      'nLab, « Lawvere interval » and Joyal’s CatLab, « Cisinski’s theory » (search snippets and the CatLab page, 2026-10-10): the subobject classifier is injective, so the Lawvere interval is a fibrant resolution of the terminal object in any Cisinski model structure; trivial fibrations are the maps with the right lifting property against all monomorphisms. Cisinski, Théories homotopiques dans les topos, J. Pure Appl. Algebra 174 (2002), 43–82, is cited there and was not opened.',
    ],
    status: 'matched',
    settle:
      'Nothing left to decide about novelty: the construction is Cisinski’s anodyne extensions on the Lawvere segment. What remains is bibliographic — cite Astérisque 308 §1.3 and JPAA 174 by exact number after reading them, and check whether axioms (1), (3), (4) of pages 15–17 coincide with Cisinski’s definition of a localiser on a topos (2002), which would make the match exact rather than by construction.',
  },
  {
    id: '105-derivator-crible-excision',
    cote: '105',
    pages: '42–45',
    kind: 'mathematical',
    claim:
      'For any derivator 𝔻 and any small category X covered by two open sieves U, U′, the folder derives from the cartesian square γ = k_*(φ̄_* ξ) that if U ∩ U′ → U′ is a 𝔻-cohomological equivalence (in W_𝔻), then so is U → X — half of axiom W7 for W_𝔻, obtained from the derivator axioms alone.',
    basis:
      'Page 45 builds the split cofibred category X̄ = 𝒢_Ψ(X) over Ψ = {0 < a, 0 < b}, computes φ̄_*(ξ) fibrewise because φ̄ is proper, and reads the restriction square of H•_𝔻(−, ξ) as the cartesian square k_*γ₀; « i₀* iso ⇒ i* iso » for all ξ gives i₀ ∈ W_𝔻 ⇒ i ∈ W_𝔻. The identification γ(1,1) ≃ H•_𝔻(X, ξ) carries the marginal « à vérifier (ou à mettre comme axiome sur les dérivateurs) », and the transcription (batch-03.fr.tex, page 45) has \\uncertain{} and \\ill{} words in the setup (« au même », « cofibrée scindée », « fibre par fibre ») and an \\ill{} at the step « e → Q ».',
    ours:
      'The reading supplies why α : X → X̄ is in W_𝔻 (a retraction r with αr ⇒ id, so α is a homotopy equivalence of categories) — the step that settles the page’s « à vérifier » — and the definition of W_𝔻, which is not on these pages but read off their use; it also corrects the page’s « i₀* iso ⇔ i* iso » to ⇒ only. Without the edition’s step the page’s argument is incomplete at exactly the point it flags. This pass notes that the statement would follow if W_𝔻 is a basic localiser closed under homotopy cobase change, and the sieve square is homotopy cocartesian (Thomason), which the reading footnotes; that derivation is this pass’s, not checked.',
    literature: [
      'D.-C. Cisinski, « Le localisateur fondamental minimal », Cahiers de topologie et géométrie différentielle catégoriques 45 (2004), 109–140 — abstract and introduction read (numdam scan, 2026-10-10): « every cohomological theory on small categories defines canonically a basic localizor », and W_∞ is the smallest basic localiser. No statement about excision for a cover by two sieves was seen in the part read; the body was not read.',
      'Web search, 2026-10-10, for derivator cohomological equivalences as a fundamental localiser: a TAC vol. 20 no. 17 paper is reported by the search summary to state (§3.7) that the 𝔻-equivalences of any derivator form a fundamental localiser; the PDF could not be fetched (HTTP 503) and was not read.',
    ],
    status: 'unsearched',
    settle:
      'First have someone read page 45 against the facsimile where the transcription has \\ill{} and \\uncertain{} in the setup. Then check Grothendieck’s Les Dérivateurs (Künzer–Malgoire–Maltsiniotis edition) and Cisinski, Astérisque 308 ch. 4–6 and « Propriétés universelles et extensions de Kan dérivées » (TAC 20, 2008), for a statement that W_𝔻, or every basic localiser, satisfies this excision for a cover by two sieves; if it is there, or follows in one line from a stated stability of basic localisers under homotopy pushouts, mark matched.',
  },
  {
    id: '105-french-run-missing-opening',
    cote: '105',
    pages: '42–52',
    kind: 'codicological',
    claim:
      'The French run on axioms W7, W8 and « Der 6 » (pages 42–52) is paginated 6 to 18 in his hand and opens on the struck end of an argument begun earlier; its pages 1–5, where the axioms W1–W8 and Der 1–Der 5, 5′ it cites would presumably be stated, are not in the folder.',
    basis:
      'The transcription (batch-03.fr.tex, header and note to page 42) records his pagination 6 (page 42) to 18 (page 52, number circled) and the struck « q ∈ W ssi q_U ∈ W cqfd » at the top of page 42; W7 and W8 are invoked by number and never stated on the pages present.',
    ours:
      'The reading repeats the transcription. This pass searched the other transcribed folders of the project (transcripts/*/*.tex) for « W7 » and « Der 6 » and found them only in folder 105; untranscribed folders were not searched, and nothing was checked against the facsimile.',
    literature: [],
    status: 'unsearched',
    settle:
      'Look for leaves paginated 1–5 in his hand on W-axioms for classes of functors tested on W_𝔻 in the untranscribed folders of the fonds (folder 104, the other transcribed folder near it, has neither « W7 » nor « Der 6 »); and compare the axioms the run uses with the localiser axioms of Pursuing Stacks and of Les Dérivateurs to identify which list W7, W8 belong to.',
  },
// Folder 109 — /find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, over a modernised reading made by Opus 5.5 (header: « Pass: Opus 5.5 (claude-opus-5-5), 2026-10-03 »). The folder is editorial (preparation of Pursuing Stacks for print); it proves nothing, and its few mathematical points (Â as a closed model category, (Ord) as a modelizer, groupoids not a topos, Â not abelian) are matches or the edition's own checks, so no mathematical entry is proposed. Typescript checked: Pursuing Stacks, ed. M. Carmona with U. Buchholtz, arXiv:2111.01000v2 (2021), table of contents and marginal typescript page numbers, read by text extraction.
  {
    id: '109-section-titles-130-133',
    cote: '109',
    pages: '5, 7, 8',
    kind: 'codicological',
    claim:
      'Page 5 is a draft of the titles that §§ 130–133 of the Pursuing Stacks typescript bear, and pages 7–8 cite that typescript by the same section and page numbers, so the folder’s working sheets refer to Pursuing Stacks in its typescript numbering.',
    basis:
      'Page 5 reads « 130. A case for non-connected bundles (as components for semisimplicial models) », a palimpsest for 131 on the spherical functor S̃ and an extension of the notion of bundles, « 132. A crazy tentative wrong-quadrant (bi)complex for the homotopy groups of a sphere » (over a struck first state), « 133. Birth of Saleyman » with « Saleyman » \\uncertain{}. The typescript’s titles are « 130 A case for non-connected bundles », « 131 Tentative description of the spherical functor S̃ and “infinitesimal” extension of the basic notion of “bundles” », « 132 » identical to the page, « 133 Birth of Suleyman ». Page 7 « p. 72 S. 41 », « p. 73, 74 / S. 42 » and page 8 « modelizer 28 », « elementary modelizer 29 », « strict test category 33, 39 », « standard simplices / cubes 34 », « aspheric 35 » agree with the typescript (§ 41 begins at typescript p. 71, § 42 at p. 72; § 28 « Modelizers », § 29 « elementary modelizers », § 34 « Examples of test categories », § 39 « strict test categories »).',
    ours:
      'The concordance is this pass’s, from the Carmona edition, not from the folder. It supports two readings of the modernised text: the bare numbers of pages 1 and 8 are section numbers, and the typescript is Pursuing Stacks. It also bears on the transcription: the typescript writes « Suleyman », which the transcription’s note already allows (« la deuxième lettre du nom peut être un u »); the § 131 phrase read « multi\\uncertain{dimensional} » stands where the typescript has « “infinitesimal” ». Page 8’s « test category 27 » does not match a section title (§ 26 « The dawn of test categories », § 29 « Provisional definition of test categories »); the line may point to a first use rather than a definition.',
    literature: [
      'A. Grothendieck, Pursuing Stacks, ed. M. Carmona with U. Buchholtz, arXiv:2111.01000v2 (2021) — Contents (§§ 26–42, 130–133) and marginal typescript page numbers [p. 71], [p. 72]',
    ],
    status: 'candidate',
    settle:
      'A person reads page 5 against the facsimile for « Suleyman » and for « infinitesimal » under the § 131 palimpsest, and checks the titles against the typescript itself or the SMF edition (Documents Mathématiques 20, 2022) rather than a retyped edition.',
  },
  {
    id: '109-volume-plan-chapters',
    cote: '109',
    pages: '6',
    kind: 'codicological',
    claim:
      'Page 6 carries an authorial plan of the first volume of Pursuing Stacks in eight chapters (I, an appendix of letters to Breen, II–VIII), and a dependency diagram running to a ninth, where the Carmona edition of the typescript divides the text into seven chapters.',
    basis:
      'Page 6 lists « Chap I », « Appendice : Lettres à Breen » looped in after Chap I, « Chap II à VIII », then notes, glossary, two indexes and « Bibliographie (?) »; of the two dependency diagrams at the foot, the left has I–VIII, the right I–IX with VI isolated in both. The Carmona edition has Part I Take-off with an Appendix of the Breen letters, then II Test categories and test functors, III Homotopy structures and contractibility structures, IV Asphericity structures and canonical modelizers, V Abelianization I, VI Schematization, VII Abelianization II (§§ 133–140).',
    ours:
      'The comparison with the Carmona edition is this pass’s. Whether the seven chapter divisions of that edition are Grothendieck’s or an editor’s was not checked, so the discrepancy may be between two plans or between a plan and an editorial division. The placing of the Breen letters after Chap. I agrees with the typescript’s own note (§ 1, « reproduced as an “appendix” at the end of this chapter ») and with the Esquisse d’un programme (« [three] letters … as an appendix to Chap. I of volume 1 »).',
    literature: [
      'A. Grothendieck, Pursuing Stacks, ed. M. Carmona with U. Buchholtz, arXiv:2111.01000v2 (2021) — Contents, Preface (translation of a section of the Esquisse d’un programme, 1984) and § 1 margin',
      'R. Brown, « The origins of Alexander Grothendieck’s “Pursuing Stacks” », groupoids.org.uk/pstacks.htm — no chapter plan mentioned',
    ],
    status: 'candidate',
    settle:
      'Check the SMF edition (Documents Mathématiques 20, 2022, ed. G. Maltsiniotis) and the original typescript for the chapter headings and whether they are authorial; then say which of page 6’s two diagrams, if either, the typescript follows.',
  },
  {
    id: '109-correction-list-dates',
    cote: '109',
    pages: '16–37',
    kind: 'codicological',
    claim:
      'The folder holds an English correction list of the Pursuing Stacks typescript, pp. 1–557, by an unnamed correspondent, sent in instalments marked « Sent 19/12/83 » after typescript p. 100 and « Sent 6/2/84 » after p. 354, so pp. 1–354 had been read for English by 6 February 1984.',
    basis:
      'Page 16 opens « Errors in 1st 100 pages of notes + letter to Quillen »; page 20 carries « Sent 19/12/83 » after p. 100, page 28 « Sent 6/2/84 » after p. 354; the list runs without gap to p. 557, where it stops a third down page 37. Pages 20 and 27 are copies of earlier states of the following entries. The typescript’s own dates put p. 89 at 27.3 (1983), p. 343 at 7.7 and p. 555 at 22.10, so the corrections follow the writing by five to seven months.',
    ours:
      'The typescript dates are this pass’s, from the Carmona edition’s dated margins. The corrector is not named in the folder; the transcription records that the same hand wrote pages 9–10. The pass does not attempt an identification.',
    literature: [
      'R. Brown, « The origins of Alexander Grothendieck’s “Pursuing Stacks” », groupoids.org.uk/pstacks.htm — mentions corrections of the 1982 translation of the Breen letters by J.-L. Loday and L. Breen, not a correction list of the 1983–84 typescript',
      'A. Grothendieck, Pursuing Stacks, ed. M. Carmona with U. Buchholtz, arXiv:2111.01000v2 (2021) — front matter and Preface searched for a correction list; none found; dated margins used for p. 89, 343, 555',
    ],
    status: 'candidate',
    settle:
      'A person reads the two « Sent » dates on the facsimile, and checks the introduction of the SMF edition (Documents Mathématiques 20, 2022) and the Bangor correspondence for an account of who corrected the typescript’s English and when.',
  },
// Folder 117 — find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, over a reading also made on Opus 5.5.
// Candidate pool (pp. 1-24) was almost entirely matches already footnoted in 117.modern.tex (prederivator, Der 1-5,
// homotopy exact squares for (co)fibred functors, cofinality of a right adjoint, fibre sequence in pointed derivators).
// Dropped without an entry: (Hot 6), which the reading had to repair (false for ordinary localisations; counterexample
// the reading's own); the p. 20 L f_! argument, which fails as written; the p. 22 gluing condition, a desideratum
// (« on veut ») that the folder does not establish. One killed candidate is kept below.
  {
    id: '117-adjunction-equivalence-criterion',
    cote: '117',
    pages: '15–17',
    kind: 'mathematical',
    claim:
      'If f : (M, W) → (M′, W′) has a right adjoint g, f⁻¹(W′) = W and every counit fg(X′) → X′ lies in W′, then f and g induce inverse equivalences W_A⁻¹Hom(A, M) ≃ W′_A⁻¹Hom(A, M′) for every small category A, compatible with the f_! and f_* of the two theories.',
    basis:
      'Pages 15 and 17 (his pp. 6–7) state conditions (i) f⁻¹(W′) = W and (ii) fg(X′) → X′ ∈ W′, note that the same conditions pass to the diagram categories objectwise, and draw the adjunction between ℋ_W(A) and ℋ_W′(A); the conclusion after « Donc » is struck and the line after the diagram is struck and unread, so the page never writes that the induced functors are equivalences. The words « fonctoriel », « compatible » and « nullement » in the setting-up sentence are \\uncertain{} and two words there are \\ill{}; conditions (i) and (ii) themselves are read without doubt (batch-01.fr.tex, pages 15 and 17).',
    ours:
      'The reading supplies the two-out-of-three property for W′, without which g need not send W′ into W, writes the argument (g preserves weak equivalences by naturality of the counit; the unit is in W by the triangle identity) and writes the struck conclusion. Both readings were made on Opus 5.5; this pass agrees with the reading on the substance.',
    literature: [
      'N. Gurski, N. Johnson and A. M. Osorno, « Extending homotopy theories across adjunctions », arXiv:1508.00054 (version of 2016-12-07), §1, Definitions 1.4, 1.8, 1.10, Lemma 1.7 and Theorem 1.11, read through ar5iv on 2026-10-10: Theorem 1.11(c) — for Q ⊣ i between categories with weak equivalences, Q creates weak equivalences and the counit is a weak equivalence — implies that the adjunction is an adjoint equivalence of homotopy theories (unit and counit weak equivalences), hence an equivalence of localisations (Lemma 1.7). With Q = f this is the page’s hypothesis for A = Δ₀; the page’s extension to every A is the objectwise application of the same statement.',
      'M. Hovey, Model Categories (1999), Cor. 1.3.16 — the model-category form (a left Quillen functor reflecting weak equivalences between cofibrant objects, with derived counit a weak equivalence, is a Quillen equivalence); cited from memory, not re-read in this pass.',
    ],
    status: 'matched',
    settle:
      'Matched in Gurski–Johnson–Osorno, Theorem 1.11(c). What remains to check is only whether their « category with weak equivalences » (Definition 1.4 and before) includes two-out-of-three, the hypothesis the reading supplies; if it does, the match is exact for the edition’s statement, and the page’s statement is the same without that hypothesis written.',
  },
// Folder 1: no pass run. transcripts/1/1.modern.tex header reads "% Pass: Fable 5.1 (claude-fable-5-1)"; find-novelty forbids any model running on a Fable reading (folders 1 and 47) until someone decides what should. Nothing searched, no entries.
  // Folder 13 — find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, over a reading made by Opus 5 (claude-opus-5, 2026-09-19); run under the one-way exception of the skill. Disagreements with the reading are stated in `ours`.
  {
    id: '13-double-lattice-invariants',
    cote: '13',
    pages: '33–34',
    kind: 'mathematical',
    claim:
      'For a ⊗-category with a fibre functor T over k, a fibre functor T′ over an extension K, and a ⊗-isomorphism φ between them over a common extension L, the elements of V that lie in the K-structure T′(V) are exactly the invariants V^H of the k-algebraic subgroup H ⊂ G = Aut⊗(T) generated by the image in G of the closed image R ⊂ G_K of Spec(L ⊗_K L) → P ×_k P → G_K, (s, u) ↦ s⁻¹u — for arbitrary k ⊂ K ⊂ L and without a base point on the torsor P = Isom⊗(T_K, T′).',
    basis:
      'Page 33 sets up (G, P, φ ∈ P(L)), treats P trivial with φ = ξg and ġ ∈ G(L)/G(K), writes V ∩ T′(V) = {x ∈ V | g⁻¹x ∈ V ⊗ K}, and defines R as the closure of the image of (s, t) ↦ ts⁻¹; page 34 takes S = p(R_K) under p : G_K → G, H the subgroup it generates, states x ∈ V ∩ T′(V) ⇔ x ∈ V^H by faithfully flat descent, and redoes the construction for P arbitrary through the bitorsor map P ⊗_K P → G_K. The formulas are legible; the sentences linking them at the foot of page 33 and in the descent step of page 34 are overwritten, struck, or carry several \\ill{}, so the argument as written is a skeleton.',
    ours:
      'The reading supplies the connecting sentences the \\ill{} gaps leave out, writes T_K × T_K where the page has T_k × T_k, and restates the page’s T′(W) as T′(V) (footnoted). It also writes the corollary as « pleinement fidèle si et seulement si V^H = V^G pour tout V » where page 34 has « fid. plat », without a footnote: this pass agrees that full faithfulness is what is meant but notes the reading changed the word silently. A further point is this pass’s own, not the page’s or the reading’s: V^H = V^G for every V says that H is an epimorphic subgroup of G (Bien–Borel), not that H = G, so the corollary is weaker than « H = G » — a parabolic subgroup already passes it. The struck block on page 48 (« … mais cette condition n’est \\ill{} un k-gpe de Borel de G … ») may be the page noticing this, but it is struck and largely illegible and nothing is claimed from it.',
    literature: [
      'J.-B. Bost and F. Charles, Some remarks concerning the Grothendieck period conjecture (Crelle 2016; arXiv 1307.1045v2), Def. 2.2–2.4, Lemma 2.5, Rmk. 2.6 — torsor of periods generated by the Zariski closure of the period point, a torsor under a Q̄-subgroup H of GL(M_B ⊗ Q̄) that need not be defined over Q',
      'T. Kreutz, M. Shen and C. Vial, De Rham–Betti classes with coefficients (arXiv 2206.08618v3), §3, Prop. 3.1, Rmk. 3.2, Prop. 3.3, Example 3.4 — for K = Q̄ the smallest subtorsor containing the period point is the de Rham–Betti torsor of M ⊗ Q̄, so its group has the Q̄-de Rham–Betti classes as invariants; the statement fails over K ≠ Q̄',
    ],
    status: 'candidate',
    settle:
      'The Q̄-coefficient version (group of the smallest subtorsor over K = Q̄; invariants = Q̄-de Rham–Betti classes) is in Kreutz–Shen–Vial Prop. 3.1, so what remains is the page’s form: invariants in V itself of the k-subgroup H obtained by pushing R down along G_K → G, for an arbitrary tower k ⊂ K ⊂ L and an arbitrary tensor category. Read André, Une introduction aux motifs (2004) §7.5 and Huber–Müller-Stach, Periods and Nori motives (2017) ch. 13 for this k-rational form; if it is there, mark matched. Independently, check the descent step of page 34 (R ⊂ G_{x,K} ⇔ p(R) ⊂ G_x, which holds because G_{x,K} = p⁻¹(G_x)) against the facsimile’s illegible words before anything rests on it.',
  },
  {
    id: '13-double-niveau-de-rham-betti',
    cote: '13',
    pages: '47–48',
    kind: 'mathematical',
    claim:
      'The folder asks whether, over an algebraic extension k of ℚ, the functor M ↦ (T_DR(M) unfiltered, T_B(M) without Hodge structure, comparison φ) is fully faithful, reduces it to k = ℚ̄, and recasts it as whether V^G = V ∩ g(V̄) for every G-module V of the motivic Galois group, noting the rank-one (Tate) case works.',
    basis:
      'Page 47 states (4.1), its reduction to (4.2) over ℚ̄, the class ġ ∈ G(ℂ)/G(ℚ̄) with T_DR(M) = g(V_ℚ̄), and the inclusion V^G ⊂ V ∩ g(V̄) whose equality is the question; page 48 re-expresses x ∈ V̄ ∩ g(V̄) through the closure R̄ of T̄ × T̄ → Ḡ, then breaks off in a struck block. The « pour tout V » of page 47 is an \\ill{} on the page.',
    ours:
      'The reading supplies « pour tout V » where the page has \\ill{}, and identifies the page-48 group with the H of pages 33–34, which no leaf states. The marginal « Regardez notamment le cas des courbes elliptiques » is \\uncertain{} and not used.',
    literature: [
      'J.-B. Bost and F. Charles, Some remarks concerning the Grothendieck period conjecture (Crelle 2016; arXiv 1307.1045v2), §2.1–2.2.2 — de Rham–Betti realisation over Q̄, Grothendieck classes and full-faithfulness conjectures alongside Hodge and Tate; Conj. 2.12 citing Grothendieck 1966, note (10)',
      'T. Kreutz, M. Shen and C. Vial, De Rham–Betti classes with coefficients (arXiv 2206.08618v3), Conj. 4.1 and Lemma 4.2 (fullness of the de Rham–Betti realisation, reduction to K = Q̄), Thm. 5.4 (André, Bost, Wüstholz: full faithfulness for abelian varieties), citing André, Une introduction aux motifs §7.5.3',
    ],
    status: 'matched',
    settle:
      'Matched: the question is the fullness of the de Rham–Betti realisation, a consequence of the Grothendieck period conjecture, stated in Bost–Charles §2.2.2 and Kreutz–Shen–Vial Conj. 4.1, and proved for abelian varieties (KSV Thm. 5.4). Kept so the next reader does not search it again. What the page adds is only the group-theoretic form V^G = V ∩ g(V̄), which is the subject of 13-double-lattice-invariants.',
  },
  {
    id: '21-depth-sheaves-of-sets-pointwise',
    cote: '21',
    pages: '15–20, 27–28',
    kind: 'mathematical',
    claim:
      'For a sheaf of sets F on a locally noetherian « special » space, F → i_*i^*F is injective (resp. bijective) relative to a closed Y iff for every x ∈ Y it is so on the localisation X_(x) relative to {x}; the condition passes to smaller closed subsets; and for torsors under a sheaf of groups the restriction functor is faithful / fully faithful / an equivalence exactly when H^i_Y(F) = 0 for i ≤ 0 / ≤ 1 / ≤ 2.',
    basis:
      'Définition 1 (p. 15), Proposition 3 and Corollaire 4 (pp. 16–18), the maximal-point induction of pp. 19–20, Corollaire 10 (p. 27) and Proposition 9 (p. 28). The connecting prose of pp. 15, 17, 19 and 20 is largely \\ill{}; the statements and displayed formulas are legible, and the definition of « espace noethérien spécial » and of Loc_x on p. 15 is not.',
    ours:
      'The reading takes « spécial » to mean a spectral space (its footnote), lowers the ranges of Cor. 10 by one (the page writes i ≤ 1, ≤ 2, ≤ 3; p. 28 and the H²_Y on p. 27 support the correction), and reads the illegible exponent on p. 27 as 1. SGA 2 XIV 1.1 3° (prof_Y ≥ n iff H^p_Y = 0 for p < n) and 1.4 (prof ≥ 3 iff torsors extend) independently confirm the corrected ranges; this pass (Opus 5.5) agrees with the reading (Opus 5) on them.',
    literature: [
      'SGA 2 (Grothendieck, Cohomologie locale des faisceaux cohérents et théorèmes de Lefschetz locaux et globaux, 1962; recomposed edition arXiv:math/0511279), Exposé XIV by M. Raynaud, « Profondeur et théorèmes de Lefschetz en cohomologie étale », §1: Prop. 1.1 1°–3° (depth ≤ 2 for sheaves of sets via F → i_*i^*F injective/bijective, ≤ 3 for sheaves of groups, H^p_Y vanishing for complexes), Déf. 1.2, Cor. 1.3 (passage to a closed Z ⊂ Y), Cor. 1.4 (restriction of torsors faithful / fully faithful / equivalence), Déf. 1.7 and Théorème 1.8 (prof_Y(F) = inf_{y∈Y} prof_y(F), proved by taking a maximal point of the complement of the largest good open); read 2026-10-10',
    ],
    status: 'matched',
    settle:
      'Matched in substance: SGA 2 XIV §1 states and proves the same sequence (definitions of depth ≤ 2 for sheaves of sets and ≤ 3 for groups, stability under smaller closed sets, the torsor interpretation, the pointwise characterisation by a maximal-point argument) for the étale topology, with strict localisations where the folder uses the Zariski localisation X_(x). The Zariski form on spectral spaces is the same argument with the localisation in place of the strict localisation and was not looked for separately. Exposé XIV is headed « D’après des notes inédites de A. Grothendieck »; whether pages 15–28 of this folder are among those notes is a separate question that only a comparison of the two texts’ structure, numbering and examples could address, and nothing here asserts it.',
  },
  {
    id: '21-stack-p3-pointwise',
    cote: '21',
    pages: '21–26',
    kind: 'mathematical',
    claim:
      'For a fibered category over the opens of a noetherian spectral space (a stack, in the reading), the restriction functor to X − Y is an equivalence on every open iff, at every x ∈ Y, the induced functor on the Zariski localisation X_(x) → X_(x) − {x} is an equivalence — the pointwise criterion stated for an arbitrary fibered category rather than for torsors or étale covers.',
    basis:
      'Définition 6 (p. 21), the translation into Hom-sheaves (p. 22), the induced fibered category F_(x) (p. 23), Proposition 7 and Corollaire 8 (p. 24), and the proof of (ii) ⟹ (i) for P₃ by noetherian induction on a maximal point of Y and gluing over W ∪ U (pp. 25–26). The hypothesis « noeth. spectral » in Prop. 7 is \\uncertain{} on both words, the marginal note on p. 21 is mostly \\ill{}, and the identification of p. 23 is introduced by « j’imagine ».',
    ours:
      'The gluing of an object over W with one over U along W ∩ U on p. 26 needs effective descent for the covering {W, U}: the reading adds that the fibered category must be a stack, which Définition 6 does not say. The reading also corrects F(W) to F(V) on p. 22 and « en X » to « en x » in Prop. 7 (ii). The statement as entered here is therefore the stack version, which is the edition’s, not the page’s.',
    literature: [
      'SGA 2, Exposé XIV §1 (M. Raynaud, arXiv:math/0511279): Cor. 1.4 and Théorème 1.8 treat the pointwise criterion for torsors under a sheaf of groups and for étale covers (homotopical depth ≥ 3), not for an arbitrary stack; read 2026-10-10',
    ],
    status: 'unsearched',
    settle:
      'Look for the pointwise criterion for arbitrary stacks (not only torsors or covers) in J. Giraud, Cohomologie non abélienne (Grundlehren 179, 1971), chapters II–III on champs and their extension along an open immersion; in SGA 1 X §3 (purity) and SGA 2 X; and in the Stacks Project chapters on stacks and on depth/purity. If any states that, for a stack on a noetherian spectral (or locally noetherian scheme’s) space, i^* is an equivalence relative to Y iff it is so on each punctured localisation at points of Y, mark matched. The status stays unsearched rather than candidate because the only source read is SGA 2 XIV, because the stack hypothesis is the edition’s, and because the hypothesis on X rests on two uncertain words.',
  },
  {
    id: '21-typescript-section-2-and-printed-ega',
    cote: '21',
    pages: '3–13',
    kind: 'codicological',
    claim:
      'The typescript « 2. Généralités sur certains foncteurs de modules » (Prop. 2.1 to Remarques 2.17), intended by its own first line for Chapitre 0_III, may not have been printed in that form in the Éléments: whether its statements (tensoring an abelian category over a ring, the Eilenberg–Watts form 2.6, the representing module H = colim T(A_n), 2.14–2.16) appear in EGA 0_III or 0_IV has not been checked.',
    basis:
      'Page 3 proposes moving the number to « Chap. O_III » with « certains des sorites du par. 7 »; the wrapper carries « Notes pour Dieud. §9 »; the typescript itself proposes rejecting the whole number in a line struck at the machine on p. 13 (« Si on rejette tout ce numéro (comme il me semble raisonnable) ») and says of 2.17 that it will probably not be needed « dans ce Chapitre ».',
    ours:
      'The reading states that nothing was compared with the printed Éléments (its footnote on p. 3); this entry only turns that gap into a check. No collation was made in this pass either.',
    literature: [],
    status: 'unsearched',
    settle:
      'Collate pages 3–13 against EGA 0_III (Publ. Math. IHÉS 11, 1961, §§8–13) and EGA 0_IV (Publ. Math. IHÉS 20, 1964, §§14–23), and against EGA IV §5.9–5.10 for the depth material and the « §9 » of the wrapper. If any of 2.1–2.17 is printed there, record where and mark matched; if none is, the codicological claim stands as « drafted for Chapter 0, not found in print ».',
  },
  // Folder 23 — find-novelty pass, Opus 5.5 (claude-opus-5-5), 2026-10-10, on a reading made by Opus 5 (pass header 2026-09-21), under the 2026-09-23 exception. The pass does not read the folder differently from the reading on any point below; where it adds a mathematical remark of its own, `ours` says so.
  // Dropped as matches or as standard: the adjunction formula and discriminant (pp. 3–5); exp/log on bialgebras and derivations as infinitesimal automorphisms (pp. 8–16); the deformation and connexion torsors (pp. 18–32); the two characteristic-p counterexamples (pp. 34–35, textbook examples of regular-not-smooth and integral-not-geometrically-integral); Auslander–Buchsbaum (p. 59, named as such by the margin); the Rees depth/Ext criterion and prime avoidance (pp. 62–63); the regular vs Koszul-regular decision (pp. 52–53, the convention now in SGA 6 VII and in current texts); zero-dimensional and absolutely flat preschemes (p. 72); the (h_0) condition and π_1-surjectivity (pp. 74–79); the ∂-category (p. 84, one axiom only); the Picard Lefschetz conditions (p. 89, SGA 2); the graded-splitting proposition (pp. 95–98, a graded Nakayama / Hilbert-series criterion whose inequality the pages do not prove). Deligne's errata to EGA (0_IV 19.3.12, 19.5.6, IV 16.1.5) are corrections to a printed text, not candidates.
  // Three of the four entries concern Deligne's letter of 17 Oct. 1966, not Grothendieck's hand; the claims are about what the folder contains, whoever wrote it.
  {
    id: '23-deligne-three-letters',
    cote: '23',
    pages: '55–64',
    kind: 'codicological',
    claim:
      'The ten leaves under « Lettres Deligne » are three letters, not four: leaves 61–64 are pages 3–6 of the letter of 17 October 1966 whose pages 1–2 are leaves 59–60, and the three letters are filed in reverse date order (15 Dec., 29 Oct., 17 Oct.).',
    basis:
      'Transcription 23: leaf 60 is noted « page 2 de la lettre, paginée ainsi par Deligne » and ends on the construction of A′ = A[[T_i]]; leaves 61–64 carry Deligne’s own numbers 3–6, leaf 61 opens « Remplaçant A par A′ », and leaf 64, signed « P. Deligne », refers back to « la démonstration tordue donnée pg 2 » of the Tor/pro-completion statement that stands on leaf 60. No \\ill{} or \\uncertain{} touches the page numbers or the join sentence.',
    ours:
      'The join across batches 3 and 4 and the restored chronology are the modernised reading’s folder-wide inference (« Ce que seule une lecture d’ensemble peut dire », point 1 and 2); each batch only says the letter continues elsewhere.',
    literature: [
      'Transcription 23, batch 3 (batch-03.fr.tex), leaves 55–60',
      'Transcription 23, batch 4 (batch-04.fr.tex), leaves 61–64 and header',
      'Modernised reading 23.modern.tex, header points 1–2 and section XI',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile that leaves 61–64 carry the author’s numbers 3–6 in the same ink and hand as « 2 » on leaf 60, and that paper and ink of 59–64 agree; the dates of the three letters read on the facsimile settle the order.',
  },
  {
    id: '23-finite-normalisation-quotient-of-regular',
    cote: '23',
    pages: '86–88',
    kind: 'mathematical',
    claim:
      'For a noetherian domain A that is a quotient of a regular ring, the integral closure of A is finite over A if and only if A has only finitely many height-one primes 𝔭 with A_𝔭 not regular and, for each, the normalisation of A_𝔭 is finite over A_𝔭.',
    basis:
      'Leaf 88 states the Remarque and its proof starts there, continues on 87 and uses the lemma on (S_k) along finite morphisms on 86: an intermediate B finite over A normal at the 𝔭_i, then C = i_* i^* B̃ across a closed set of codimension ≥ 2, shown (S_2) and (R_1) by Serre’s criterion. The key words of the proof — « cohérent », « normale », « anneau », « module », « partout », « quotient » — are \\uncertain{} on leaf 87, and several connecting phrases on 87 and 88 are \\ill{}; the statement on 88 itself is clearly read.',
    ours:
      'The reading supplies the step the page brackets without argument — that A is universally catenary, so heights are preserved along the finite birational A ⊂ C — and the coherence of C rests on a sentence of leaf 88 whose middle is illegible. The statement is the page’s; two links of its proof are the edition’s.',
    literature: [
      'Web search, 2026-10-10 (one query): found nothing stating this criterion; the results (Stacks Project tag 0333, notes on Krull domains, arXiv 1506.08738) are background only and were not read further.',
    ],
    status: 'unsearched',
    settle:
      'Read EGA IV 6.11–6.12 and 7.8 (openness of S_k loci, Nagata rings, finiteness of normalisation), EGA IV 5.11 (coherence of i_* across codimension 2), Nagata, Local Rings, ch. V, Matsumura, Commutative Ring Theory §§ 31–32, and the Stacks Project chapter on Japanese/Nagata rings; if a criterion reducing finiteness of the normalisation to the height-one non-regular primes, under « quotient of a regular (or CM) ring », is in any of them, mark matched.',
  },
  // Folder 39 — find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, over a reading made by Opus 5 (claude-opus-5, 2026-09-13).
  // Pool reviewed and dropped as matches: Weierstrass division over a linearly topologised ring (pp. 18–19; Bourbaki AC VII §3 per the reading),
  // algebraic power series as the henselisation (p. 3; Artin approximation setting), formal Frobenius (p. 6), Hasse derivatives (p. 14).
  // Dropped as unsettled questions rather than statements: (H') ⇒ (H) (p. 3 margin) and faithful flatness of S_n over A_n (p. 12 margin).
  {
    id: '39-inverse-function-axioms-henselian',
    cote: '39',
    pages: '9–12, 14',
    kind: 'mathematical',
    claim:
      'Over an arbitrary commutative base ring k, a family A_n ⊂ k[[t_1,…,t_n]] containing the coordinates, closed under substitution of topologically nilpotent arguments, made of unital subrings, and closed under inversion of formal automorphisms of X_n (H) is closed under the implicit function theorem, and (A_n, A_n ∩ m_n) is a Zariskian henselian pair; adding closure under Hasse-coefficient extraction (D) puts A_n inside k_0[[t]], k_0 = A_0. Weierstrass division is never taken as an axiom.',
    basis:
      'Pages 9–10 state (I), (S), (R); page 11 states (H) and Cor. 1–2 (unit inversion, Zariskian and henselian pair); page 12 Cor. 3 derives the implicit function theorem by inverting (x, z) ↦ (x, P(x, z)); page 14 states (D) and the corollary A_n ⊂ k_0[[t]]. None of these statements rests on an \\uncertain{}; the \\ill{} on pages 11–12 are in struck passages.',
    ours:
      'Cor. 1 as the page proves it substitutes t_{n+1} = 1, which (S) forbids — the page objects to this itself in the margin. The reading proves it with (D) of page 14 (f⁻¹ is the t_{n+1}-coefficient of f⁻¹t_{n+1}), so the Zariskian property, and hence the pair statement, holds in the reading under (I)+(S)+(R)+(H)+(D), not under (H) alone as the page claims. The reading also supplies (S) in its strong form and the remark that a nilpotent-constant endomorphism with invertible Jacobian is an automorphism over a ring. This pass (Opus 5.5) agrees with the reading on these points and adds nothing.',
    literature: [
      'Denef–Lipshitz Weierstrass-system axioms (Math. Ann. 1984), consulted only as restated in arXiv:2207.03979 (Analytic Nullstellensätze and the model theory of valued fields): there the axioms are over a field and take Weierstrass division as primary — not the axiom list of this folder.',
      'Rolin–Speissegger–Wilkie, Quasianalytic Denjoy–Carleman classes and o-minimality, J. AMS 16 (2003) 751–777: abstract only; the closure conditions themselves were not read.',
    ],
    status: 'candidate',
    settle:
      'The search is thin and the statements are elementary consequences once the axioms are posed, so the question is whether this axiom list (inverse-function closure plus coefficient closure, over an arbitrary base ring, with no division axiom) is already in print. Read Denef–Lipshitz 1984 §1 and its positive-characteristic axioms, Rolin–Speissegger–Wilkie 2003 §1 (closure under composition, implicit functions, differentiation, monomial division), and the Fermat-theory / C^∞-ring axiomatics (Dubuc, Kock, Synthetic Differential Geometry). If any of them states this list over a ring, mark matched.',
  },
// Folder 42, find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, over a reading made by Opus 5 (claude-opus-5, 2026-08-23) — the one-way exception of 2026-09-23.
  {
    id: '42-sections-limit-of-local-rings',
    cote: '42',
    pages: '3–5',
    kind: 'mathematical',
    claim:
      'For a locally noetherian scheme X, Γ(X, 𝒪_X) is the inverse limit of the local rings 𝒪_{X,x} over the specialization order, obtained as a case of a general criterion: on a locally noetherian sober space, a sheaf whose stalk maps F_y → F_x are injective for y in a non-empty open of the closure of x has Γ(X, F) = lim F_x.',
    basis:
      'Page 3 states the Proposition and proves its Lemme 1 (the agreement locus is stable under generization and constructible, hence open); page 4 states Corollaire 1 and Lemme 2 (A noetherian, p prime: some f ∉ p makes A_f → A_p injective); page 5 completes Lemme 2. The governing word « injective » is compressed on the page and could be read « surjective »; the transcription settles it by the use made of it on pages 4–5, and several connective lines of pages 3–4 are \\ill{}.',
    ours:
      'The reading corrects the page’s gloss of ker(A → A_p) as « l’annulateur de A − p » and treats « d’où s_x = ξ_y » on page 3 as a slip for s_y = ξ_y; the constructibility criterion and « constructible + stable under generization ⟹ open » are named by the reading (EGA IV), not by the page. This pass (Opus 5.5) agrees with the reading’s mathematics here.',
    literature: [
      'D. Ferrand, « On the inverse limit of localizations », note dated February 2004 (perso.imj-prg.fr) — Proposition 3: if M → M_{p1} × … × M_{pn} is injective for finitely many primes, M → lim_{p ∈ Spec A} M_p is an isomorphism; for A noetherian and M of finite type the associated primes serve, which gives the affine case of Corollaire 1; read 2026-10-10',
      'D. Ferrand, « Sur les modules qui sont limite projective de leurs localisés », C. R. Acad. Sci. Paris 262 (1966), 609–611 — cited by the 2004 note as the announcement without proof, and its proof described there as extending each x(p) to a section on an open U and gluing, the route of pages 3–5; not read',
      'F. Nordström, Recovering a module from its local structure, Master’s thesis, KTH Stockholm, 2003 — cited by Ferrand 2004; not read',
    ],
    status: 'matched',
    settle:
      'Matched for the affine ring case (Ferrand 2004, Prop. 3 and the remark on noetherian rings; the scheme case follows by gluing over an affine cover). Still open: whether the general sheaf-theoretic criterion of page 3 (hypothesis (H) on an arbitrary sheaf over a locally noetherian sober space) is stated anywhere — read the 1966 Comptes rendus note and Nordström’s thesis for it. Kept as a killed candidate.',
  },
  {
    id: '42-reseau-functor-fully-faithful',
    cote: '42',
    pages: '1–2, 5–6',
    kind: 'mathematical',
    claim:
      'For S locally noetherian and X, Y locally of finite type over S with Y separated over S, S-morphisms X → Y are in bijection with homomorphisms of « réseaux d’anneaux locaux » p(X) → p(Y) over p(S) — order-preserving maps of the specialization posets with compatible local homomorphisms O_{Y,φ(x)} → O_{X,x}.',
    basis:
      'Page 1 defines the réseau (ordered set with an inductive system of local rings, each generization a localization of the more special ring) and the functor p; page 2 states full faithfulness on preschemes locally of finite type over S, its first proof crossed out; pages 5–6 give Corollaire 2 (a morphism is a coherent family of germs) and Corollaire 3 (a morphism is a homomorphism p(X) → p(Y)), the latter with an \\ill{} at the very noun « un \\ill{} de p(X) dans p(Y) ». The word « réciproque » in the definition of p_{xy} is \\ill{} on page 1 and reconstructed by the reading.',
    ours:
      'The separatedness of Y is the edition’s, not the page’s: the reading adds it to Lemme 3 and Corollaires 2–3, with the doubled-origin line as a counterexample to Lemme 3. The reading also reverses the page’s « q générisant p » to q ⊇ p, and supplies the surjectivity step through the EGA IV limit theorem lim_{U∋x} Hom_S(U, Y) ≅ Hom_S(Spec O_{X,x}, Y), which the page does not write. The page itself asks, beside Corollaire 3, whether the noetherian hypothesis on S is needed, and leaves it open.',
    literature: [
      'Ferrand 2004 note (as above) — modules only; no statement about morphisms of schemes or about posets of local rings; read 2026-10-10',
      'arXiv 2507.03139 (« An Alternative Model for Coherent Sheaves over Noetherian Schemes ») — abstract only: the topology of a noetherian scheme is recovered from its specialization poset, coherent sheaves described over it; no statement on morphisms seen',
      'Web searches (2026-10-10) for morphisms of schemes recovered from local rings along the specialization order: no source found stating it either way',
    ],
    status: 'candidate',
    settle:
      'Search EGA I (2nd ed., 1971) and EGA IV § 8 for a statement that Hom_S(X, Y) is the limit of Hom_S(Spec O_{X,x}, Y) over the specialization order for Y locally of finite presentation and separated, and the Stacks project chapters on limits of schemes; the searches so far were web searches and one note, which is thin. If the statement is there, mark matched.',
  },
  {
    id: '42-reseau-theorem-needs-hypothesis',
    cote: '42',
    pages: '2, 6',
    kind: 'mathematical',
    claim:
      'The folder asserts (page 2) that p is fully faithful on all S-preschemes locally of finite type over a locally noetherian S; as stated this fails without a separatedness (or quasi-compactness) hypothesis on the target, and what stands is the separated case of the entry 42-reseau-functor-fully-faithful.',
    basis:
      'Page 2 states « p : S_{0/S} → R_{/S} est pleinement fidèle » with no hypothesis on Y beyond local finite type, and Corollaire 3 on page 6 adds none; the reading flags the gap and leaves open whether the theorem itself survives without separatedness.',
    ours:
      'The counterexample is this pass’s own step (Opus 5.5) and goes beyond the reading (Opus 5), whose footnote says the pages do not settle the non-separated case and declines to settle it. Check: k a field with infinitely many elements, S = Spec k, X = A¹_k; Y is glued from copies V_0, V_1, V_2, … of A¹, V_n glued to V_m along A¹ minus the points a_n, a_m (a_n distinct closed points), so that each a_n is doubled; Y is locally of finite type, quasi-separated, neither separated nor quasi-compact. The réseau homomorphism sending a_n to the copy of a_n in V_n, every other point to V_0, with identity local rings, is order-preserving and compatible with generization; a morphism A¹ → Y realizing it would send the quasi-compact A¹ into finitely many V_n, while the copy of a_n lies in V_n alone, for every n. So p(X) → p(Y) is not in the image. Whether a quasi-compact non-separated Y (the line with one doubled origin) is also a counterexample was not checked.',
    literature: [],
    status: 'refuted',
    settle:
      'A reader should check the counterexample (in particular that the gluing data satisfy the cocycle condition and that the réseau homomorphism respects the definition of page 1), then decide between the two remaining repairs: Y separated, as the reading has it, or Y quasi-compact and quasi-separated.',
  },
  {
    id: '44-cartan-integrality-from-axioms',
    cote: '44',
    pages: '4',
    kind: 'mathematical',
    claim:
      'A cancelled leaf on root systems (page 4) appears to derive the integrality of the Cartan numbers ⟨γ_α, β⟩ from three axioms — Δ finite and generating a lattice P, reduced, stable under a symmetry S_a for each root — rather than taking it as an axiom; as far as the pass can check, those three axioms alone do not imply it, so whatever the page establishes must rest on the extra indivisibility its bracket invokes.',
    basis:
      'Page 4 sets axioms a)–c), realises every S_α through the invariant form Σ⟨x,a⟩⟨y,a⟩, writes S_α x = x − ⟨γ_α, x⟩α with γ_α ∈ P′^ℚ, and then « \\ill{} que l’on a en fait γ_α ∈ P′ », with a bracket attributing this to each α being indivisible in P because it can belong to a « système fondamental de racines ». The word governing the assertion and most of the bracket are illegible, so it is not known whether the page asserts, proposes to prove, or asks.',
    ours:
      'The reading (Opus 5) takes the page as asserting integrality as a consequence and calls the order « remarquable ». This pass (Opus 5.5) reads it differently and its own check says so: in P = ℤΔ with Δ = {±e₁, ±e₂, ±(e₁+e₂)/3, ±(e₁−e₂)/3}, axioms a)–c) hold (the reflections generate the Weyl group of type B₂), yet ⟨e₁^∨, (e₁+e₂)/3⟩ = 2/3, e₁ = 3·(e₁/3) is divisible in P, and e₁ still belongs to a simple system {e₁, (e₂−e₁)/3} — so neither « part of a fundamental system ⇒ indivisible » nor a)–c) ⇒ integrality holds without integrality already in hand. The counterexample is the pass’s own step, not the page’s or the literature’s.',
    literature: [],
    status: 'unsearched',
    settle:
      'First read the illegible word before « que l’on a en fait » and the bracket on the facsimile (transcription work, /transcribe-grothendieck): if the page only asks or proposes, the entry reduces to the reading’s footnote being too strong and should be withdrawn; if it asserts, mark refuted on the counterexample above. Independently, check whether the derivation of integrality from indivisibility of roots in the lattice they generate is stated in Bourbaki, Lie VI §1, or in SGA 3 Exp. XXI §1, and mark matched if so.',
  },
  {
    id: '46-semilocal-hilbert90-inertia',
    cote: '46',
    pages: '84–89',
    kind: 'mathematical',
    claim:
      'For a noetherian semi-local ring 𝒪 with a finite group Γ acting faithfully and transitively on its maximal ideals, and a finite 𝒪-algebra A (not necessarily commutative) with semi-linear Γ-action, the maps H¹(Γ, A*) → H¹(Γ_d, A_𝔪*) → H¹(Γ_i, A_𝔪*) to the decomposition and inertia groups are injective as maps of pointed sets, not merely of trivial kernel.',
    basis:
      'Page 84 states the injectivity; pages 85–86 pass to the completion, where Â* is induced from Γ_d, and descend by a density (Artin–Rees) argument on the kernel of u ↦ (u g(γ) − f(γ) γ(u))_γ; pages 86–89 reduce injectivity to the kernel by twisting the action by f, pass to Γ/Γ_i by inflation–restriction, and settle Γ_i = {e} by dévissage along (A/𝔪ⁿ⁺¹A)* → (A/𝔪ⁿA)* using H¹(Γ, k) = 0 and the field case of pages 82–83.',
    ours:
      'The reading supplies the hypothesis that A is finite over 𝒪 (the page strikes « de type fini »), corrects « Γ mod Γ_i » to Γ/Γ_d as the group permuting the factors of Â, replaces the struck arguments of pages 84–85 and 86–87, and makes explicit the passage from « trivial mod 𝔪ⁿ for every n » to trivial by Artin–Rees (« reproduisant un raisonnement déjà fait »). The step that Γ/Γ_i acts faithfully on the residue field of 𝒪^{Γ_i} is given on the page as known (« on sait que ») and holds in the normal/Galois setting; the reading admits it with the page, so the statement may need that hypothesis. The word « transitivité » on page 84 is an \\uncertain{} reading.',
    literature: [
      'M. Lorenz, K₀ of invariant rings and nonabelian H¹ (arXiv math/9808032, 1998) — main theorem, Prop. 2.6 and Lemma 3.6, consulted only through an automated summary of the HTML version: restriction–reduction maps to inertia groups appear there with trivial kernel, for S commutative; no general injectivity claim',
    ],
    status: 'candidate',
    settle:
      'Read Lorenz 1998 in full, Serre, Cohomologie galoisienne I §5.8 and the Lemme 1 it cites, and Chase–Harrison–Rosenberg (Memoirs AMS 52), and check whether injectivity (rather than trivial kernel) of H¹(Γ, A*) → H¹(Γ_i, A_𝔪*) for non-commutative finite A over a semi-local base, without assuming 𝒪 normal, is stated there; then decide whether the « on sait que » step needs a normality hypothesis. The single source here was read only in summary, so the status is weak.',
  },
  {
    id: '46-sylow-reduction-criterion',
    cote: '46',
    pages: '90–92',
    kind: 'mathematical',
    claim:
      'For 𝒪 local with Γ finite acting trivially on the residue field, and A a finite (𝒪, Γ)-algebra with A^Γ → A/𝔪A surjective, a class in H¹(Γ, A*) that dies in H¹(Γ, (A/𝔪A)*) and in H¹(Λ, A*) for a Sylow p-subgroup Λ (p the residue characteristic) is trivial; in particular reduction mod 𝔪 has trivial kernel when p ∤ |Γ|.',
    basis:
      'Page 90 states injectivity of H¹(Γ, A*) → H¹(Γ, (A/𝔪A)*) × H¹(Λ, A*); pages 91–92 prove triviality mod 𝔪ⁿ by induction, reducing each step to additive cohomology H¹(Γ, 𝔪ⁿA/𝔪ⁿ⁺¹A), using the hypothesis on Λ, an invariant lift v ∈ A^Γ of ε(u), and injectivity of restriction to Λ since [Γ:Λ] is invertible on A.',
    ours:
      'The hypothesis A^Γ → A/𝔪A surjective is the margin\'s, which is largely \\ill{} and \\uncertain{} (« plus généralement supposons que … surjectif »); the main text\'s hypothesis (Γ trivial on A/𝔪A) does not imply it for an imperfect residue field. The reading states only the trivial-kernel form, because the page\'s reduction of injectivity to the kernel by twisting needs the hypothesis to survive the twist, which the page does not check; the final passage to the limit is by Artin–Rees, made explicit by the reading.',
    literature: [],
    status: 'unsearched',
    settle:
      'Compare with Lorenz 1998 (arXiv math/9808032), Lemma 3.6 (reduction modulo the Jacobson radical has trivial kernel) and with the standard Sylow-restriction argument in Serre, Corps locaux / Cohomologie galoisienne; and re-read the margin of page 90 on the facsimile, since the hypothesis the proof uses rests on illegible words.',
  },
  {
    id: '46-homeomorphism-affine',
    cote: '46',
    pages: '17',
    kind: 'mathematical',
    claim:
      'A morphism of schemes f : T → S that is a homeomorphism is affine (the page states it for f of finite presentation; the hypothesis is not used).',
    basis:
      'Page 17 proves it by taking, around each s ∈ S, an affine neighbourhood U of the unique point over s and an affine V ⊂ f(U), and concluding that f⁻¹(V) is affine.',
    ours:
      'The reading drops the finite-presentation hypothesis and repairs the step « morphisme de schémas affines » (valid only for S separated) by taking V a principal open of an affine; several words of the page\'s proof are \\ill{}.',
    literature: [
      'Stacks Project, Tag 04DE (Lemma 29.45.4): a morphism that is a homeomorphism onto a closed subset of the target is affine',
    ],
    status: 'matched',
    settle:
      'Nothing left to decide: the statement, in a more general form, is Stacks Tag 04DE. Kept so that the lemma is not proposed again.',
  },
// Folder 49: pass run on Opus 5.5 (claude-opus-5-5) over a reading made by Opus 5 (claude-opus-5), under the 2026-09-23 exception.
// Everything else in the folder was dropped as a match, not written up: Pic^0 of a projective abelian scheme is an abelian scheme,
// R*f_*O_A = exterior algebra on R^1f_*O_A, phi_L an isogeny with finite flat kernel, Pic^tau open and closed, NS_{A/S} -> Hom(A, A^vee),
// and Pic^0 = primitive classes are all textbook (Mumford, GIT ch. 6 and Abelian Varieties §§8, 13; FGA exp. 236; SGA 6 XIII), and the
// reading's footnotes already say so.
  {
    id: '49-flatness-lemma-pushforward',
    cote: '49',
    pages: '3',
    kind: 'mathematical',
    claim:
      'A flatness criterion across a morphism: for φ : X → Y of finite type over a locally noetherian S, F quasi-coherent on X and flat over S, G coherent on Y, and G → φ_*F injective on the fibre over s at the points above y, G is flat over S at y.',
    basis:
      'Page 3 states this Lemme just after noting an injective map of local rings O_{A^vee_0,x′} → O_{A_0,x}, and before the smoothness of A^vee is claimed; the hypotheses F, G and the φ-morphism G → F are an interlinear addition, the letter in clause a) is overwritten and read \\uncertain{F}, and clause c) as retained is cut off by an \\ill{}, so the statement rests on the struck line « G_s → φ_{s*}(F_s) est injectif \\ill{} y ».',
    ours:
      'The reading takes the struck form of clause c) as the statement and supplies the application (X = A, Y = A^vee, φ = φ_L, F = O_A, G = O_{A^vee}), which the page never writes. This pass adds one point the reading does not make: as the reading phrases it (« un faisceau cohérent qui se plonge fibre à fibre dans un plat est plat »), the target φ_*F is not coherent over Y, so the usual module-level criterion, with source and target finite over the same local ring, does not apply directly; whether the page’s version needs an extra hypothesis (φ finite or quasi-finite at the points above y, say) has not been checked.',
    literature: [],
    status: 'unsearched',
    settle:
      'Compare with the local flatness criterion of EGA IV_3 §11.3 (around 11.3.7) and the Stacks Project, Lemma 10.99.1 (u : N → M, M flat over R, u ⊗ k injective ⇒ u injective with flat cokernel), to see whether either covers a target that is a pushforward along φ rather than a module over the same local ring; one web query pointed to the Stacks lemma but neither source has been read for this, so nothing is recorded under literature. First decide whether the statement holds at all without a finiteness hypothesis on φ at the points above y, and settle the reading of clause c) against the facsimile.',
  },
// Candidate findings for folder 52, written by /find-novelty on Opus 5.5 (claude-opus-5-5), 2026-10-10,
// on a reading and a transcription both made by Opus 5 (52.modern.tex and batch-01.fr.tex, 2026-09-13), under the 2026-09-23 exception.
// Not merged into src/content/findings.ts: other agents edit that file in parallel.
// The rest of the candidate pool was dropped as matches the reading already footnotes: injectivity of Aut(C) -> Aut(J) (classical),
// infinitesimal Torelli via Max Noether and its failure on the hyperelliptic locus (Oort-Steenbrink 1980), and the closure of the
// Jacobian locus by products recognised by an irreducible theta divisor (Matsusaka 1959, Hoyt 1963, Ran 1981).
  {
    id: '52-hyperelliptic-unique-isomorphism',
    cote: '52',
    pages: '13',
    kind: 'mathematical',
    claim:
      'Over a reduced base S all of whose fibres A_s are hyperelliptic Jacobians, two curves C, C′ over S with isomorphisms of polarised Jacobians φ : J⁰_{C/S} → A and φ′ : J⁰_{C′/S} → A are related by exactly one S-isomorphism u : C → C′ compatible with φ and φ′. No sign correction is needed, because −1 on the Jacobian comes from the hyperelliptic involution.',
    basis:
      'Page 13, Corollaire 3 (ii), states this with « réduit » underlined and « et un seul »; the leaf stops on the statement, without proof.',
    ours:
      'The hypothesis is half-illegible on the page. The transcription reads « Supposons que S soit réduit \\ill{} aux [struck] s ∈ S \\ill{} que A_s soit hyperelliptique », and the reading takes it to mean « at every point ». « isom. de \\ill{} \\ill{} relations polarisées » is read as isomorphisms of polarised Jacobians. The proof is entirely the edition’s: the closed subscheme Z ⊂ S cut out by Cor. 3 of page 4, classical Torelli up to sign, the sign fixed by the hyperelliptic involution, and then Z = S because S is reduced. This pass (Opus 5.5) agrees with the Opus 5 reading. It adds its own step: reducedness cannot be dropped. Over S = Spec k[ε], a first-order deformation of a hyperelliptic C in the kernel of the Kodaira–Spencer map of pages 8–9 has a trivial Jacobian deformation. It therefore gives a pair (C, φ), (C × S, φ′) whose only fibre is hyperelliptic, but no compatible u. That step is unchecked by a person.',
    literature: [
      'A. Landesman, « The Torelli map restricted to the hyperelliptic locus », Trans. AMS Ser. B 8 (2021), arXiv:1911.02084 — abstract and search summary only, not read: H_g → A_g is an immersion in characteristic ≠ 2 and a radimmersion over ℤ, with g − 2-dimensional tangent kernel in characteristic 2',
      'F. Oort and J. Steenbrink, « The local Torelli problem for algebraic curves » (1980) — cited from memory, not consulted',
    ],
    status: 'matched',
    settle:
      'Read Landesman 2021 and check two things. In characteristic ≠ 2, the immersion H_g → A_g gives (ii) for families in H_g, and the reduced hypothesis is then what puts a family with pointwise hyperelliptic fibres into H_g. In characteristic 2, where that map is only radicial, check whether the paper or Oort–Steenbrink states the reduced-base uniqueness of (ii) or something equivalent. If neither does, the characteristic-2 case reverts to candidate. A person also checks the hypothesis of (ii) on the facsimile.',
  },
  // Folder 55 — find-novelty pass on Opus 5.5 (claude-opus-5-5) over a reading made by Opus 5 (claude-opus-5), under the 2026-09-23 exception.
  // Dropped as matches or as the edition's repairs: the Stein-compact dictionary and Lemme A (Cartan A/B, Serre-style); the Frisch/Siu noetherianity
  // of Γ(K, O) as a statement about polycylinders; the typescript margins (dimension inequality with flat equality, EGA IV); the non-algebraic torus of
  // pages 16–17 (a classical kind of example, and the page's own lattice splits, so the working example is the edition's); the reading's counterexamples on page 14.
  {
    id: '55-lemma-b-identity-principle',
    cote: '55',
    pages: '13',
    kind: 'mathematical',
    claim:
      'For a quasi-compact ringed space with coherent structure sheaf and noetherian local rings, an abstract identity principle — for every coherent Ideal J and every point y of Y = Supp(O/J) with O_{Y,y} a domain, some open neighbourhood U of y in Y on which every section vanishing near y vanishes — is stated as making every increasing sequence of coherent subsheaves of a coherent sheaf stationary, hence (with Lemme A) Γ(X, O_X) noetherian.',
    basis:
      'Page 13 writes Lemme B with conditions (i), (ii), (iv), (v) and its corollary « A = Γ(X, O_X) est un anneau noethérien », then names compact analytic polycylinders as a case where they hold (« espace de Stein » struck for « polycylindre analytique (compact) »), with « premier espoir » in the margin. No proof is on the page.',
    ours:
      'The derivation of the corollary from the lemma, through Corollaire 1 of page 5 (Lemme A), is the reading’s; the page does not cite Lemme A. Neither the page nor the reading proves Lemme B, and the reading says it does not check that (i)–(v) suffice for an arbitrary ringed space. The pass’s own observation, not on the page: condition (v) fails for a Stein compact whose trace on an analytic set has infinitely many connected components accumulating at a point, so (v) appears to play the role of Siu’s finiteness condition — this is the pass’s step, unverified.',
    literature: [],
    status: 'unsearched',
    settle:
      'First decide whether (i)–(v) actually imply the conclusion for an abstract ringed space (a proof or a counterexample); then compare (v) with the hypotheses of J. Frisch, « Points de platitude d’un morphisme d’espaces analytiques complexes », Invent. Math. 4 (1967) 118–138, Th. I.9, and Y.-T. Siu, « Noetherianness of rings of holomorphic functions on Stein compact subsets », Proc. AMS 21 (1969) 483–489. Both were located by title in this pass but not read, so the status stays unsearched. If either states an identity-principle criterion of this form, mark matched.',
  },
  {
    id: '55-page-11-before-9',
    cote: '55',
    pages: '9, 11',
    kind: 'codicological',
    claim:
      'The manuscript notes on polynomial algebras are bound out of writing order: page 11 precedes page 9, the text breaking off on « Ceci prouve » at the foot of page 11 and resuming at the head of page 9.',
    basis:
      'Page 11 ends « … ce qui implique α. Ceci prouve … »; page 9 opens on an illegible word then « que le foncteur M ↦ M~ … est pl. fidèle … (en utilisant seulement la condition α) », which is what the α-argument of page 11 establishes. The leaves between them (10, 12) are unrelated typescript.',
    ours:
      'The transcription already flags the continuation as probable (« semble en être la suite ») and leaves the order as bound; the reading follows 11 then 9. The first word of page 9 is \\ill{}, so the join rests on sense, not on a word read across the break.',
    literature: ['Transcription 55, batch 1 (batch-01.fr.tex), pages 9 and 11, and their notes'],
    status: 'candidate',
    settle:
      'A person checks the facsimile: whether pages 9 and 11 are recto and verso of one sheet or separate leaves, and whether ink and hand agree across the join.',
  },
  // Folder 88, pass by Opus 5.5 (claude-opus-5-5) on a reading made by Opus 5 (claude-opus-5), 2026-09-13; exception of 2026-09-23.
  // Run 1 (pages 2-8) dropped: the Phi-question is answered wrongly on the page and the reading's Proposition is the edition's repair;
  // the order 2*lcm(n_ij) of sigma_{l-2}sigma_{l-1} on the flags of the Coxeter complex is a direct computation from the dihedral
  // stars of codimension-2 faces, not worth listing. One matched entry is kept so the next reader does not search run 2 again.
  {
    id: '88-standard-maps-quotients',
    cote: '88',
    pages: '10–15',
    kind: 'mathematical',
    claim:
      'Every simply connected quasi-regular map of type (p,q) is regular and determined by its type (the standard map C_{p,q}), Aut(C_{p,q}) is the extended triangle group Γ_{p,q} = Γ̂/⟨ρ_s^p, ρ_f^q⟩, C_{p,q} is a geodesic tessellation of the sphere, Euclidean plane or hyperbolic plane according as 1/p + 1/q is >, = or < 1/2, and every map of type (p,q) is the quotient of C_{p,q} by a subgroup of Γ_{p,q} acting freely, regular exactly when that subgroup is normal.',
    basis:
      'Articles (1)–(3), (5)–(7) of the « Théorème (à prouver) » on pages 10–15; the page states them and proves none of them, and heads the whole run « à prouver ».',
    ours:
      'The presentation of Γ̂ is the Esquisse’s, not written on the page; the angle criterion 1/p + 1/q vs 1/2 is the reading’s (the page gives lists, and its (c₂) form of the hyperbolic case is wrong as written and was replaced); the reading of « régulières » as « quasi-régulières » in (7), and the second half of (4), are reconstructed around illegible words; « isotopique » in (2) is an uncertain reading.',
    literature: [
      'G. A. Jones and D. Singerman, « Theory of maps on orientable surfaces », Proc. London Math. Soc. (3) 37 (1978), 273–307 — universal maps on the sphere, plane and hyperbolic plane; every oriented map of type (m,n) a quotient of the universal one by a subgroup of the triangle group, regular iff normal (from knowledge of the paper; not re-read in this pass)',
      'R. P. Bryant and D. Singerman, « Foundations of the theory of maps on surfaces with boundary », Quart. J. Math. 36 (1985), 17–41 — the same for unoriented maps and extended triangle groups (bibliographic record and the summary of Bryant’s 1984 Southampton thesis seen by web search; full text not read)',
      'H. S. M. Coxeter and W. O. J. Moser, Generators and Relations for Discrete Groups, ch. 8 (regular maps) — the groups [q,p] and the spherical/Euclidean/hyperbolic trichotomy (from knowledge; not re-read in this pass)',
    ],
    status: 'matched',
    settle:
      'Open Jones–Singerman 1978 §§3–6 and Bryant–Singerman 1985 with pages 10–15 beside them and confirm that the unoriented statement with the extended group Γ_{p,q}, including the degenerate types (2,q), (p,2) and the (ℝ² ⊃ ℝ) exception of (1), is covered; if some degenerate case is not, that case alone becomes a candidate.',
  },
  {
    id: '103-gr-stacks-relative-cohomology-BG',
    cote: '103',
    pages: '14–15',
    kind: 'mathematical',
    claim:
      'The folder asserts, without proof, that for a Group G on a topos X (not necessarily commutative) and a G-Module N, the strict Picard 2-category of Gr-stacks on X pinned by (G, N) corresponds to the truncated complex τ≤2(RΓ(B_G mod X, N)[1]) — relative cohomology of the classifying topos B_G with respect to q_G : X ≃ (B_G)_{/P} → B_G — a pinned Gr-stack being essentially a 2-gerbe on B_G bound by N and trivialised over X, and that the localised version over X is τ≤2(Rp_{G*} Coker(N → q_{G*} C(q_G^* N))).',
    basis:
      'Page 14 states the complex and the 2-gerbe description (« On trouve que … »); page 15 says the 3-arrows of these 2-gerbes are trivial, which « exprime H⁰(B_G/X, N) = 0 », and gives the localised complex with C a « rés. inj. ». Only « un » in « cela un fait » is uncertain; no word of the statements is illegible. Page 15 says « champs de Picard … épinglés par G, N » where Gr-stacks are meant.',
    ours:
      'The reading reads « champs de Picard » on page 15 as Gr-champs, replaces Rq_{G*} by q_{G*} on injectives, and checks, as its own step, that on the punctual topos the complex gives H³(G, N) for classes of pinned Gr-categories, H²(G, N) for pinned auto-equivalences and Z¹(G, N) for automorphisms of the identity — Sính’s theorem of page 3. This pass re-did the point computation from the relative long exact sequence (N/N^G → H¹(B_G mod pt, N) → H¹(G, N) → 0, so H¹ of the relative group is Z¹(G, N)) and agrees. The general statement over X is the page’s; nothing in the folder proves it. Written on Opus 5.5 against a reading made on Opus 5.5.',
    literature: [
      'Web search of 2026-10-10 (result summaries only, no section read): L. Breen, « On the classification of 2-gerbes and 2-stacks », Astérisque 225 (1994), table of contents (a chapter on stacks, group extensions and gr-stacks); L. Breen, « Monoidal categories and multiextensions », arXiv math/9809104 (gr-stacks with abelian π₀, π₁ classified by a hypercohomology H³ of a classifying object). Neither summary mentions relative cohomology of B_G with respect to X.',
    ],
    status: 'unsearched',
    settle:
      'Read Breen, Astérisque 225 (1994), the chapters on gr-stacks and 2-gerbes, for a classification of gr-stacks with π₀ ≃ G non-commutative and π₁ ≃ N by (relative) cohomology of the classifying topos B_G; also L. Breen, « Bitorseurs et cohomologie non abélienne » (Grothendieck Festschrift I, 1990), and Hoàng Xuân Sính, Gr-catégories (thèse, Paris VII, 1975). If the statement, or H³(B_G mod X, N) as the group of classes, is there, mark matched. Nothing has been read beyond search snippets.',
  },
  {
    id: '103-letter-leaf-order-missing-leaf',
    cote: '103',
    pages: '12–15',
    kind: 'codicological',
    claim:
      'In the letter to Deligne of 27.8.74 the archivists’ pages 12–13 follow pages 14–15 in the order of writing, and the leaf that continued page 13 (ending « J’ai ») is not in the folder, so the letter reads 8–11, 14–15, 12–13 and is incomplete.',
    basis:
      'Page 12 refers to « B_e → B_G plus haut » (« plus haut » uncertain), and B_G appears only on pages 14–15; page 13 ends mid-sentence on « J’ai » in the « Question pour Illusie », and page 14 opens « Je te signale que j’ai réfléchi aux Gr-champs », which does not continue it, while 15 → 12 (« Je profite de l’occasion … ») reads as a new paragraph.',
    ours:
      'The order is inferred from content by the transcription and adopted by the reading; the argument rests partly on « plus haut », read with doubt. No facsimile was consulted for this pass. Folder 134-1’s copy carries only the first four pages (8–11 here), so it cannot supply the missing leaf.',
    literature: [
      'Transcription 103, batch 1 (batch-01.fr.tex), header and pages 12–15',
      'Modernised reading 103 (103.modern.tex), « Le fil du dossier » and the footnotes to pages 12–15',
      'findings.ts entry 134-1-first-four-of-eight-pages',
    ],
    status: 'candidate',
    settle:
      'A person checks on the facsimile whether pages 12–13 and 14–15 are recto/verso of single leaves (which would fix their order physically), confirms « plus haut » on page 12, and looks for any numbering by the writer; the continuation after « J’ai » would have to be sought in Deligne’s or Illusie’s papers, not here.',
  },
  // Folder 107 — find-novelty pass on Opus 5.5 (claude-opus-5-5), reading also Opus 5.5 (2026-10-03).
  // Dropped as matches or as the edition's repairs: the weighted-limit cotensor X^M and the tensor X ⊗ M
  // (Quillen, Homotopical Algebra II.1–2); the matching object (p. 14); the external-product Proposition
  // and Corollary of p. 13 and L^M = L of p. 15, all false as the page states them, true forms the edition's.
  {
    id: '107-hot-sequential-colimits',
    cote: '107',
    pages: '18, 20, 24',
    kind: 'mathematical',
    claim:
      'The folder asks whether, for a sequence of monomorphisms X₀ ↪ X₁ ↪ ⋯ of presheaves on a test category, the colimit X_∞ is a colimit in Hot — reduced to the bijectivity of Hom_Hot(X_∞, Y) → lim Hom_Hot(X_i, Y), proves surjectivity, and leaves injectivity « not clear at all »; injectivity fails in general, the defect being Milnor’s lim¹.',
    basis:
      'Page 18 makes the reduction to monomorphisms and to (*); page 20 with page 22 gives the surjectivity by extending homotopies along cofibrations into a fibrant Y; page 24 reduces injectivity to whether lim π₀ of the sets of extensions Z_i → Y is non-empty, and stops on « Ask Ronnie Brown! ».',
    ours:
      'Everything negative is the edition’s: the identification of the defect with lim¹ of π₁ of the mapping spaces, and the example S¹ with degree-d maps into K(ℤ,2), H²(X_∞) ≅ Ẑ_d/ℤ ≠ 0. The induction giving surjectivity is the reading’s; the page only says « we are through ». The word after π₀ on page 24 is illegible, so the exact object of the last question is paraphrased; « point » before it is an uncertain reading.',
    literature: [
      'J. Milnor, On axiomatic homology theory, Pacific J. Math. 12 (1962) — the lim¹ exact sequence for a telescope (cited from the pass’s knowledge, not re-read for this entry)',
      'A. K. Bousfield and D. M. Kan, Homotopy Limits, Completions and Localizations, LNM 304 (1972), ch. IX — π₀ of the limit of a tower of fibrations and lim¹ (cited from the pass’s knowledge, not re-read for this entry)',
    ],
    status: 'matched',
    settle:
      'Nothing to settle about novelty: the question is answered in Milnor 1962 and Bousfield–Kan IX. What remains is editorial — check the edition’s example against Milnor’s sequence with the two texts open, and recover the illegible word after π₀ on page 24 from the facsimile.',
  },
  {
    id: '107-relative-square-rectification',
    cote: '107',
    pages: '20, 22',
    kind: 'mathematical',
    claim:
      'In a model category, given a square p g = g′ i with i a cofibration between cofibrant objects and p a fibration between fibrant ones, a diagonal φ making both triangles commute up to homotopies k and h can be replaced by a homotopic diagonal making them commute strictly if (and, by the edition, only if) k and h can be chosen compatible, p∘k = h∘(i ⊗ J) up to homotopy rel endpoints — and the condition can fail.',
    basis:
      'Page 22 states that « all we have to do is to check that we can choose these homotopies compatible with i and p », and that the case Y′ final is immediate; the margin of page 20 states the criterion as an equivalence and adds that it is « sans doute pas toujours satisfait ». The page relates the problem to Quillen, Homotopical Algebra, ch. II, n° 2.4, proposition 4.',
    ours:
      'The margin of page 20 is very doubtfully read, so the « only if » and the « rel endpoints » rest on the edition; the proofs of necessity and sufficiency and the counterexample (path fibration over S¹, i : {0,1} → [0,1]) are the edition’s. On the page alone the statement is the sufficiency direction, with « by assumption » and « simplicial » added between lines.',
    literature: [],
    status: 'unsearched',
    settle:
      'Read Quillen, Homotopical Algebra (LNM 43, 1967), ch. II §2, prop. 4, with page 20 open: if the criterion is that proposition or an immediate consequence, mark matched. Otherwise look for the « homotopy-commutative lifting square » lemma in Hovey, Model Categories, ch. 1, and Hirschhorn, Model Categories and their Localizations, ch. 7; it is most likely folklore, and a pass should expect to mark it matched.',
  },
// 111: no new entry. The folder is a third witness of the typescript « Tapis de Quillen » already read in 162-5 (pp. 2-17, 32-48); its one surviving mathematical candidate (pp. 11-13, the universal bordism correspondence category) is 162-5-bordism-correspondences-universal, and its relation to the other witnesses is in 162-5-photocopy-taken-after-ink and 162-5-karoubi-note-later-than-typescript; the rest of the reading is matches (Quillen/Illusie Ho(Cat) ≃ Ho(sSet), Dold-Kan, Deligne SGA 4 XVIII), conjectures the page announces without establishing (pp. 3-4, 9), or corrections of the page that are the edition's (pp. 3, 4, 8, 16), none of which qualifies.
  {
    id: '118-groupoid-products-not-totally-aspherical',
    cote: '118',
    pages: '32–35',
    kind: 'mathematical',
    claim:
      'For a small category A, stability of 𝒲_A under finite products does not imply that A is aspherical, nor that products a × b of representables are aspherical: a connected groupoid with non-trivial automorphism group G, with the usual weak equivalences, has 𝒲_A equal to the isomorphisms, hence stable under finite products, while A ≃ BG is not aspherical.',
    basis:
      'Page 35 asks whether a connected A satisfying (ii) (« 𝒲_A stable par produits finis ») must be aspherical and answers « Non » with « A un groupoïde, dans lequel 𝒲_A est formé des seuls iso (car ici 𝒲 est l’équiv. faible habituelle), donc stable par produits finis »; pages 33–34 prove (i) ⇔ (ii) + « A asphérique ».',
    ours:
      'The page says only « un groupoïde »: connectedness and G ≠ 1 are the reading’s, as is the reason 𝒲_A consists of isomorphisms (a map of G-sets bijective on orbits and an isomorphism on stabilisers is bijective). « habituelle » and, on page 34, « stable » in (ii) are \\uncertain{}. The comparison with the literature is this pass’s own: Cisinski 2006, Proposition 4.3.2, lists as its condition (g) « Les W-équivalences de préfaisceaux sur A sont stables par produits finis » among conditions equivalent to (a) « a × b W-asphérique for all representables », and adds that for non-empty A each condition implies A W-aspherical, with (c) ⇔ (g) said to follow « trivialement » from the stability of W under finite products in Cat. For A = BG, G ≠ 1, and W the usual weak equivalences, (g) holds by the page’s example while (a) and (c) fail (take X = Y = the terminal G-set: BG → BG × BG is not a weak equivalence), so only (c) ⇒ (g) appears to follow. Maltsiniotis’s Proposition 7.1 (version provisoire, 2001) lists (a)–(d) without (g), and is consistent with the example.',
    literature: [
      'Cisinski, Les préfaisceaux comme modèles des types d’homotopie, Astérisque 308 (2006), 4.3.1–4.3.2 (author’s copy, cisinski.app.uni-regensburg.de/smf_ast_308.pdf)',
      'Maltsiniotis, La théorie de l’homotopie de Grothendieck, version provisoire août 2001 (prst.pdf), Proposition 7.1, Définition 7.2, Remarque 7.3',
    ],
    status: 'candidate',
    settle:
      'A person checks the computation for A = BG (𝒲_A = isomorphisms; A/(e × e) → A/e × A/e not a weak equivalence) and whether the published Astérisque 308 or a later erratum restricts condition (g) of Proposition 4.3.2; the published Astérisque 301, Proposition 1.6.1, should also be read. If (g) is stated differently there, mark matched or drop.',
  },
  {
    id: '118-pushout-along-cofibrations-in-cat',
    cote: '118',
    pages: '18–20',
    kind: 'mathematical',
    claim:
      'For any basic localizer 𝒲, a cocartesian and cartesian square Y → X, Y → Y′, X → X′, Y′ → X′ in Cat in which i′ : Y′ → X′ and f : X → X′ are Grothendieck opfibrations, and over each object of X′ one of the fibres of f or i′ is equivalent to the point, is homotopy cocartesian: the comparison ∫(i, g) → X′ is an opfibration with aspherical fibres, so i ∈ 𝒲 ⇒ i′ ∈ 𝒲 and g ∈ 𝒲 ⇒ f ∈ 𝒲.',
    basis:
      'Page 20 states the Theorem and identifies the fibres as ∫(Y′_{x′} ← Y′_{x′} × X_{x′} → X_{x′}), of the form ∫(A = A, A → e), which retracts onto the cone C(A); pages 18–19 show the square is cocartesian when f is an opfibration with point fibres over the open complement; page 20 states the Corollary.',
    ours:
      'The cartesian hypothesis is the reading’s: the page writes the fibre formula Y_{x′} = Y′_{x′} × X_{x′} (overwritten) without stating it. The derivation of the Corollary from the Theorem and the functoriality of ∫ is the reading’s, as is the completion of the cocartesianity argument of pages 18–19, which breaks off. The deformation-retraction sentence has an \\ill{} word, and the margin’s weakening (« au lieu de ponctuelle, il suffit … soit asphérique ») has an \\ill{} and is unproved.',
    literature: [
      'Cisinski, Astérisque 308 (2006), §5.1: 5.1.2 (W-homotopy cocartesian squares), Lemmas 5.1.10–5.1.12, Propositions 5.1.13 and 5.1.16 — results conditioned on the immersion (closed immersions, formal cofibrations), not on opfibration hypotheses on f and i′',
    ],
    status: 'candidate',
    settle:
      'Search Thomason, Cat as a closed model category (1980), on Dwyer maps, and Cisinski §5.2 and Maltsiniotis Astérisque 301 for a pushout criterion stated through (op)fibration hypotheses on the opposite sides; then check whether the square of the Theorem reduces to a pushout along a Dwyer map or formal cofibration, in which case mark matched.',
  },
  {
    id: '118-product-condition-iv',
    cote: '118',
    pages: '33–34',
    kind: 'mathematical',
    claim:
      'A^ → Hot(𝒲) commutes with binary products iff a × b is aspherical for all objects a, b of A, by the isomorphism (A_{/X×Y})_{/α} ≃ A_{/a×b}; and A is totally aspherical iff this holds and A is aspherical.',
    basis:
      'Page 34 reduces (iv) to A_{/X×Y} → A_{/X} × A_{/Y} ∈ 𝒲, specialises to X = a, Y = b, and proves the converse via the slice isomorphism; page 33 proves (i) ⇔ (ii) + « A asphérique ».',
    ours:
      'The reading restates the page’s « conditions équivalentes » lemma, false as stated, as what pages 33–35 prove. « tot. » is \\uncertain{} throughout, as are « le second membre » and « conclut » on page 34.',
    literature: [
      'Maltsiniotis, La théorie de l’homotopie de Grothendieck, version provisoire août 2001, Proposition 7.1 (a) ⇔ (b) ⇔ (b′), with the same isomorphism (A/(F × G))/((a,p),(b,q)) ≃ A/a × b, and Définition 7.2',
      'Cisinski, Astérisque 308 (2006), 4.3.1 and Proposition 4.3.2 (a) ⇔ (c) ⇔ (d)',
    ],
    status: 'matched',
    settle:
      'Nothing to settle: the statement and its proof are in Maltsiniotis’s Proposition 7.1, which presents itself as an exposition of Pursuing Stacks.',
  },
  {
    id: '118-strong-saturation',
    cote: '118',
    pages: '39–40',
    kind: 'mathematical',
    claim:
      'Every basic localizer 𝒲 on Cat is strongly saturated (a functor invertible in Hot(𝒲) is in 𝒲), and so is each 𝒲_A.',
    basis:
      'Page 39 states « L’ens. 𝒲 est saturé » and the Corollary for 𝒲_A; page 40 argues through a sequence of open immersions X_0 → X_1 → … whose consecutive composites are in 𝒲, passing to the colimit.',
    ours:
      'The page’s proof uses a calculus of fractions in Cat that the folder establishes only in presheaf categories, and a passage to the limit the reading justifies by the filtration theorem of pages 38–39; the Corollary’s one-line proof is the reading’s.',
    literature: [
      'Cisinski, Astérisque 308 (2006), Proposition 4.2.4 (« Tout localisateur fondamental est fortement saturé »), proved via a W-test category, not via the folder’s telescope',
    ],
    status: 'matched',
    settle:
      'Nothing to settle for the statement. Whether the page’s telescope route can be completed without a test category is a separate question, open on the calculus of fractions in Cat.',
  },
  // Folder 131 — find-novelty pass on Opus 5.5 (claude-opus-5-5), 2026-10-10, on a reading made by Opus 5.5 (2026-09-24).
  // Sources actually read: J. P. Murre, « Representation of unramified functors. Applications (according to unpublished
  // results of A. Grothendieck) », Séminaire Bourbaki exp. 294 (mai 1965), pp. 243–261, full text from Numdam.
  {
    id: '131-locally-quasi-finite-representability',
    cote: '131',
    pages: '1–5, 13, 15',
    kind: 'mathematical',
    claim:
      'A functor F on schemes over a locally noetherian S is representable by a locally quasi-finite separated S-scheme if and only if it satisfies fpqc descent (tested on B → B^), local finite presentation, effectivity on B^ = lim B_n, pro-representability over artinian rings by rings finite over them, the valuative criterion of separatedness, and two « modularity » conditions — a local one over complete local bases (modular at the closed point ⇒ modular at every point of a finite local B) and a generic one (modular at a point over the generic point of an irreducible S′ ⇒ modular on an open neighbourhood).',
    basis:
      'Page 13 (ending at the top of page 15) states the Théorème with conditions (1)–(8); pages 1–5 give a first list and a proof by induction on dim S, citing the formal results of pages 22–40 (Prop. 1, Cor. 1–2, Prop. 2, Prop. 3). The statement of (7) carries an \\ill{} inside its bracket « [… que ξ soit modulaire] », and the end of (8) on page 15 reads « en \\uncertain{Z} ».',
    ours:
      'The proof on the pages is incomplete and the reading says so: the last step stops at « on est ramené à vérifier la condition de constructibilité » (deriving constructibility from (8) is not written); the gluing « autre proposition formelle » of page 40 and the Lemme of page 38 are not proved; effectivity of the descent datum in step (3) is asserted (the reading supplies the quasi-compact case only). The reading also strengthens (L4) to bijectivity on page 30, extends injectivity through (L2) on page 26, and reads the definition of « modulaire » (p. 34) with its variance corrected and « pro-modulaire » (undefined on the pages) as pro-representation by the completed local ring. So what is on the page is a statement of necessary-and-sufficient conditions with a partial proof, not a proved theorem.',
    literature: [
      'J. P. Murre, Séminaire Bourbaki exp. 294 (1965), §1 Theorem 1 and Corollaries 1–2, §2 (proof), appendix — read in full: the theorem is stated and sketched for unramified separated X only (conditions (F1)–(F8)); at the end of §1 Murre writes « it is possible to prove a statement similar to theorem 1 with "unramified" replaced by "locally quasi-finite" over S », without stating the conditions. His Proposition 1 (effective descent for separated locally quasi-finite schemes along fpqc morphisms, appendix) covers the descent step the folder asserts at step (3).',
      'S. Kleiman, « The Picard scheme », arXiv math/0504020, Thm 4.18.2 — seen only as a web-search summary (2026-10-10): restates Murre’s unramified theorem (F1)–(F8); no locally quasi-finite version reported there.',
    ],
    status: 'candidate',
    settle:
      'Look for the locally quasi-finite statement with explicit conditions in M. Artin, « Algebraization of formal moduli I » (1969) and « Algebraic approximation of structures over complete local rings » (Publ. IHÉS 36, 1969), Knutson, Algebraic Spaces (1971), and the Stacks Project chapters « Artin’s Axioms » and « More on Morphisms of Spaces » (separated locally quasi-finite spaces over a scheme are schemes): if a criterion with a local and a generic openness-of-versality condition plus finite pro-representing hulls is there, mark matched. Murre’s remark shows the generalisation was announced in 1965; the candidate is only the explicit list of conditions (5), (7), (8), not the existence of such a theorem, and nothing here dates the folder relative to the exposé.',
  },
  {
    id: '131-unramified-and-etale-corollaries',
    cote: '131',
    pages: '11, 15–16',
    kind: 'mathematical',
    claim:
      'The folder’s criteria for representability by an unramified (resp. étale) separated S-scheme — conditions (1)–(6), F unramified, and an extension condition over one-dimensional local rings whose spectrum is irreducible — together with the announced applications (Hom of abelian schemes, Picard scheme over a non-empty open of the base, projectivity of abelian schemes), are the theorem and applications of Murre’s Bourbaki exposé 294.',
    basis:
      'Page 15, Corollaires 1 and 2 (draft on page 11, with condition (RG) as 9°), Remarque 3 and (RG) on pages 15–16, and the « applications en vue » of page 16. The condition b) of Corollaire 2 rests on bracketed, partly illegible words (« [\\uncertain{idéal} \\ill{}] », « [idéal] I [tel que I_p = 0] »).',
    ours:
      'The reading repairs b): as bracketed on the page (« I_p = 0 ») it fails already for a closed immersion, and the reading states it with A → A_p injective and I nilpotent arbitrary, taking p to be the minimal prime (the page does not say which prime). Murre’s (F7) has the same shape with A complete, dim A = 1, A having one associated prime and N·I = 0 (N the nilradical) — close to the reading’s repaired form, not to the page’s bracket. The reading also notes that page 16’s « un schéma abélien … connexe est projectif » is false in general (Raynaud 1970); Murre §3 states projectivity of an abelian scheme over a normal base.',
    literature: [
      'J. P. Murre, « Representation of unramified functors. Applications (according to unpublished results of A. Grothendieck) », Séminaire Bourbaki exp. 294 (1965): §1 Theorem 1 (unramified, conditions (F1)–(F8), with (F7) the extension condition over complete one-dimensional local rings and (F8) its generic form), Corollary 2 (étale case: (F1), (F2), (F3), (F6) and (F5) bijective), §2 Proposition 2 and Lemmas 2–4 (passing from the local schemes Spec O_{S,s} to S, gluing by SGA 3 XI Prop. 3.5 — the route of the folder’s Prop. 3), §3 Theorem 4 and Corollary 1 (Hom of abelian schemes, unramified), Corollary 3 (Picard scheme over a non-empty open of an integral base), and projectivity of abelian schemes over a normal base — read in full.',
    ],
    status: 'matched',
    settle:
      'Nothing remains to settle for the unramified and étale cases: they are Murre’s Theorem 1 and Corollary 2. What could still differ is the exact form of the extension condition b) once the page’s bracket is read from the facsimile; that is /transcribe-grothendieck’s work, not a literature question.',
  },
];
