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
      'Total asphericity does not depend on the basic localizer: for a small category A, being totally W∞-aspherical, being totally W-aspherical for any basic localizer W, and being non-empty with a × b 0-connected in Â for all objects a, b are all equivalent.',
    basis:
      'Proposition 4 states the three conditions and the proof turns on the sandwich W∞ ⊆ W ⊆ W₀ that every basic localizer satisfies, total asphericity being easier to obtain the larger the class of equivalences. The page stops at « namely » where W₀ should be named.',
    ours:
      'W₀ is identified in the reading as the maximal basic localizer, the one given by π₀-bijections — the only coherent reading, and flagged as the edition’s and not the page’s. The minimality of W∞, which the proposition needs and the page assumes, is attributed to Cisinski (2004) rather than to Grothendieck.',
    literature: [
      'D.-C. Cisinski, Le localisateur fondamental minimal, Cah. Topol. Géom. Différ. Catég. (2004)',
      'Cisinski, Les préfaisceaux comme modèles des types d’homotopie, Astérisque 308 (2006)',
    ],
    status: 'unsearched',
    settle:
      'Look up total asphericity in Astérisque 308 and establish whether the localizer-independence is stated there in this form, and whether the elementary criterion (iii) — a × b 0-connected — is the one used. The minimality of W∞ is settled and published; what is not checked is whether Proposition 4 itself is. An external review (Kimi, shared conversation of 2026-08) calls it the folder’s sharpest result but names no source for it.',
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
    literature: [],
    status: 'unsearched',
    settle:
      'Three of R1–R4 read cleanly; R4 carries three \\ill{} in its statement and is not fully recoverable, and page 193 is cancelled by long diagonals, so the equivalence rests on a page its author struck. Any search should therefore first settle what R4 says, which is /transcribe-grothendieck’s work and not this skill’s. Then compare with the modern axiomatisations of a Galois category without a fibre functor (finite limits, disjoint distributive coproducts, an effective descent morphism to the terminal object with a finite decomposition property) and with the stack-theoretic treatments of tame coverings — Kerz–Schmidt, Generators and relations for the étale fundamental group, arXiv math/0703139, which reduces statements about open varieties to proper stacks by Abhyankar’s lemma. An orienting web search found the axiomatisation of Galois categories without a fibre functor, and the stack-theoretic treatment of tame π₁, but no axiomatisation of a stack of such categories carrying a realisation functor. That is a reason to look, not a search of the sources.',
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
    literature: [],
    status: 'unsearched',
    settle:
      'Check the log-geometric literature on degenerations — Kato–Nakayama, and the computation of the tame or log fundamental group of the germ of a normal crossings degeneration — for a statement identifying the extension class with the self-intersection. The P¹ case, giving cyclic monodromy of order the prime-to-p part of the self-intersection degree, is the sharp form to look for and is what a cyclic quotient singularity would predict. Pages 91 and 93 are the faintest of the run and much of their connective prose is illegible, so what can be claimed is the two lemmas and the two examples, not the passage between them.',
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
    literature: [],
    status: 'unsearched',
    settle:
      'This is the condition for a morphism of log schemes with normal crossings log structure to induce an isomorphism on the Kummer-étale inertia, and it should be checked against the log-geometric literature on Kummer morphisms and log blow-ups (Kato, Illusie, Nakayama) before being treated as anything but a restatement. The determinant condition, rather than the invertibility of N over the ring, is the form to look for.',
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
      'The run « Métriques canoniques sur les surfaces conformes » is to be read 26, 44, 27, 45, 28–40, 41–43 — pages 44 and 45 being inserts between his sheets 1 and 2 and between his sheets 2 and 3, and pages 41–43 continuing his sheet 15 — although the circled numbers read on pages 41–45, « 10 », « 11 », « 12 », « 17 », « 21 », either repeat the numbers 10–12 already carried by pages 35–37 or fall outside his series 1–15.',
    basis:
      'Page 44 carries a « Corollaire 3 » after Cor. 1 and 2 of page 26, refers to « (i) ci-dessus », page 26’s condition (i), and ends « On trouve donc de plus », which page 27, noted as lacking its lead-in, continues with « les surfaces suivantes ». Page 45 completes case (1) of page 27 (the unique metric of curvature −1 when X is compact) and breaks off in case 2) on « La constante multiplicative », which page 28, noted as lacking the start of case 2, continues with « déterminée par la condition que l’aire totale de X soit = 1 ». Page 40 breaks off on « la deuxième », and page 41 goes on with the conformal surfaces with boundary begun on page 39. Batch 2 records his numbers 1–15 on pages 26–40, hence 10–12 on pages 35–37; batch 3 records circled numbers on pages 41–45, those of 42 and 43 as « sans doute », and puts pages 44–45 on another paper than pages 41–43.',
    ours:
      'The order is the reading’s, established from the text; neither transcription states it. Batch 3 treats the numbers of pages 41–45 as continuing a series begun in batch 2 and says his sheets 13–16 and 18–20 are missing, without noting that 10–12 already occur on pages 35–37. The join 40 → 41 is the weakest of the three, since the first word of page 41 is illegible. That « 17 » and « 21 » might be « 1′ » and « 2′ », which would fit the inserts’ positions, is the edition’s conjecture, made for this entry, and nothing in the claim rests on it. No facsimile was consulted.',
    literature: [
      'Transcription 67, batch 2 (batch-02.fr.tex), header and pages 26–28, 35–40',
      'Transcription 67, batch 3 (batch-03.fr.tex), header and pages 41–45',
      'Modernised reading 67 (67.modern.tex), header « Order of the leaves » and « L’ordre des feuillets sur les métriques canoniques »',
    ],
    status: 'candidate',
    settle:
      'A person reads the circled numbers of pages 41–45 on the facsimile — whether « 17 » and « 21 » are « 1′ » and « 2′ », and whether « 10 » to « 12 » are 16 to 18 or a second series — and compares the paper of pages 44–45 with the tractor-feed sheets of pages 26–40. If the numbers stand as read, pages 41–43 belong to a second numbered redaction whose text happens to continue page 40, and its missing sheets should be looked for in the neighbouring folders of the group [66–89].',
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
      'The reading adds that page 52 carries « 82 » by hand, which no transcription records. It also compares the theme of paired contraries with the yin and yang of Récoltes et semailles, while saying that nothing shows the typescript to be a state of it; the entry keeps that comparison out of the claim. The transcriptions do not record whether each typed face is the back of the blue-ink page before it, and no facsimile was consulted.',
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
];
