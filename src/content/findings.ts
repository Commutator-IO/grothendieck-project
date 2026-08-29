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
];
