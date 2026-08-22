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
      'Check whether this dévissage hypothesis, rather than local or core-compactness, appears in Johnstone (Stone Spaces II.4, Elephant C1.1 and C4.1) or in Isbell’s papers on locale products. If it is there, mark matched. An external review of the folder (Kimi, shared conversation of 2026-08, covering 115, 161-1 and 161-3) judged the folder to contain no new theorems and its results « published in SGA 4 or standard by the 1970s », but named no source for this claim in particular, so the status is unchanged and the check below still stands.',
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
      'Compare with the standard statement that a product of locales is spatial when almost all factors are compact and the rest locally compact, and check whether the two-clause form is a genuine weakening or a restatement. An external review of the folder (Kimi, shared conversation of 2026-08, covering 115, 161-1 and 161-3) judged the folder to contain no new theorems and its results « published in SGA 4 or standard by the 1970s », but named no source for this claim in particular, so the status is unchanged and the check below still stands.',
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
      'Check whether the epimorphism form of flatness appears as a definition of hypercovering for a general index category, rather than only as the "covering flat" condition in Diaconescu-type theorems. Sources to try: SGA 4 V appendix and Artin–Mazur (simplicial hypercoverings); Dugger–Hollander–Isaksen, Hypercovers and simplicial presheaves (2004); Kondô–Yasuda and Shulman on covering-flat functors. If a category-indexed notion with this axiom is there, mark matched.',
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
];
