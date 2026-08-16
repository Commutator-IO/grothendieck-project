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
      'Check whether this dévissage hypothesis, rather than local or core-compactness, appears in Johnstone (Stone Spaces II.4, Elephant C1.1 and C4.1) or in Isbell’s papers on locale products. If it is there, mark matched.',
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
      'Compare with the standard statement that a product of locales is spatial when almost all factors are compact and the rest locally compact, and check whether the two-clause form is a genuine weakening or a restatement.',
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
];
