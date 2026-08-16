import type { Novelty } from '../lib/types.ts';

/**
 * Candidate novelties, written by `/find-novelty` and rendered by the
 * Novelties tab.
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
export const NOVELTIES: Novelty[] = [
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
