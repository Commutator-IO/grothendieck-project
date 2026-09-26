/**
 * Statements of the modernised readings proved in Lean (lean/, issue #26).
 *
 * One entry per proof file. Written by hand when a proof lands, alongside its
 * section of docs/lean/article.tex, which gives the same statement with its
 * proof written out. The notation is the findings' hybrid (Unicode operators,
 * TeX indices), rendered by lib/notation.tsx.
 */
export interface Proof {
  folder: string;
  /** Where the reading's statement is, as the reader addresses it. */
  batch: number;
  page: string;
  /** The reading's name for it. */
  name: string;
  statement: string;
  /** What the formalisation turned up — the point of doing it. */
  found: string;
  /** The verdict in one word, for the badge. */
  verdict: 'holds' | 'holds, more generally' | 'holds; the gloss was false' | 'false on the page' | 'the reading dropped a hypothesis' | 'partly proved' | 'already in mathlib';
  lean: string;
  theorems: string[];
}

export const PROOFS: Proof[] = [
  {
    folder: '42',
    batch: 1,
    page: '4',
    name: 'Lemme 2',
    statement:
      'Let A be a Noetherian ring and 𝔭 a prime ideal. (1) Some f ∉ 𝔭 makes A_f → A_𝔭 injective. (2) If moreover A → A_𝔭 is injective, then A_𝔮 → A_𝔭 is injective for every prime 𝔮 ⊇ 𝔭.',
    found:
      'Both parts hold as the reading states them; no hypothesis is missing. Part (2) does not need the Noetherian hypothesis: it holds over any commutative ring. Part (1) uses it only to make the kernel of A → A_𝔭 finitely generated, and needs that kernel described exactly — the elements killed by some element outside 𝔭 — which is the correction the reading’s footnote makes to the page’s « l’annulateur de A − 𝔭 ».',
    verdict: 'holds, more generally',
    lean: 'lean/Grothendieck/Folder42.lean',
    theorems: ['lemme2_1', 'lemme2_2'],
  },
  {
    folder: '158',
    batch: 3,
    page: '44',
    name: 'Proposition 1',
    statement:
      'A finite monoid M, pseudo-cofiltering (for all u, v there are u′, v′ with uu′ = vv′) and whose group completion is trivial, has an element p with up = p for every u — so p² = p and M is cofiltering.',
    found:
      'The Proposition holds as the leaf states it, and finiteness is used exactly where the page says « comme E₀ est fini ». The reading’s modern gloss was false: it called p a left zero and the Rees kernel a point. In {1, a, b} with xa = a and xb = b, both a and b qualify and the kernel is {a, b}; p is a right zero, and not unique. The reading is corrected.',
    verdict: 'holds; the gloss was false',
    lean: 'lean/Grothendieck/Folder158.lean',
    theorems: ['etape1', 'proposition1', 'contre_noyau_non_ponctuel'],
  },
  {
    folder: '153',
    batch: 1,
    page: '3',
    name: 'Lemme',
    statement:
      'For a free k₀-module M, Ω ⊗ M → K₀[T] ⊗ M is injective, its image is the set of F with F(x) ∈ M for every x, and membership is decided coordinate by coordinate in a basis (Ω the integer-valued polynomials).',
    found:
      'Holds as stated. The inclusion k₀ ⊂ K₀ is never used: any k₀-algebra K₀ will do. Freeness is used twice, for flatness and for the coordinates.',
    verdict: 'holds, more generally',
    lean: 'lean/Grothendieck/Folder153.lean',
    theorems: ['lemme_injective', 'lemme_range', 'lemme_coordonnees'],
  },
  {
    folder: '152',
    batch: 1,
    page: '9',
    name: 'Dictionary',
    statement:
      'Circularised graphs and contours with a fixed-point-free involution correspond: σ_C = σ_Γ, ρ_C = ρ_Γσ_Γ, ρ_Γ = ρ_Cσ_C; the vertices are the orbits of ρ_Cσ_C; a contour with one cycle gives a connected graph.',
    found:
      'The dictionary holds. The page’s head line ρ_Γ = ρ_C contradicts its own table (it would force σ = 1), as the reading’s footnote says. Not proved: the correspondence between embeddings in oriented surfaces and rotation systems, which needs a theory of surfaces.',
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder152.lean',
    theorems: ['formules', 'sommets', 'tete_page9_incompatible', 'connexe_of_une_face'],
  },
  {
    folder: '88',
    batch: 1,
    page: '8',
    name: 'Order 2ν; article (6)',
    statement:
      'On the cartographic torsor, σ_{ℓ−2}σ_{ℓ−1} has order 2ν, ν the lcm of the n_ij; and the spherical, Euclidean and hyperbolic cases of (6) are as listed.',
    found:
      'Both hold, including the reading’s corrected (c₂). Most of the hypotheses are unused — being a Weyl group, b), d), finiteness — and 2ν holds with infinite orders too. Not proved: the geometric content of (6), maps on surfaces.',
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder88.lean',
    theorems: ['proposition_ordre', 'spherique_iff', 'euclidien_iff', 'hyperbolique_iff'],
  },
  {
    folder: '113',
    batch: 1,
    page: '3',
    name: 'Karoubi envelope; Morita',
    statement:
      'The Karoubi envelope is the free completion under retracts, and (Kar P)^k ≃ P^k: restriction along P → Kar P is an equivalence on additive functors to any idempotent-complete additive category.',
    found:
      'The first is classical (and in mathlib); the second holds in additive form, without the smallness or abelianness the reading assumes. Not proved: the k-linear form, Kar P ≃ Proj_tf(P^k), Freyd–Mitchell.',
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder113.lean',
    theorems: ['enveloppe_libre', 'morita', 'morita_module'],
  },
  {
    folder: '104',
    batch: 1,
    page: '6',
    name: 'Categories of models',
    statement:
      'In a category of models, (*) Hom(D′, D) → subobjects is injective, the classes form an order, u_d = id; and the three examples — semi-simplicial, cubical, hemispherical — have 2ⁿ⁺¹ − 1, 3ⁿ and 2n + 1 cells.',
    found:
      'Nothing wrong; both of the reading’s corrections to Example 3 are confirmed, and hypothesis (i) is not needed for the order or for u_d = id. Not proved: the simplicial identities, the Reedy condition, M ≃ M₀.',
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder104.lean',
    theorems: ['etoile_injective', 'isIso_of_aller_retour', 'id_of_idempotent_bijective'],
  },
  {
    folder: '125',
    batch: 1,
    page: '2',
    name: 'The three étages; Lemme III-18',
    statement:
      'In a long exact sequence, the vanishing of C_p for p ≥ m is equivalent to L_p → G_p bijective for p > m and surjective for p = m; and under Serre duality to the dual statement for q ⩽ r − m. Lemme III-18: a map of finite modules bijective at 𝔭 is so near 𝔭.',
    found:
      'The statements hold; the reading’s prose has a slip — « q < r − m » should be « q ⩽ r − m » under p + q = r. III-18 is a classical fact about finitely presented modules; the margin’s hypotheses only make B finitely presented. Serre duality is taken as given.',
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder125.lean',
    theorems: ['etage1_iff_etage2', 'etage2_iff_etage3', 'lemme_III18'],
  },
  {
    folder: '161-1',
    batch: 1,
    page: '3',
    name: 'Condition (1); idempotent adjunctions',
    statement:
      'u restricted to E′ is fully faithful and vu(E′) ⊂ Ē′ if and only if η is invertible on E′; the four idempotency conditions are equivalent; the Σ-local objects are the essential image of the reflective subcategory.',
    found:
      'Nothing wrong. The margin asks for an example showing the second condition is needed; one is given (E′ = {∅} in sets, over a point), as the reading says. The manuscript’s paired idempotency conditions are redundant: any one implies the others.',
    verdict: 'holds',
    lean: 'lean/Grothendieck/Folder161_1.lean',
    theorems: ['condition1', 'condition1_non_surabondante', 'idempotent_tfae', 'local_iff_mem_essImage'],
  },
  {
    folder: '22',
    batch: 1,
    page: '10',
    name: '3.3–3.5',
    statement:
      'For M finitely presented, M ⊗ ∏ Pᵢ ≅ ∏ (M ⊗ Pᵢ); if every finitely generated module is finitely presented (« par exemple A noethérien »), a product of flat modules is flat; a countable strict limit of projectives is flat.',
    found:
      '« Par exemple A noethérien » is misleading: the hypothesis of 3.4 is equivalent to Noetherian, and the proof needs only a coherent ring. 3.5 is proved for ℕ-indexed systems with surjective maps. Not proved: formal smoothness and Cohen algebras.',
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder22.lean',
    theorems: ['lemme3_3', 'corollaire3_4', 'corollaire3_5', 'hypothese_iff_noetherien'],
  },
  {
    folder: '41',
    batch: 1,
    page: '11',
    name: 'Proposition 1',
    statement:
      'For f with a generic-point section, (i) f open, (ii) the section continuous, (iii) generizations lift, (iii bis) are equivalent when f is locally of finite presentation.',
    found:
      'Holds. (i) ⇔ (ii) ⇒ (iii) ⇔ (iii bis) need no hypothesis at all, not even continuity; finiteness is needed exactly for (iii bis) ⇒ (ii), the classical openness criterion, and a counterexample shows it cannot be dropped.',
    verdict: 'holds, more generally',
    lean: 'lean/Grothendieck/Folder41.lean',
    theorems: ['i_iff_ii', 'iii_iff_iiibis', 'proposition1', 'iiibis_not_imp_ii'],
  },
  {
    folder: '21',
    batch: 1,
    page: '13',
    name: 'Proposition 2.15; Corollaire 2.16',
    statement:
      'Over a Noetherian ring, an I-torsion module H is injective iff Hom(−, H) is right exact on finitely generated modules killed by a power of I; Γ_I preserves injectives.',
    found:
      'Nothing false. Artin–Rees must be used with the ambient module in the intersection — the reading’s correction to the page’s N ∩ IᵐN. Not proved: 2.1–2.14, the sheaf and Hartogs half.',
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder21.lean',
    theorems: ['proposition2_15', 'corollaire2_16'],
  },
  {
    folder: '39',
    batch: 1,
    page: '18',
    name: 'Formal preparation',
    statement:
      'If A is I-adically complete, a₀, …, a_{N−1} ∈ I and a_N a unit, F is regular and every G is QF + r uniquely with deg r < N; the same when a₀, …, a_{N−1} are nilpotent.',
    found:
      'Nothing wrong; it follows from classical Weierstrass division. Not proved: the general linearly topologised case, and the exact hypothesis aᵢ ∈ √I.',
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder39.lean',
    theorems: ['preparation_adique', 'preparation_discrete'],
  },
  {
    folder: '19',
    batch: 1,
    page: '4',
    name: 'Théorème 1.12; Gabriel–Popescu',
    statement:
      'For an adjunction f ⊣ g with comparison functor h: a) if A has equalizers and f preserves them, h is essentially surjective; b) h is an equivalence if and only if f is conservative and, for every pair (u, v) whose image under f has an equalizer, the equalizer of (u, v) exists and f preserves it (condition C).',
    found:
      'a) and the « if » of b) hold — Beck’s theorem. The « only if » of b) is false as the page states it: the inclusion of the pairs of sets (X, Y) with Y ≠ ∅ ⇒ X ≠ ∅ is coreflective, hence comonadic and conservative, yet the pair (∗, ∗) ⇉ ({0, 1}, ∗) has equalizer (∅, ∗) below and (∅, ∅) above. The reading had called condition C Beck’s f-split condition; it is not, and the reading is corrected. Gabriel–Popescu holds in the reading’s form and is classical.',
    verdict: 'false on the page',
    lean: 'lean/Grothendieck/Folder19.lean',
    theorems: ['theoreme_a', 'theoreme_b_suffisance', 'theoreme_b_necessite_fausse', 'beck_iff', 'gabriel_popescu'],
  },
  {
    folder: '161-2',
    batch: 2,
    page: '33',
    name: 'Monadicity, descent, Gabriel–Ulmer',
    statement:
      'The crude monadicity theorem (p. 33); the descent criterion (p. 34); a cocomplete category is locally presentable iff it has a small dense subcategory of presentable objects (p. 61); for Σ with finite colimits, Ind(Σ) is the category of left-exact presheaves on Σ (p. 77).',
    found:
      'Nothing false. The descent criterion needs no topos: it holds for any left-exact conservative left adjoint out of a category with finite limits. Not proved: the p. 54 theorem on π-accessible categories and the non-accessibility of (Ens)° and (Ab)°.',
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder161_2.lean',
    theorems: ['monadicite', 'descente', 'caracterisation_gabriel_ulmer', 'lemme_ind'],
  },
  {
    folder: '16',
    batch: 1,
    page: '9',
    name: 'sl₂ against (6.7)',
    statement:
      'On a primitive vector of weight μ, ΛL^{k+1}x = (k+1)(μ−k)L^k x; the sl₂ Λ satisfies (6.7)’s ΛLx = x only when μ = 1; the commutator [L, Λ] follows from (6.7); in the exterior algebra, Λ₀L₀(1) = n.',
    found:
      'Nothing false; the last identity confirms the reading’s correction of p. 13, where the page identifies the contraction Λ₀ with the Λ₀ of (6.15). Only the algebra is proved; Hard Lefschetz and the geometry are not.',
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder16.lean',
    theorems: ['sl2_normalisation', 'identification_seulement_si', 'commutateur_pseudo_inverse', 'lambda0_L0_un_ne_un'],
  },
  {
    folder: '106',
    batch: 1,
    page: '9',
    name: 'Brown factorisation; W₀⁻¹C ≅ W⁻¹C',
    statement:
      'In a cofibration category (Baues’s C1–C3): cofibrant replacement, weak lifting, and Brown’s factorisation of a weak equivalence between cofibrant objects; when every object is cofibrant, inverting W₀ = W ∩ cof inverts W, so W₀⁻¹C ≅ W⁻¹C.',
    found:
      'Nothing false; the last statement answers the doubt the page raises on p. 11, as the reading says. Hypotheses unused: α_x ∈ W in the weak lifting, f ∈ W except for i ∈ W, the two weak-equivalence clauses of C2 and « isomorphisms are cofibrations ».',
    verdict: 'holds, more generally',
    lean: 'lean/Grothendieck/Folder106.lean',
    theorems: ['remplacementCofibrant', 'relevementFaible', 'factorisationDeBrown', 'localisation_W₀_iso_localisation_W'],
  },
  {
    folder: '114',
    batch: 1,
    page: '3',
    name: 'Proposition 4 and the minimal localiser',
    statement:
      'For fundamental localisers W∞ ⊆ W ⊆ W₀: (i) A totally W∞-aspheric ⇒ (ii) totally W-aspheric ⇒ (iii) A non-empty and every a × b 0-connected; W₀-aspheric means 0-connected, and the minimal fundamental localiser exists.',
    found:
      'W₀ is a fundamental localiser, totally W₀-aspheric is exactly (iii), and the minimal localiser exists; (i) ⇒ (ii) holds for all W, (ii) ⇒ (iii) for W ⊆ W₀. The reading had dropped the page’s « satisfying Loc 4) »: without it, W ⊆ W₀ fails (all functors; functors reflecting emptiness, for which B(ℤ/2) satisfies (ii) but not (iii)). (iii) ⇒ (i) is refuted in the literature and not treated.',
    verdict: 'the reading dropped a hypothesis',
    lean: 'lean/Grothendieck/Folder114.lean',
    theorems: ['W₀_localisateurFondamental', 'totalementAspherique_W₀_iff', 'Wmin_inclus', 'proposition4_ii_iii', 'contreExemple_proposition4'],
  },
];
