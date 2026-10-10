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
    page: '3–5',
    name: "Proposition, Lemme 1, Corollaire 1, Lemme 2",
    statement:
      "On a Noetherian sober space, a sheaf satisfying (H) has open coherence loci (Lemme 1) and its sections are the coherent families of germs (Proposition, p. 3); for A Noetherian, Lemme 1 and Corollaire 1 on Spec A; Lemme 2 (1), (2) and the page’s form (A_f)_𝔔 → A_𝔭.",
    found:
      "Nothing false. The step « constructible, donc … ouvert » never uses constructibility: stability under generization plus a non-empty open in each x̄ is enough, proved directly. (H) is used in a weaker form than the page states; injectivity needs neither (H) nor the Noetherian hypothesis; Corollaire 1 needs from Lemme 2 only one f killing ker(A → A_𝔭); Lemme 2 (2) holds over any commutative ring. Not proved: Corollaire 1 off the affine case, Lemme 3, Corollaires 2–3, the two counterexamples. Two of these are already in mathlib: the f killing ker(A → A_𝔭) follows from Module.mem_support_iff_of_finite and Module.notMem_support_iff′, and Lemme 2 (2) from IsLocalization.injective_of_map_algebraMap_zero. The openness criterion is proposed to mathlib without constructibility (leanprover-community/mathlib4#44707).",
    verdict: 'holds, more generally',
    lean: 'lean/Grothendieck/Folder42.lean',
    theorems: ["lemme2_1", "lemme2_2", "isOpen_of_stableUnderGeneralization", "lemme1_faisceau", "proposition", "lemme2_page", "lemme1", "corollaire1"],
  },
  {
    folder: '158',
    batch: 3,
    page: '44',
    name: 'Proposition 1',
    statement:
      'A finite monoid M, pseudo-cofiltering (for all u, v there are u′, v′ with uu′ = vv′) and whose group completion is trivial, has an element p with up = p for every u — so p² = p and M is cofiltering.',
    found:
      'The Proposition holds as the leaf states it, and finiteness is used exactly where the page says « comme E₀ est fini ». The reading’s modern gloss was false: it called p a left zero and the Rees kernel a point. In {1, a, b} with xa = a and xb = b, both a and b qualify and the kernel is {a, b}; p is a right zero, and not unique. The reading is corrected. Proposition 1 with its converse is proposed to mathlib (leanprover-community/mathlib4#44702).',
    verdict: 'holds; the gloss was false',
    lean: 'lean/Grothendieck/Folder158.lean',
    theorems: ['etape1', 'proposition1', 'contre_noyau_non_ponctuel'],
  },
  {
    folder: '153',
    batch: 1,
    page: '2–7',
    name: "Lemme; co-operations; Pólya, Vandermonde; Ω = Ω₀ ⊕ Ω⁰",
    statement:
      "The lemma on integer-valued polynomials and free modules; the co-addition and co-multiplication of Int(k₀) exist, are unique and obey the composition rules (K₀ a localisation of k₀, Ω free); the Pólya basis and Vandermonde for Int(ℤ); the decomposition Ω = Ω₀ ⊕ Ω⁰; the examples and counterexamples of p. 7 (Appl, k[T], 𝔽_q, k[[T]]⁺).",
    found:
      "Holds. The inclusion k₀ ⊂ K₀ is never used; what is used is that K₀ is a localisation, not K₀ ⊗ K₀ = K₀, and whether the latter alone suffices is left open. The decomposition needs neither axiom 3) nor the unit T. Appl(A, A) fails 3a) for every infinite non-zero unital A. The reading’s footnote on k[[T]]⁺: the matrix is Pascal’s without its (0, 0) entry; the counterexample holds in every characteristic.",
    verdict: 'holds, more generally',
    lean: 'lean/Grothendieck/Folder153.lean',
    theorems: ["lemme_injective", "lemme_range", "Phi_injective", "coaddition_existsUnique", "polya", "vandermonde", "isCompl_constants_zeroPart", "appl_not_coaddition", "geom_not_finite_coaddition"],
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
    page: '6–10',
    name: "Categories of models; well-foundedness; simplicial identities",
    statement:
      "In a category of models, (*) is injective, the classes form an order, u_d = id, and the three examples have 2ⁿ⁺¹ − 1, 3ⁿ and 2n + 1 cells; a skeletal category of models whose strict relation is well-founded is a direct (Reedy) category, and conversely; in Example 1, the simplicial identities hold, every arrow factors through a face, and the category is direct.",
    found:
      "Nothing wrong. Well-foundedness is a real extra hypothesis, as the reading’s « dès que » says: ℤ as a category satisfies (i) and (ii) and is not direct. The Reedy statement needs the category skeletal (« rigide », p. 9); (i) is not used. Not proved: the full decomposition of an arrow into faces, M ≃ M₀.",
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder104.lean',
    theorems: ["etoile_injective", "isIso_of_aller_retour", "id_of_idempotent_bijective", "reedyDirecte", "wf_of_degre", "entiers_relatifs_non_directe", "deltaInjReedy"],
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
    page: '2–6',
    name: "Idempotent adjunctions",
    statement:
      "Conditions (1) and (2), the five conditions of p. 3, the fixed parts E₀ ≃ F₀, the conditions 1), 3), 4) of p. 5; under idempotency E₀ is reflective with a colimit-preserving reflector and F₀ coreflective; the descent of p. 6.",
    found:
      "Nothing wrong. The fifth condition of p. 3 repeats the second word for word. The descent of p. 6 holds without β fully faithful, which the page assumes. Not proved: the reconstruction of an idempotent adjunction from (E₀, F₀, E₀ ≃ F₀), pp. 9–19.",
    verdict: 'holds, more generally',
    lean: 'lean/Grothendieck/Folder161_1.lean',
    theorems: ["condition1", "condition2", "five_conditions_tfae", "fixedEquiv", "reflectorAdj", "reflector0_preservesColimits", "condition4", "descent"],
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
    name: 'Théorème 1.12; Gabriel–Popescu; comonad over a product base',
    statement:
      'For an adjunction f ⊣ g with comparison functor h: a) if A has equalizers and f preserves them, h is essentially surjective; b) h is an equivalence if and only if f is conservative and, for every pair (u, v) whose image under f has an equalizer, the equalizer of (u, v) exists and f preserves it (condition C). Over a product base B = ∏ Bᵢ (pp. 7–9), the comonad fg is a matrix φ_ji = f_j g_i with comultiplication λ_kji, determined by its entries when the f_j preserve products; with fully faithful g′, g″ it collapses to two crossed functors and two units.',
    found:
      'a) and the « if » of b) hold — Beck’s theorem. The « only if » of b) is false as the page states it: the inclusion of the pairs of sets (X, Y) with Y ≠ ∅ ⇒ X ≠ ∅ is coreflective, hence comonadic and conservative, yet the pair (∗, ∗) ⇉ ({0, 1}, ∗) has equalizer (∅, ∗) below and (∅, ∅) above. The reading had called condition C Beck’s f-split condition; it is not, and the reading is corrected. Gabriel–Popescu holds in the reading’s form and is classical. On p. 7, the proviso « ou I fini » is false: a left adjoint need not preserve finite products (f = Bool × − on sets gives 2 elements against 4); exactness is the hypothesis that works.',
    verdict: 'false on the page',
    lean: 'lean/Grothendieck/Folder19.lean',
    theorems: ['theoreme_a', 'theoreme_b_suffisance', 'theoreme_b_necessite_fausse', 'beck_iff', 'gabriel_popescu', 'matrice', 'comult_matrice', 'lam_isIso_left', 'deuxFacteurs_left', 'matrice_fini_fausse'],
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
    page: '6–16, 47–48',
    name: "sl₂ against (6.7); projectors; Cayley–Hamilton",
    statement:
      "On a primitive vector of weight μ, ΛL^{k+1}x = (k+1)(μ−k)L^k x, and the sl₂ Λ satisfies (6.7) only when μ = 1; in a graded ring, one-sided inverses of L^{n−i} put every grading projector in the ring, over ℤ, with no module (no. 5, (6.3)); any algebraic isomorphism H^{2n−i} → H^i makes the inverse of L^{n−i} algebraic, by Cayley–Hamilton (pp. 47–48).",
    found:
      "Confirms the reading’s correction of p. 13. Finds the reading wrong on one point: its universal ring Φ₀ = ℤ[L₀, Λ₀], with Λ₀ in the sense of (6.15), does not exist over ℤ for n ≥ 2, since ξ₀ⁿ is divisible by n! and no y has ξ₀ⁿ ∧ y = vol; over ℚ the obstruction disappears. Not proved: Λ and the primitive projectors in the ring, the universal property of Φ₀, Hard Lefschetz. The Cayley–Hamilton lemma is proposed to mathlib in a more general form, for integral units of a subalgebra over an Artinian ring (leanprover-community/mathlib4#44708).",
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder16.lean',
    theorems: ["sl2_normalisation", "identification_seulement_si", "lambda0_L0_un_ne_un", "projecteurs_mem_lefschetz", "inverse_Lefschetz_algebrique", "not_exists_xi₀_pow_mul_eq_vol"],
  },
  {
    folder: '106',
    batch: 1,
    page: '9',
    name: 'Brown factorisation; W₀⁻¹C ≅ W⁻¹C; the criterion (⋆⋆)',
    statement:
      'In a cofibration category (Baues’s C1–C3): cofibrant replacement, weak lifting, and Brown’s factorisation of a weak equivalence between cofibrant objects; when every object is cofibrant, inverting W₀ = W ∩ cof inverts W, so W₀⁻¹C ≅ W⁻¹C.',
    found:
      'Nothing false; the last statement answers the doubt the page raises on p. 11, as the reading says. Hypotheses unused: α_x ∈ W in the weak lifting, f ∈ W except for i ∈ W, the two weak-equivalence clauses of C2 and « isomorphisms are cofibrations ». On pp. 11–15, with every object cofibrant, q′ from the spans x → ỹ ← y to W⁻¹C is faithful, full and an isomorphism with no further condition, so the criterion (⋆⋆) always holds and the finding’s « iff » holds with both sides true; the sufficiency is proved without comparing two sections.',
    verdict: 'holds, more generally',
    lean: 'lean/Grothendieck/Folder106.lean',
    theorems: ['remplacementCofibrant', 'relevementFaible', 'factorisationDeBrown', 'localisation_W₀_iso_localisation_W', 'critere_of_fidele', 'fidele', 'fidele_iff_critere', 'plein', 'qFunctor_iso'],
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
  {
    folder: '67',
    batch: 5,
    page: '90',
    name: "Involutions and triples (finding)",
    statement:
      "For any ring k and any k-module M on which 2 is injective, involutions σ of M correspond to triples (P, Q, m) — P = M₊, Q = M₋, m ⊂ P/2P ⊕ Q/2Q meeting each summand trivially — by an equivalence of categories, with no finiteness hypothesis.",
    found:
      "Holds as stated, for non-commutative k too, since 2 is central. 2-regularity is the only hypothesis used; fullness needs no finiteness, a σ-map being determined on 2P × 2Q. Not proved: the two Corollaries (pp. 90, 99). The finding’s literature question stays open.",
    verdict: 'holds, more generally',
    lean: 'lean/Grothendieck/Folder67.lean',
    theorems: ["equivalence", "inverse_obj_iso", "essSurj_witness"],
  },
  {
    folder: '133',
    batch: 3,
    page: '46–52',
    name: "Centre and derived group by two crossed modules (finding)",
    statement:
      "For N ⊃ D(G) and N′ ⊂ Cent(G): N′ = Cent(G) iff Ψ_G is injective (p. 46); N = D(G) iff the values of λ_G generate (pp. 51–52); under a central extension E of π₀ by π₁, the commutators of G₁ change by c_E (pp. 48, 52).",
    found:
      "Holds. Page 46 needs only N′ ⊂ Cent(G), from which [N, N′] = 1 follows; π₀ commutative follows from N ⊃ D(G); the page’s open sign is fixed, the correction term being c_E(ḡ, z̄). Partly proved: the change of Ψ and λ is proved as an identity of commutators in G₁, not as equality of maps.",
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder133.lean',
    theorems: ["injective_Psi_iff", "eq_commutator_iff_lam_surjective", "commutator_G1", "Psi_G1", "lam_G1"],
  },
  {
    folder: '156-1',
    batch: 1,
    page: '10–13',
    name: "The segment model is a biorder (finding)",
    statement:
      "A model of a one-dimensional form that is a single segment (F1–F5 with F′3) is the same as a poset with distinct least and greatest elements, dense and locally directed both ways, segments being the intervals; the order need not be total.",
    found:
      "Holds in both directions, with a non-total example in ℚ². The forward direction uses only F1, F2, F′3 and F4; F′3 is exactly the two directedness conditions; in the converse F4 holds without its regularity hypothesis.",
    verdict: 'holds',
    lean: 'lean/Grothendieck/Folder156_1.lean',
    theorems: ["biorder", "le_swap", "intervals_axioms", "intervals_segModel", "example_segModel"],
  },
  {
    folder: '156-3',
    batch: 1,
    page: '11–15',
    name: "Betweenness from the cuts (finding)",
    statement:
      "For a tronçon ordonné, comparability and the unlabelled partitions of the C(ε) determine strict betweenness, hence the order up to reversal; comparability alone does not.",
    found:
      "Holds; only density and directedness are used. The reading’s footnote on p. 11 is false when the extremities are incomparable: R̄(a, b, c) ⇔ R(a, b, c) ∨ b ∈ {a, c} needs a and c comparable (counterexample: the product order on ℕ²); the lemma of p. 13 never meets that case.",
    verdict: 'holds',
    lean: 'lean/Grothendieck/Folder156_3.lean',
    theorems: ["middle_iff", "order_of_cuts", "cmp_alone_insufficient", "btwLe_reading_fails"],
  },
  {
    folder: '77',
    batch: 4,
    page: '68–71, 87',
    name: 'The universal discriminant',
    statement:
      'For the universal quadratic form of odd rank, the determinant of the polar form is divisible by 2 in ℤ[Y], so the half-discriminant δ′ is defined over any base. In even rank 2n, (−1)ⁿΔ = B² − 4C with B the sum over perfect matchings of the products of the off-diagonal coefficients.',
    found:
      'The odd case holds for every odd rank: modulo 2 the polar matrix equals an antisymmetric matrix over ℤ[Y], whose determinant vanishes, a shorter route than the page’s count of graphs. The even case is proved in ranks 2 and 4, where the opposite sign is refuted and the coefficients of p. 87 are confirmed; the general even rank needs a Pfaffian, which mathlib lacks.',
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder77.lean',
    theorems: ['two_dvd_det_polar', 'det_polar_eq', 'disc_rank_two', 'disc_rank_four', 'not_dvd_rank_four'],
  },
  {
    folder: '84',
    batch: 4,
    page: '63–64, 85–86',
    name: 'Product of quadratic algebras',
    statement:
      'In split coordinates, over any commutative ring and without dividing by 2, 2U₁U₂ + b₁U₂ + b₂U₁ satisfies the quadratic equation with b = b₁b₂, c = c₁b₂² + c₂b₁² − 4c₁c₂, so δ = δ₁δ₂. The map from E₁ ⊗ E₂ modulo Im(σ₁⊗σ₂ − id) to E₁ * E₂ is bijective iff 2R + b₁R + b₂R = R.',
    found:
      'Both hold over the ring itself, with no base change and no rank argument; the reading’s correction of « 4c₁c₁ » to 4c₁c₂ is confirmed. For the invariants, the page’s « universally » is needed: over ℤ[X] with b₁ = X, b₂ = 0 the map is an isomorphism while (2, X) is a proper ideal. The pointwise and intrinsic forms are not proved.',
    verdict: 'holds',
    lean: 'lean/Grothendieck/Folder84.lean',
    theorems: ['identity_page64', 'tensor_root', 'disc_mul', 'coinvariants_bijective_iff', 'invariants_universally_iff', 'invariants_not_iff'],
  },
  {
    folder: '85',
    batch: 2,
    page: '10, 30, 40',
    name: 'The invariant of a rotation of order 5',
    statement:
      'For g ∈ GL₂(R) nowhere scalar, with A(g) = Tr(g)²/det g − 2, g⁵ is scalar iff A(g)² + A(g) − 1 = 0; then A(g²) = −1 − A(g). An explicit (2,3,5) model exists over ℤ[ζ₅].',
    found:
      'The computation holds over every base, characteristics 2, 3 and 5 included; the exclusion of characteristic 5 on p. 30 is needed only without the hypothesis « nowhere scalar ». An explicit split model needs ℤ[ζ₅], which is why p. 40 speaks of forms of PGL₂. Rigidity and representability by Spec ℤ[T]/(T² + T − 1) are not proved.',
    verdict: 'partly proved',
    lean: 'lean/Grothendieck/Folder85.lean',
    theorems: ['invA_smul', 'sq_add_sub_of_pow_five', 'pow_five_of_sq_add_sub', 'invA_sq_of_root', 'exists_model_adjoinRoot'],
  },
];
