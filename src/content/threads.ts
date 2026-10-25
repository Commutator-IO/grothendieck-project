import type { FindingLink, Thread } from '../lib/types.ts';

/**
 * The fifteen threads and the typed links between findings.
 *
 * A thread follows one object or question across folders; its order is that of
 * the question, not a chronology. A link records that an object, a notation or
 * a question recurs or is carried on, never influence or priority. Every step
 * and link gives its basis: `edition` marks our own inference (« rapprochement
 * de l'édition »). Dates are not stored here: the page reads them at render
 * time from the inventory (catalogue.ts), dated-leaves.json and
 * proposed-datings.json. French quotations from the leaves stay in « ».
 */
export const THREADS: Thread[] = [
  {
    id: "topoi-classifying-theories",
    title: "Topoi: classifying theories, multiplying spaces",
    intro:
      "Folders 161-1 to 161-4 (inv. [vers 1963-1973]; proposed 1973 for 161-3 and 161-4) ask two questions about topoi. First: which algebraic structures (fields, absolutely flat rings, rings of definite characteristic, rings with irreducible spectrum) have a classifying topos, and how to present it by subtopoi and topologies, coherent or not. Second: when is the topos of a product the product of the topoi? The thread follows the lattice of subtopoi, the tool both questions use, then the criteria saying that a category is a topos or a topos of presheaves, up to SGA 4 (folder 37) and the gluing of folder 116.",
    steps: [
      { id: "161-3-fields-partition" },
      {
        id: "161-2-lambda-types-split-with-161-3",
        from: {
          sentence:
            "The λ-types manuscript that this page belongs to (161-3, pp. 35–43) and the fair copy in 161-2 (pp. 97–106) are one campaign: the half-legible line of 161-2 p. 92 is the argument written out in 161-3 pp. 39–41. (Same notation S^T_λ, R^λ_T; finding of the next card.)",
          basis: "same-object",
        },
      },
      {
        id: "161-2-vn-regular-cartesian-presheaf-classifier",
        from: {
          sentence:
            "In the same campaign, pp. 41–42 of 161-2 pass from fields to « pseudo-fields » (A ≅ A_f × A/fA), whose theory is cartesian.",
          basis: "same-object",
        },
      },
      {
        id: "161-2-field-classifier-absolutely-flat-site",
        from: {
          sentence:
            "The classifier of fields is obtained from this presheaf classifier by imposing a single covering family, Spec A_f ⊔ Spec A/f.",
          basis: "same-object",
        },
      },
      {
        id: "161-2-irreducible-and-zero-dimensional-not-coherent",
        from: {
          sentence:
            "Same approach: present a subtopos of the classifier of rings by a topology on affine schemes of finite type over ℤ, for rings with irreducible spectrum and rings of dimension 0. The resulting topologies are not quasi-compact.",
          basis: "same-object",
        },
      },
      {
        id: "161-2-definite-characteristic-join-of-subtopoi",
        from: {
          sentence:
            "Non-coherence returns for rings of definite characteristic: the subtopos classifying them is the join of an open subtopos and a non-open one.",
          basis: "same-object",
        },
      },
      {
        id: "161-3-two-product-by-intersection",
        from: {
          sentence:
            "The joins and meets of the lattice of subtopoi also serve for the 2-product, built as the intersection of two subtopoi of the topos of presheaves on C × D. (The link between the two folders, same tool, is the edition's inference.)",
          basis: "edition",
        },
      },
      {
        id: "161-4-topos-leaves-continue-161-6",
        from: {
          sentence:
            "The question (C × D)^ ≈? Ĉ × D̂ returns on the two topos leaves filed in 161-4, which continue page 22 of 161-6.",
          basis: "cross-reference", where: "161-4.modern.tex l. 185; 161-6.modern.tex l. 176",
        },
      },
      {
        id: "161-3-product-converse",
        from: {
          sentence:
            "From presheaves to spaces: Top(X × Y) → Top(X) × Top(Y) under a hypothesis weaker than local compactness. (Same question, the topos of a product; the order 161-4 → 161-3 is the edition's inference.)",
          basis: "edition",
        },
      },
      {
        id: "161-3-locale-spatiality-suprema-proof",
        from: {
          sentence:
            "Same pages: the spatiality of a product of locales is proved in three passages to the join in the lattice of subobjects.",
          basis: "same-object",
        },
      },
      {
        id: "161-3-infinite-product-criterion",
        from: {
          sentence:
            "The finite argument is repeated for an arbitrary family, with two « all but one » clauses.",
          basis: "same-object",
        },
      },
      {
        id: "161-1-giraud-recognition-half-page",
        from: {
          sentence:
            "Another identification « topos = sheaves on a site »: Giraud's recognition criterion, obtained in half a page as a converse. (The reading of 161-3 elsewhere refers to « page 13 of folder 161-1, where [the same construction] is written independently ».)",
          basis: "edition", where: "161-3.modern.tex l. 1137",
        },
      },
      {
        id: "37-ind-topos-exercise",
        from: {
          sentence:
            "Same question, recognising a topos, in the form of an exercise typed for SGA 4 VI: when is Ind(C) a topos?",
          basis: "edition",
        },
      },
      {
        id: "116-presheaf-gluing-continuous-gluing-functor",
        from: {
          sentence:
            "When is a topos glued along an open a topos of presheaves? Gluing along an open is already what gives the join of 161-2 pp. 47–49 (step 6). (The pairing of the two periods is the edition's.)",
          basis: "edition",
        },
      },
    ],
  },
  {
    id: "test-categories-derivators",
    title: "Test categories, localizers, derivators",
    intro:
      "Folders 104 to 118 (1982-1983, many written on dated machine listings) and 158 (about 1990-1991) work on test categories and asphericity, then on classes of weak equivalences (basic localizers) and model categories, and finally on derivators. The thread starts from a question asked without argument (« Is Δ° a test category? »), passes through a proposition false as stated (114) and its correct form (118), and ends, with 158, on the question of what the homotopy condition imposes on a finite category.",
    steps: [
      { id: "108-delta-op-not-test" },
      {
        id: "112-linearization-beyond-the-simplex",
        from: {
          sentence:
            "Another question about what remains of simplicial theory when one leaves Δ: the Dold–Kan correspondence for a small category A. (The edition's inference.)",
          basis: "edition",
        },
      },
      {
        id: "114-total-asphericity-independent-of-localizer",
        from: {
          sentence:
            "From linearisation to total asphericity: 114 asserts that it does not depend on the localizer. (The edition's inference.)",
          basis: "edition",
        },
      },
      {
        id: "118-product-condition-iv",
        from: {
          sentence:
            "In 118 the product condition is stated correctly: A^ → Hot commutes with binary products if and only if the a × b are aspherical, and total asphericity further requires A to be aspherical.",
          basis: "same-object",
        },
      },
      {
        id: "118-groupoid-products-not-totally-aspherical",
        from: {
          sentence:
            "Same pages: a connected groupoid shows that stability under products does not suffice for asphericity.",
          basis: "same-object",
        },
      },
      {
        id: "118-strong-saturation",
        from: {
          sentence:
            "Still in 118: every basic localizer is strongly saturated.",
          basis: "same-object",
        },
      },
      {
        id: "117-adjunction-equivalence-criterion",
        from: {
          sentence:
            "From localizers to functors between categories with weak equivalences: an adjunction criterion that induces equivalences on all diagram categories. (The edition's inference; 117 is dated on its leaves 24 November 1983 and December 1983.)",
          basis: "edition",
        },
      },
      {
        id: "106-section-criterion-span-faithfulness",
        from: {
          sentence:
            "Same framework (a category with weak equivalences and cofibrations), this time to know when the zigzags of an arrow compute W⁻¹C. (The edition's inference.)",
          basis: "edition",
        },
      },
      {
        id: "107-relative-square-rectification",
        from: {
          sentence:
            "The same difficulty, making strict what commutes only up to homotopy, appears for a lifted square in a model category. (The edition's inference.)",
          basis: "edition",
        },
      },
      {
        id: "107-hot-sequential-colimits",
        from: {
          sentence:
            "Same folder, same pages 20–22: extension of homotopies along cofibrations gives surjectivity for sequential colimits in Hot.",
          basis: "same-object",
        },
      },
      {
        id: "105-interval-anodyne-generators",
        from: {
          sentence:
            "In a topos where the cofibrations are the monomorphisms, the trivial cofibrations are generated from intervals. (The edition's inference.)",
          basis: "edition",
        },
      },
      {
        id: "105-derivator-crible-excision",
        from: {
          sentence:
            "Same folder: half of axiom W7 follows from the derivator axioms alone.",
          basis: "same-object",
        },
      },
      {
        id: "158-finite-monoid-right-zero",
        from: {
          sentence:
            "In the notes around the Derivators, the homotopy condition (simply connected categories of elements) is compared with cofilteredness, first for a finite monoid. (The edition's inference; date about 1990-1991.)",
          basis: "edition",
        },
      },
      {
        id: "158-minimal-monoid-cofiltered",
        from: {
          sentence:
            "Same question for a monoid with a minimal element: the folder builds an explicit M-set that makes the condition fail.",
          basis: "same-object",
        },
      },
      {
        id: "158-finite-category-cofiltered",
        from: {
          sentence:
            "Same question for a finite category, which page 70 relates to the total asphericity of X°: we are back at the question of step 3.",
          basis: "same-object",
        },
      },
    ],
  },
  {
    id: "gr-categories-picard-stacks",
    title: "Gr-categories and Picard stacks (around 1974)",
    intro:
      "We start from the sign ε(L) that prevents ordering a tensor product of invertibles. We then pass through Sinh's theorem (a thesis whose typescript forms folder 135) and the letter to Deligne of 27 August 1974, two incomplete copies of which are divided between 134-1 and 103, on Picard stacks and pinned Gr-stacks. We end with the obstructions in H³ that folders 133 and 132 find again, for crossed modules and for extensions of non-connected topological groups.",
    steps: [
      { id: "161-1-epsilon-sign-obstruction" },
      {
        id: "135-sinh-theorem-classification",
        from: {
          sentence:
            "The reading of 161-1 refers to folder 135, which computes the smallest case of a non-strict Picard category, that of graded lines with the Koszul rule.",
          basis: "cross-reference", where: "161-1.modern.tex l. 428",
        },
      },
      {
        id: "134-1-picard-sign-sequence",
        from: {
          sentence:
            "The letter of 27.8.74 classifies Picard stacks pinned by M, N, and the last term of its exact sequence is the symmetry invariant of L ⊗ L, the object of step 1.",
          basis: "cross-reference", where: "134-1.modern.tex l. 162 et 134; -2.modern.tex l. 1264",
        },
      },
      {
        id: "134-1-sign-realisation-universal-argument",
        from: {
          sentence:
            "Same page 5: every homomorphism M → ₂N would be realised (« barring error ») by a Picard stack.",
          basis: "same-object",
        },
      },
      {
        id: "134-1-first-four-of-eight-pages",
        from: {
          sentence:
            "The copy in 134-1 stops at page 6, whereas the reproduction kept in 103 continues four pages further.",
          basis: "cross-reference", where: "103.modern.tex l. 527; 134-1.modern.tex l. 147",
        },
      },
      {
        id: "103-letter-leaf-order-missing-leaf",
        from: {
          sentence:
            "In the copy in 103 the leaves read 8–11, 14–15, 12–13, and one is missing. (The same letter.)",
          basis: "same-object",
        },
      },
      {
        id: "103-gr-stacks-relative-cohomology-BG",
        from: {
          sentence:
            "In this continuation of the letter, the Gr-stacks pinned by (G, N) are described by the relative cohomology of B_G. (Pp. 14–15 of 103.)",
          basis: "same-object",
        },
      },
      {
        id: "133-centre-and-derived-group-from-two-crossed-modules",
        from: {
          sentence:
            "Folder 133 finds again « the same scheme as that of the Gr-categories of folder 135 », with an obstruction in H³(B_π₀/X, π₁), for two crossed modules.",
          basis: "cross-reference", where: "133.modern.tex l. 384",
        },
      },
      {
        id: "132-taylor-obstruction",
        from: {
          sentence:
            "An obstruction in H³(π₀H, π) returns for extensions of a non-connected topological group. (Same obstruction H³ and indeterminacy H²; the pairing of the two folders is the edition's.)",
          basis: "edition",
        },
      },
      {
        id: "132-nonconnected-extension-classification",
        from: {
          sentence:
            "Same page 19: when the extension exists, it classifies the extensions by an arbitrary discrete group.",
          basis: "same-object",
        },
      },
      {
        id: "132-fibre-product-pi2-defect",
        from: {
          sentence:
            "Pp. 1–3 compare the fundamental groupoid of a fibre product with the 2-categorical fibre product, and the defect comes from π₂.",
          basis: "same-object",
        },
      },
      {
        id: "132-peripheral-gr-category",
        from: {
          sentence:
            "Pp. 5–8 compute the 2-group of self-equivalences of the model of a surface with boundary, which opens thread 10.",
          basis: "same-object",
        },
      },
    ],
  },
  {
    id: "pursuing-stacks-typescript",
    title: "Pursuing Stacks, from the letters to Breen to the typescript",
    intro:
      "This thread follows the physical pieces of Pursuing Stacks scattered among 134-1, 134-2, 134-8, 106, 109, 112 and 113: the annotated copies of the 1974 letter, the 1975 letters to Breen reprinted as an appendix, the listing sheets of 1982 that bound the drafts from below, the plans and titles of 1983, the circulation of the typescript and the list of corrections sent in December 1983 and February 1984.",
    codicological: true,
    steps: [
      { id: "134-1-margin-notes-forwarding-undated" },
      {
        id: "134-2-breen-letters-printed",
        from: {
          sentence:
            "The cover of 134-1 reads « Lettres Breen 75, 76 »; the three 1975 letters to Breen are printed in an appendix to chapter I. (134-2.modern.tex l. 435 refers to the letter of 134-1; dates.)",
          basis: "cross-reference", where: "134-2.modern.tex l. 435",
        },
      },
      {
        id: "134-2-july-letter-junction",
        from: {
          sentence:
            "In the July 1975 letter as printed, pages 56 and 57 follow each other with no gap.",
          basis: "same-object",
        },
      },
      {
        id: "106-listing-dates-not-notebook",
        from: {
          sentence:
            "The 1982 drafts are written on listings whose machine date bounds them only from below. (24-25 August 1982 in 106.)",
          basis: "date",
        },
      },
      {
        id: "113-listing-stamps-bound-below-only",
        from: {
          sentence:
            "Same observation in 113 (stamp of 16 September 1982). (Same listing paper; dates.)",
          basis: "same-object",
        },
      },
      {
        id: "112-listing-paper-undated",
        from: {
          sentence:
            "112 is on the same listing paper as 115 (2 June 1982), but the inventory leaves it « s.d. ». (Same paper; dates.)",
          basis: "same-object",
        },
      },
      {
        id: "109-volume-plan-chapters",
        from: {
          sentence:
            "In 109, a plan of the first volume in eight chapters, with the appendix of the letters to Breen. (The edition's inference, same work; inv. 1983-1984.)",
          basis: "edition",
        },
      },
      {
        id: "109-section-titles-130-133",
        from: {
          sentence:
            "Same folder: draft of the titles of §§ 130–133 and references to the typescript by its numbering.",
          basis: "same-object",
        },
      },
      {
        id: "134-8-modelizing-story-distribution",
        from: {
          sentence:
            "The « Modelizing Story » section (pp. 259–381 of the typescript) is reproduced in three copies and sent to Brown, Mebkhout and Contou-Carrère. (Same object: the typescript's numbering.)",
          basis: "same-object",
        },
      },
      {
        id: "134-8-copying-leaf-misfiled",
        from: {
          sentence:
            "The same instruction sheet does not belong to the chapter VII that the folder's title announces.",
          basis: "same-object",
        },
      },
      {
        id: "109-correction-list-dates",
        from: {
          sentence:
            "Reading the typescript for its English reaches p. 354 on 6 February 1984. (Dates: « Sent 19/12/83 », « Sent 6/2/84 ».)",
          basis: "date",
        },
      },
    ],
  },
  {
    id: "lefschetz-standard-conjectures",
    title: "Lefschetz and the standard conjectures",
    intro:
      "This thread starts from Poincaré algebras and the formalism of correspondences (11). It passes to purely algebraic criteria for the hard Lefschetz theorem and to the variants A′⁰, A″⁰ of the Lefschetz-type conjecture (16, letters to Coates of 1966-1967). It ends in the theory of cycles of degree one (14, letter to Serre of 27.8.1965) and Griffiths' theorem by an algebraic route (36). The part « Algebraic cycles and standard conjectures » of the Lean article already groups 11 and 16.",
    steps: [
      { id: "11-simplicial-bivariant-poincare-equivalence" },
      {
        id: "11-page-47-breaks-off",
        from: {
          sentence:
            "On the same correspondences between the powers X^I, the draft of pp. 41–47 breaks off in mid-sentence. (Same object, pp. 37–47.)",
          basis: "same-object",
        },
      },
      {
        id: "11-tautological-diagonal-product-rule",
        from: {
          sentence:
            "The next leaf in his hand (p. 50) opens the « tautological subalgebra of H*(X^n) ». (Same object as the previous card.)",
          basis: "same-object",
        },
      },
      {
        id: "16-graded-ring-lefschetz-criterion",
        from: {
          sentence:
            "The Lefschetz package (L, Λ, primitive projectors) is characterised in a graded ring, with no underlying module. (The edition's inference, same family of graded algebras with duality; inv. 1966-1967 for 16.)",
          basis: "edition",
        },
      },
      {
        id: "16-universal-lefschetz-ring",
        from: {
          sentence:
            "Same folder: the universal ring Φ₀ = ℤ[L₀, Λ₀]. (Pp. 13–16.)",
          basis: "same-object",
        },
      },
      {
        id: "16-page-21-not-gorenstein",
        from: {
          sentence:
            "The six-dimensional algebra of p. 21 separates the Lefschetz property from the non-vanishing of the top power.",
          basis: "same-object",
        },
      },
      {
        id: "16-hodge-algebras-order-2",
        from: {
          sentence:
            "The « Hodge algebras of order 2 » make Lefschetz and Poincaré two non-degeneracy conditions.",
          basis: "same-object",
        },
      },
      {
        id: "16-algebraic-iso-suffices",
        from: {
          sentence:
            "From algebra to cycles: any algebraic isomorphism H^{2n−i} → H^i suffices. (Same object, the letter of p. 47 dated 6.1.1966.)",
          basis: "same-object",
        },
      },
      {
        id: "16-weak-variants-imply-strong",
        from: {
          sentence:
            "On the next page, A′⁰ and A″⁰ together imply A⁰. (P. 49.)",
          basis: "same-object",
        },
      },
      {
        id: "14-albanese-equivalence-ring",
        from: {
          sentence:
            "From conjectures on classes to equivalences on cycles: « Albanese equivalence », placed between rational and algebraic equivalence. (The edition's inference; the letter to Serre of 27.8.1965 filed in 14 states the conjectures on cycles.)",
          basis: "edition",
        },
      },
      {
        id: "14-two-albanese-redactions",
        from: {
          sentence:
            "Two drafts of this theory use the same numbers for different statements.",
          basis: "same-object",
        },
      },
      {
        id: "14-nakai-euler-characteristic-criterion",
        from: {
          sentence:
            "Same folder: an ampleness criterion by growth of χ (Mumford–Nakai). (Same object, folder 14, pp. 93–94; the thematic link is the edition's.)",
          basis: "edition",
        },
      },
      {
        id: "36-griffiths-conditional-l-adic",
        from: {
          sentence:
            "A Lefschetz decomposition given by an algebraic correspondence serves as hypothesis to an ℓ-adic Griffiths theorem. (Same object, hypothesis a) of 36; the pairing is the edition's.)",
          basis: "edition",
        },
      },
    ],
  },
  {
    id: "tannakian-motive-realisations",
    title: "Tannakian categories and realisations of motives",
    intro:
      "The thread begins with thesis subject no. 22 (1964), « algebraic preliminary to the theory of motives », annotated « travail Saavedra en train ». It passes through the question of the De Rham/Betti double lattice (13, letter to Mumford of 1965), the numerical invariants and polarisations of ⊗-categories (10), positive forms on motives (12), real fibre functors and the real Frobenius (15, 18), and ends on the Hopf algebroid of 155, whose reading refers to folder 10. The readings of 12, 14 and 15 refer to one another for notation.",
    steps: [
      { id: "66-subject-22-commissioned" },
      {
        id: "13-double-niveau-de-rham-betti",
        from: {
          sentence:
            "A question on Tannakian categories with two fibre functors: is the functor M ↦ (T_DR, T_B, φ) fully faithful? (The edition's inference; date: the letter to Mumford of 1.11.1965 in 13.)",
          basis: "edition",
        },
      },
      {
        id: "13-double-lattice-invariants",
        from: {
          sentence:
            "Same folder: V ∩ T′(V) = V^H in full generality, which reformulates the question. (Same object: V^G = V ∩ g(V̄), pp. 33–34 and 47–48.)",
          basis: "same-object",
        },
      },
      {
        id: "10-numerical-character-rank-one-torus",
        from: {
          sentence:
            "A Tannakian category whose band is a rank-one torus is determined by its « numerical characters ». (12.modern.tex l. 341–342 relates the notations of 10 and 13; same object: band, fibre functor.)",
          basis: "cross-reference", where: "12.modern.tex l. 341–342",
        },
      },
      {
        id: "10-split-ring-ga-rtimes-gm",
        from: {
          sentence:
            "Same folder: classification of the representations of 𝔾_a ⋊ 𝔾_m and of their ring.",
          basis: "same-object",
        },
      },
      {
        id: "10-hodgian-polarisations-torsor",
        from: {
          sentence:
            "The « Hodgian » polarisations of a graded ⊗-category form a torsor.",
          basis: "same-object",
        },
      },
      {
        id: "10-polarisation-leaves-undated-against-p108",
        from: {
          sentence:
            "Nothing dates these leaves relative to the typed programme of p. 108, addressed to Saavedra (step 1). (Same object; reference to the same name.)",
          basis: "same-object",
        },
      },
      {
        id: "12-positive-forms-leaves-order",
        from: {
          sentence:
            "The positive forms on motives (12) take up the polarisation axioms, with their changes of sign. (The edition's inference; 12 refers to 10 for notation, 12.modern.tex l. 342.)",
          basis: "edition", where: "12.modern.tex l. 342",
        },
      },
      {
        id: "15-real-fibre-functor-criterion",
        from: {
          sentence:
            "For a motivic category over ℚ, the existence of a real fibre functor depends on the connectedness of U. (15.modern.tex l. 170 and l. 326 refer to 12 and 10.)",
          basis: "cross-reference", where: "15.modern.tex l. 170 et",
        },
      },
      {
        id: "18-real-frobenius-trivial-converse",
        from: {
          sentence:
            "The real Frobenius of a motive over ℝ: the characterisation of 18 p. 35 is false as stated. (Same object: motives over ℝ, ℚ(−2n).)",
          basis: "same-object",
        },
      },
      {
        id: "18-archimedean-lattice-cocycle",
        from: {
          sentence:
            "Same folder: comparing the integral Betti lattices attached to the archimedean places gives a cocycle with values in G(k).",
          basis: "same-object",
        },
      },
      {
        id: "155-takeuchi-idealiser",
        from: {
          sentence:
            "The Hopf algebroid structure over a non-central base, presented by an idealiser. (155.modern.tex l. 275 refers to pp. 156–179 of folder 10.)",
          basis: "cross-reference", where: "155.modern.tex l. 275",
        },
      },
    ],
  },
  {
    id: "crystals-barsotti-tate",
    title: "Crystals and Barsotti–Tate groups",
    intro:
      "This thread goes from artinian rings with divided powers (5) to ordinary moduli spaces and formal groups (6, letter to Tate of May 1966), then to the lattice det T_p (9, proposed 1966, Pisa). It passes through the « laïus » of November-December 1966 on stratifying cohomology and a site without divided powers (7), then crystalline torsion (4). It continues with the universal extension and the orthogonality of Frobenius kernels (54), the Lubin–Tate lifting by the Hodge filtration (8), the Nice talk (1970) and the drafts of the Montreal volume (1974) (129). It ends on the leaves of 161-5 that nothing dates relative to the « mysterious functor ».",
    steps: [
      { id: "5-universal-artinian-pd-normal-form" },
      {
        id: "6-ordinary-moduli-complete-intersection",
        from: {
          sentence:
            "Deformations of ordinary abelian varieties are described by extensions of Barsotti–Tate groups. (The edition's inference; dates: 5 is 1965, 6 is the letter to Tate, May 1966.)",
          basis: "edition",
        },
      },
      {
        id: "6-same-formal-group-not-isogenous",
        from: {
          sentence:
            "Same folder: two abelian surfaces can have the same formal group without being isogenous. (Same object: the formal group.)",
          basis: "same-object",
        },
      },
      {
        id: "6-formal-group-not-in-abelian-variety",
        from: {
          sentence:
            "Same folder: a formal group that embeds in no abelian variety.",
          basis: "same-object",
        },
      },
      {
        id: "9-det-etale-tate-iso",
        from: {
          sentence:
            "For A ordinary, det T_p(φ̃)_ét / √deg φ̃ does not depend on the polarisation. (Dates: proposed-datings.json ties p. 2 of 9 to the stay in Pisa and to the letter to Tate in 6; same object: the étale part of T_p of an ordinary variety.)",
          basis: "same-object",
        },
      },
      {
        id: "7-catalogue-date-1967",
        from: {
          sentence:
            "The « laïus » of November-December 1966 (and not 1967) is about de Rham cohomology of varieties in characteristic p. (Dates.)",
          basis: "date",
        },
      },
      {
        id: "7-strat-invariance-problem",
        from: {
          sentence:
            "Same notebook, pp. 70–71: is stratifying cohomology invariant under nilpotent immersion?",
          basis: "same-object",
        },
      },
      {
        id: "7-noninfinitesimal-site",
        from: {
          sentence:
            "The fair copy of 1967 (pp. 16–18) proposes a site without divided powers. (Same object; dates: pp. 2–18 dated July-August 1967.)",
          basis: "same-object",
        },
      },
      {
        id: "4-vanishing-unit-root-bound",
        from: {
          sentence:
            "A bound on the unit eigenvalues of Frobenius on vanishing crystalline cohomology, under admitted crystalline hypotheses. (The edition's inference; 4 is proposed 1966.)",
          basis: "edition",
        },
      },
      {
        id: "54-universal-extension-de-rham-dual",
        from: {
          sentence:
            "The universal vector extension and the Hodge filtration of H¹_dR of the dual. (The edition's inference: de Rham and crystalline cohomology of abelian varieties.)",
          basis: "edition",
        },
      },
      {
        id: "54-frobenius-kernels-orthogonal",
        from: {
          sentence:
            "Same folder: orthogonality of ker F_A and ker F_B for the Weil pairing.",
          basis: "same-object",
        },
      },
      {
        id: "8-lubin-tate-via-hodge-filtration",
        from: {
          sentence:
            "The Hodge filtration also determines the Lubin–Tate lifting, by crystalline deformation theory alone. (Same object: the Hodge filtration of a BT group; the pairing of 54 and 8 is the edition's.)",
          basis: "edition",
        },
      },
      {
        id: "129-nice-outline",
        from: {
          sentence:
            "The outline of the Nice talk: BT groups, Serre–Tate, divided powers, the crystalline site, programme of the crystalline Dieudonné functor. (Dates: 1970; same object.)",
          basis: "same-object",
        },
      },
      {
        id: "129-drafts-of-montreal-volume",
        from: {
          sentence:
            "Same folder: the drafts of the Montreal volume (1974). (Same object, 129.)",
          basis: "same-object",
        },
      },
      {
        id: "161-5-leaves-undated-mysterious-functor",
        from: {
          sentence:
            "Nothing dates the leaves of 161-5 relative to the public statement of the « mysterious functor » problem (1970). (The edition's inference; the reading of 133 also refers to pp. 22–23 of 161-5 for BT groups, 133.modern.tex l. 1296.)",
          basis: "edition", where: "133.modern.tex l. 1296",
        },
      },
    ],
  },
  {
    id: "tame-pi1-to-sga7",
    title: "From tame π₁ to SGA 7",
    intro:
      "This thread starts from the letter to Serre of 1959 on the fundamental group scheme (29). It passes through the 1967 exchange with Murre on tame ramification, the axiomatics of « ramification domains », the Kummer gerbe, the tame π₁ of a formal scheme and tame inertia. It then joins SGA 7: the action of inertia on π₁ (34), the plan and the distribution of the talks (35), then monodromy and the defect of invariant cycles (36). The reading of 36 refers to the plan of 35.",
    steps: [
      { id: "29-fundamental-group-scheme-via-torsors" },
      {
        id: "29-order-not-chronology",
        from: {
          sentence:
            "In the folder, the order of the pages is not the order of writing: the 1959 letter is at p. 124, the 1967 exchange with Murre at the front and out of order. (Dates.)",
          basis: "date",
        },
      },
      {
        id: "29-ramification-domain-axioms",
        from: {
          sentence:
            "The synthesis the folder is heading to: the « ramification domains ». (Same object, pp. 188–216.)",
          basis: "same-object",
        },
      },
      {
        id: "29-kummer-gerbe-root-stack",
        from: {
          sentence:
            "Example 2 of the same synthesis: tame coverings of (S, D) as étale coverings of a gerbe of μ_n. (Same object, pp. 199–200.)",
          basis: "same-object",
        },
      },
      {
        id: "29-formal-tame-pi1-self-intersection",
        from: {
          sentence:
            "The tame π₁ of a regular formal scheme is a central extension whose class is the self-intersection. (Same object: tame π₁ relative to a normal crossings divisor.)",
          basis: "same-object",
        },
      },
      {
        id: "29-inertia-matrix-determinant",
        from: {
          sentence:
            "The induced map on tame inertia is given by the matrix of multiplicities. (Same object: the typescript « Comportement fonctoriel des groupes d'inertie ».)",
          basis: "same-object",
        },
      },
      {
        id: "34-lci-local-1-asphericity",
        from: {
          sentence:
            "In SGA 7: a morphism with complete-intersection closed fibre is locally 1-aspherical, and specialisation of H¹ is bijective for groups of order prime to p. (The edition's inference; the title of 29 is « Autour de SGA 4 et SGA 7 ».)",
          basis: "edition",
        },
      },
      {
        id: "34-wild-inertia-outer-pi1",
        from: {
          sentence:
            "Talk VI: an open subgroup of inertia acts tamely, by outer automorphisms, on π₁^(p′). (Same object: inertia and π₁ prime to p.)",
          basis: "same-object",
        },
      },
      {
        id: "34-multiparameter-tame-monodromy",
        from: {
          sentence:
            "Same talk, over a strictly local base of any dimension. (Same object: Theorem 1.4, p. 167.)",
          basis: "same-object",
        },
      },
      {
        id: "35-exposes-reassigned",
        from: {
          sentence:
            "The plan of SGA 7 with the distribution of the talks: speakers' names crossed out and replaced. (Same object: SGA 7.)",
          basis: "same-object",
        },
      },
      {
        id: "35-dependency-graphs-redrawn",
        from: {
          sentence:
            "Same folder: three dependency graphs, the last of which separates qualitative and quantitative theorems.",
          basis: "same-object",
        },
      },
      {
        id: "36-h1-invariant-cycle-defect",
        from: {
          sentence:
            "« SGA 7 (ma part) »: an exact sequence for the defect of invariant cycles in H¹. (36.modern.tex l. 249: « Le plan de SGA 7 du dossier 35 portait… ».)",
          basis: "cross-reference", where: "36.modern.tex l. 249",
        },
      },
      {
        id: "36-orthogonality-regular-adic-base",
        from: {
          sentence:
            "Same folder: orthogonality between the toric part and the finite torsion part, over a regular adic base.",
          basis: "same-object",
        },
      },
    ],
  },
  {
    id: "non-flat-descent",
    title: "Non-flat descent and representability",
    intro:
      "The folders of the « Descentes » group (126 to 133, largely undated; 127 proposed 1965-1970) ask when one can descend along morphisms that are not flat: nilpotent ones, finite ones, epimorphisms of schemes. They lead to representability criteria by quasi-finite, unramified and étale schemes (131, about 1971), to an open-immersion criterion (102) and to Weil restriction (91), whose conditions 102 takes up.",
    steps: [
      { id: "126-fpqc-generated-topology" },
      {
        id: "126-nilpotent-deformation-quotient",
        from: {
          sentence:
            "Same folder: a flat equivalence relation that is effective modulo a nilpotent is effective before reduction. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "126-generic-descent",
        from: {
          sentence:
            "Same folder: descent data defined only on a dense open extend.",
          basis: "same-object",
        },
      },
      {
        id: "127-non-flat-descent-artinian-epimorphism",
        from: {
          sentence:
            "In 127, « non-flat descent » proper: the flat quotient problem descends along every epimorphism onto an artinian base. (128.modern.tex l. 178 places 126 to 133 in the same group; same object.)",
          basis: "cross-reference", where: "128.modern.tex l. 178",
        },
      },
      {
        id: "127-closure-flatness-artinian-or-trait",
        from: {
          sentence:
            "The « final statement » reduces flatness of the closure to artinian bases and traits. (Same object, pp. 2–4, 15.)",
          basis: "same-object",
        },
      },
      {
        id: "128-colength-one-equivalence-criterion",
        from: {
          sentence:
            "The reading of 127 refers to 128 for the exactness of A → A′ ⇉ A′ ⊗_A A′ when A′ is finite over an artinian local ring. (127.modern.tex l. 886, which the reading itself calls a pairing.)",
          basis: "cross-reference", where: "127.modern.tex l. 886",
        },
      },
      {
        id: "128-nilpotent-conductor-flat-descent",
        from: {
          sentence:
            "Same folder: effective descent of flat modules across a Milnor square. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "128-infinitesimal-descent-theorem",
        from: {
          sentence:
            "Same folder: an infinitesimal descent theorem for A′ finite over a semilocal ring.",
          basis: "same-object",
        },
      },
      {
        id: "100-proper-epimorphism-hom-descent",
        from: {
          sentence:
            "Another non-flat « epimorphism » (O_S → f_*O_S′ injective), this time to descend Homs of formally unramified schemes. (The edition's inference.)",
          basis: "edition",
        },
      },
      {
        id: "131-locally-quasi-finite-representability",
        from: {
          sentence:
            "The conditions of fpqc descent, effectivity on completions and artinian pro-representability become a representability criterion. (The edition's inference.)",
          basis: "edition",
        },
      },
      {
        id: "131-unramified-and-etale-corollaries",
        from: {
          sentence:
            "Same folder: the unramified and étale variants, and the announced applications.",
          basis: "same-object",
        },
      },
      {
        id: "102-open-immersion-criterion",
        from: {
          sentence:
            "An open-immersion criterion under hypotheses of the same type (fpqc sheaf, filtered colimits, adic limits of artinian rings). (The edition's inference.)",
          basis: "edition",
        },
      },
      {
        id: "91-res-representable-by-scheme",
        from: {
          sentence:
            "The reading of 102 notes that p. 4 of 91 checks these same conditions for a representability theorem. (102.modern.tex l. 179.)",
          basis: "cross-reference", where: "102.modern.tex l. 179",
        },
      },
      {
        id: "91-local-functor-right-adjoint",
        from: {
          sentence:
            "Same folder: Weil restriction and the Greenberg functor as two cases of the same right adjoint.",
          basis: "same-object",
        },
      },
    ],
  },
  {
    id: "teichmuller-long-march",
    title: "Teichmüller and the Long March",
    intro:
      "This thread starts from the exact sequence 0 → ℤ^I → TS → T → 𝔖_I → 1 (132, 1974). It passes through the « operations » on maps (138) and the « variant » π₁ of the trinion and the equivariant trivialisation exponents (146, June 1978). Then come the equivariant Picard group of U₀,₃ (140-1), the Spring 81 exercise (145), the weightings of triangulations (144) and the Galois–Teichmüller category (142). The thread continues with anabelian faithfulness and the specialisation of cusps (149), the class of M₁,₁ over ℤ (147), and ends on the multimarked Teichmüller groupoid and the chart of special structures of M₀,₅ (148, October-November 1983). The readings of folders 142 to 149 almost all refer to 141 and 145.",
    steps: [
      { id: "132-teichmuller-boundary-sequence" },
      {
        id: "138-operations-belyi-extending",
        from: {
          sentence:
            "The « operations » on oriented maps are compositions with a covering of the sphere ramified over 0, 1, ∞. (The edition's inference: the cartographic group, surfaces with boundary.)",
          basis: "edition",
        },
      },
      {
        id: "146-variant-pi1-trinion",
        from: {
          sentence:
            "The « variant » fundamental group of the trinion, an extension of 𝔖_I by ℤ^I, redoes the sequence of step 1 on three points. (Same object: ℤ^I and 𝔖_I; the pairing is the edition's.)",
          basis: "edition",
        },
      },
      {
        id: "146-equivariant-trivialising-exponents",
        from: {
          sentence:
            "Same folder: the smallest exponents that trivialise the tangent bundles L_i 𝔖_I-equivariantly on M₀,I. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "140-1-equivariant-pic-u03",
        from: {
          sentence:
            "The Picard group of the stack [(P¹ − {0, 1, ∞})/𝔖₃] is ℤ/6, and the invariant section of O(6) answers the « L^⊗6 ≃ 1 » of 146. (Same object: exponent 6 for n = 4; the pairing is the edition's.)",
          basis: "edition",
        },
      },
      {
        id: "145-unit-exponent-exercise",
        from: {
          sentence:
            "Spring 81: in the free profinite group on l₀, l₁, the exponent p = 1 is the only possible one (« Exercice ! »). (The edition's inference; dates: 1981 for both.)",
          basis: "edition",
        },
      },
      {
        id: "144-triangulation-weighting-obstruction",
        from: {
          sentence:
            "The weightings of triangulations by {0, 1, ∞} and their obstruction in H¹(X, ℤ/3). (144.modern.tex l. 233–234 refers to 141 and to the extension ℰ of 145.)",
          basis: "cross-reference", where: "144.modern.tex l. 233–234",
        },
      },
      {
        id: "142-teichmuller-galois-category-etale",
        from: {
          sentence:
            "A single category of anabelian curves of all types, with the profinite completions of the isotopy classes. (142.modern.tex l. 265 refers to the order of the second draft of 145.)",
          basis: "cross-reference", where: "142.modern.tex l. 265",
        },
      },
      {
        id: "142-galois-image-conditions-single-curve",
        from: {
          sentence:
            "Same folder: necessary conditions for an automorphism of Π̂₁(X, I) to come from Gal(K̄/K). (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "149-dominant-faithfulness-curves",
        from: {
          sentence:
            "Two dominant morphisms to a hyperbolic curve that induce the same outer homomorphism are equal. (The edition's inference: faithfulness of the π₁ functor; the reading of 149 refers to 141 and 145, 149.modern.tex l. 119, 249.)",
          basis: "edition", where: "149.modern.tex l. 119, 249",
        },
      },
      {
        id: "149-cusp-specialisation-index",
        from: {
          sentence:
            "Same folder: rational sections and loop subgroups of the cusps under specialisation. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "147-m11-stratified-class-over-z",
        from: {
          sentence:
            "The structure at infinity of the M_g,ν: the class of M₁,₁ over Spec ℤ, stratum by stratum. (149.modern.tex l. 1542 refers to 147.)",
          basis: "cross-reference", where: "149.modern.tex l. 1542",
        },
      },
      {
        id: "148-multimarked-teichmuller-groupoid",
        from: {
          sentence:
            "The Teichmüller groupoid of cut surfaces, with any number of marked points on each circle. (148.modern.tex l. 417, 567 refers to 141 and 145; dates: October 1983.)",
          basis: "cross-reference", where: "148.modern.tex l. 417, 567",
        },
      },
      {
        id: "148-m05-special-structures-chart",
        from: {
          sentence:
            "Same folder: 542 special structures as base points of a presentation of the groupoid of M₀,₅. (Same object.)",
          basis: "same-object",
        },
      },
    ],
  },
  {
    id: "stratified-spaces-tubes",
    title: "Stratified spaces: from tame topology to tubes",
    intro:
      "The thread starts from the set-theoretic axiomatics of « tame spaces » (120) and cell decompositions as open finite T₀ quotients (121, 1974). It passes through the unfolding of a stratification into an ordered space (150, December 1981–January 1982), then through the gluing of tubes indexed by covering pairs alone and the observation that the Π₁ level is too coarse (151). The punctured tubular neighbourhood of 147 is related to 151, and the thread ends on the hypercoverings of 151 and on the 1990 letter on the back of which part of 151 is written. The two readings refer to each other: 150 → 151, 120 → 121.",
    steps: [
      { id: "120-axiomatic-pushouts-along-embeddings" },
      {
        id: "120-collapse-separation-over-a-field",
        from: {
          sentence:
            "Same folder: over a field, the second half of axiom (M6) follows from the first. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "121-coarsest-cell-decomposition",
        from: {
          sentence:
            "The reading of 120 notes that folder 121 « explicitly provides such factorisations ». (120.modern.tex l. 506.)",
          basis: "cross-reference", where: "120.modern.tex l. 506",
        },
      },
      {
        id: "121-cell-decomposition-open-quotient",
        from: {
          sentence:
            "Same folder: the partitions satisfying the boundary condition are the open finite T₀ quotients. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "150-flag-fibration-smoothness",
        from: {
          sentence:
            "The ordered set of strata, with its specialisation order, becomes the index of the unfolding of an equisingular stratification. (The edition's inference: same reading keywords, specialisation preorder.)",
          basis: "edition",
        },
      },
      {
        id: "150-unfolding-as-ordered-space",
        from: {
          sentence:
            "Same folder: the unfolding is a single ordered topological space. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "151-tube-gluing-covering-pairs",
        from: {
          sentence:
            "« Folder 151, which follows in the inventory, takes up the same question through tubes and gluing. » (150.modern.tex l. 107.)",
          basis: "cross-reference", where: "150.modern.tex l. 107",
        },
      },
      {
        id: "151-mixed-tubes",
        from: {
          sentence:
            "Same folder: the mixed tubes V^j_{i,k}, intermediate between the punctured tube and the full tube. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "151-pi1-too-coarse-for-the-sphere",
        from: {
          sentence:
            "The formalism is tried on P¹_C: at the Π₁ level it is too coarse. (Same object: the diagram of tubes, pp. 61–63.)",
          basis: "same-object",
        },
      },
      {
        id: "147-deleted-neighbourhood-codim-two",
        from: {
          sentence:
            "In 147, the punctured tubular neighbourhood of a normal crossings divisor is a homotopy colimit, and its fundamental groupoid an amalgamated sum. (The edition's inference: same object, amalgamated sum of groupoids of punctured neighbourhoods.)",
          basis: "edition",
        },
      },
      {
        id: "151-hypercovering-any-index-category",
        from: {
          sentence:
            "Back to 151: hypercoverings indexed by an arbitrary small category. (The edition's inference: gluing and cohomological descent.)",
          basis: "edition",
        },
      },
      {
        id: "151-page-17-intercalated",
        from: {
          sentence:
            "Page 17, interleaved in another series, does the computation of φ_! missing from pp. 13–14. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "151-letterhead-1990",
        from: {
          sentence:
            "These pages are written on the back of a letter dated 6 December 1990. (Dates.)",
          basis: "date",
        },
      },
    ],
  },
  {
    id: "geometry-of-shapes-1986",
    title: "Geometry of shapes, June–July 1986",
    intro:
      "The nine chapters 156-1 to 156-9 are dated day by day. The thread follows the axiomatics of one-dimensional shapes (segments, biorders, bifurcations). It passes through the « banks » of a closed set, the reconstruction of an order from its betweenness relation and figures as configurations, and ends on the self-duality of correspondences between orthogonality spaces. It notes in passing the layers of rereading that the dates allow us to place. This is the only thread in which almost every transition rests on a date or on an explicit cross-reference.",
    steps: [
      { id: "156-1-segment-biorder" },
      {
        id: "156-1-branching-without-branch-point",
        from: {
          sentence:
            "Same chapter: the local axioms F1–F5 let a bifurcation without branch point through, hence F6. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "156-1-written-alongside-156-2",
        from: {
          sentence:
            "Chapter I is still being written on 7 June, after chapter II was opened on the 6th. (Dates; 156-1.modern.tex l. 111, 915.)",
          basis: "cross-reference", where: "156-1.modern.tex l. 111, 915",
        },
      },
      {
        id: "156-2-rives-cut-along-closed-set",
        from: {
          sentence:
            "Chapter II: the banks of a closed set, which cut a fault in two. (156-2.modern.tex l. 144; 156-4.modern.tex l. 179.)",
          basis: "cross-reference", where: "156-2.modern.tex l. 144; 156-4.modern.tex l. 179",
        },
      },
      {
        id: "156-3-order-from-betweenness",
        from: {
          sentence:
            "Chapter III: the order of an ordered stretch is recovered from its betweenness relation. (156-3.modern.tex l. 121–123; date: 8 June.)",
          basis: "cross-reference", where: "156-3.modern.tex l. 121–123",
        },
      },
      {
        id: "156-3-betweenness-from-cuts",
        from: {
          sentence:
            "Same chapter: comparability and cuts suffice to recover betweenness. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "156-4-figures-as-configurations",
        from: {
          sentence:
            "Chapter IV: the sets of « figures » are configurations. (156-3.modern.tex l. 185; date: 10 June.)",
          basis: "cross-reference", where: "156-3.modern.tex l. 185",
        },
      },
      {
        id: "156-4-supports-boolean-presumption",
        from: {
          sentence:
            "Same chapter: the presumption that saturated sets form a Boolean algebra is false. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "156-5-gf-viii-rereading",
        from: {
          sentence:
            "Chapter V was reread after chapter VIII had reached its pp. 37 and 44–45. (156-5 refers to « GF VIII »; dates.)",
          basis: "cross-reference",
        },
      },
      {
        id: "156-6-dates-past-catalogue",
        from: {
          sentence:
            "Chapter VI runs on to 22 June, not to the 20th as the inventory says. (Dates; 156-5.modern.tex l. 153.)",
          basis: "cross-reference", where: "156-5.modern.tex l. 153",
        },
      },
      {
        id: "156-7-page1-index-later-layer",
        from: {
          sentence:
            "Chapter VII begins on 23 June, and the cross-reference on its page 1 is later than its last page. (Dates; 156-6.modern.tex l. 175.)",
          basis: "cross-reference", where: "156-6.modern.tex l. 175",
        },
      },
      {
        id: "156-8-page2-table-later-layer",
        from: {
          sentence:
            "Likewise, in chapter VIII the table on p. 2 is a summary written after p. 77. (The same phenomenon, a layer of rereading; 156-7.modern.tex l. 142.)",
          basis: "cross-reference", where: "156-7.modern.tex l. 142",
        },
      },
      {
        id: "156-9-crossref-156-8",
        from: {
          sentence:
            "The cross-reference « cf. p. 110, 111 » of chapter IX points to pp. 118–119 of 156-8. (156-9.modern.tex l. 208.)",
          basis: "cross-reference", where: "156-9.modern.tex l. 208",
        },
      },
      {
        id: "156-9-disposition-correspondences",
        from: {
          sentence:
            "Same chapter: the transposable correspondences between orthogonality spaces form a self-dual category. The « closed for the polarity » is the object that chapter IV presumed Boolean. (Same object: polarity, saturated sets; pairing with step 8 is the edition's.)",
          basis: "edition",
        },
      },
    ],
  },
  {
    id: "regular-polytopes-over-rings",
    title: "Regular polygons and polyhedra over a ring",
    intro:
      "This thread starts from standard maps and flags (88, 76) and passes to the closure criterion u_α^n = id ⇔ F_n(α) = 0 over an arbitrary ring (78). It continues with the universal formulae for regular polytopes in double cosines and the icosahedron over ℤ[α]/(α² + α − 1) (70), the model of the hemi-icosahedron (86), pinned realisations and their automorphism group 𝒰_ρ (72), and ends on the moduli of representations of Coxeter groups in forms of PGL₂ (85), where the icosahedron ring reappears. The readings of the group 69–89 refer to one another a great deal.",
    steps: [
      { id: "88-standard-maps-quotients" },
      {
        id: "76-flag-presheaf-gset-lemma",
        from: {
          sentence:
            "The same generators σ₀, …, σ_n as in 88, here with no involution condition. (72.modern.tex l. 237: « le σ₀, …, σ_n … est celui des dossiers 76 et 88 »; 76.modern.tex l. 141.)",
          basis: "cross-reference", where: "72.modern.tex l. 237; 76.modern.tex l. 141",
        },
      },
      {
        id: "78-closure-criterion-over-rings",
        from: {
          sentence:
            "From the cartographic group we pass to the affinity u_α of the regular polygon. (78.modern.tex l. 380–381 refers to 81 and 89 for the description of a polygon.)",
          basis: "cross-reference", where: "78.modern.tex l. 380–381",
        },
      },
      {
        id: "78-parabola-p-gon",
        from: {
          sentence:
            "Same folder: in characteristic p, α = 2 gives a p-gon inscribed in a parabola. (Same object: F_n, Ψ_p.)",
          basis: "same-object",
        },
      },
      {
        id: "78-strip-2p-gon",
        from: {
          sentence:
            "Same folder: regular 2p-gons on two parallel lines. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "70-universal-formulae-double-cosines",
        from: {
          sentence:
            "The realisations by reflections of the polytopes {p₁, …, p_n}: « ρ_s^p = id ⇔ F_p(α) = 0 », with the polynomials of 78. (Same object, F_p; 85.modern.tex l. 279: « les polynômes de ℤ[U] sont ceux du dossier 78 ».)",
          basis: "cross-reference", where: "85.modern.tex l. 279",
        },
      },
      {
        id: "70-icosahedron-integral-faithful",
        from: {
          sentence:
            "Same folder: the icosahedron over ℤ[α]/(α² + α − 1), faithful in every characteristic. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "70-icosahedron-char5-conic",
        from: {
          sentence:
            "Its reduction modulo 5: the vertex directions form the conic. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "86-hemi-icosahedron-five-set-model",
        from: {
          sentence:
            "The hemi-icosahedron reconstructed from an oriented five-element set. (70.modern.tex l. 348–350: « l'antipodisme de l'icosaèdre [est] celui du dossier 86 ».)",
          basis: "cross-reference", where: "70.modern.tex l. 348–350",
        },
      },
      {
        id: "72-pinned-realisations-over-base",
        from: {
          sentence:
            "From dimension 3 to the universal regular map of dimension n: its pinned realisations over an arbitrary base. (85.modern.tex l. 229 and 72.modern.tex l. 499 tie 70, 72 and 87 to the same family.)",
          basis: "cross-reference", where: "85.modern.tex l. 229 et 72",
        },
      },
      {
        id: "72-automorphisms-deform-gm-to-ga",
        from: {
          sentence:
            "Same folder: the automorphism group scheme is 𝒰_ρ, a torus or 𝔾_a according to the position of the centre. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "85-dinfty-torsor-classification",
        from: {
          sentence:
            "The same group 𝒰_{2−α} classifies homomorphisms of D_∞ into forms of PGL₂. (Same notation, law λ + λ′ + ρλλ′; 85.modern.tex l. 286: « discriminant au sens du dossier 72 ».)",
          basis: "cross-reference", where: "85.modern.tex l. 286",
        },
      },
      {
        id: "85-g2-pgl2-moduli-over-z",
        from: {
          sentence:
            "Same folder: the Coxeter group G₂ and its trace invariants (α₀, α₁). (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "85-a5-pgl2-moduli-spec-z-phi",
        from: {
          sentence:
            "Same folder: the icosahedral subgroups of PGL₂, with moduli Spec ℤ[T]/(T² + T − 1), the same ring as in step 7. (Same object, same ring.)",
          basis: "same-object",
        },
      },
    ],
  },
  {
    id: "quadratic-forms-characteristic-2",
    title: "Quadratic forms and algebras, characteristic 2 included",
    intro:
      "This thread starts from the involutions of 2-regular modules (67) and the discriminants of universal quadratic forms (77). It passes through the classification of quadratic coverings by triples, stated in 77 and in 84, then through the product of quadratic algebras without dividing by 2 (84). It continues with twists and the Azumaya criterion in rank 4 (83), then with the forms of sl(2) and the conic in characteristic 2 (82). It ends on the affine quadric and the Arf covering (77). The readings of 77, 82, 83 and 84 refer to one another closely.",
    steps: [
      { id: "67-involution-modules-triples" },
      {
        id: "77-odd-rank-half-discriminant",
        from: {
          sentence:
            "The same condition (2 not a zero divisor), applied to quadratic forms: the half-discriminant in odd rank. (The edition's inference.)",
          basis: "edition",
        },
      },
      {
        id: "77-universal-even-rank-discriminant-mod-4",
        from: {
          sentence:
            "Same folder: in even rank, (−1)ⁿΔ = B² − 4C. (Same object: expansion of Δ in graphs, pp. 65–71.)",
          basis: "same-object",
        },
      },
      {
        id: "77-two-regular-classification-matched",
        from: {
          sentence:
            "The congruence modulo 4 gives the classification of quadratic coverings by (L, 𝔇, b₀). (Same object; 77.modern.tex l. 384, on Stickelberger, refers to 84.)",
          basis: "cross-reference", where: "77.modern.tex l. 384",
        },
      },
      {
        id: "84-two-regular-triplet-classification",
        from: {
          sentence:
            "Folder 84 « states the same [theorem] » with T₀² ≡ δ mod 4. (77.modern.tex l. 1260.)",
          basis: "cross-reference", where: "77.modern.tex l. 1260",
        },
      },
      {
        id: "77-discriminant-extension-across-2",
        from: {
          sentence:
            "Back in 77: when does (L, Δ) come from a quadratic covering? It suffices to check it at the maximal points of V(2). (Same object: corollary 3 of 77 p. 63.)",
          basis: "same-object",
        },
      },
      {
        id: "84-product-quadratic-algebras-formula",
        from: {
          sentence:
            "The product of quadratic algebras without dividing by 2, with δ = δ₁δ₂. (Same object: the discriminant; the pairing is the edition's.)",
          basis: "edition",
        },
      },
      {
        id: "84-chi-trivialised-extension-product",
        from: {
          sentence:
            "Same folder: χ-split extensions form a symmetric monoidal category. (Same object, pp. 65–79.)",
          basis: "same-object",
        },
      },
      {
        id: "84-product-coinvariants-one-etale",
        from: {
          sentence:
            "Same folder: when the product is identified with the invariants of A₁ ⊗ A₂. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "83-twist-line-degenerate-locus-is-product",
        from: {
          sentence:
            "In 83, pp. 126–180 « develop the same theory as the second part of folder 84 »: the Hamilton–Cayley structures on H ⊗ H′. (83.modern.tex l. 353 and l. 1544.)",
          basis: "cross-reference", where: "83.modern.tex l. 353 et",
        },
      },
      {
        id: "83-two-generator-azumaya-criterion",
        from: {
          sentence:
            "Same folder: Azumaya criterion for the two-generator algebra. (Same object: the reduced discriminant.)",
          basis: "same-object",
        },
      },
      {
        id: "82-char2-sl2-forms-affine",
        from: {
          sentence:
            "Forms of sl(2) and of gp(1) = pgl(2) in characteristic 2. (84.modern.tex l. 273 refers to 82; 77.modern.tex l. 451 « GP(1) pour PGL₂, comme le dossier 82 ».)",
          basis: "cross-reference", where: "84.modern.tex l. 273; 77.modern.tex l. 451",
        },
      },
      {
        id: "82-char2-conic-frobenius",
        from: {
          sentence:
            "Same folder: for a quaternion algebra in characteristic 2, the conic and the relative Frobenius. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "77-affine-quadric-weil-restriction",
        from: {
          sentence:
            "The affine quadric q = −1 is the complement of the conic in a Weil restriction. (77.modern.tex l. 1523, 1536 refer to the formulae of 82.)",
          basis: "cross-reference", where: "77.modern.tex l. 1523, 1536",
        },
      },
      {
        id: "77-arf-cover-stein-factorisation",
        from: {
          sentence:
            "Same folder: isotropic flag schemes, the Arf covering and the Dickson homomorphism, characteristic 2 included. (Same object.)",
          basis: "same-object",
        },
      },
    ],
  },
  {
    id: "treatise-workshop-ega-sga",
    title: "The treatise workshop: EGA and SGA in the fonds",
    intro:
      "Typed states of the Éléments and the Séminaires have remained in folders that deal with something else: EGA 0_III, EGA IV §§ 18 and 21, SGA 2 XII, SGA 3 XII, SGA 4 VIII. To these are added plans for EGA V-VII whose chapter numbers do not agree with the titles in the inventory. The thread follows the order of the treatises, then the order of the chapters. It says nothing of the genesis of the texts: it only records where these states are found and how they differ from the printed version.",
    codicological: true,
    steps: [
      { id: "21-typescript-section-2-and-printed-ega" },
      {
        id: "25-letter-1965-before-folder-range",
        from: {
          sentence:
            "A letter to Dieudonné on EGA IV, when the 4th fascicle was still in preparation. (The edition's inference: correspondence with Dieudonné on the Éléments; envelope of 21: « Notes pour Dieud. ».)",
          basis: "edition",
        },
      },
      {
        id: "25-appendix-18-joint-paper",
        from: {
          sentence:
            "Same letter: the refusal to publish an « ex-Appendice au par. 18 » on his own. (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "5-ega-iv-typescript-versos",
        from: {
          sentence:
            "The versos of 5 are pages IV-977 of a typescript of EGA IV § 18.13. (Same object, EGA IV § 18; the link between the letter and this typescript is the edition's inference.)",
          basis: "edition",
        },
      },
      {
        id: "97-ega-iv-1102-margin",
        from: {
          sentence:
            "Another leaf of the EGA IV typescript, IV-1102 (§ 21.6), annotated in his hand. (Same object: the EGA IV typescript.)",
          basis: "same-object",
        },
      },
      {
        id: "127-ega-iv-typescript-leaf",
        from: {
          sentence:
            "Again § 21, no. 21.10 (leaf IV-1131?), with « Créditer Kaplansky ». (Same object.)",
          basis: "same-object",
        },
      },
      {
        id: "58-typed-leaf-sga2-xii-3-1",
        from: {
          sentence:
            "A typed leaf of SGA 2 XII 3.1, whose wording differs from the printed version. (The edition's inference: a typed state of a treatise.)",
          basis: "edition",
        },
      },
      {
        id: "56-sga3-xii-corrected-typescript",
        from: {
          sentence:
            "Fourteen leaves of a corrected state of SGA 3 XII. (The edition's inference.)",
          basis: "edition",
        },
      },
      {
        id: "10-sga3-typescript-cites-1966-67",
        from: {
          sentence:
            "Another SGA 3 talk (nos. 10 and 11), typed at the earliest when a seminar of « 1966/67 » could be cited. (Same object: SGA 3; dates.)",
          basis: "same-object",
        },
      },
      {
        id: "26-sga4-viii-79-draft",
        from: {
          sentence:
            "A state of SGA 4 VIII 7.9.1–7.9.3 earlier than the printed version. (The edition's inference.)",
          basis: "edition",
        },
      },
      {
        id: "48-typescript-leaves-reversed",
        from: {
          sentence:
            "Two other leaves on the same no. 7.9 of SGA 4 VIII (Theorem 7.9), in the folder of the EGA VII plan and filed upside down. (Same object: SGA 4 VIII 7.9; that they belong to one typescript is not established.)",
          basis: "same-object",
        },
      },
      {
        id: "37-sga4-viii-section-10",
        from: {
          sentence:
            "A § 10 of SGA 4 VIII (« espaces algébriques et étendues algébriques ») that is neither in the printed version nor in the IHÉS typescript. (Same object: SGA 4 VIII; dates, 37: 1967-1971.)",
          basis: "same-object",
        },
      },
      {
        id: "26-wrapper-numbered-v",
        from: {
          sentence:
            "The wrapper of EGA « VI » bears the number V. (The edition's inference: plans of unpublished chapters.)",
          basis: "edition",
        },
      },
      {
        id: "48-chapter-number-discrepancy",
        from: {
          sentence:
            "The cover of 48 reads « Plan EGA VII », the plan itself « EGA Chap. VI ». (Same object: numbering of the planned chapters.)",
          basis: "same-object",
        },
      },
      {
        id: "41-chapter-number",
        from: {
          sentence:
            "The title leaf of 41 reads « Chap. VI », not the « Chap. V » of the inventory. (Same object.)",
          basis: "same-object",
        },
      },
    ],
  },
];

/** Typed links between findings that no thread joins, or that join two threads. */
export const LINKS: FindingLink[] = [
  {
    from: "9-det-etale-tate-iso",
    to: "9-symmetric-positive-det-sqrt-degree",
    kind: "uses",
    basis: "same-object",
    note: "The independence reduces to Δ(u) = δ(u) (9, pp. 24, 26)",
  },
  {
    from: "4-vanishing-unit-root-bound",
    to: "4-revision-reverses-surjectivity",
    kind: "uses",
    basis: "cross-reference",
    note: "Cross-reference on the leaf: margin p. 4 « en vertu de 8.4.4 »",
  },
  {
    from: "77-so-even-rank-smooth-connected-matched",
    to: "77-arf-cover-stein-factorisation",
    kind: "uses",
    basis: "same-object",
    note: "SO(q) defined by its action on Arf (77, pp. 155–157)",
  },
  {
    from: "12-weights-paper-typescript",
    to: "12-immersion-level-bound",
    kind: "same-question",
    basis: "same-object",
    note: "Cover « Poids et niveaux », same folder",
  },
  {
    from: "104-pinned-posets-nonsingular-presheaves",
    to: "76-semisimplicial-vertex-order",
    kind: "generalises",
    basis: "cross-reference", where: "76.modern.tex l. 920",
    note: "76.modern.tex l. 920, « le cas Δ_inj de l'équivalence vérifiée pour la cote 104 »",
  },
  {
    from: "132-teichmuller-boundary-sequence",
    to: "132-peripheral-gr-category",
    kind: "uses",
    basis: "same-object",
    note: "TS defined pp. 5–7, the sequence p. 8 (joins threads 3 and 10)",
  },
  {
    from: "15-brandt-picard-category",
    to: "135-sinh-theorem-classification",
    kind: "same-question",
    basis: "edition",
    note: "Strictly commutative Picard category, 2-group Eqv(C)",
  },
  {
    from: "115-isbell-duality-derived-from-kernels",
    to: "115-wheel-eleven-curryings",
    kind: "uses",
    basis: "same-object",
    note: "Kernels X ∈ (A × B)^",
  },
  {
    from: "115-isbell-reflexivity-left-open",
    to: "115-isbell-envelope-self-dual",
    kind: "same-question",
    basis: "same-object",
    note: "Reflexivity, retracts of representables (p. 13)",
  },
  {
    from: "156-9-disposition-correspondences",
    to: "115-isbell-envelope-self-dual",
    kind: "same-question",
    basis: "edition",
    note: "Self-dual completion and category",
  },
  {
    from: "86-combinatorial-five-triedres",
    to: "86-hemi-icosahedron-five-set-model",
    kind: "same-question",
    basis: "same-object",
    note: "Icosahedron and five-element set",
  },
  {
    from: "72-invariant-subspaces-string",
    to: "72-automorphisms-deform-gm-to-ga",
    kind: "same-question",
    basis: "same-object",
    note: "Centre c, hyperplane at infinity",
  },
  {
    from: "85-a5-pgl2-moduli-spec-z-phi",
    to: "70-icosahedron-integral-faithful",
    kind: "same-question",
    basis: "same-object",
    note: "The ring ℤ[α]/(α² + α − 1)",
  },
  {
    from: "79-commutant-octahedral-exception",
    to: "64-gl2-z4-combinatorial-model",
    kind: "same-question",
    basis: "edition",
    note: "ℤ/4, octahedron, GL₂(ℤ/4)",
  },
  {
    from: "64-octahedral-configurations-relative",
    to: "64-gl2-z4-combinatorial-model",
    kind: "same-question",
    basis: "same-object",
    note: "Same object (folder 64, octahedron)",
  },
  {
    from: "79-homothety-distance-three",
    to: "79-commutant-octahedral-exception",
    kind: "same-question",
    basis: "same-object",
    note: "The homotheties are the commutant",
  },
  {
    from: "74-gq2t-latin-square-reduction",
    to: "69-triangle-q8-baer-torsor",
    kind: "same-question",
    basis: "cross-reference", where: "74.modern.tex l. 246",
    note: "74.modern.tex l. 246, « traite des mêmes objets »",
  },
  {
    from: "83-leaves-from-folder-79-section-xi",
    to: "79-pages-33-35-dated-1982",
    kind: "continues",
    basis: "cross-reference", where: "83.modern.tex l. 137",
    note: "Two discarded versions of pages of § XI of 79, reused in 83; cross-reference 83.modern.tex l. 137",
  },
  {
    from: "14-brauer-typescript-shared-with-12",
    to: "12-positive-forms-leaves-order",
    kind: "continues",
    basis: "same-object",
    note: "Same object (conditional): perhaps the same English typescript on the Brauer group",
  },
  {
    from: "15-brauer-section-5-leaves",
    to: "14-brauer-typescript-shared-with-12",
    kind: "same-question",
    basis: "edition",
    note: "The Brauer group",
  },
  {
    from: "62-bourbaki-versos",
    to: "98-versos-bourbaki-redactions",
    kind: "same-question",
    basis: "same-object",
    note: "Bourbaki rédactions reused (« paper » in dated-leaves)",
  },
  {
    from: "64-page-156-june-1981-notice",
    to: "116-leaves-undated-vocabulary-dates-nothing",
    kind: "same-question",
    basis: "date",
    note: "Administrative notices of 9, 16 and 19 June 1981",
  },
  {
    from: "108-dated-from-unrelated-verso",
    to: "116-leaves-undated-vocabulary-dates-nothing",
    kind: "same-question",
    basis: "edition",
    note: "A dated foreign piece does not date the writing",
  },
  {
    from: "7-catalogue-date-1967",
    to: "156-6-dates-past-catalogue",
    kind: "same-question",
    basis: "date",
    note: "The inventory's title contradicted by the leaves",
  },
  {
    from: "162-1-date-precedes-inventory",
    to: "25-letter-1965-before-folder-range",
    kind: "same-question",
    basis: "date",
    note: "A leaf earlier than the inventory's bound",
  },
  {
    from: "63-level3-notes-after-march-1968",
    to: "79-pages-33-35-dated-1982",
    kind: "same-question",
    basis: "date",
    note: "A terminus post quem narrower than the inventory's",
  },
  {
    from: "31-local-ring-cd-lower-bound",
    to: "31-phi-specialisation-criterion",
    kind: "same-question",
    basis: "edition",
    note: "Cd_ℓ of local rings, a term of the φ-criterion",
  },
  {
    from: "31-imperfection-bound-conjectures",
    to: "31-phi-specialisation-criterion",
    kind: "continues",
    basis: "edition",
    note: "The case where ℓ is the residue characteristic",
  },
  {
    from: "125-cd-complement-formal-comparison",
    to: "58-lef-permanence-projective-flat",
    kind: "same-question",
    basis: "same-object",
    note: "Comparison H^i(X, F) → H^i(X_{/Y}, F_{/Y})",
  },
  {
    from: "57-cone-completion-class-group",
    to: "58-local-hom-comparison-depth-off-y",
    kind: "same-question",
    basis: "edition",
    note: "Comparison with the completion along Y (« Lefschetz–Grauert »)",
  },
  {
    from: "57-analytic-pic-completion-criterion",
    to: "57-cone-completion-class-group",
    kind: "same-question",
    basis: "same-object",
    note: "Pic and completion",
  },
  {
    from: "47-chow-fourier-todd-over-base",
    to: "47-relative-fourier-inversion",
    kind: "continues",
    basis: "same-object",
    note: "Fourier transform over a base S",
  },
  {
    from: "47-cup-to-pontrjagin-sign-kleiman",
    to: "47-chow-fourier-todd-over-base",
    kind: "same-question",
    basis: "same-object",
    note: "The cup → Pontrjagin formula and its sign",
  },
  {
    from: "2-chern-ring-not-injective-pn",
    to: "2-chern-ring-gamma-comparison",
    kind: "continues",
    basis: "same-object",
    note: "Φ_K, « Est-ce que φ_K est toujours bijectif ??? — Non »",
  },
  {
    from: "42-reseau-functor-fully-faithful",
    to: "42-reseau-theorem-needs-hypothesis",
    kind: "corrects",
    basis: "same-object",
    note: "The same statement, with Y separated",
  },
  {
    from: "90-equivariant-resolution-general-base",
    to: "90-saturated-subcoalgebras",
    kind: "generalises",
    basis: "same-object",
    note: "From a Dedekind ring to an arbitrary base",
  },
  {
    from: "90-saturated-subcoalgebras",
    to: "90-components-criterion",
    kind: "uses",
    basis: "same-object",
    note: "The hypothesis of Lemma 1, which 90-components-criterion wrongly characterises",
  },
  {
    from: "22-p23-proposition-reconstruction",
    to: "22-power-series-discrete-obstruction",
    kind: "generalises",
    basis: "same-object",
    note: "Obstruction for A = K[[t]] and the discrete topology",
  },
  {
    from: "21-stack-p3-pointwise",
    to: "21-depth-sheaves-of-sets-pointwise",
    kind: "generalises",
    basis: "same-object",
    note: "From sheaves of sets to stacks",
  },
  {
    from: "160-dickson-geometric-route",
    to: "160-ga-subgroups-additive-kernels",
    kind: "uses",
    basis: "same-object",
    note: "Additive polynomials and Dickson invariants",
  },
  {
    from: "160-relative-moore-determinant",
    to: "160-special-linear-structures-sign",
    kind: "same-question",
    basis: "same-object",
    note: "Δₙ and A₀ = ±Δₙ^{p−1}",
  },
  {
    from: "101-sheaf-duality-dim-two-fails",
    to: "101-sheaf-duality-dim-one",
    kind: "continues",
    basis: "same-object",
    note: "The same local duality, in dimension 2",
  },
  {
    from: "137-perfect-complexes-universal-sigma-exact",
    to: "136-pd-de-rham-shadows",
    kind: "same-question",
    basis: "cross-reference", where: "137.modern.tex l. 236",
    note: "137.modern.tex l. 236 « (dossier 136) »",
  },
  {
    from: "162-5-de-rham-hochschild-flat-formal-category",
    to: "162-5-formal-categories-flat-conormal-de-rham",
    kind: "continues",
    basis: "same-object",
    note: "« sous les mêmes hypothèses »",
  },
  {
    from: "154-cyclic-order-determines-position",
    to: "80-skeleton-full-faithfulness",
    kind: "same-question",
    basis: "cross-reference", where: "154.modern.tex l. 204",
    note: "154.modern.tex l. 204 refers to folder 80",
  },
  {
    from: "81-dessins-dating-cannot-support-precedence",
    to: "138-operations-belyi-extending",
    kind: "same-question",
    basis: "same-object",
    note: "Spherical maps and Belyi coverings",
  },
];
