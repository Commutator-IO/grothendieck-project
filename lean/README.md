# The readings, proved

Lean 4 proofs, against mathlib, of statements the modernised readings make
(issue [#26](https://github.com/Commutator-IO/grothendieck-project/issues/26)).
A proof here says that what a reading states **holds together**, not that it is
what the page says: a perfectly formalised statement can be a perfectly
formalised misreading.

```bash
cd lean && lake exe cache get && lake build   # fails on any warning, so on any sorry
```

Twenty-seven folders: the eighteen of issue #26 (tier 1, and the five rows of tier 2), and nine findings of the Findings tab (1, 67, 74, 77, 84, 85, 133, 156-1, 156-3), proved as stated — which says nothing about whether they are in the literature. Each statement, its written-out proof and
what the verification found are in the appendix
[`docs/lean/article.pdf`](../docs/lean/article.pdf), served at
<https://grothendieck.commutator.io/article/grothendieck-lean.pdf>, and on the
site's Findings page. `./axioms.sh`, run after `lake build`, lists the axioms
of every theorem and fails on any beyond Lean's three standard ones.

| Folder | File | Scope | Found |
|---|---|---|---|
| 42 | `Folder42.lean` | Prop. p. 3 and Lemme 1 for sheaves on Noetherian sober spaces; Lemme 1 and Cor. 1 for Spec A, A Noetherian; Lemme 2 (1), (2) and the page's (A_f)_q → A_p form | « constructible ⇒ open » used only as « stable under generization + a nonempty open of each x̄ ⇒ open », proved directly; (H) used in its weak form; injectivity needs neither (H) nor Noetherian; Cor. 1 needs from Lemme 2 only one f killing ker(A → A_p); (2) needs no Noetherian hypothesis |
| 158 | `Folder158.lean` | Proposition 1 | the reading's gloss was false (Rees kernel not a point); corrected |
| 153 | `Folder153.lean` | Lemme p. 3; co-operations of Int(k₀) (K₀ a localisation, Ω free): existence, uniqueness, composition rules; Pólya basis and Vandermonde for Int(ℤ); Ω = Ω₀ ⊕ Ω⁰; examples p. 7 (Appl, k[T], 𝔽_q, k[[T]]⁺) | k₀ ⊂ K₀ not needed; localisation used instead of K₀⊗K₀ = K₀; the decomposition needs neither 3) nor T; Appl fails 3a) for infinite nonzero unital rings; the footnote's matrix is Pascal minus its (0,0) entry |
| 152 | `Folder152.lean` | dictionary, partial | the page's head line contradicts its table |
| 88 | `Folder88.lean` | order 2ν, (6), partial | most hypotheses unused |
| 113 | `Folder113.lean` | Karoubi, Morita (additive), partial | smallness, abelianness unused |
| 104 | `Folder104.lean` | categories of models (i)(ii), (*), order on classes, τ_n, u_{d_n}=id; well-foundedness ⇒ Reedy direct (mathlib ReedyStructure) and converse; Δ: simplicial identities, factorisation through a face, Δ direct; three examples' counts; globular complex (p. 4) | nothing wrong; well-foundedness is a real extra hypothesis (ℤ satisfies (i)(ii), is not direct); the Reedy statement needs M skeletal ("rigide" p. 9); (i) not used |
| 125 | `Folder125.lean` | étages, III-18, partial | prose slip `q < r − m` → `q ⩽ r − m` |
| 161-1 | `Folder161_1.lean` | conditions (1), (2), the five conditions of p. 3, E₀ ≃ F₀, idempotency, p. 5 conditions 1), 3), 4), reflector preserves colimits, local objects, p. 6 descent | nothing wrong; p. 3's fifth condition repeats the second; p. 6 descent needs no full faithfulness of β |
| 22 | `Folder22.lean` | 3.3–3.5, partial | « par exemple noethérien » is equivalent, not an example |
| 41 | `Folder41.lean` | Proposition 1 | finiteness needed only for (iii bis) ⇒ (ii) |
| 21 | `Folder21.lean` | 2.15, 2.16, partial | nothing false |
| 39 | `Folder39.lean` | adic preparation, partial | nothing wrong |
| 19 | `Folder19.lean` | Théorème 1.12, Gabriel–Popescu, comonad over a product base (matrix φ_ji, λ_kji, two-factor collapse) | **the « only if » of 1.12 b) is false on the page**; condition C is not Beck's; « ou I fini » on p. 7 is false: left adjoints need not preserve finite products (counterexample) |
| 161-2 | `Folder161_2.lean` | monadicity, descent, Gabriel–Ulmer, Ind(Σ), partial | descent needs no topos |
| 16 | `Folder16.lean` | sl₂ against (6.7); πᵢ ∈ ℰ from one-sided inverses (no. 5, (6.3)); Cayley–Hamilton: any algebraic iso makes (L^{n−i})⁻¹ algebraic (pp. 47–48); ℤ-obstruction for the exterior model | confirms the reading's correction of p. 13; the reading's Φ₀ = ℤ[L₀, Λ₀] does not exist over ℤ for n ≥ 2 (ξ₀ⁿ divisible by n!), fine over ℚ |
| 106 | `Folder106.lean` | weak lifting, Brown factorisation, W₀⁻¹C ≅ W⁻¹C; pp. 11–15: Ch′₀, 𝒞̃′, q′ and the criterion (⋆⋆) (finding) | all hold as stated; with every object cofibrant q′ is an isomorphism unconditionally, so (⋆⋆) always holds and the finding's « iff » holds with both sides true; sufficiency proved without comparing sections |
| 114 | `Folder114.lean` | Proposition 4, minimal localiser, partial | the reading dropped « satisfying Loc 4) »; without it W ⊆ W₀ fails |
| 67 | `Folder67.lean` | Page 90: 2-regular modules with an involution ≌ triples (P, Q, m), for any ring k, no finiteness | holds as stated, for non-commutative k too; 2-regularity is the only hypothesis used; fullness needs no finiteness since a σ-map is determined on 2P × 2Q |
| 156-1 | `Folder156_1.lean` | segment model ⇔ bounded dense locally bi-directed poset (pp. 10–13), both directions; non-total example | forward needs only F1, F2, F′3, F4 (not F3, F5); F4 holds without regularity in the converse |
| 156-3 | `Folder156_3.lean` | betweenness from the cuts of C(ε) (p. 15), order up to reversal (pp. 11–13) | only density and directedness b) used; reading's R̄ ⇔ R ∨ b∈{a,c} fails for incomparable a, c; comparability alone insufficient |
| 133 | `Folder133.lean` | Page 46 (N′ = Cent G ⇔ Ψ_G injective), pp. 51–52 (N = D G ⇔ λ_G surjective), pp. 48/52 commutator formula in G₁ = (G ×_{π₀} E)/π₁, partial | only N′ ⊂ Cent G needed for page 46; π₀ commutative follows from N ⊃ D G; the page's open sign is fixed: the correction term is c_E(ḡ, z̄) |
| 77 | `Folder77.lean` | Odd-rank universal discriminant divisible by 2 (all odd n), half-discriminant δ′ over any base; (−1)ⁿΔ ≡ B² mod 4 in ℤ[Y] for every even rank 2n, B the hafnian (C explicit in ranks 2, 4); canonical symmetry σ = id − π⊗a of (T, q, a): π(a) = 2, isometry, σ² = id, uniqueness among isometries fixing ker π, centre a/2 if 2 invertible, transvection if 2 = 0 | odd case via an antisymmetric lift; even case without Pfaffian (det K ≡ (1−2n) det P mod 4, det K a square in ℤ[Y] by integral closure, its root ≡ B mod 2); −(−1)ⁿ refuted in ranks 2, 4; p. 87 coefficients confirmed; uniqueness of σ needs a connected base (solutions id − eπ⊗a, e idempotent); σ² = id needs π(a) = 2 (page: π(a) = 1) |
| 84 | `Folder84.lean` | Product of quadratic algebras in split coordinates (identity p. 64, b = b₁b₂, c = c₁b₂² + c₂b₁² − 4c₁c₂, δ = δ₁δ₂); coinvariants iso ⇔ (2, b₁, b₂) = R; invariants iso universally iff; p. 48 free case: iso ⇔ V = εU + t, and with 2 regular ⇔ δ′ = ε²δ, b′ ≡ εb mod 2; over ℤ, discriminants ≡ 0, 1 mod 4; χ-split extensions in coordinates: product associative, commutative, unital, cocycle u″ = u + u′, invertible ⇔ bR + χR = R (L = 𝒪), pushout ≅ pullback when γχ = 2 | « 4c₁c₁ » read 4c₁c₂ confirmed; p. 85 holds over R with no base change; the converse of p. 86 needs the base change (ℤ[X]); « 2 regular » needed on p. 48 (𝔽₂ × 𝔽₂ and 𝔽₄); γχ = 2 necessary already for the unit objects |
| 85 | `Folder85.lean` | A(g)² + A(g) − 1 = 0 ⇔ g⁵ scalar for g nowhere scalar, (2,3,5) model over ℤ[ζ₅]; G₂ → PGL₂ (p. 4): (*) at every point ⇔ traceless τᵢ with (α₀+2)(α₁+2)(α₀+α₁) a unit; rigidity over any ring; conjugacy over a field containing a root of T² − α₀T + 1; normal form over R[T]/(T² − α₀T + 1); exact orders 3, 4, 6 | each factor of the discriminant matches one condition of (*); no hypothesis on 2; the split realisation needs the quadratic extension, hence forms of PGL₂; order 6 needs 6 invertible in PGL₂; representability not proved |
| 1 | `Folder1.lean` | Ky Fan's inequality (system (16) for m ≤ 1, every n) in finite dimension; (16) ⟹ (15) for each n; (15) for n = 1 | Ky Fan is not in mathlib; the maximum principle holds for orthogonal families of norm ≤ 1; (16) for m ≥ 2 not reached (no Hilbert structure on exterior powers in mathlib) |
| 74 | `Folder74.lean` | Props 1–5 around a triangle; Γ = Γ̃/σ is a Latin square, Γ̃ the pull-back of each double cover, transitive system, counts; Scholie as a graph isomorphism; converse under β_Γ̃ + (Ka); p. 116 group lemma | (Ka) reconstructed (its end is illegible): axiom 1 ⇔ (Ka) under (*), and the p. 97 claim fails without it (order-2 Latin square, trivial covers); axiom 3 not needed; p. 116 proves only the group-table case |
