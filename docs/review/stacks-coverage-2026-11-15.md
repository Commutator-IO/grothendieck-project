# What AxiomMath's Stacks library can fill in the edition's Lean files (2026-11-15)

## Scope and method

This review asks which Lean results of the edition were left unproved, or proved only in part,
because Mathlib lacked a notion or a theorem, and whether the Lean formalization of the Stacks
Project published by AxiomMath (<https://github.com/AxiomMath/Stacks>, Apache-2.0) now supplies
the missing piece.

The edition's side was read from three places: the `lean` field of the entries of
`src/content/findings.ts` (49 entries whose text says « Partly », « not proved », or names a
Mathlib gap), the docstrings of `lean/Grothendieck/*.lean` that state what Mathlib does not have,
and the « not formalised » paragraphs of `docs/lean/sections/*.tex`. The 383 findings without a
`lean` field were screened by keyword for algebraic geometry (schemes, sheaves, étale, flat,
descent, cohomology, EGA/SGA): 197 match, of which 128 are neither matched nor refuted. Those
are research-level statements about moduli, abelian schemes, étale cohomology or topoi, and none
of them is within reach of a single Stacks declaration; they are summarised at the end rather
than ranked.

The Stacks side is a copy of the upstream default branch taken on 2026-11-15 (64,215 Lean files,
StacksCore human-reviewed, StacksFrontier AI-written, no `sorry`). Declarations were located by
their `@[stacks TAG]`, `@[ega …]` and `@[sga …]` attributes, by file and declaration names, and
by reading statements. For each candidate file the column « closure » counts the Stacks files it
pulls in transitively through its `import StacksCore.…`/`import StacksFrontier.…` lines, the file
itself included. Mathlib imports are not counted: our Mathlib (`715a03a`) is already built, and
every Mathlib module imported by the closures used below exists at our pin.

Feasibility is graded as: **done** (proved in this round), **high** (closure small, statement
fills the gap directly), **medium** (closure small, but real glue work or a partial fill),
**low** (closure above about 40 files, or the Stacks result covers only part of the gap), and
**none** (nothing relevant found).

## Ranked table

| # | Item (cote, finding or file) | Missing piece | Stacks declaration(s), file, tier | Closure | Feasibility |
|---|---|---|---|---|---|
| 1 | 22, `22-power-series-discrete-obstruction` (`Folder22.lean`) | the `t`-adic half: `k[[t]]` formally smooth over `k` for the `t`-adic topology; Mathlib has no formal smoothness of topological rings | `RingHom.FormallySmoothNAdic` (tag 07NI), `StacksFrontier/RingTheory/FormallySmooth/Topological.lean`; `powerSeries_hom_ext`, `StacksFrontier/RingTheory/MvPowerSeries/HomExt.lean`; Frontier | 3 | **done** (`Folder22Adic.lean`) |
| 2 | FG_IL_5_SGA6_2_3, `FG_IL_5_SGA6_2_3-K0-triangulated-basics`, section `ihes-sga6-2-3` | `K(A) ≅ K(D^b(A))` for an abelian `A` (n° 2); Mathlib has no `K₀` of an abelian category | `DerivedCategory.Bounded.exists_addEquiv_K0` (tag 0FCP), `StacksFrontier/Algebra/Homology/DerivedCategory/KGroup.lean`; `KZero` (02MU); `Pretriangulated.K0` (0FCN); Frontier, two Core files in the closure | 7 | **done** (`IhesSGA6_2_3Db.lean`) |
| 3 | 94, `94-generic-tor-regular-sequences` (`Folder94.lean`) | the Koszul step: from `R_𝔭`-regularity of `t` to vanishing of the higher homology; Mathlib has no Koszul complex of a sequence | `Koszul.IsKoszulRegularOn`, `Koszul.IsKoszulRegular` (062E), `isKoszulRegularOn_and_isKoszulRegular_of_regular` (062F), `StacksFrontier/RingTheory/Koszul/Regular.lean`; Frontier | 9 | **done**, in Koszul-homology form (`Folder94Koszul.lean`); the identification with Mathlib's `Tor` is not made |
| 4 | 94, same finding, Lemme 16 | generic flatness for `X` of finite type over `S` | `Module.exists_ne_zero_free_localizedModule_away` (051R; EGA IV 6.9.2), `StacksFrontier/Algebra/Category/Ring/Epi/GenericFlatness/Noetherian.lean`; `…/GenericFlatness/FinitePresentation.lean` (051S); Frontier | 5 (6 for 051S) | **high**: the file elaborates unchanged against our Mathlib (checked). Remaining work: pass from a domain to the reduced ring `A/J` through its finitely many minimal primes, and give the `J`-adic layers of a finite `B`-module their `B/JB`-module structure |
| 5 | FG_IL_5_SGA6_2_3, section `ihes-sga6-2-3` | the Euler formula `Σ(−1)ⁱχ(Xⁱ) = Σ(−1)ⁱχ(Hⁱ)` for any additive function on an abelian category (proved only for dimensions) | `KZero.lift`, `KZero.universal` (02MU), `StacksFrontier/CategoryTheory/Abelian/GrothendieckGroup.lean`; Euler characteristic `eulerChar` in `…/DerivedCategory/KGroup.lean`; Frontier | 2 (7) | **high**: `KZero` is the universal additive function, so the formula reduces to one identity in `KZero A`, by the usual two short exact sequences per degree |
| 6 | 55, `55-lemma-b-identity-principle` (`Folder55.lean`) | coherent sheaves on a ringed space, to show that the identity principle (v) gives the uniformity used in Lemme B | `SheafOfModules.IsCoherent` (01BV, EGA 0 5.3.7), `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`; Frontier | 5 | **medium**: the definition and finite-type closure properties are there; supports of `O/J`, stalks and primary decomposition at stalks still have to be written |
| 7 | 128, `128-nilpotent-conductor-flat-descent` (`Folder128.lean`) | Cor. 2 and 3 (preschemes, flat base change); faithfully flat descent of modules beyond comonadicity | faithfully flat effective descent of modules (023N), `StacksFrontier/AlgebraicGeometry/Descent/Modules/FaithfullyFlatEffectiveDescent.lean`; effective descent (08XA), `…/Descent/Modules/EffectiveDescent.lean`; Milnor patching (0D2F), `StacksFrontier/RingTheory/MilnorPatching/ModuleCategory.lean`; Frontier | 23; 21; 4 | **medium** for the affine statements (our file already proves flat descent directly); **low** for the prescheme corollaries, which need gluing along schemes |
| 8 | 100, `100-baire-dimension-one-points` (`Folder100.lean`) | the page's own route through Cohen's structure theorem (the statement itself is already proved another way) | Cohen structure theorem (0323, 032A), `StacksFrontier/RingTheory/CompleteLocalRing/CohenStructureTheorem/CoefficientRing.lean`; complete regular local rings (0C0S), `…/CompleteLocalRing/Regular.lean`; Frontier | 96; 101 | **low**: closure too large, and the finding is already settled |
| 9 | 101, `101-sheaf-duality-dim-one` (`Folder101.lean`) | Ext and local cohomology of `O_X`-modules on `Spec A`; the identification of `Ext¹_A(K, A)` with a cokernel | local cohomology (0952, 0A6R), `StacksFrontier/RingTheory/LocalCohomology/CechModel.lean`, `StacksFrontier/RingTheory/Dualizing/LocalCohomology/RightAdjoint.lean`; Frontier | 102 | **low**; the `Ext¹` identification is better done with Mathlib's own `Ext` long exact sequence |
| 10 | 22, docstring of `Folder22.lean` | Cohen algebras, formal smoothness and geometric regularity (3.2, 3.6–3.13) | formally smooth ⇔ geometrically regular (07NQ), `StacksFrontier/RingTheory/GeometricallyRegular/FormalSmoothness.lean`; regular local rings (07EI), `StacksFrontier/RingTheory/FormallySmooth/RegularLocal.lean`; the multivariable power-series transfer (EGA 0 19.3.4), `StacksFrontier/RingTheory/FormallySmooth/CompleteLocalTransfer.lean`; Frontier | 397; 227; 628 | **low** (closures) |
| 11 | 29, `29-inertia-matrix-determinant` (`Folder29.lean`) | tame inertia of regular schemes, the Kummer computation of the inertia map | Abhyankar's lemma (0BRM), `StacksFrontier/RingTheory/DiscreteValuationRing/Abhyankar/AbhyankarLemma.lean`; tame covers along a regular divisor (0EYG), `StacksFrontier/AlgebraicGeometry/FundamentalGroup/Abhyankar/RegularDivisorUnconditional.lean`; Frontier | 279; 4,384 | **low** |
| 12 | 2, `2-trivial-total-chern-class` (`Folder2.lean`) | the K-group of coherent sheaves and Chern classes, to see that `i_!(O_Y)` is nonzero | Grothendieck groups of coherent and perfect complexes, `StacksFrontier/AlgebraicGeometry/Perfect/GrothendieckGroupCoherentNonzero.lean`; first Chern class of divisors, `StacksFrontier/AlgebraicGeometry/Divisors/WeilDivisorClass/FirstChernClassInjective.lean`; Frontier | 254; 991 | **low**; no total Chern class on `K` was found |
| 13 | 29, `29-degree-n-as-primitive` | universal effective descent morphisms in general, and for finite sets | descent along coverings of a site, `StacksFrontier/CategoryTheory/Sites/Stack/EffectiveDescent*.lean`; Frontier | not counted | **none** for the categorical statement needed (effective descent for an abstract class of morphisms in a category, and its identification in `FintypeCat`) |
| 14 | FG_IL_5_SGA6_2_4, `FG_IL_5_SGA6_2_4-ext-effaceability-criterion` | effaceability of positive-degree `Ext` classes in an arbitrary abelian category | `StacksCore/CategoryTheory/Abelian/DeltaFunctor/Effaceable.lean` (universality of effaceable δ-functors); Core | 4 | **none**: it is the converse direction (effaceable ⇒ universal); the effaceability of Yoneda classes is not there |
| 15 | 145, `145-unit-exponent-exercise` | free profinite groups, `ℤ̂`-powers | profinite integers only (`StacksFrontier/NumberTheory/TraceFormula/ProfiniteIntegersProcyclic.lean`) | — | **none** |
| 16 | 115, `115-isbell-duality-derived-from-kernels` | Isbell duality | — | — | **none** |
| 17 | 161-3, three findings | a 2-category of topoi | ringed topoi and their morphisms appear in many files, but not a 2-category of topoi with localic products | — | **none** for the statement needed |
| 18 | 113, `Folder113.lean` | projective generators of a functor category | only for derived categories of schemes (`StacksFrontier/AlgebraicGeometry/Perfect/ProjectiveGenerator*.lean`) | — | **none** |
| 19 | 46, `46-semilocal-hilbert90-inertia` | Lang's theorem over a finite residue field; completion and Artin–Rees descent in the wild case | nothing found by name for Lang's theorem | — | **none** |
| 20 | 13, 1, 150, 152, 154, 88 and the other non-geometric gaps (Lindemann, Schatten classes, stratified spaces, maps on surfaces, oriented matroids) | outside algebraic geometry | — | — | **none**: out of the library's scope |

## Notes on the three proofs written

**Folder 22, the `t`-adic half** (`lean/Grothendieck/Folder22Adic.lean`). For every commutative
ring `k`, `C : k → k[[t]]` satisfies `RingHom.FormallySmoothNAdic` for the ideal `(t)`
(`formallySmoothNAdic_C_X`), for every ideal containing `t` (`formallySmoothNAdic_C_of_X_mem`),
and over a field for the maximal ideal (`formallySmoothNAdic_C_maximalIdeal`); `adic_not_discrete`
puts the two halves of pages 22 and 24 side by side for `k = ℚ(x_i : i ∈ I)`, `I` infinite. The
argument lifts the image of `t` to a nilpotent element, evaluates power series there with
Mathlib's `PowerSeries.eval₂Hom`, and checks the lift with the Stacks uniqueness lemma
`powerSeries_hom_ext`. It is the one-variable case of a Stacks theorem whose file has too large a
closure to vendor, rewritten for `PowerSeries`.

**SGA 6 2/3, `K(A) ≅ K(D^b(A))`** (`lean/Grothendieck/IhesSGA6_2_3Db.lean`). The edition's
`K₀` of a pretriangulated category is definitionally the Stacks `Pretriangulated.K0`
(`K₀_eq_K0`, by `rfl`), so tag 0FCP applies as stated: `exists_addEquiv` gives the isomorphism
with `[X] ↦ cl(X[0])`, `addEquiv_unique` its uniqueness, and `exists_cl_eq` the corollary that
every element of `K(A)` corresponds to the class of one object of `D^b(A)`.

**Folder 94, the Koszul step of Lemme 6** (`lean/Grothendieck/Folder94Koszul.lean`).
`exists_isOpen_dense_isKoszulRegularOn`: on the dense open of the existing
`exists_isOpen_dense_isWeaklyRegular'`, every `A_𝔭`-weakly regular sequence `t` has acyclic
Koszul complex `K_•(t)` and `H_i(K_•(t) ⊗ R_𝔭) = 0` for `i > 0`. The first vanishing makes
`K_•(t)` a free resolution of `A_𝔭/(t)`, so the second is the vanishing of
`Tor_i(R_𝔭, A_𝔭/(t))`; the comparison with Mathlib's derived-functor `Tor` is not formalised.

All three files elaborate under `lake build` (with the project's `warningAsError = true`), and
`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for every theorem.

## Vendoring

Sixteen Stacks files (472 KB of source) are copied to `lean/Stacks/`, at their upstream module
paths, with the upstream `LICENSE` and a `NOTICE.md`. Two library entries in
`lean/lakefile.toml` (`StacksCore`, `StacksFrontier`, `srcDir = "Stacks"`, globs on the module
prefix, warnings not errors) make the imports resolve. Every copied file elaborates unchanged
against Mathlib `715a03a`: no API drift had to be fixed, and the attribute files
(`StacksCore/Tactic/StacksAttribute.lean`, `EgaSgaAttribute.lean`) are vendored as they are, so
no attribute was stripped. The generic-freeness files of row 4 were also copied and built
without change, then removed again since no proof uses them yet; they can be re-vendored as they
are.

## Findings without a Lean entry

Of the 128 unsettled algebraic-geometry findings with no `lean` field, the statements concern
moduli of abelian varieties and curves (6, 9, 59, 64, 123, 147), ℓ-adic and tame monodromy (12,
34, 36, 60), topoi and stacks (103, 134-1, 161-2), representability and descent of functors (94,
102, 126, 127, 131), and group schemes (27, 45, 57, 129, 133). The library offers the
infrastructure several of them start from (fpqc descent, Artin's axioms, Picard schemes, étale
fundamental groups, local cohomology), but each claim is a new statement whose proof would be a
project of its own, and none can be closed by citing a declaration. The nearest is
`23-finite-normalisation-quotient-of-regular` (finiteness of normalisation for quotients of
regular rings), for which the library's Nagata and excellence material would be the place to
look first.

## Second round (from the roadmap overlap)

### Method

The first round started from the edition's gaps and searched Stacks by their names. This round
starts from the Stacks directories that the Tau Ceti overlap page (`Overlap-with-AxiomMath-Stacks`
on the TauCeti wiki) matches to Michel's roadmaps: `CategoryTheory/Sites/Topos` and `Sites/`,
`AlgebraicGeometry/Groupoids/` (with `FiniteFlatQuotient` and `FiniteFlatAffine`),
`AlgebraicGeometry/WeilCohomology/`, `AlgebraicGeometry/GroupScheme/`, `RingTheory/DeRham/Cartier`,
`AlgebraicGeometry/DeRham/` and `Crystalline/`, `AlgebraicGeometry/FundamentalGroup/`,
`SetTheory/`, and, where a folder called for them, `Cotangent/`, `Deformation/`, `Picard/` and
`PicardScheme/`. For each directory the declarations were listed by their `@[stacks …]`
attributes and module docstrings, then compared with the unproved or partly proved items of
the folders on the same subjects: the `lean` fields of `src/content/findings.ts` that say
« Partly », « not formalised » or « not proved » or name a Mathlib gap, the findings without a
`lean` field in those folders, the « Not formalised » paragraphs of the `lean/Grothendieck/*.lean`
docstrings, and the « n'est pas formalisé » sentences of `docs/lean/sections/*.tex`. One
directory outside the list, `AlgebraicGeometry/Variety/`, is included because the matching
`GroupScheme/OverField` file imports it. Every row was checked by reading the Stacks
statement, not only its file name. Closures are counted as in the first round (Stacks files
reached through `import StacksCore…`/`import StacksFrontier…`, the file itself included);
nothing was vendored or elaborated against our Mathlib this round. Rows already in the first
round's table are not repeated.

### Ranked table

| # | Item (cote, finding or file) | Missing piece | Stacks declaration(s), file, tier | Closure | Feasibility |
|---|---|---|---|---|---|
| 1 | 53, page 9, the criterion of geometric irreducibility (`Folder53.lean`, second part; section 53) | the scheme-level statement with Mathlib's `GeometricallyIrreducible`: the Galois action on `X_{k'}` and its transitivity on fibres, the reduction from all fields to finite Galois (or separable) extensions, the radicial step | `geometricallyIrreducible_tfae_of_isSepClosure` (038I, EGA IV 4.5.9), `StacksFrontier/AlgebraicGeometry/Variety/Geometrically/IrreducibleSeparableClosure.lean`; `fiber_irreducibleComponentsBaseChangeMap_eq_orbit` (04KY), `…/Variety/GeometricIrreducibleComponents/GaloisOrbit.lean`; `fixed_geometricComponent_iff_exists_geometricallyIrreducible_component` (038J), `StacksFrontier/AlgebraicGeometry/GroupScheme/OverField/GaloisFixedComponentDescent.lean`; Frontier | 15; 14; 18 | **high**: 038I is the reduction to `k^sep` (the radicial part is inside it), 04KY the transitivity of the Galois group on the components over a component of `X`, and 038J says that a Galois-fixed component of `X_{k^sep}` is the inverse image of a geometrically irreducible component of `X`, which is the page's last step when `X` is irreducible. All three use Mathlib's `GeometricallyIrreducible`. Remaining work: pass hypothesis b) (the image of `Z` meets no point lying on two components of `X_k̄`) from `k̄` to `k^sep`, and show the component containing `f'(Z')` is fixed |
| 2 | 19, the remark after theorem 1.12 (section 19, `Folder19.lean`) | the application to topoi: for a morphism of topoi `u : E → F` with `u*` conservative, `F` is the category of coalgebras of the comonad `u* u_*`; « mathlib n'ayant pas les morphismes de topos » | `MorphismOfTopoi` (structure: pushforward, inverse image, adjunction, left exactness of the inverse image; SGA 4 IV 3.3.1 on `id` and `comp`), `StacksFrontier/CategoryTheory/Sites/Topos/MorphismOfTopoi.lean`; `IsMorphismOfSites.morphismOfTopoi` (00XC), same file; Frontier | 4 | **high**: the structure carries exactly the data the remark uses, and the proof is our `theoreme_b_suffisance` (Beck, already in `Folder19.lean`) applied to `u.adj`, equalizers being finite limits. The Stacks structure only bundles what Mathlib can state; what it adds is a shared name and the morphisms of topoi of sites (00XC) to apply the statement to |
| 3 | 113, `Folder113.lean`, the `k`-linear form of Morita invariance | « the `k`-linear form (and the remark itself) is not formalised »: `Kar(P)` as a `k`-linear category, so that restriction along `P° → (Kar P)°` can be read on `k`-linear functors | `CategoryTheory.Idempotents.Karoubi.linear`, `Karoubi.instModule`, `Karoubi.comm_iff_exists` (in the file tagged 0FGA), `StacksFrontier/AlgebraicGeometry/WeilCohomology/Motives/Category.lean`; Frontier | 4 | **high**: the instance is the missing ingredient; it is declared `local` upstream, so it is used through `letI`, and it is short enough to restate. Remaining work: the `k`-linear analogue of `additive_of_toKaroubi_op` (a functor on `(Kar P)°` is `k`-linear when its restriction to `P°` is) and the restricted equivalence. The remark that additive functors are automatically `k`-linear stays to be proved separately |
| 4 | 136, `136-pd-de-rham-shadows` (`Folder136.lean`) | « the differential `d(x^{(n)}) = x^{(n−1)}dx` on `Γ(Φ) ⊗ Λ^•Ψ` and its agreement with `pdD` in this basis » | divided power differentials `Crystalline.dividedPowerDifferentials` and the divided power de Rham complex `Crystalline.dividedPowerDeRhamComplex`, with its uniqueness (07HZ), `StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/DeRham.lean`; `dividedPowerDifferentialsDividedPowerPolynomialEquiv` (07HS: `Ω¹` of `B⟨x_w⟩` is `P ⊗ Ω¹_B ⊕ ⨁ P dx_w`), `…/Differentials/DividedPowerPolynomialAlgebra.lean`; Frontier | 7; 30 | **medium**: 07HZ builds the complex with the rule `d(δ_{n+1}x) = δ_n x · dx` over any divided power ring, and 07HS identifies its first term for divided power polynomials over any base, which is the coordinate model of pages 5–7. Remaining work: Stacks uses its own divided power polynomial algebra, not Mathlib's `DividedPowerAlgebra` used in `Folder136.lean`, so the two must be identified (both have the monomial basis), and `pdD` compared with the Stacks differential on that basis. Stacks puts divided powers on the augmentation ideal of Mathlib's `Γ` only for torsion-free bases (`StacksFrontier/RingTheory/DividedPowers/AugmentationIdeal.lean`, closure 5), which is why the route goes through 07HS |
| 5 | 136, same finding, Proposition 1 | « the acyclicity of `C^{p,q}_*` for `p ≥ 1` (Proposition 1, `Φ_* ≃ 0`) » | `Crystalline.simplexVertexModule` and its contracting homotopy (07L7), `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/Preparation.lean`; `homotopic_exteriorPower_map`, tensor and completion parts of 07KQ, `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial.lean`; null homotopy ⇒ acyclic Moore complex, `…/Cosimplicial/Acyclicity.lean`; Frontier | 8; 7; 8 | **medium**: `[n] ↦ k^{n+1}` on the vertices of `[n]` is the page's `Φ_*`, and 07L7 is its contraction; 07KQ carries a homotopy through `⊗` and `Λ^q`. Missing: the divided power case `Γ^p` (07KQ as formalised has tensor, exterior powers and completion, not `Γ`), which has to be written on the model of `homotopic_exteriorPower_map`, and the passage from the cosimplicial module to sections over an arbitrary simplicial set |
| 6 | 11, `11-simplicial-bivariant-poincare-equivalence` (`Folder11.lean`) | « the graded case with Koszul signs » and p. 41's « full faithfulness of `A ↦ (A(pt), Δ)`, whose axioms on `Δ` the page does not write » | `Stacks.WeilCohomology.DiagonalExpansion`: `exists_expansion`, `sum_trace_mul_smul`, `isPerfPair_tracePairing`, `bijective_diagonalContract`, `trace_unique` (the algebra of the proofs of 0FIJ and 0FIK; the file carries no attribute), `StacksFrontier/AlgebraicGeometry/WeilCohomology/Concrete/DiagonalExpansion.lean`; Frontier | 1 | **medium**: for `ℤ`-graded, graded-commutative algebras with a bijective Künneth map, a class `η` with `η·p₁a = η·p₂a` and `(id ⊗ λ)(κ⁻¹η) = 1` makes the trace pairing perfect and determines `λ`. These are candidate axioms for the page's `Δ`, with the signs included, and the uniqueness of `λ` is the step that full faithfulness needs. Remaining work: write the gauged algebras in the graded setting and derive full faithfulness from `trace_unique` |
| 7 | `EffectiveVenken.lean` (section `effective-venken`) | « the scheme-theoretic language (`R` is handled through its ideal) », and the comparison with the flat case | pre-relations and equivalence relations of schemes, `equivalence_sourceTargetRel` (022Q), `StacksFrontier/AlgebraicGeometry/GroupScheme/Relations/PreRelations.lean`; the groupoid of an equivalence relation (0232, 0233), `…/GroupScheme/OverField/GroupoidOfEquivalenceRelation.lean`; for the flat contrast, `isFiniteLocallyFree_objectsToInvariantSpectrum`, `isPullback_objectsToInvariantSpectrum` (03BM, SGA 3 V 4.1), `StacksFrontier/AlgebraicGeometry/Groupoids/FiniteFlatAffine/AffineQuotient.lean`, and `isIntegral_invariantRing` (03BJ), `…/FiniteFlatAffine/IntegralInvariants.lean`; Frontier | 7; 6; 529; 101 | **medium** for the language: the definitions of 022Q and 0233 let Venken's `R ⊂ Spec B × Spec B` be stated as an equivalence relation of schemes, and the translation from our equivalence ideals is a short computation on affine schemes. **Low** for the contrast with 03BM (for finite locally free `R` on an affine scheme, `Spec B → Spec B^R` is finite locally free with `R` as kernel pair), whose closure is 529 |
| 8 | 93, Cartier descent (section 93, `Folder93.lean`) | « La descente de Cartier n'est formalisée que sur le fibré trivial, quand l'anneau a une coordonnée »; the passage to a smooth curve | `KaehlerDifferential.Cartier.inverseCartier`, `inverseCartier_bijective_of_isFrobeniusCoordinates` (Cartier isomorphism for an algebra with Frobenius coordinates), `StacksFrontier/RingTheory/DeRham/Cartier/Coordinates.lean`; `inverseCartier_bijective_mvPolynomial`, `…/Cartier/Polynomial.lean`; no `@[stacks]` attribute on these files; Frontier | 42; 43 | **medium**: the Cartier isomorphism in degrees 0 and 1 in several coordinates is the input to Cartier descent for a connection `d + ω` of rank one, where `p`-curvature zero says that `ω` is fixed by the Cartier operator. Partial fill: the descent statement itself, nontrivial bundles and higher rank are not there, and the étale-over-polynomial case of Frobenius coordinates is announced in the docstring, not checked here. Closure at the threshold |
| 9 | 16, `Folder16.lean` (Problem 5) | « Not formalised: weak and hard Lefschetz, Weil cohomologies » | `ClassicalWeilCohomologyTheory` (0FGV), with abstract `ChowCycleData`, `cycleClass_externalProduct`, `integration_pullback_mul_cycleClass`, `StacksFrontier/AlgebraicGeometry/WeilCohomology/ClassicalTheory.lean`; Frontier | 64 | **low**: the definition of a classical Weil cohomology theory is there with abstract Chow data, so `A⁰(X)`, `A'⁰`, `A''⁰` could be stated inside one; weak and hard Lefschetz are not among its axioms, and the closure exceeds 40 |
| 10 | 11, `11-tautological-diagonal-product-rule` | « the geometric setting and excess intersection »: `δ² = χ y₁y₂` on `X²` in an actual cohomology theory | `eulerCharacteristic_eq_degree_diagonal_mul`, `eulerCharacteristic_eq_degree_diagonal_mul_eq_degree_chernCap` (0FH0), `StacksFrontier/AlgebraicGeometry/WeilCohomology/ClassicalEulerCharacteristic.lean`; `degree_diagonal_mul_eq_degree_chernCap_tangentSheaf` (0FH0), `…/ClassicalDiagonalSelfIntersection.lean`; Frontier | 15,264 | **low**: 0FH0 is the degree form of the page's first relation (`deg([Δ]·[Δ]) = Σ(−1)ⁱ dim Hⁱ = deg c_d(T_X)`), but the closure is out of reach; the algebraic model already in `Folder11.lean` stays the right place |

### Directories with no match

- **`SetTheory/` (8 files).** Reflection for `V_α` (000G), cofinality (05N2, 05N3) and a size
  bound (046U). No Lean item or finding of the edition needs a Grothendieck universe or `V_κ`;
  the occurrences of « universe » in `lean/Grothendieck/` are Lean `universe` declarations.
- **`AlgebraicGeometry/FundamentalGroup/` (457).** Galois categories, étale `π₁`,
  specialization and purity. The fundamental-group folders' open items are the free profinite
  group of 145 (first round, row 15), the Teichmüller and Galois–Teichmüller statements of 142,
  146, 148 and 149, and the stratified `Π₁` of 151, none of which is a statement about the étale
  `π₁` of a scheme. The finite-set descent of 29 is first-round row 13.
- **`CategoryTheory/Sites/Topos` beyond row 2.** 2-morphisms of topoi and their compositions
  (04IA, 04I9, `TwoMorphismOfTopoi.lean`, closure 5) and localisation `Sh(C)/F ≃ Sh(C/F)` (0791,
  `LocalizationOfTopoi.lean`, closure 2) are there, but no 2-product of topoi, localic topos,
  Giraud theorem or `Ind_π`; first-round row 17 (161-3) stands, and 161-1 and 161-2 have no
  match.
- **`AlgebraicGeometry/GroupScheme/` beyond row 1.** Group schemes over a field (separated
  047L, smooth in characteristic 0 047N, identity component 047M, 0B7R), torsors (0498–049A),
  abelian varieties (03RO, 03RP, 0BFA). No monoid schemes (53, first part), no Krull–Schmidt or
  tannakian categories (10), nothing on the ranks of 27, the affine quotients of 133 or the
  Picard groups of 123, and no genus-0 curves over a base with an étale trisection (62).
- **`Deformation/`, `Cotangent/`, `Picard/`, `PicardScheme/`.** The Rim–Schlessinger lifts
  (06JE–06JH) and square-zero algebra extensions (0GPT–0GPY) are general; the liftings of smooth
  groups and the obstruction in `FG_IL_2_GIRAUD69` would need group-scheme and gerbe versions
  that are not there. No Picard group of a quotient stack was found (140-1, where the reading
  says « Mathlib n'a pas les champs quotients ni leur groupe de Picard »).
- **De Rham and crystalline beyond rows 4, 5 and 8.** The de Rham–Hochschild comparison of
  162-5 and the de Rham application of `93-derived-morphism-homotopy-torsor` are statements about
  formal categories and sheaf torsors; the crystalline files concern the crystalline site and
  have no counterpart there.

### Reading

Rows 1 to 3 have small closures and statements that fill the named gap directly; row 1 is the
best of this round, since three tagged Stacks results cover the three steps that
`Folder53.lean` lists as not formalised. Rows 4 to 8 supply real pieces but each leaves glue to
write (a second model of divided powers, the `Γ^p` homotopy, the graded gauged algebras, the
affine translation, the descent statement). Rows 9 and 10 are out of reach by closure.

## Buffalo entries

The Buffalo lectures (1973) have their own Lean library, `lean/Buffalo/`, with one status record
per entry of the three indexes in `docs/buffalo-{ag,topos,groupes}/lean/Part*.json`. Of the 2,357
algebraic-geometry records, 532 were `partial` and 239 `not-formalised`; topos and group schemes
add 353 and 192. They were screened by the reason their note gives (a notion or theorem missing
from Mathlib) and matched against the same Stacks copy as above, by tag, by declaration name and
by reading statements. « Closure » counts Stacks files as above, with the number not yet vendored
in brackets. Rows 1–15 are proved in `lean/Buffalo/AlgebraicGeometry/AGPart04Stacks.lean`, `Part05Stacks.lean`,
`Part06Stacks.lean`, `Part06dStacks.lean` and `Part07Stacks.lean`, and their records updated.

| # | Buffalo entry (AG unless said) | Missing piece | Stacks declaration(s), file, tier | Closure | Feasibility |
|---|---|---|---|---|---|
| 1 | 23907, invertible ⇔ finite projective of rank one at every prime | the converse (a Mathlib TODO) | `Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse` (0B8I), `StacksFrontier/Algebra/Module/Projective/Invertible.lean`; Frontier | 3 [1] | **done** |
| 2 | 7990, Koszul complex of a regular sequence acyclic | Koszul complexes | `Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular` (062F), `StacksFrontier/RingTheory/Koszul/Regular.lean`; Frontier | already vendored | **done** |
| 3 | 8250, `A` regular ⇔ `Â` regular | regularity of the completion | `isRegularLocalRing_iff_adicCompletion_maximalIdeal` (07NY) in `StacksFrontier/RingTheory/AdicCompletion/PermanenceOfProperties.lean` (closure 230, too large), so 07NV and 07NY reproved over `AdicCompletion.isNoetherianRing` (0316); Frontier | 3 [2] | **done** |
| 4 | 33941 and 33684, the relative spectrum of a quasi-coherent algebra, representable, `Spec Γ(U, 𝒜)` over affine `U` | quasi-coherent algebras, relative Spec | `relativeSpecFunctor_isRepresentable` (01LU), `relativeSpecRepresentableBy` (01LV), `GluedSpectrum.chart_isPullback` (01LP), `StacksFrontier/AlgebraicGeometry/RelativeSpec/Representability.lean`; Frontier | 22 [20] | **done** |
| 5 | 34520 and 34263, `f_*𝒪_X` quasi-coherent for `f` affine, anti-equivalence with quasi-coherent algebras, essential image | the same | `isQuasicoherent_pushforwardAlgebra` (02KG), `affineQuasicoherentEquivalence` (01SA), `StacksFrontier/AlgebraicGeometry/RelativeSpecEssSurj/Basic.lean`; Frontier | 19 [0 after row 4] | **done** |
| 6 | 17370, the equivalent definitions of a separable algebra (any perfect extension `K₁`) | the implications beyond Mathlib's definition | `Algebra.isGeometricallyReduced_tfae` (030V), `Algebra.IsGeometricallyReduced.isReduced_tensorProduct` (034N), `StacksFrontier/RingTheory/GeometricallyReduced/{TFAE,TensorProduct}.lean`; Frontier | 28 [25] (with rows 7–10) | **done** |
| 7 | 19493, products of separable (and of geometrically irreducible) `k`-schemes | the separable half; universal openness over a field | `geometricallyReduced_pullback_over_field` (035Z), `.../Variety/Geometrically/ReducedProduct.lean`; universal openness is Mathlib's instance (0383, `.../Morphisms/Open/OverField.lean` only restates it) | same closure | **done** |
| 8 | 16790 and 17116, perfect fields and reduced tensor products | arbitrary reduced algebras and extensions | `PerfectField.isReduced_tensorProduct` (00I4), `.../GeometricallyReduced/TensorProduct.lean` | same closure | **done** |
| 9 | 17899, over a perfect field reduced ⇒ separable | the perfect-field converse | `Algebra.IsGeometricallyReduced.of_perfectField` (00I4), `geometricallyReduced_of_isReduced` (020I), `.../Variety/Geometrically/Reduced.lean` | same closure | **done** |
| 10 | 17970, `X` separable over `k` ⇔ `X_{k'}` over `k'` | the descent direction | `geometricallyReduced_iff_baseChange_fieldExtension` (0384), `.../Variety/Geometrically/ReducedBaseChange.lean` | same closure | **done** |
| 11 | 8055, `𝔾_m` and `GL_n` regular | regularity of localizations of regular rings | `isRegularRing_of_isLocalization` (after 00OD), `StacksFrontier/RingTheory/RegularRing/Defs.lean` | 1 [1] | **done** |
| 12 | 2525, completions of noetherian rings noetherian | noetherianity of `AdicCompletion` | `AdicCompletion.isNoetherianRing` (0316), `.../AdicCompletion/NoetherianRing/PowerSeriesSurjection.lean` | 3 [2] | **done** for this half; `Â ⊗_A Â` non-noetherian not formalised |
| 13 | 19954, 20993, 21315, products of geometrically connected `k`-schemes | the universal-openness hypothesis | none needed: Mathlib's `UniversallyOpen` instance over a field (0383); hypothesis dropped | 0 | **done** for these parts; the separably-closed and descent parts remain |
| 14 | 8313, Cohen's structure theorem for complete regular local rings | Cohen structure theorem | `StacksFrontier/RingTheory/CompleteLocalRing/CohenStructureTheorem.lean` (032D, 032A) | 99 [83] | low |
| 15 | 8121, Serre's criterion (regular ⇔ finite global dimension) | global dimension | `isRegularLocalRing_tfae` (00OC), `StacksFrontier/RingTheory/RegularLocalRing/GlobalDimension.lean` | 532 | low |
| 16 | 7860, regular local ⇔ maximal ideal generated by a regular sequence | the comparison with `dim` | 00NQ in `StacksFrontier/Algebra/Module/RegularLocalNakayama.lean`; `isWeaklyRegular_of_span_range_eq_maximalIdeal` in `.../Blowup/ProjectiveLineExceptional.lean` | 42 [39]; 1,913 | low |
| 17 | 22510, 22572, coherent sheaves of modules | coherent `𝒪_X`-modules | `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentIffFinitePresentation.lean` (on ringed sites) | 27 [22] | medium: closure fine, but the statements are for sheaves on sites and need glue to Mathlib's `SheafOfModules` on a scheme |
| 18 | 3491, descent of finite presentation for modules | fpqc descent of finite presentation | 03C4 only for `M^~` (`StacksFrontier/AlgebraicGeometry/FlatBaseChange/Descent.lean`) | 52 [48] | low |
| 19 | Groupes 6070, determinant of a projective module | determinants of non-free modules | `K0.exists_determinant_hom` (0AFX), `StacksFrontier/KTheory/Grothendieck/Determinant.lean`; the determinant itself is private there | 15 [13] | low: no public determinant to state the entry with |
| 20 | 24233, 28043–29412, 25093–27544, 31422–33600, 18281–19653 and the other ℙ(E), ample and very ample entries (about 60) | ℙ(E), ample invertible sheaves | `StacksFrontier/AlgebraicGeometry/ProjectiveBundle/…`, `.../Ample*/…`, `.../AmpleFamilyCartier/Basic.lean` | 5,642; 1,029; `AmpleWire/Basic.lean` 18 but only a wiring file | low |
| 21 | 16640, 17552, 18219 and the effective descent of schemes | a category of descent data of schemes | `StacksFrontier/AlgebraicGeometry/Stacks/…` (descent for algebraic stacks) | hundreds | low |
| 22 | Topos 02d, 03b, 05a, 07b: Grothendieck topoi, geometric morphisms, `Cat_D` | a notion of Grothendieck topos | only auxiliary structures (`ToposPoint`, `ToposAdjointPair` in `StacksFrontier/CategoryTheory/Sites/…`), no class of topoi | — | **none** |
| 23 | Topos 01d, colimits in `GrpCat`; Groupes 03a, discrete `Gal(k_s/k)`-sets; group schemes (Cartier, quotients, `G⁰`, pseudo-compact duals) | outside the library's scope or not by name | nothing found by name | — | **none** |

Rows 3 and 12 vendor only `PowerSeriesSurjection.lean` and `EvalFactorPow.lean`; the two lemmas
of tags 07NV and 07NY are proved again in `Part06Stacks.lean` from Mathlib (going down for the flat
completion, `AdicCompletion.maximalIdeal_eq_map`, `AdicCompletion.spanFinrank_maximalIdeal_eq`),
since `PermanenceOfProperties.lean` pulls in 230 files. Row 13 needed no Stacks file: the
Buffalo docstring that universal openness over a field was missing from Mathlib was wrong at our
pin. All the proofs elaborate under `lake build` with `warningAsError`, and `#print axioms`
reports only `propext`, `Classical.choice` and `Quot.sound`. Forty-nine Stacks files were vendored
for them, unchanged, and are listed in `lean/Stacks/NOTICE.md`.
