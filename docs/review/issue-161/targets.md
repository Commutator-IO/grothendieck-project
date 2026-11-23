# Tau Ceti roadmaps against AxiomMath's Stacks: tags and moves (2026-11-23)

This file covers the first two steps of issue #161, « Tags, not paths » and « Per roadmap, sort
the targets ». It replaces the file-name matching of the TCR wiki survey with the `@[stacks TAG]`
attributes of the library. A draft of the first review claim is in `claim-00XA-00XC.md`.

## Method

- **Stacks side.** I read a full checkout of AxiomMath/Stacks at `f56a316` (18 Nov 2026, the
  commit the fork `mycaule/Stacks` was created at), 64,216 Lean files. `scripts/index.py` collects
  every tag in an `@[stacks …]` attribute (multi-line ones too), with its file and the declaration
  after it. `scripts/addidx.py` adds the tags registered over Mathlib with `add_to_stacks`. The
  index holds 16,515 tags in 44,069 (tag, declaration) entries. A tag is **Core** when a `StacksCore/` file
  carries it, **Frontier** when only `StacksFrontier/` files do, and **not formalized** otherwise.
  `scripts/look.py` prints the status of a list of tags.
- **Roadmap side.** I took the heads of the nine pull requests on TauCetiProject/TauCetiRoadmap
  (the eight of the issue's table, plus #2295, which the issue lists as a supplier case).
  `scripts/targets.py` lists the `sorry`'d declarations of each `Suggested.lean`. Each target was
  matched to a tag from the tags its README and `Suggested.lean` cite, and from the declarations
  found by grepping the checkout. A tag is given only when it was seen attached to a matching
  statement. A row marked « by name » was matched on names without reading the statement.
- **Moves.** 2 = claim on a tag not formalized; 3 = review claim, Frontier → Core; 4 = stays in
  Tau Ceti, either because the statement is not in the Stacks Project or because Stacks states it
  at another generality. Move 1 is dropped (issue, update of 21 Nov).

## Result

| Roadmap (TCR PR) | Targets | Move 2 | Move 3 | Move 4 |
|---|---|---|---|---|
| GrothendieckTopoi (#1520) | 44 | 0 | 8 | 36 |
| FiniteEquivalenceRelations (#1929) | 22 | 0 | 6 | 16 |
| GroupSchemesOverABase (#1522) | 25 | 0 | 6 | 19 |
| ClassifyingTopoi (#1997) | 28 | 0 | 1 | 27 |
| ProjectiveModulesOverPolynomialRings (#2295) | 18 | 0 | 1 | 17 |
| LefschetzStructures (#1061) | 12 | 0 | 0 | 12 |
| PCurvature (#1747) | 11 | 0 | 0 | 11 |
| GrothendieckTeichmuller (#1058) | 15 | 0 | 0 | 15 |
| GrothendieckUniverses (#1783) | 8 | 0 | 0 | 8 |
| **Total** | **183** | **0** | **22** | **161** |

What the numbers say:

1. **No move 2.** The roadmaps cite 60 distinct tags. 56 of them have a declaration in Stacks,
   all in Frontier. Four cited tags have none: 03BE (Section 39.23), 08WE (Section 35.4),
   and 000F, 000H (GrothendieckUniverses). All four are sections, so there is nothing to claim. No
   exercise appears, so the scope question about exercises (« Access and requirements » in the
   issue) does not come up yet.
2. **Every match is Frontier only.** No tag a roadmap needs is in `StacksCore`. At `f56a316`,
   Core has no `AlgebraicGeometry/` directory. Its `CategoryTheory/Sites/` holds 30 tags
   (presheaves, sheafification, cocontinuity), none of them a target here. So the only
   contribution these roadmaps lead to is move 3, the one CONTRIBUTING.md calls « one of the most
   useful ».
3. **Move 3 covers a site-level or field-level case, rarely the whole target.** GrothendieckTopoi
   states its targets for an abstract `IsGrothendieckTopos E`, while Stacks works with
   `Sheaf J (Type w)`. GroupSchemesOverABase works over a base, while Stacks's group-scheme files
   work over a field. In both cases a review makes the Stacks half reliable, and the general
   statement stays in Tau Ceti.
4. **The issue's « strong » and « partial » labels hold up only in part.** The survey's strong and
   partial overlaps (GrothendieckTopoi, FiniteEquivalenceRelations, GroupSchemesOverABase) produce
   20 of the 22 review targets. LefschetzStructures and PCurvature, labelled « partial » from
   directory names, produce none: `WeilCohomology/` has nothing on the Lefschetz operator, and
   `DeRham/Cartier/` carries no tags. Those directories hold background, not targets.

## Review candidates, ranked

| Rank | Tags | Stacks files (`StacksFrontier/…`) | Serves | Note |
|---|---|---|---|---|
| 1 | 00XA, 00XC | `CategoryTheory/Sites/Topos/MorphismOfTopoi.lean`, `ToposDefs.lean`, `Sites/MorphismOfSites.lean` | GrothendieckTopoi 2.1–2.2 (definitions), and the base of ranks 2–5 | **drafted**: `claim-00XA-00XC.md`. The closure is 3 files; 716 Frontier files use `MorphismOfTopoi` |
| 2 | 00XL, 00XR | `CategoryTheory/Sites/CoverLifting.lean` | GrothendieckTopoi 2.4 | same generality as the target |
| 3 | 04GZ, 04IP, 09X6 | `Sites/ToposLocalizationSheaf.lean`, `Sites/SliceTopos/`, `Sites/Topos/PresheafLocalization.lean` | GrothendieckTopoi 3.1–3.2 | site-level |
| 4 | 08XA, 08X7, 0EUA | `AlgebraicGeometry/Descent/Modules/EffectiveDescent.lean`, `…/TensorEqualizer/`, `…/EffectiveEpi/QuasicoherentSectionsEqualizer/UniversalEffectiveEpi.lean` | FiniteEquivalenceRelations (descent along universally injective maps) | Stacks uses its own descent-data category; Tau Ceti needs an adapter to `Comonad.comparison` |
| 5 | 03BM, 0233, 02V8 | `AlgebraicGeometry/Groupoids/FiniteFlatAffine/`, `…/FiniteFlatQuotient/`, `…/GroupScheme/Relations/PreRelations.lean` | FiniteEquivalenceRelations (finite flat quotients) | Stacks is more general (any base, both projections finite locally free) |
| 6 | 047L, 047N, 047P, 047R | `AlgebraicGeometry/GroupScheme/OverField/` | GroupSchemesOverABase, the field case | 0B7R and 047M are partial (a translation or finiteness step is missing) |
| 7 | 00Y4, 00Y5, 00YA, 00YC, 00YL, 00YQ | `CategoryTheory/Sites/Point/` | GrothendieckTopoi 6.1, 6.2, 6.4 | the two directions of 6.1 are separate lemmas; Deligne's criterion is more general than the coherent case |
| 8 | 00QO | `Algebra/Category/Ring/FinitePresentation.lean` | ClassifyingTopoi 4.1 | stated under `R`; the target is `R = ℤ` in `CommRingCat` |
| 9 | 00EQ, 00NX | `RingTheory/Localization/Glueing/Modules.lean`, `RingTheory/Module/LocallyFree/FiniteProjective.lean` | ProjectiveModulesOverPolynomialRings 3.6 | the target is a two-element special case that follows from both |

Ranks 2, 3 and 7 depend on rank 1: their files use `MorphismOfTopoi`. As the issue proposes,
submit rank 1 alone, see how long its review takes, then go on.

## Open points

- Unchecked: the SGA 4 references on `MorphismOfTopoi.id`, `comp` and `Functor.IsMorphismOfSites`
  (claim draft, point 4). Checking them needs SGA 4 IV at hand.
- Borderline rows the sorting flagged (details in the Note columns):
  - ClassifyingTopoi 4.2 `isSheaf_forget_zariskiTopology`: move 4, or move 3 through 00EJ.
  - FiniteEquivalenceRelations `nonempty_comonadicLeftAdjoint_invariants`: move 4, or move 3
    through 03BM and 023M.
  - FiniteEquivalenceRelations `isColimit_cofork`: move 4. Its tag 03BE is a section, and the
    flat analogue in Stacks carries no tag.
- Targets marked « — » were checked by the tag index and by keyword greps. An untagged Frontier
  declaration could still have been missed.
- Stacks has no CI and the fork has no workflow yet (step « Formalize »). Nothing here has been
  compiled: this is a reading of statements, not a build.


## GrothendieckTopoi against AxiomMath/Stacks (f56a316)

Of the 44 `sorry`'d targets, **8 have a tagged counterpart in `StacksFrontier`** (move 3), **0 are
unformalised Stacks tags** (move 2), and **36 stay in Tau Ceti** (move 4). Nothing the roadmap needs is in `StacksCore`. The
Core tier of `CategoryTheory/Sites` holds 30 tags, mostly presheaves, sheafification and
cocontinuity (00XJ), registered over Mathlib with `add_to_stacks`; none of them is a target here. The roadmap's
targets are stated for an abstract `IsGrothendieckTopos E`, while Stacks always works with the topos
`Sheaf J (Type w)` of a given site. So even a move-3 row covers only the site-level case of its
target, and the abstract statement stays in Tau Ceti. The most useful review candidates, in order:
00XA/00XC (morphisms of topoi, `MorphismOfTopoi`, used by 716 Frontier files), 00XL/00XR
(cocontinuous functors, target 2.4), 04GZ/04IP (slices and localization, 3.1–3.2), and 00YA/00YC/00YQ
(points and Deligne's criterion, 6.1 and 6.4).

| Target (Suggested.lean) | Tag(s) | Status | Stacks declaration (file) | Move | Note |
|---|---|---|---|---|---|
| `IsGrothendieckTopos.hasLimits` | — | — | — | 4 | Mathlib already has limits of `Sheaf J A`; the abstract predicate is Tau Ceti's |
| `IsGrothendieckTopos.hasColimits` | — | — | — | 4 | same |
| `IsGrothendieckTopos.hasSubobjectClassifier` | — | — | — | 4 | no subobject classifier in Stacks |
| `IsGrothendieckTopos.wellPowered` | — | — | — | 4 | |
| `IsGrothendieckTopos.wellPowered_op` | — | — | — | 4 | |
| `isGrothendieckTopos_iff_giraudAxioms` | — | — | — | 4 | Giraud's theorem: not in the Stacks Project |
| `GeometricMorphism.exists_iff_preservesFiniteLimits_preservesColimits` | (00XA) | Frontier (definition only) | `SheafToposMorphism` (`StacksFrontier/CategoryTheory/Sites/Topos/ToposDefs.lean`) | 4 | the definition is 00XA; the existence criterion (special adjoint functor theorem) is not a Stacks tag |
| `IsGrothendieckTopos.nonempty_geometricMorphism_type` | — | — | — | 4 | |
| `GeometricMorphism.nonempty_unique_hom_to_type` | (04I9, 04IA) | Frontier (2-morphisms only) | `TwoMorphismOfTopoi`, `hcomp` (`…/Sites/Topos/TwoMorphismOfTopoi.lean`) | 4 | 2-cells are there; uniqueness of the map to `Type` is not |
| `GeometricMorphism.exists_of_isCocontinuous` | 00XL, 00XR | Frontier | `sheafAdjunctionPullbackCocontinuous`, `preservesFiniteLimits_sheafPullbackCocontinuous` (00XL); `sheafPullbackCocontinuousIsoSheafPushforwardContinuous`, `sheafAdjunctionLowerShriek` (00XR) (`…/Sites/CoverLifting.lean`) | 3 | same generality (small sites, SGA 4 III 2.3) |
| `nonempty_geometricMorphism_equiv_isFiltering` | — | — | — | 4 | Diaconescu's theorem |
| `IsGrothendieckTopos.over` | 04GZ | Frontier | `Sheaf.exists_over_equiv_sheaf` (`…/Sites/ToposLocalizationSheaf.lean`) | 3 | site-level only: `Over F ≌ Sheaf K (Type u)` for a sheaf `F` |
| `nonempty_sheafOverEquiv` | 04GZ, 09X6 | Frontier | `sheafOverLocalization` (`…/Sites/ToposLocalizationSheaf.lean`); `nonempty_sheafEquiv_over_sheafification` (`…/Sites/Topos/PresheafLocalization.lean`) | 3 | 09X6 is the representable case the target states (by name) |
| `IsGrothendieckTopos.exists_etale` | 04GZ, 04IP | Frontier | `sheafOverLocalization` (`…/ToposLocalizationSheaf.lean`); `localizationMorphism`, `toposLocalization` (`…/Sites/SliceTopos/`) | 3 | inverse image `toOver F` is `Over.star` up to the slice equivalence |
| `exists_universalClosureOperator_equiv_subtopos` | (08LV) | Frontier (definition only) | `IsSubtopos` (`…/Sites/Subtopos/Defs.lean`) | 4 | the correspondence with closure operators or topologies `J′ ≥ J` is not there |
| `GeometricMorphism.exists_surjection_embedding` | (08LU) | Frontier (embeddings only) | `MorphismOfTopoi.IsEmbedding` (`…/Sites/Subtopos/Embedding.lean`) | 4 | the factorization is not there |
| `GeometricMorphism.exists_hyperconnected_localic` | — | — | — | 4 | |
| `GeometricMorphism.isEssential_iff_preservesProducts` | — | — | — | 4 | SGA 4 IV Exercice 7.6 |
| `nonempty_point_equivalence` | 00Y4, 00Y5, 00YA, 00YC | Frontier | `PointOfTopos` (`…/Sites/Point/Defs.lean`); `SitePoint` (`…/Point/SitePoint.lean`); `pointOfTopos`, `isIso_sheafFiberComparison` (`…/Point/Topos.lean`); `equivFiber` (`…/Point/SitePointOfPreservesFiniteLimits.lean`) | 3 | Stacks has both directions as separate lemmas; the equivalence of categories of points is not assembled |
| `hasEnoughPoints_sheaf_iff` | 00YL | Frontier | `nonempty_isLimit_iff`, `eq_of_forall_sheafFiber_map_eq` (`…/Point/SitesWithEnoughPoints.lean`) | 3 | partial (by name): consequences of enough points, not the comparison of the two notions |
| `hasEnoughPoints_coherentTopology` | 00YQ, 0DW0 | Frontier | `hasEnoughPoints_of_exists_finite_refinement`, `hasEnoughPoints_of_coversTop_of_exists_finite_refinement` (`…/Point/CriterionForExistenceOfPoints/DeligneCriterion.lean`) | 3 | Stacks states Deligne's criterion for sites whose coverings have finite refinements; the coherent topology is a special case to derive |
| `exists_equiv_presheaf_iff_essential_points` | — | — | — | 4 | Roos's theorem, SGA 4 IV Exercice 7.6 d) |
| `epi_piMap_presheaf` | — | — | — | 4 | |
| `isIso_sigma_pi_presheaf` | — | — | — | 4 | |
| `isIrreducibleObject_yoneda_iff` | — | — | — | 4 | Caramello |
| `isIrreducibleObject_iff_projective_preservesCoproducts` | — | — | — | 4 | |
| `nonempty_equiv_presheaf_of_isRigid` | — | — | — | 4 | |
| `isRigidTopology_iff_nonempty_equiv_presheaf` | — | — | — | 4 | |
| `GeometricMorphism.isLocalic_iff_nonempty_equiv_sheaf` | — | — | — | 4 | locales are outside the Stacks Project |
| `exists_sublocale_orderIso_subtopos` | — | — | — | 4 | |
| `LocallyCompactSpace.coreCompactSpace` | — | — | — | 4 | general topology |
| `quasiSober_pi` | — | — | — | 4 | general topology |
| `quasiSober_prod` | — | — | — | 4 | |
| `isFrameCoproduct_opens_prod` | — | — | — | 4 | |
| `not_isFrameCoproduct_opens_rat_prod` | — | — | — | 4 | |
| `preservesFiniteLimits_sheafPullback_overForget` | 03DJ | Frontier | `extensionByZero_exact` (`…/Sites/Modules/ExtensionByZeroExactness.lean`, `…ExactnessGeneral.lean`) | 3 | Stacks states it for `O`-modules; abelian sheaves are the case `O = ℤ` (by name) |
| `faithful_sheafPullback_overForget` | — | not found | — | 4 | no faithfulness statement for `j_!` found by name |
| `recollement_extensionByZero` | (08LY) | Frontier (closed complement only) | `isSubtopos_closedComplement` (`…/Sites/Subtopos/Subtopoi.lean`) | 4 | the recollement sequence is SGA 4 IV §14, not a Stacks tag found |
| `bijective_comp_kernelι_of_isZero` | — | — | — | 4 | |
| `nonempty_cokernel_iso_rightDerived_one` | — | — | — | 4 | |
| `nonempty_rightDerived_succ_iso_rightDerived_pushforward` | — | — | — | 4 | |
| `nonempty_supportFunctor_iso_supportedSectionsFunctor` | — | — | — | 4 | bridge to Tau Ceti's own supported sections |
| `nonempty_rightDerived_supportFunctor_iso_supportedHSheaf` | — | — | — | 4 | |
| `isZero_of_projective_sheaf_real` | — | — | — | 4 | |

Layer 1.1 (the predicate `IsGrothendieckTopos`) and the definitions of 2.1–2.2 are not `sorry`'d, so
they do not appear above. Their Stacks counterparts are 00XA and 00XC, for topoi of sites. That is
the first review claim drafted (`claim-00XA-00XC.md`).

## FiniteEquivalenceRelations against AxiomMath/Stacks (f56a316)

22 sorry'd targets: move 2: 0, move 3: 6, move 4: 16. Every tag the roadmap cites is either in StacksFrontier only or has no declaration; `StacksCore` has no `AlgebraicGeometry` directory, so nothing here is Core. The most useful review candidates are the 08XA pair in `Descent/Modules/EffectiveDescent.lean` (descent and effective descent for modules iff universally injective), which serve 4.2 once they are related to Mathlib's comonad comparison, and the 03BM block in `Groupoids/FiniteFlatAffine/AffineQuotient.lean` (finite locally free quotient of a finite flat affine equivalence relation, kernel pair), which serves 2.1 together with 0233 (groupoid of an equivalence relation). 0EUA and 08X7 are secondary candidates. The non-flat material (1.2, 1.3, the Raicu examples, the toric theorem, 4.1, 4.3) has no Stacks counterpart and stays in Tau Ceti.

All file paths are relative to the checkout.

| Target (Suggested.lean) | Tag(s) | Status | Stacks declaration (file) | Move | Note |
|---|---|---|---|---|---|
| `IsEquivIdeal.map_quotient` | 02V8 | Frontier | `AlgebraicGeometry.PreRelation.isEquivalenceRelation_restrict` (StacksFrontier/AlgebraicGeometry/GroupScheme/Relations/PreRelations.lean) | 3 | Stacks restricts along any `U' → U` over any base; the target is the ideal form for a closed subscheme, so it still needs `isEquivalenceRelation_iff`. |
| `isEquivalenceRelation_iff` | 022P | Frontier (definition only) | `add_to_stacks 022P` on Mathlib's `IsEquivalenceRelation`; `Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation` (StacksFrontier/AlgebraicGeometry/Spaces/EquivalenceRelations.lean, GroupScheme/Relations/PreRelations.lean) | 4 | The tag is a definition. The ideal ↔ internal equivalence relation step is a Tau Ceti adapter. The Frontier mono + T-points lemma (untagged) is a useful input. |
| `isEquivIdeal_iff_isSpecEquivRel` | — | — | — | 4 | Adapter to Tau Ceti's `RingHom.IsSpecEquivRel`. |
| `isColimit_cofork` | 03BE | not formalized | — (flat analogue: `GroupoidScheme.existsUnique_comp_objectsToInvariantSpectrum_scheme`, StacksFrontier/AlgebraicGeometry/Groupoids/FiniteFlatAffine/InvariantQuotientSchemes.lean, untagged) | 4 | 03BE is a section and only defines `A^R`. The target has no flatness (FGA III); the Frontier categorical quotient assumes finite locally free `s, t`. |
| `isEffectiveEquivalenceRelation_iff` | — | — | — | 4 | Kollár's criterion `I = J_B`. Not in Stacks. |
| `isEffectiveEquivalenceRelation_iff_finrank` | — | — | — | 4 | Dimension criterion. Not in Stacks. |
| `isEffectiveEquivalenceRelation_of_flat` | 03BM (with 0233) | Frontier | `GroupoidScheme.isFiniteLocallyFree_objectsToInvariantSpectrum`, `GroupoidScheme.isPullback_objectsToInvariantSpectrum` (StacksFrontier/AlgebraicGeometry/Groupoids/FiniteFlatAffine/AffineQuotient.lean); `existsUnique_groupoidScheme_of_isEquivalenceRelation` (StacksFrontier/AlgebraicGeometry/GroupScheme/OverField/GroupoidOfEquivalenceRelation.lean) | 3 | Stacks: affine groupoid over any base, `s, t` finite locally free, equivalence relation. The target (finite over a field, one projection flat) is a special case. Still needs the ideal adapter and the symmetry step to get both projections flat. |
| `raicuIdeal_isEquivIdeal` | — | — | — | 4 | Raicu/Kollár example. |
| `raicuIdeal_finite` | — | — | — | 4 | Example. |
| `differenceIdeal_raicuIdeal_ne` | — | — | — | 4 | Example. |
| `not_isEffectiveEquivalenceRelation_raicuArtin` | — | — | — | 4 | Non-flat counterexample. Not in Stacks. |
| `eq_differenceIdeal_of_sq_eq_bot` | — | — | — | 4 | Square-zero case. Not in Stacks. |
| `raicuCocycle_not_mem_differenceIdeal` | — | — | — | 4 | Computation over `𝔽₃`. |
| `eq_differenceIdeal_of_isToric` | — | — | — | 4 | Raicu's theorem 4.1. Not in Stacks. |
| `bijOn_baseChange` | (023G definition only) | — | — | 4 | Mesablishvili's statement for one module. Stacks states only the all-modules version. Frontier `DescentData` (023G) is a different encoding. |
| `isAmitsurEqualizer_iff_bijOn` | — | — | — | 4 | Converse for one module. Not in Stacks. |
| `forall_isAmitsurEqualizer_iff` | 08WE, 08X7, 08WL | 08WE not formalized (section); 08X7, 08WL Frontier | `ModuleCat.tensorPushforward_isEqualizer` (StacksFrontier/AlgebraicGeometry/Descent/Modules/TensorEqualizer/Equalizer.lean); `Algebra.UniversallyInjective` (StacksFrontier/AlgebraicGeometry/Descent/UniversallyInjective/Defs.lean) | 3 | 08X7 gives the hard direction (pure ⇒ equalizer) for Frontier descent data. Specialising it to the canonical datum of `B ⊗ N` needs an adapter. The converse is immediate. |
| `full_faithful_comparison_iff` | 08XA, 08WY | Frontier | `ModuleCat.isDescentMorphismForModules_iff_universallyInjective` (StacksFrontier/AlgebraicGeometry/Descent/Modules/EffectiveDescent.lean) | 3 | Same generality (any ring map). Frontier phrases it as full faithfulness of its own base-extension functor into `DescentData`, not Mathlib's `Comonad.comparison`. Needs an equivalence of the two categories. |
| `nonempty_comonadicLeftAdjoint_iff` | 08XA, 08WY | Frontier | `ModuleCat.isEffectiveDescentMorphismForModules_iff_universallyInjective` (same file) | 3 | As above, phrased as an equivalence of categories onto Frontier descent data, not `ComonadicLeftAdjoint`. |
| `universally_effectiveEpi_iff` | 0EUA | Frontier | `AlgebraicGeometry.quasicoherentSectionsEqualizer_iff_isUniversalEffectiveEpiFamily` (StacksFrontier/AlgebraicGeometry/Descent/EffectiveEpi/QuasicoherentSectionsEqualizer/UniversalEffectiveEpi.lean) | 3 | Families of affine schemes with AxiomMath's own universal effective epi notion, not Mathlib's `MorphismProperty.universally`. Serves as the route step only. |
| `isEffective_invariants` | — | — | — | 4 | Amitsur condition for `A^R → A` for every ideal. Not in Stacks. |
| `nonempty_comonadicLeftAdjoint_invariants` | — | — | — | 4 | Composite of 2.1 and Mathlib's faithfully flat descent. The Frontier 03BM/023M results would supply faithful flatness only. |

## GroupSchemesOverABase against AxiomMath/Stacks (f56a316)

24 sorry'd targets: move 2: 0, move 3: 6, move 4: 18. Nothing is in StacksCore, which has no `AlgebraicGeometry` directory. The Stacks Project treats group schemes in this range only over a field, so every target over a general base stays in Tau Ceti: the identity component over a base, diagonalizable groups, multiplicative type, isotriviality, rigidity and density of torsion. The same holds for Chevalley, affinization, `π₀` and Perrin, which have no Stacks tag in the roadmap or checkout. The useful review candidates are all in `StacksFrontier/AlgebraicGeometry/GroupScheme/OverField(Properties)`. 047L, 047P and 047N match their targets directly. 047R with 047P covers `exists_reduced_subgroup`. 0B7R with 047M covers most of the identity component over a field, but openness in the locally-of-finite-type case is missing. 047T is only the immersion case of `isClosedImmersion_of_mono`.

All file paths are relative to the checkout.

| Target (Suggested.lean) | Tag(s) | Status | Stacks declaration (file) | Move | Note |
|---|---|---|---|---|---|
| `exists_identityComponent` | — | — | (field case: 0B7R, see below) | 4 | Smooth group over an arbitrary base (SGA 3 VI_B). Stacks has the field case only. |
| `bijective_diagonalizableMap` | — | — | — | 4 | `D_S(M)` over a connected base. No tag found. |
| `smooth_diagonalizable_iff` | — | — | — | 4 | No tag found. |
| `etale_diagonalizable_iff` | — | — | — | 4 | No tag found. |
| `flat_surjective_diagonalizableMap` | — | — | — | 4 | No tag found. |
| `isKernel_diagonalizableMap` | — | — | — | 4 | No tag found. |
| `IsMultiplicativeType.exists_etale_cover` | — | — | — | 4 | SGA 3 X. Not in Stacks. |
| `IsMultiplicativeType.isotrivial` | — | — | — | 4 | SGA 3 X. Not in Stacks. |
| `exists_torus_not_isotrivial` | — | — | — | 4 | Counterexample over the nodal curve. |
| `bijective_baseChange_map_of_thickening` | — | — | — | 4 | Rigidity, SGA 3 X. |
| `hom_eq_of_eq_fibre` | — | — | — | 4 | Rigidity, SGA 3 IX. |
| `eq_of_eq_on_torsion` | — | — | — | 4 | Density of torsion. |
| `chevalley` | — | — | — | 4 | Chevalley's structure theorem (Conrad). Nothing found in the checkout. |
| `affinization` | — | — | — | 4 | Demazure–Gabriel. No tag found. |
| `isSeparated_of_field` | 047L | Frontier | `AlgebraicGeometry.isSeparated_of_groupScheme_over_field` (StacksFrontier/AlgebraicGeometry/GroupScheme/OverField/Separated.lean) | 3 | Concludes absolute separatedness of `G.X.left`. Over `Spec k` this is the same as `IsSeparated G.X.hom`, which the proof builds internally. Same generality. |
| `smooth_of_isReduced` | 047P | Frontier | `smooth_of_isReduced_groupScheme_of_perfectField` (StacksFrontier/AlgebraicGeometry/GroupScheme/OverField/SmoothPerfectField.lean) | 3 | Exact match: perfect field, locally of finite type, reduced. Stated with `GrpObj (Over.mk f)` instead of `Grp (Over _)`. |
| `exists_reduced_subgroup` | 047R, 047P | Frontier | `exists_closedSubgroupScheme_reduction` (StacksFrontier/AlgebraicGeometry/GroupScheme/OverFieldProperties/Reduction.lean) + 047P above | 3 | 047R gives `G_red` as a closed subgroup scheme over a perfect field (no finiteness). Smoothness comes from 047P. |
| `smooth_of_charZero` | 047N | Frontier | `smooth_of_groupScheme_of_charZero` (StacksFrontier/AlgebraicGeometry/GroupScheme/OverField/SmoothCharacteristicZero.lean) | 3 | Cartier: char 0, locally of finite type. Same generality. |
| `isClosedImmersion_of_mono` | 047T | Frontier (weaker statement) | `isClosedImmersion_of_isImmersion` (StacksFrontier/AlgebraicGeometry/Groupoids/GroupSchemeProperties/Immersion.lean) | 4 | Stacks/Frontier: an immersion is a closed immersion. The target assumes only a quasi-compact monomorphism (SGA 3 VI_B 1.4.2), which is not in Stacks. 047T is a partial input only. |
| `exists_identityComponent_of_field` | 0B7R, 047M | Frontier | `identityComponent`, `identityComponent_range`, `identityComponent_geometricallyIrreducible`, `identityComponent_compactSpace` (StacksFrontier/AlgebraicGeometry/GroupScheme/OverField/IdentitySubgroup.lean); `existsUnique_irreducibleComponent_containing_identity` (…/OverField/IdentityComponent.lean) | 3 | 0B7R is for any group over a field: a closed flat subgroup on the connected component of `e`, geometrically irreducible and quasi-compact. The target also needs an open immersion when `G` is locally of finite type. No Frontier declaration states that (grep found none). Partial review candidate. |
| `isIrreducible_connectedComponent` | 047M, 0B7Q | Frontier (partial) | `existsUnique_minimalPrime_stalk` (…/OverField/LocalMinimalPrime.lean); `irreducibleSpace_of_connectedSpace` (…/OverField/Irreducible.lean) | 3 | Frontier has unique minimal primes of local rings and the irreducibility of a connected group. Irreducibility of every connected component still needs translation or a local-finiteness step. Partial. |
| `exists_connectedComponentScheme` | — | — | — | 4 | `π₀(X/k)` (Milne). No tag found in the roadmap or checkout. |
| `exists_componentGroup` | — | — | — | 4 | `π₀(G/k)`. No tag found. |
| `exists_isLimit_of_quasiCompact` | — | — | — | 4 | Perrin's approximation. Not in Stacks. |
| `exists_flat_closedImmersion_factorization` | — | — | — | 4 | Perrin, SGA 3 VI_A 6.7. Not in Stacks. |

## ClassifyingTopoi against AxiomMath/Stacks (f56a316)

28 targets: move 2: 0, move 3: 1, move 4: 27. Geometric logic, classifying sites and topoi, presheaf-type theories and the classifying topoi of rings and local rings are not in the Stacks Project, so nearly everything stays in Tau Ceti. The one real review candidate is Tag 00QO (finitely presented algebras are the finitely presentable ones), StacksFrontier `finitePresentation_tfae_colimit_hom` together with the untagged `isFinitelyPresentable_under_tfae` in the same file: with base ring `ℤ` it gives 4.1, after passing from `Under ℤ` to `CommRingCat`. Frontier also has nearby inputs that are not statements of these targets: morphisms of topoi (00XA, 00XC, 04I9), ring objects along a morphism of topoi (00YV, the commutative-ring case of 1.4 only), subtopoi and embeddings (08LV, 08LU, definitions with no topology correspondence), and the standard-cover exactness for rings (00EJ), which is the ring-level step of 4.2.

| Target (Suggested.lean) | Tag(s) | Status | Stacks declaration (file) | Move | Note |
|---|---|---|---|---|---|
| `GeometricFormula.realize_hom` (1.2) | — | — | — | 4 | Geometric logic, not in Stacks. |
| `GeometricFormula.realize_toInf` (1.2) | — | — | — | 4 | Tau Ceti `L_{∞ω}` translation. |
| `CatStructure.isModel_ofStructure_iff` (1.3) | — | — | — | 4 | Categorical semantics in `Type u`. |
| `CatStructure.IsModel.map` (1.4) | — | — | (related: 00YV, `toposAlgebraicStructureAdjunctions`, StacksFrontier/CategoryTheory/Sites/Topos/AlgebraicStructureAdjunctions.lean) | 4 | Arbitrary geometric theory; Stacks has only ring objects (00YV, Frontier), a narrower case, not a review candidate for this target. |
| `exists_morleyization` (1.5) | — | — | — | 4 | Model theory, not in Stacks. |
| `GeometricFormula.exists_interp_eq_iSup_exs` (2.2) | — | — | — | 4 | Normal form of geometric formulas. |
| `exists_isClassifyingSite` (2.3) | — | — | — | 4 | Syntactic site. |
| `IsClassifyingSite.exists_equivalence` (2.4) | — | — | — | 4 | Uniqueness of classifying topos. |
| `IsClassifyingSite.exists_interp_eq_of_subobject` (2.4) | — | — | — | 4 | |
| `IsClassifyingSite.exists_quotient_topology` (2.5) | — | — | (related: 08LV `IsSubtopos`, StacksFrontier/CategoryTheory/Sites/Subtopos/Defs.lean) | 4 | Stacks defines subtopoi but has no subtopos/topology correspondence. |
| `IsClassifyingSite.exists_quotient_theory` (2.5) | — | — | — | 4 | Same. |
| `isOfPresheafType_of_isHorn` (3.1) | — | — | — | 4 | |
| `isClassifyingSite_genericObject` (3.2) | — | — | — | 4 | Object classifier. |
| `isClassifyingSite_genericTorsor` (3.3) | — | — | — | 4 | Stacks has torsors on sites (Cohomology/Torsors) but not their classifying topos. |
| `moritaEquivalent_torsorTheory_iff` (3.3) | — | — | — | 4 | |
| `isClassifyingSite_genericInterval` (3.4) | — | — | — | 4 | |
| `isOfPresheafType_iff_forall_covered` (3.5) | — | — | — | 4 | |
| `exists_isClassifyingSite_fpModel` (3.5) | — | — | — | 4 | |
| `GeometricFormula.isIrreducible_iff_exists_presentedBy` (3.5) | — | — | — | 4 | |
| `exists_isPresentedBy_irreducible_of_isFinitelyPresentable` (3.5) | — | — | — | 4 | |
| `nonempty_equivalence_irreducible_fpModel` (3.5) | — | — | — | 4 | |
| `isIdempotentComplete_irreducible` (3.5) | — | — | — | 4 | |
| `exists_quotient_isSetModel_iff_isHomogeneous` (3.6) | — | — | — | 4 | |
| `isSetModel_iff_isIrreducibleObject` (3.6) | — | — | — | 4 | |
| `finitePresentation_of_isFinitelyPresentable` (4.1) | 00QO | Frontier | `finitePresentation_tfae_colimit_hom` (tagged 00QO); `isFinitelyPresentable_under_tfae` (untagged, ega attrs) (StacksFrontier/Algebra/Category/Ring/FinitePresentation.lean) | 3 | Read: TFAE for `S : Under R`, incl. finite presentation ⇔ `IsFinitelyPresentable.{u}`. Target is the case `R = ℤ` stated in `CommRingCat`; needs the `Under ℤ` ≌ `CommRingCat` transport. Good review candidate. |
| `isClassifyingSite_genericRing` (4.1) | — | — | — | 4 | Classifying topos of rings. |
| `isSheaf_forget_zariskiTopology` (4.2) | (00EJ, input only) | — | (related: 00EJ `alphaLin_injective`, `ker_betaLin_eq_range_alphaLin`, StacksFrontier/RingTheory/Localization/Glueing/Functions.lean) | 4 | Sheaf condition on Tau Ceti's site `FPRing.{u}ᵒᵖ`; not a Stacks statement. 00EJ (Frontier) is the ring-level exactness it reduces to; reviewing 00EJ would help indirectly. |
| `isClassifyingSite_localRingTheory` (4.3) | — | — | — | 4 | Zariski topos classifies local rings. |

## ProjectiveModulesOverPolynomialRings against AxiomMath/Stacks (f56a316)

18 targets: move 2: 0, move 3: 1, move 4: 17. Suslin's `r!` theorem, Serre's stable freeness, Quillen patching, the dilation lemma, Horrocks, Bass and Quillen–Suslin are not in the Stacks Project, and `StacksFrontier/RingTheory/Polynomial/MonicLocalization.lean` (defines `R⟨X⟩`) carries no tags and states neither 4.1 target. The one review candidate is Zariski gluing (3.6): StacksFrontier proves glueing of modules along a finite family of localizations (Tag 00EQ, `ModuleGluingData`, `proj_isLocalizedModule`) and the characterisation of finite projective modules, including locality on a standard cover (Tag 00NX, `Module.finite_projective_tfae`); together they give 3.6 as a special case (two comaximal elements). Nearby but not matching: Kaplansky (0591–0593, no finiteness, local ring; 4.2 is about `A[X]`), stably free modules (0BC3–0BC5), Milnor patching (0D2J, needs a surjection, so it does not cover the Zariski square), unimodular completion over Bézout domains (0ASW; 5.4 is over `k[X₁,…,Xₙ]`, not Bézout in general).

| Target (Suggested.lean) | Tag(s) | Status | Stacks declaration (file) | Move | Note |
|---|---|---|---|---|---|
| `exists_specialLinearGroup_row_pow` (1.1) | — | — | — | 4 | Suslin's `r!` theorem. |
| `isStablyFree_mvPolynomial` (2.1) | — | — | — | 4 | Serre; Stacks has stably free basics (0BC3–0BC5, Frontier) only. |
| `isExtendedFrom_iff_evalZero` (3.1) | — | — | — | 4 | |
| `exists_unit_lift_dilation` (3.2) | — | — | — | 4 | Quillen's dilation lemma. |
| `exists_ideal_isExtendedAfter_away` (3.3) | — | — | — | 4 | Quillen ideal. |
| `isExtendedFrom_of_forall_isMaximal` (3.4) | — | — | — | 4 | Quillen patching. |
| `isExtendedFrom_mvPolynomial_of_forall_isMaximal` (3.5) | — | — | — | 4 | |
| `exists_finite_projective_glue` (3.6) | 00EQ, 00NX | Frontier | `ModuleGluingData`, `psi_apply_of_mem_gluedModule`, `proj_isLocalizedModule` (StacksFrontier/RingTheory/Localization/Glueing/Modules.lean); `Module.finite_projective_tfae` (StacksFrontier/RingTheory/Module/LocallyFree/FiniteProjective.lean) | 3 | Read. 00EQ glues modules over a finite family `f : ι → R` (more general: any modules, any finite family; the file states no unit-ideal hypothesis on the gluing). 00NX gives finite projective from finite free/projective on a standard cover. Target is the two-element, finite projective case, in its own universe; derivable, not stated. Review candidate. |
| `isPrincipalIdealRing_monicLocalization` (4.1) | — | — | (related: `monicSubmonoid`, untagged, StacksFrontier/RingTheory/Polynomial/MonicLocalization.lean) | 4 | Quillen's Lemma 2 not in Stacks. |
| `isField_monicLocalization` (4.1) | — | — | (same file, untagged) | 4 | |
| `free_of_free_monicLocalization_of_isLocalRing` (4.2) | — | — | — | 4 | Local Horrocks. Kaplansky (0593, Frontier) is a different statement. |
| `isExtendedFrom_of_isExtendedFrom_monicLocalization` (4.3) | — | — | — | 4 | Affine Horrocks. |
| `nonempty_linearEquiv_of_monicLocalization` (4.4) | — | — | — | 4 | Bass. |
| `free_of_free_monicLocalization` (4.5) | — | — | — | 4 | Quillen's Horrocks. |
| `exists_mulVec_eq_eval_zero` (5.1) | — | — | — | 4 | |
| `free_mvPolynomial` (5.2) | — | — | — | 4 | Quillen–Suslin absent from Stacks. |
| `isExtendedFrom_mvPolynomial` (5.3) | — | — | — | 4 | Dedekind case. |
| `exists_generalLinearGroup_col_eq_of_isUnimodular` (5.4) | — | — | (related: 0ASW `bezout_unimodular_completion`, StacksFrontier/RingTheory/ElementaryDivisorDomain.lean) | 4 | 0ASW is over a Bézout domain (read); `k[X₁,…,Xₙ]` is Bézout only for `n = 0`, or `n = 1` with `k` a field, so only those cases are covered. Not a review candidate for this target. |

## LefschetzStructures against AxiomMath/Stacks (f56a316)

Summary. 12 sorry'd targets: move 2: 0, move 3: 0, move 4: 12. None of the targets is a Stacks Project statement. They are abstract linear algebra on graded vector spaces with a Lefschetz operator (primitive decomposition, Lefschetz inverse, sl2 triple) and conditional algebraicity results for the standard conjectures; the Stacks chapter on Weil cohomology theories does not treat the Lefschetz operator, and weak and hard Lefschetz are not among the axioms of 0FGV. The only nearby Stacks material is the setting the roadmap imports from MotivesAndAlgebraicCycles: classical Weil cohomology theories (0FGV), the projection formula (0FGT) and Chow motives (0FGA), all StacksFrontier only. A review of those is a matter for MotivesAndAlgebraicCycles, not for a target here. Cayley–Hamilton (00DX) is in StacksCore, as `add_to_stacks 00DX Matrix.aeval_self_charpoly` (Mathlib's lemma), and is an ingredient of Layer 1.3, not a target. No review candidate for this roadmap.

| Target (Suggested.lean) | Tag(s) | Status | Stacks declaration (file) | Move | Note |
|---|---|---|---|---|---|
| `grade_eq_iSup_primitive` | — | — | — | 4 | Primitive decomposition, abstract graded linear algebra. |
| `existsUnique_isLefschetzInverse` | — | — | — | 4 | Lefschetz inverse; not in Stacks. |
| `lambda_pow_L_pow` | — | — | — | 4 | Left inverse of a power of `L`. |
| `L_pow_lambda_pow` | — | — | — | 4 | Right inverse of a power of `L`. |
| `exists_sl2` | — | — | — | 4 | sl2 triple from Lefschetz data; no sl2 material in Stacks. |
| `projectorsAlgebraic_of_inverses` | — | — | — | 4 | Standard-conjecture style conditional result. |
| `lambdaAlgebraic_of_inverses` | — | — | — | 4 | Same. |
| `projectorsAlgebraic_of_lambdaAlgebraic` | — | — | — | 4 | Same. |
| `inv_mem_of_charpoly` | — | — | — | 4 | Uses Cayley–Hamilton; 00DX is Core (`Matrix.aeval_self_charpoly` via `add_to_stacks`, StacksCore/LinearAlgebra/Matrix/Charpoly/Basic.lean), but the target is a different statement. |
| `exists_inverse_L_pow_of_charpoly` | — | — | — | 4 | Graded version of the previous row. |
| `lambdaAlgebraic_of_charpoly` | — | — | — | 4 | Conditional algebraicity of the Lefschetz inverse. |
| `pairingNondegenerate_of_lambdaAlgebraic_of_positive` | — | — | — | 4 | Nondegeneracy on algebraic classes; not in Stacks. |

## PCurvature against AxiomMath/Stacks (f56a316)

Summary. 11 sorry'd targets: move 2: 0, move 3: 0, move 4: 11. Restricted Lie algebras, Jacobson's formula, Hochschild's formula, the p-curvature, Cartier's theorem in rank one, Kronecker's theorem and Honda's theorem are not Stacks Project statements, and no `@[stacks]` attribute in the checkout covers them. Nearby StacksFrontier material, untagged, could supply proofs but not a review claim: `StacksFrontier/RingTheory/DeRham/Cartier/` has `D_pow_char` (d of a p-th power vanishes) and the inverse Cartier map for algebras with Frobenius coordinates. The closest tagged statement, 07PH (`exists_derivation_apply_ne_zero_of_not_pow_fractionRing`, Frontier), is at a different generality (domains of finite type over a complete Noetherian local ring, absolute derivations, p-th powers in the fraction field) from `kaehlerD_eq_zero_iff` (smooth over a base of characteristic p); it does not serve as a review candidate for this target. No review candidate for this roadmap.

| Target (Suggested.lean) | Tag(s) | Status | Stacks declaration (file) | Move | Note |
|---|---|---|---|---|---|
| `add_pow_eq_jacobson` | — | — | — | 4 | Jacobson's formula in an associative algebra. Frontier has only the commutative two-variable polynomial `addPowQuotient` (RingTheory/DeRham/Cartier/Basic.lean), untagged. |
| `iterate_leibniz` | — | — | — | 4 | p-th iterate of a derivation is a derivation. |
| `pPow_smul` | — | — | — | 4 | Hochschild's formula. |
| `ad_pPow` | — | — | — | 4 | `ad` of the p-th power. |
| `pPow_add` | — | — | — | 4 | Jacobson's formula for derivations. |
| `rankOne_pCurvature_eq` | — | — | — | 4 | p-curvature in rank one. |
| `apply_eq_zero_of_mem_frobeniusImage` | — | — | — | 4 | Derivations kill p-th powers; cf. untagged Frontier `D_pow_char` (RingTheory/DeRham/Cartier/Basic.lean), for the universal derivation only. |
| `kaehlerD_eq_zero_iff` | — | — | — | 4 | Kernel of d for smooth algebras in char p. No tag found. 07PH (Frontier, RingTheory/Derivation/Regularity.lean) is a related detection statement at a different generality; not a review candidate. Untagged Frontier Cartier files may help a proof. |
| `exists_unit_horizontal_iff` | — | — | — | 4 | Cartier in rank one, one variable. |
| `exists_intCast_eq_of_forall_pow_sub_mem` | — | — | — | 4 | Kronecker's theorem via Chebotarev; not in Stacks. |
| `honda` | — | — | — | 4 | Honda's theorem over a number field. |

## GrothendieckTeichmuller against AxiomMath/Stacks (f56a316)

Summary. 15 sorry'd targets: move 2: 0, move 3: 0, move 4: 15. The parameter monoid on the profinite integers times the free profinite group of rank two, Drinfeld's relations, the profinite pure braid group and GT̂ are not in the Stacks Project, and grep finds no free profinite groups, braid groups or Grothendieck–Teichmüller material in the checkout. The étale fundamental group via Galois categories (0BNB, Frontier, AlgebraicGeometry/FundamentalGroup/FiniteEtaleGaloisCategory.lean) is the setting of the Galois action but is not a target here. No review candidate for this roadmap.

| Target (Suggested.lean) | Tag(s) | Status | Stacks declaration (file) | Move | Note |
|---|---|---|---|---|---|
| `beta_mul` | — | — | — | 4 | `β` is multiplicative. |
| `beta_one` | — | — | — | 4 | `β` of the unit is the identity. |
| `param_mul_assoc` | — | — | — | 4 | Associativity of the parameter product. |
| `param_one_mul` | — | — | — | 4 | Left unit. |
| `param_mul_one` | — | — | — | 4 | Right unit. |
| `eq_of_beta_eq` | — | — | — | 4 | Parameter determined by its endomorphism. |
| `closure_artin` | — | — | — | 4 | Generators of the pure braid group P4; no braid groups in Stacks. |
| `isGT_one` | — | — | — | 4 | Unit satisfies the GT relations. |
| `IsGT.mul` | — | — | — | 4 | GT relations stable under product. |
| `isUnit_iff_bijective_beta` | — | — | — | 4 | Units of GT̂^mon. |
| `isGT0_iff` | — | — | — | 4 | Drinfeld's form of GT̂₀. |
| `GTHat.isGT0` | — | — | — | 4 | GT̂ inside GT̂₀. |
| `GTHat.injective_mk_betaEquiv` | — | — | — | 4 | Injection into outer automorphisms. |
| `isClosed_setOf_isGT` | — | — | — | 4 | GT̂^mon closed. |
| `GTHat.isClosedEmbedding_betaEquiv` | — | — | — | 4 | GT̂ as a closed subgroup of automorphisms. |

## GrothendieckUniverses against AxiomMath/Stacks (f56a316)

8 targets: move 2: 0, move 3: 0, move 4: 8. The Stacks Project avoids Grothendieck universes and works with partial universes `V_α` instead, so none of the targets is a Stacks statement. The README's tags 000F and 000H are section tags (no declaration carries them; files cite 000H only as a section on size bounds). StacksFrontier/SetTheory has the reflection principle (000G, `reflection_principle`, ZFC/Reflection.lean), cofinality lemmas (05N3 `exists_ordinal_cof_gt`, 05N2 `exists_factorization_of_mk_lt_cof`, Cardinal/Cofinality.lean) and a size bound (046U); none states a target here, and none defines universes or inaccessible stages. No review candidates.

| Target (Suggested.lean) | Tag(s) | Status | Stacks declaration (file) | Move | Note |
|---|---|---|---|---|---|
| `isGrothendieckUniverse_vonNeumann` (1.1) | — | — | — | 4 | `V_κ` for inaccessible `κ` is a universe; not in Stacks. |
| `isGrothendieckUniverse_vonNeumann_omega0` (1.1) | — | — | — | 4 | `V_ω`. |
| `isGrothendieckUniverse_iff` (1.2) | — | — | — | 4 | Williams's classification. |
| `IsGrothendieckUniverse.isInaccessible_card` (1.3) | — | — | — | 4 | |
| `IsGrothendieckUniverse.eq_vonNeumann_card` (1.3) | — | — | — | 4 | |
| `IsGrothendieckUniverse.mem_or_eq_or_mem` (2.1) | — | — | — | 4 | |
| `exists_least_isGrothendieckUniverse` (2.2) | — | — | — | 4 | |
| `forall_exists_isGrothendieckUniverse_iff` (2.3) | — | — | — | 4 | Universe axiom vs inaccessibles; Stacks uses 05N3/000G-style bounds instead, not this. |
