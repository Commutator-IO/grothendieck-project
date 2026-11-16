# Open findings in an area of Stacks, against AxiomMath/Stacks (16 November 2026)

Issue 162, section « Sweep of the open findings in an area of Stacks ». The Findings chart counts 83 open mathematical rows whose `reach` is `beyond` and whose `theory` falls in an area that AxiomMath's Lean Stacks library covers (`inStacks` in `src/components/FindingsChart.tsx`). Each row was checked against [AxiomMath/Stacks](https://github.com/AxiomMath/Stacks) at `c496df0`: the `@[stacks …]`, `@[ega …]` and `@[sga …]` attributes (39,710), and the declarations found by keyword. Every declaration name below was checked to exist in the sources. "Closure" is the number of Stacks modules that the named modules import, transitively (the Mathlib modules are not counted). The method is the one of [`stacks-coverage-2026-11-15.md`](stacks-coverage-2026-11-15.md), which did the same for the Lean files.

Feasibility:

- **done**: Stacks already contains the claim or a direct consequence;
- **medium**: a proof from Stacks results looks feasible in a few hundred lines, closure under about 600 modules;
- **heavy**: feasible in principle, but the closure is large or the glue long;
- **statable**: Stacks and Mathlib state the claim faithfully, but a proof would be new mathematics or far beyond the library;
- **none**: a notion needed to state the claim is missing.

## Summary

| Feasibility | Rows |
|---|---|
| done | 0 |
| medium | 1 |
| heavy | 7 |
| statable | 30 |
| none | 45 |
| total | 83 |

One row becomes provable at a reasonable cost, `49-flatness-lemma-pushforward`: its `reach` is set to `reachable`, and it is added to issue 162. The seven heavy rows are listed in the issue without being scheduled. The 30 statable rows could be stated as `Prop`s in `OpenProblems/` of GrothendieckArchivesProofs.

**What Stacks lacks**, by frequency among the 45 `none` rows: formal and p-divisible groups, Néron models; the dual abelian scheme, Néron–Severi, Albanese, Pic⁰ and polarisations; reductive group schemes (Borels, the Steinberg map); Picard stacks in Deligne's sense, Gr-stacks, 2-gerbes and non-abelian bands; classifying topoi and the 2-category of topoi; Teichmüller groups and tame π₁ of hyperbolic curves; ℓ-adic Verdier duality, ε-constants and weights; integral crystalline cohomology with Frobenius; motives and algebraic equivalence.

**Homonyms.** Stacks' `PicardStack` files are the stack of invertible modules, not Deligne's Picard stacks; its `Neron` files are Néron desingularisation (Popescu), not Néron models; its « Verdier » hits are Verdier quotients, not duality.

## Medium: provable from Stacks in a few hundred lines (1)

### `49-flatness-lemma-pushforward` (folder 49, p. 3)

Declarations: `Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing` (00ME, `StacksFrontier.RingTheory.Flat.LocalCriteria.FibreCriteria`); `IsCoherentRing.tfae_flat_pi` (05CZ, `StacksFrontier.RingTheory.Coherent.Flat`); `isCoherentRing_of_isNoetherianRing` (05CY, `StacksFrontier.RingTheory.Coherent.Basic`).

Closure: 9.

Missing: only geometric glue: stalks of φ_*F, the map G_y → ∏_{x↦y} F_x, and the identification (∏F_x)⊗k(s) = ∏(F_x⊗k(s)) over a noetherian local ring

Lemma 00ME (the lemma the settle field cites as 10.99.1) asks only that the target be flat, not finite. Map G_y into ∏ F_x over the points x above y: that product is flat over O_{S,s} by Chase's theorem (05CZ, noetherian ⇒ coherent), so 00ME gives flatness of G_y. This likely matches the literature (EGA IV 11.3.x style), and the formal proof is a few hundred lines of scheme glue with algebra closure 9. Caveat: it depends on reading 'injective on the fibre at the points above y' as injectivity into the product of fibres.

## Heavy: provable in principle, large closure or long glue (7)

### `101-sheaf-duality-dim-two-fails` (folder 101, p. 10, 14–15)

Declarations: `Dualizing.isIso_matlisEvaluation_of_isArtinian` (08Z9, `StacksFrontier.RingTheory.Dualizing.ResidueFieldHull.Matlis`); `Stacks.Cohomology.SupportedComplexes.derivedSupportedSections` (—, `StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedExcision`); `Stacks.Sites.ExtensionByZero.extensionByZeroHomEquiv` (03DI, `StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroDirectSumSheafification`).

Closure: 329.

Missing: No ready computation of H²_x of a non-quasi-coherent O_X-module on a two-dimensional local scheme, and no comparison of its Matlis dual with completions at height-one primes.

Every notion exists (j_!, cohomology with supports, injective hull and Matlis duality) and the closure is 329. But the non-surjectivity needs an explicit H¹ computation on the punctured spectrum and duals of non-finitely-generated modules. That is well over a few hundred lines, and the edition's sketch is unchecked.

### `126-nilpotent-deformation-quotient` (folder 126, p. 4–7)

Declarations: `Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation` (022P/022Q, `StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations`); `Deformation.ToposThickening.isFinitePresentation_iff_pullbackModules_of_isFlat` (08VU, `StacksFrontier.Deformation.ToposThickening.FinitePresentationFlatLift`); `ModuleCat.DescentData.faithfullyFlatInvariantsEquivalence (namespace as in file)` (023N, `StacksFrontier.AlgebraicGeometry.Descent.Modules.InvariantsInverseFunctor`).

Closure: 426.

Missing: effectivity of a flat equivalence relation as a scheme-level coequaliser with fpqc quotient; Čech H⁰ of ℋ¹ for fpqc covers of an affine; building the thickened quotient Y

Equivalence relations in schemes, flatness across first-order thickenings and faithfully flat descent of modules are all present (closure 426). Constructing Y and checking that it is effective is long glue, though known mathematics of SGA 3 type. The settle field still points first to SGA 3 V–VI_A.

### `126-radicial-etale-factorisation` (folder 126, p. 17–23)

Declarations: `Stacks.Descent.isAffineHom_isLocalAtTarget_fpqc` (02L5, `StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine`); `exists_algEquiv_prod_of_henselianLocalRing` (04GJ, `StacksFrontier.RingTheory.Henselian.FiniteType.Basic.ProductOfLocalRings`).

Closure: 505.

Missing: the étale part π₀(X/Y) of a finite morphism; no Stacks lemma on finite universally open maps with constant geometric fibre cardinality was found

Stating it needs only Mathlib notions (finite, universally open, universally injective, étale). A proof would build X^ét étale-locally from the splitting of finite algebras over henselian rings (04GJ) and descend (02L5), thousands of lines of glue. The row also rests on an uncertain reading of « univ. ouvert », which should be checked first.

### `23-finite-normalisation-quotient-of-regular` (folder 23, p. 86–88)

Declarations: `IsN1` (032F, `StacksFrontier.RingTheory.Nagata.Defs`); `isJapaneseRing_iff_finite_integralClosure_isPurelyInseparable` (032H, `StacksFrontier.RingTheory.Nagata.JapaneseCriteria`); `Dualizing.propertySkModule_canonicalModule` (0AWE, `StacksFrontier.RingTheory.Dualizing.CanonicalModuleDepth`); `AlgebraicGeometry.isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one` (0345, `StacksFrontier.AlgebraicGeometry.Properties.Serre`).

Closure: 521 (0AWE), 551 (0345), 4 (032H); 1000 together.

Missing: S₂-ification as a finite extension (Hom(ω, ω)), dualizing complexes on quotients of regular rings of possibly infinite dimension, and the glue from finitely many height-one primes

The statement is directly expressible. A plausible route is to enlarge A finitely at the bad height-one primes, take the S₂-ification through the canonical module (0AWE), and conclude normality by Serre's criterion (0345), but this needs a closure of about 1000 modules and long glue. The finite-dimension hypothesis for dualizing complexes may force a localisation argument.

### `58-lef-permanence-projective-flat` (folder 58, p. 40–43)

Declarations: `Stacks.Cohomology.FormalFunctions.exists_formalFunctionsEquiv_of_isProper` (02OC (EGA III 4.1.7), `StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ArtinReesChain`).

Closure: 3676.

Missing: No (LG)_n / Lef / Leff conditions and no cohomology of the formal completion X_{/Y} as an object. The comparison step Rf_* commuting with completion for a projective flat W → X, and the perfect-complex dévissage, are not packaged.

This is plausible (Rf_*F is perfect with Tor-amplitude [0, r], hence a complex of locally frees in degrees ≥ 0, so the hypercohomology filtration respects the range i ≤ n), but the proof is the edition's own, the strict case (iii) is unverified, and the formal-functions closure is 3,676 modules.

### `58-local-hom-comparison-depth-off-y` (folder 58, p. 45–51)

Declarations: `Stacks.Algebraization.completionFunctor_map_bijective_of_satisfiesStrictDepthInequalities` (0EJ7, `StacksFrontier.AlgebraicGeometry.Algebraization.StrictDepthFullyFaithful`); `Stacks.Algebraization.SatisfiesStrictDepthInequalities` (0EJ3, `StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities`); `Stacks.LocalCohomology.cohomologicalDimension_span_singleton_le_one` (0DX9, `StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusDimensionCriterion`); `Dualizing.isGorensteinRing_formalFibre_of_isDualizingComplex` (0AWY, `StacksFrontier.RingTheory.Dualizing.GorensteinFormalFibres`); `(dualizing complex of a quotient; 0A7I surjective case)` (0A7I, `StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DerivedCoextensionIsDualizing`); `(formal catenarity, EGA IV 7.1.11)` (0AW6, `StacksFrontier.RingTheory.Catenary.Formal`).

Closure: 4257.

Missing: only glue: show that the strict (1,2)-inequalities of 0EJ3 follow from depth >= 2 at the closed points of X'-Y' when I=(t) and A is a quotient of a regular ring

Stacks 0EJ7 (I=(t), Z=closed point, d=1) asks depth >= 2 exactly at points of U off Y whose closure meets Y only in Z, i.e. the closed points of X'-Y', which is the folder's hypothesis, plus the strict (1,2)-inequalities on the completion. Those can fail only for an associated prime of a completed stalk at a closed point of Y' with 1-dimensional quotient; with CM formal fibres and formal catenarity that comes from an associated point of F of 2-dimensional closure, which forces depth <= 1 at closed points of X'-Y'. So the claim looks true and essentially Stacks' Lemma 52.19.6; this is a sketch to be checked, and the closure is large.

### `91-hom-unramified-rigidification` (folder 91, p. 15–20, 30–31)

Declarations: `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_and_isLocallyOfFinitePresentation` (0D1C, `StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismAlgebraicSpaceUnconditional`); `AlgebraicGeometry.Space.isSeparated_and_isLocallyOfFinitePresentation_relativeHomProjection_unconditional` (0DPN, `StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismSeparatedFinitePresentationUnconditional`).

Closure: 18256.

Missing: No open subfunctor cut out by the unramifiedness of composition with φ, and no tangent / deformation description of Mor_S(X, Y).

Mor_S(X, Y) is an algebraic space, locally of finite presentation (0D1C, 0DPN), so the statement can be made. Unramifiedness would need an infinitesimal criterion for the composition map. That is feasible in principle with an 18k-module closure; two steps on the pages are « admis ».

## Statable, not provable from the library (30)

### `100-formal-abelian-curve-criterion` (folder 100, p. 30–38)

Declarations: `AlgebraicGeometry.IsAbelianScheme` (—, `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint`); `AlgebraicGeometry.Space.isEquivalence_completionFunctorProperOver` (08BE, `StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistenceSpaces`).

Closure: 14324.

Missing: formal abelian schemes as a notion (one can use compatible systems of abelian schemes over R/mⁿ), algebraization of formal polarisations

With IsAbelianScheme over each Spec R/mⁿ, 'algebraizable' can be stated, and Grothendieck existence is present (closure about 14,000). The curve criterion itself is beyond the library and possibly new.

### `100-full-faithfulness-connected-components` (folder 100, p. 2–3, 20)

Declarations: `AlgebraicGeometry.IsAbelianScheme` (no tag, `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint`); `CategoryTheory.GrpObj.torsion` (SGA 3 IX 4.7, `StacksFrontier.AlgebraicGeometry.GroupScheme.Torsion`).

Closure: 710.

Missing: p-divisible groups as objects (only the levels A[p^n] as separate group schemes); rigidity and Tate/de Jong-type full faithfulness over a char-p base

The claim can be stated with abelian schemes and compatible families of homomorphisms A[p^n] -> B[p^n]; the proof (no normality assumed) is research-level and nothing in Stacks approaches it.

### `100-proper-epimorphism-hom-descent` (folder 100, p. 22–24)

Declarations: `AlgebraicGeometry.IsAbelianScheme` (no tag, `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint`).

Closure: 592.

Missing: descent of morphisms into unramified schemes along non-flat proper maps (Rydh-type submersive descent); the representability of Hom of abelian schemes used for the corollary

Proper, O_S → f_*O_S′ injective, formally unramified (Mathlib) and the equaliser diagram are all expressible. The exactness is the open point, and the corollary also needs the Hom scheme of abelian schemes, which Stacks does not construct.

### `102-open-immersion-criterion` (folder 102, p. 12)

Declarations: `AlgebraicGeometry.Space.FormallyEtale` (no tag, `StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs`); `AlgebraicGeometry.Scheme.IsLimitPreserving` (no tag, `StacksFrontier.AlgebraicGeometry.Limits.LimitPreservingFunctorOfPoints`).

Closure: 28.

Missing: commutation with adic limits of artinian rings (effectiveness of formal objects) for functors, and a representability criterion for open subfunctors of arbitrary fpqc sheaves

Formally étale maps of functors and limit preservation exist at small closure, so the claim is statable once 'adic limits of artinian rings' is written out. The criterion is for F not assumed algebraic, beyond Stacks' Artin-axioms chapter. Truth is plausible but unproved.

### `126-generic-descent` (folder 126, p. 26–29)

Declarations: `CategoryTheory.Functor.SieveDescentDatum` (026B, `StacksFrontier.CategoryTheory.Sites.Descent.IsStack.SieveDescentDatum`); `pullback descent data (file)` (02ZD, `StacksFrontier.CategoryTheory.Sites.Descent.PullbackDescentData`).

Closure: 22.

Missing: No descent data defined only on dense opens of T ×_S T, and no generic-extension lemma for fibred categories.

Fibred categories and descent data exist with a small closure, so the statement can be written. The argument is the edition's own reordering of a page the reading calls circular. That makes it new and delicate, with long scheme-topology glue (dense opens, constructible parts).

### `127-closure-flatness-artinian-or-trait` (folder 127, p. 2–4, 15, 19)

Declarations: `Dualizing.isGorensteinRing_formalFibre_of_isDualizingComplex` (0AWY, `StacksFrontier.RingTheory.Dualizing.GorensteinFormalFibres`).

Closure: 1364.

Missing: 'U universally G-dense relative to Y' (EGA IV 11.10.2) as a definition; the valuative criterion of flatness (EGA IV 11.8) is not present (no 'IV 11.8' attribute)

Coherent sheaves, flatness, base change, formal fibres and schematic density are available, so the criterion can be written after defining relative universal density; the proof would need the EGA IV 11.8/11.10 machinery, which Stacks lacks.

### `127-hironaka-reduced-base-openness` (folder 127, p. 7, 9, 10, 12)

Declarations: `IsGRing` (07GH, `StacksFrontier.RingTheory.GRing.Defs`); `isRegularRingHom_tfae_localizations` (07C0, `StacksFrontier.RingTheory.Regular.RegularRingHom`); `Algebra.IsGeometricallyNormal` (—, `StacksFrontier.RingTheory.GeometricallyNormal.Defs`); `AlgebraicGeometry.IsGeometricallyNormal` (—, `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal`).

Closure: 732.

Missing: a packaged 'normal ring map' (flat with geometrically normal fibres) for formal fibres. The rest is in Mathlib: universally open morphisms, finite type, reduced schemes. Equidimensional fibres need an ad hoc formulation.

Every notion can be stated, and the formal-fibre condition can be modelled on the regular version used for G-rings. A proof is Hironaka/Kollár-level flatness theory, far beyond the library.

### `127-non-flat-descent-artinian-epimorphism` (folder 127, p. 2–3)

Missing: no descent theory along non-flat epimorphisms of schemes; the lemma is unproved in the source and its truth is undecided

Epimorphisms of schemes, flat quotients of a given module and universal injectivity can all be expressed with Mathlib and Stacks. Per its settle field the row must first be decided true or false, so a formal proof is not a meaningful target yet.

### `129-ext2-vanishing-p-odd` (folder 129, p. 95)

Declarations: `AlgebraicGeometry.BigFppfSite` (021R/021S, `StacksFrontier.AlgebraicGeometry.Topologies.Fppf`); `CategoryTheory.Abelian.Ext (Mathlib) on abelian fppf sheaves` (—, `Mathlib`).

Closure: 22.

Missing: No sheaf 𝐸𝑥𝑡 on the fppf site, and no finite locally free commutative group schemes as fppf abelian sheaves. These are definable.

It is statable. The general claim is doubtful as unproved: Breen 1975 gives vanishing only in a restricted range and for smooth targets, and Illusie 2023 calls a direct proof out of reach. It would be new mathematics.

### `131-locally-quasi-finite-representability` (folder 131, p. 1–5, 13, 15)

Declarations: `AlgebraicGeometry.Space.isAlgebraicSpace_of_artinAxioms` (07Y1, `StacksFrontier.AlgebraicGeometry.Spaces.ArtinAxiomsAlgebraicSpace`); `AlgebraicGeometry.Space.isRepresentable_of_locallyQuasiFinite_separated` (03XX, `StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable`).

Closure: 8136.

Missing: a bridge from the folder's conditions (effectivity on B^, pro-representability by finite rings, the two modularity conditions) to Artin's axioms, in particular openness of versality

Artin's criterion for algebraic spaces and 'separated locally quasi-finite over a scheme is a scheme' are both in Stacks, so the statement can be written; deriving Artin's axiom [5] from the folder's modularity conditions is the real content and is not in the library.

### `133-affine-quotient-not-constructible` (folder 133, p. 42–43)

Declarations: `AlgebraicGeometry.IsAbelianScheme` (—, `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint`); `AlgebraicGeometry.Scheme.toSpecΓ (Mathlib, affinization)` (—, `Mathlib`).

Closure: 592.

Missing: No largest affine quotient G_aff (Chevalley–Rosenlicht), no anti-affine groups, no extensions of an abelian scheme by 𝔾_a (Ext¹(A, 𝔾_a) ≅ Lie of the dual).

Over a field G_aff can be stated as Spec Γ(G, O_G), and abelian schemes exist, so the example is statable. Proving it needs the vector extension in characteristic 0 and Rosenlicht's theory, which is far beyond the library.

### `136-automorphism-group-scheme` (folder 136, p. 161–179, 189–199)

Closure: 0.

Missing: the simplicial divided-power de Rham algebras 𝒜(S,S⁺,t)_* themselves; a ready-made 'automorphism functor is an affine group scheme' API

Mathlib has simplicial objects, divided-power structures and affine group schemes via Hopf algebras, so the claim could be stated by building the algebras by hand. Stacks' crystalline de Rham files (07LG) concern a different object. The classification is the edition's own computation, and a proof would be new and long.

### `16-weak-variants-imply-strong` (folder 16, p. 49)

Declarations: `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory` (0FGV, `StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheory`).

Closure: 64.

Missing: the Lefschetz operator and restriction to a hyperplane section as named objects; weak and hard Lefschetz, which are not axioms of 0FGV

The axiomatic Weil cohomology gives cycle class maps, Gysin pullback and cup product (closure 64 with Chow groups left abstract), so A⁰, A′⁰ and A″⁰ can be written down as conditions on the cycle-class image. The step A′⁰+A″⁰ ⇒ A⁰ is the open part of the row and would be new work. It probably needs Lefschetz-type input that the axioms do not supply.

### `161-2-definite-characteristic-join-of-subtopoi` (folder 161-2, p. 47–49)

Declarations: `IsSubtopos` (08LV, `StacksFrontier.CategoryTheory.Sites.Subtopos.Defs`); `IsOpenSubtopos` (08LX, `StacksFrontier.CategoryTheory.Sites.Subtopos.IsOpen`); `IsClosedSubtopos` (08LZ, `StacksFrontier.CategoryTheory.Sites.Subtopos.Closed`); `CategoryTheory.Sites.Subtopos.MorphismOfTopoi.isEmbedding_overLocalization_iff_isSubterminal` (08LW, `StacksFrontier.CategoryTheory.Sites.Subtopos.Subtopoi`).

Closure: 11.

Missing: Joins and meets of subtopoi (the lattice), coherent topoi, and the classifying topos of rings with its subtopoi X_{Z/p}, X_Q are absent.

Subtopoi of Sh(C,J), open and closed ones, are there (small closure), and joins can be stated through Mathlib's lattice of Grothendieck topologies. The gluing criterion would need new lattice API; the ring-theoretic example and non-coherence need the classifying topos, which is not in the library.

### `29-h1-five-classes-infinite-group` (folder 29, p. 170–171)

Declarations: `AlgebraicGeometry.IsTorsorFor` (no tag, `StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Torsor`); `AlgebraicGeometry.IsFppfTorsor` (04TY, `StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Torsor`); `AlgebraicGeometry.exists_openCover_finiteLocallyFree_refinement` (05WN, `StacksFrontier.AlgebraicGeometry.Topologies.Fppf.LocallyQuasiFiniteRefinement`).

Closure: 689 (Torsor); 944 with 05WN.

Missing: precoverages for the five classes (finite principal, finite étale principal, quasi-finite) and the comparison theorems; nothing on V̂/V, complete local rings or infinite discrete G

IsTorsorFor takes an arbitrary precoverage J, so each H¹_{C_i} can be stated as torsors of the constant group scheme trivialised by a C_i-family. 05WN (fppf coverings refined by finite locally free ones) is the starting point for C₃ ≃ C₂, but the four comparisons, especially over a Dedekind ring and a complete DVR, are research-level.

### `29-ramification-domain-axioms` (folder 29, p. 190–193)

Declarations: `Stack` (026F (weaker: no effectivity), `StacksFrontier.CategoryTheory.Sites.Descent.IsPrestack`); `AlgebraicGeometry.FiniteEtaleOver` (—, `StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper`); `CategoryTheory.PreGaloisCategory (Mathlib), used with fibre-functor lemmas` (0BN0, `StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctor`).

Closure: 7.

Missing: No multigaloisian category, no stack of such categories over the small étale site with a geometric realisation; the axioms R1–R4 would have to be written out by hand.

Mathlib's PreGaloisCategory (Galois axioms without fibre functor) and Stacks' stacks over a site make a faithful statement possible. The R2 ⟺ faithfulness step looks elementary once the setting exists, but the setting is new definitions. Per 'ours', the page itself proves only faithful ⟹ R2; the converse is the reading's.

### `31-local-ring-cd-lower-bound` (folder 31, p. 22)

Declarations: `AlgebraicGeometry.Scheme.etaleCohomologicalDimension` (0F0Q, `StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension`); `AlgebraicGeometry.Scheme.IsTorsionVanishingBound` (no tag, `StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TorsionVanishingBound`); `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_le_add_trdeg` (0F0T, `StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FieldExtension`).

Closure: 792 (0F0Q); 1412 (IsTorsionVanishingBound); 13988 (0F0T).

Missing: an r-primary cd_r (definable from IsTorsionVanishingBound with n = r); any lower bound for cd: Stacks proves only upper bounds (0F0T, 0F0V, Gabber)

The statement can be written with IsTorsionVanishingBound for n = r and Mathlib's orderable (formally real) fields. Proving it needs non-vanishing of residue maps in Galois cohomology and the real-field exception (SGA 4 X 2.4, Gabber–Orgogozo), none of which is in Stacks.

### `32-pullback-kernel-index` (folder 32, p. 10–11)

Declarations: `AlgebraicGeometry.unit_comp_abelianTrace_eq_nsmul` (03SH, `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.TraceDegree`).

Missing: trace for finite flat (non-étale) multisections and a proper pushforward or Gysin map on étale cohomology with coefficients in complexes

Étale cohomology of complexes and the index of the generic fibre can be stated. Stacks has the trace only for finite étale maps of constant degree (unit ≫ trace = d), which covers separable multisections over an open set. Extending over all of Y and to inseparable degrees needs the missing pushforward.

### `34-lci-local-1-asphericity` (folder 34, p. 153–155)

Declarations: `AlgebraicGeometry.IsSpecializationMap` (no tag, `StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMap`); `AlgebraicGeometry.surjective_specializationMap_of_isProper_of_flat` (0C0P, `StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationSurjective`); `AlgebraicGeometry.exists_continuousMulEquiv_primeToP_of_isProP_ker` (SGA 1 X 3.8 (smooth case), `StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationPrimeToP`); `AlgebraicGeometry.EtaleFundamentalGroup` (no tag, `StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup`).

Closure: 9717.

Missing: local 1-asphericity (vanishing of local prime-to-p H^1 along the singular locus) for lci singularities of codimension >= 2; the prime-to-p specialisation isomorphism is only proved for smooth proper f

For proper f the claim can be stated through specialization maps of pi_1 and surjectivity follows from 0C0P (lci + regular in codim 1 gives normal, hence reduced, fibres); injectivity on prime-to-p quotients is the new content, Stacks has it only for smooth f. Closure is huge.

### `34-multiparameter-tame-monodromy` (folder 34, p. 167, 175–180)

Declarations: `AlgebraicGeometry.EtaleFundamentalGroup` (—, `StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup`); `AlgebraicGeometry.exists_isSpecializationMap_comm_square` (0C0K, `StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapSquare`); `Stacks.Divisors.HasStrictNormalCrossingsEtaleCharts` (—, `StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.ChartStrictHenselization`).

Closure: 1704.

Missing: No prime-to-p quotient π₁^(p′), no outer action of π₁(U) on the fundamental group of a geometric fibre (homotopy exact sequence), no relative normal-crossings boundary.

The ingredients can be defined over EtaleFundamentalGroup, but the theorem is a multi-parameter generalisation of Kisin's result and the hypotheses rest on uncertain readings. It is new mathematics.

### `41-irreducible-components-etale-criterion` (folder 41, p. 3, 8–10)

Declarations: `AlgebraicGeometry.fiber_irreducibleComponentsBaseChangeMap_eq_orbit` (04KY, `StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.GaloisOrbit`).

Closure: 14.

Missing: the functor of geometric irreducible components of the fibres of a morphism, and its representability by an étale (finite) Y-scheme; specialisation of components over traits

Stacks has geometric irreducible components over a field and their Galois orbits (04KY, 04KZ), enough to state the claim fibrewise. The existence criterion is research, and the statement itself needs re-reading against the facsimile per the settle field.

### `45-h1-surjectivity-dim-one` (folder 45, p. 3–10)

Declarations: `AlgebraicGeometry.IsPseudoTorsor` (0498, `StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Torsor`); `Stacks.EtaleCohomology.BrauerScheme.BrauerGroup` (—, `StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AlgebraSheaf`); `Stacks.GaloisCohomology.brauerDeltaEquiv` (—, `StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.BrauerGroupIsomorphism`).

Closure: 699.

Missing: No nonabelian flat H¹ as a pointed set of fppf torsor classes, no maximal tori or Cartan subalgebras of group schemes, no Serre dimension ≤ 1, no Steinberg-type theorems.

Torsors under group schemes over a field and Brauer groups exist, so it is statable with some definitions. The proof (normalisers of tori, radicial kernels) is research-level, and much of the statement is the reading's.

### `47-chow-fourier-todd-over-base` (folder 47, p. 9–10)

Declarations: `Stacks.Chow.chowGroup` (no tag, `StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs`); `AlgebraicGeometry.VectorBundleKZero.existsUnique_ringHom_of_tensorMultiplicative` (0FEM, `StacksFrontier.AlgebraicGeometry.Chow.ChernCharacterKGroup`); `AlgebraicGeometry.IsAbelianScheme` (no tag, `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint`).

Closure: 1099.

Missing: Todd class and Grothendieck-Riemann-Roch (no GRR anywhere, only Riemann-Roch for curves); the Pontryagin product on CH of an abelian scheme

Chow groups, Chern classes, the Chern character on K_0 and abelian schemes exist, so the formulas are writable once Todd and the Pontryagin product are defined; the proof needs GRR, which is far beyond the library.

### `57-generic-hyperplane-h1-injective` (folder 57, p. 98–99)

Declarations: `AlgebraicGeometry.pointsPresheaf` (no tag, `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint`).

Closure: 592.

Missing: Pic^tau of a general projective X (Picard schemes are present only for curves); a ready notion of the generic hyperplane section

H^1(X,G_a) is coherent cohomology and fppf H^1 with coefficients in finite commutative group schemes is available on the big fppf site, so the main statement is writable; the Pic^tau corollary is not. As the settle field says, injectivity of H^1(X,O) -> H^1(Y,O) should be tested against characteristic-p failures of Kodaira vanishing before any formalisation.

### `57-rigid-subgroups-one-fibre` (folder 57, p. 42–49)

Declarations: `AlgebraicGeometry.ClosedSubgroupScheme` (no tag, `StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs`).

Closure: 4.

Missing: the 'rigid' notion (geometric fibres the schematic closure of prime-to-p torsion) and any rigidity theorem: no groups of multiplicative type, no SGA 3 IX–X rigidity

With closed subgroup schemes, flatness, fibres and scheme-theoretic image, the notion and the claim can be written down. The unified proof is the open question of the row and is far beyond the library, which lacks even the multiplicative-type special case.

### `91-centraliser-condition-R` (folder 91, p. 4–9)

Declarations: `AlgebraicGeometry.ClosedSubgroupScheme` (no tag, `StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs`); `AlgebraicGeometry.OpenSubgroupScheme` (no tag, `StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs`).

Closure: 4.

Missing: centraliser, transporter and normaliser functors of group schemes and their representability (SGA 3 VI_B 6); no Raynaud–Gruson-style flatness results for this

Condition (R) (open subgroups containing the special fibre) and the functors are definable from Mathlib group objects in Over S and OpenSubgroupScheme. The connected-fibre case is already matched in SGA 3, but none of it is in Stacks, so the open case is research.

### `91-res-representable-by-scheme` (folder 91, p. 24–28, 31)

Declarations: `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom` (0D1C, `StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismAlgebraicSpace`); `CategoryTheory.Presheaf.depProdObj` (no tag, `StacksFrontier.CategoryTheory.DependentProduct`); `AlgebraicGeometry.Space.isRepresentable_of_locallyQuasiFinite_separated` (03XX, `StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable`).

Closure: 18255.

Missing: scheme-valued (not algebraic-space) representability criteria for Res_{X/S}(P) under conditions (a)-(c), normal flatness along Z_i

Hom_S(X,Y) is an algebraic space in Stacks (0D1C) and the Weil restriction exists as a presheaf, so the claim can be stated; the passage to a scheme under the folder's conditions is new and the closure is enormous.

### `91-weil-restriction-finite-etale-criterion` (folder 91, p. 53, 55–58)

Declarations: `CategoryTheory.Presheaf.depProd` (— (sga 3 III 0.1.1), `StacksFrontier.CategoryTheory.DependentProduct`).

Closure: 2.

Missing: representability of the Weil restriction of schemes along a finite locally free morphism (there is only the presheaf dependent product and the closed-subscheme case of 07AI), and the count ν(s) of geometric points as a function

Res_{T/S} can be stated as the presheaf dependent product, with 'is finite étale' read as representable by a finite étale scheme; Mathlib supplies finite and étale morphisms. Proving the equivalence needs representability theory that the library does not have, so this is beyond the library even if it is classical (CGP A.5, BLR 7.6).

### `94-representability-criterion` (folder 94, p. 15–16)

Closure: 0.

Missing: nothing essential for stating it: Mathlib has module categories, filtered colimits, adic completion, systems of parameters and finite modules; the 'generic commutation with reduction modulo systems of parameters' must be formulated by hand

The criterion can be stated over Mathlib alone, and Stacks adds nothing specific (no coherent-functor theory). A proof is research-level. The settle field also asks whether the conditions already imply preservation of products, which would make the 'no products' claim weaker than it looks.

### `FG_IL_5_SGA7_4-depth-local-acyclicity` (folder FG_IL_5_SGA7_4, p. 28 (with 21–27 for 5.1–5.7 a))

Declarations: `AlgebraicGeometry.IsLocallyAcyclicAt` (0GJP, `StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.Basic`); `AlgebraicGeometry.EtaleFundamentalGroup` (—, `StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup`).

Closure: 1337.

Missing: No truncated ('locally n-acyclic') variant, no 1-asphericity of Milnor fibres, no geometric depth.

The vanishing-cycles fibre map of 0GJP lets one define n-acyclicity by truncation, so the conjecture is statable. It is open per the row's own search, hence new mathematics.

## Not statable: a notion is missing (45)

### `100-neron-extension-p-divisible` (folder 100, p. 47–52)

Missing: p-divisible (Barsotti–Tate) groups, Néron models and the Néron mapping property, and Tate's full-faithfulness theorem.

None of them is in Stacks.

### `103-gr-stacks-relative-cohomology-BG` (folder 103, p. 14–15)

Missing: Gr-stacks and their pinnings, 2-gerbes, the classifying topos B_G with relative cohomology, and the strict Picard 2-category.

Nothing in Stacks to state it with.

### `119-foliation-quotient-topos-equivalence` (folder 119, p. 144–145)

Closure: 0.

Missing: local equivalence relations on spaces, étendues / 'multiplicités topologiques' as a 2-category, locally connected and locally open geometric morphisms

Neither library has a 2-category of topoi with these morphism classes. The coverage review of 2026-11-15 noted the same gap for 161-3.

### `12-immersion-level-bound` (folder 12, p. 115, 117, 119)

Declarations: `AlgebraicGeometry.SmallEtale.LAdicSheaf` (—, `StacksFrontier.AlgebraicGeometry.Topologies.Etale.LAdicSheaves`); `Stacks.EtaleCohomology.IsMixedOfWeightLE` (—, `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusWeights`).

Closure: 55.

Missing: No level (niveau) of ℓ-adic or Hodge constituents, no mixedness of R^i f_* ℚ_ℓ (Weil II) for an immersion, no regularity-based purity.

There are ℓ-adic sheaves and Frobenius weights of endomorphisms, so weight bounds could be phrased pointwise, but the level, which is the content of the bound, cannot be stated.

### `123-grothendieck-springer-pic-twisted-torus` (folder 123, p. 10–12)

Closure: 0.

Missing: reductive group schemes, the scheme of Borel subgroups, the abstract maximal torus, the Grothendieck-Springer resolution

No reductive group or Borel subgroup notion anywhere in Stacks (grep 'reductive', 'Borel' finds nothing relevant).

### `123-kostant-rigidifications-count` (folder 123, p. 21, 28, 30, 34)

Missing: reductive and simple adjoint group schemes, maximal tori, Borel subgroups, Coxeter number, Kostant's tori in apposition

Stacks has no reductive groups (no match for Reductive, MaximalTorus, Coxeter outside the EGA/SGA index). The count |N(T) ∩ N(T′)| = h·z·φ(h) is itself unproved per the row.

### `123-steinberg-no-resolution-picard` (folder 123, p. 10–13)

Missing: Reductive group schemes over a base, maximal tori, the Weyl group, T/W, the Steinberg map, the regular locus and the Grothendieck–Springer resolution.

None of these is in Stacks.

### `130-neron-symbol-component-correction` (folder 130, p. 3–5)

Missing: Néron models of abelian varieties, component groups, Néron's local symbol. The 'Neron' files are Néron desingularisation (smoothing).

There is nothing to state it with.

### `130-quasi-function-sheaf` (folder 130, p. 39–48)

Closure: 0.

Missing: M_K absolute values on a field, Weil (admissible) functions, M_K-units

Nothing on Weil functions or Diophantine height machinery; Cartier divisors exist but the sheaves Phi_X, QF_X do not.

### `134-1-picard-sign-sequence` (folder 134-1, p. 3–5)

Declarations: `CategoryTheory.Gerbe.nonempty_fiber_of_cohomology_vanishing` (0CK0, `StacksFrontier.CategoryTheory.Sites.Gerbe.ExistenceOfAnObject`).

Closure: 51.

Missing: Picard stacks in Deligne's sense (stacks of symmetric monoidal groupoids, strict or not), their classification by τ≤2 RHom, the symmetry invariant

Stacks' 'PicardStack' files are the stack of invertible modules, not Deligne's Picard stacks. Gerbes and banded gerbes with their H² link exist (closure 51), but the sheaf P(M,N) and the triangle cannot be stated.

### `134-1-sign-realisation-universal-argument` (folder 134-1, p. 5)

Missing: Picard stacks in Deligne's sense (stacks of strictly commutative Picard categories) and their classification by Ext of complexes are absent. The 'PicardStack' files are the stack of line bundles, which is a different object.

There is nothing to state the symmetry invariant or the obstruction in Ext³(X; M, N) with.

### `14-albanese-equivalence-ring` (folder 14, p. 23–29, 33)

Declarations: `Stacks.Chow.chowGroup` (no tag, `StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs`).

Closure: 16.

Missing: the Albanese variety/map alb_T, algebraic equivalence of cycles, correspondences Z_* on X x T

Chow groups modulo rational equivalence exist, but neither algebraic equivalence nor any Albanese construction does, so the new equivalence cannot be defined.

### `142-teichmuller-galois-category-etale` (folder 142, p. 2–16)

Missing: anabelian curves of type (g, ν), isotopy classes of maps, profinite Teichmüller groups, profinite completion of categories under condition (*)

Stacks has Galois categories and fundamental groups, but nothing on mapping class groups or Teichmüller towers.

### `147-m11-stratified-class-over-z` (folder 147, p. 62–64)

Declarations: `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.ModuliStackIsAlgebraic` (072R, `StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesAlgebraic`).

Closure: 5.

Missing: coarse moduli spaces, the Grothendieck ring of varieties or of stacks, stratification by automorphism group, compactified M̄_{1,1}

M_{1,1} exists as an algebraic stack, but nothing in Stacks defines the invariant, so the claimed class cannot be stated. The settle field asks first whether the invariant itself is in print.

### `149-cusp-specialisation-index` (folder 149, p. 72–77, 84–93)

Missing: Relative hyperbolic curves and cusps, the tame fundamental group of a punctured neighbourhood, cuspidal loop subgroups, decomposition groups of sections.

EtaleFundamentalGroup exists, but not the tame or cuspidal structure the claim needs.

### `15-brandt-picard-category` (folder 15, p. 71–77)

Missing: strict Picard categories, torsor-categories under a Picard category, the 2-group of autoequivalences, orders in semisimple algebras over a Dedekind ring

Stacks has a Picard stack of line bundles (Quot/PicardStack*), but not Picard categories in Deligne's sense or invertible bimodules over orders. Mathlib's symmetric monoidal categories would be the starting point, not Stacks.

### `161-2-field-classifier-absolutely-flat-site` (folder 161-2, p. 41–42, 92–95)

Declarations: `IsAbsolutelyFlat` (092B, `StacksFrontier.RingTheory.AbsolutelyFlat.Basic`); `IsAbsolutelyFlat.absolutelyFlat_tfae (stated as absolutelyFlat_tfae in that file)` (092F, `StacksFrontier.RingTheory.AbsolutelyFlat.Basic`).

Closure: 128.

Missing: classifying toposes: geometric theories, models of a theory in a topos, field objects in a topos, Diaconescu's theorem

Stacks has absolutely flat rings and their characterisations, and Mathlib has sheaves on a site, but nothing says what it means for a topos to classify fields. The site-theoretic part can be stated; the classification cannot.

### `161-2-irreducible-and-zero-dimensional-not-coherent` (folder 161-2, p. 39, 41–42)

Closure: 0.

Missing: geometric theories and their classifying topoi; coherent topoi; points of a topos in this sense

No classifying topos, coherent topos or geometric logic in Stacks (grep finds none); only the ring-theoretic side (irreducible spectrum, zero-dimensional rings) is available through Mathlib.

### `162-5-de-rham-hochschild-flat-formal-category` (folder 162-5, p. 27–30)

Declarations: `Crystalline.GlobalCrystallineSituation.SmallSite.crystalPairDeRhamDerivedPlusIso` (07LG, `StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamDerived07LG`).

Closure: 3400.

Missing: formal categories (formal groupoids) over X₀ with flat, not necessarily finite, conormal Ω; descent data relative to them; their Hochschild complex

The closest result is 07LG, crystalline cohomology of a crystal computed by the de Rham complex through the Čech–Alexander cosimplicial module. It is the special case of the PD-envelope of a diagonal, not a general formal category, so the claim cannot be stated.

### `162-5-formal-categories-flat-conormal-de-rham` (folder 162-5, p. 21–26)

Closure: 0.

Missing: formal categories/groupoids (complete augmented pro-rings with counital coassociative comultiplication, i.e. formal bialgebroids) and the functor to (Lambda^.Omega, delta)

Stacks has de Rham complexes and DG algebras but no formal groupoid, Hopf/bialgebroid or Lie algebroid notion (grep empty); the equivalence is out of reach of statement.

### `18-archimedean-lattice-cocycle` (folder 18, p. 46–61)

Closure: 0.

Missing: motives, Betti realisation at a complex place, adelic comparison, the motivic Galois group G

No motives or Betti/adelic realisations in Stacks.

### `27-semicontinuity-proof` (folder 27, p. 27–36)

Declarations: `AlgebraicGeometry.IsAbelianScheme` (no tag, `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint`).

Closure: 592.

Missing: Chevalley decomposition of fibres, unipotent/reductive/semisimple rank, affine part of a group scheme over a field

Group schemes over a base and abelian varieties/schemes exist, but none of the structure theory defining the ranks (no 'reductive', 'maximal torus', 'semisimple rank' anywhere).

### `29-domram-morphisms-fully-faithful` (folder 29, p. 197)

Declarations: `Stacks.FundamentalGroup.isGaloisCategory_finiteEtaleFiberFunctor` (0BNB, `StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleGaloisCategory`).

Closure: 116.

Missing: the notion of a ramification domain (pair (R,r) built from a Galois category and a G-scheme Z) and the 2-category of such over S

Stacks (and Mathlib's GaloisCategory) supply Galois categories and the finite etale one, but nothing like ramification domains or their 2-category; the rigidity claim cannot even be written.

### `2ILL5-p8-full-faithfulness-conjecture` (folder 2ILL5, p. 8)

Closure: 0.

Missing: motives over X, de Rham-crystalline coefficients with Frobenius

A conjecture about motives; Stacks has neither motives nor such coefficient categories, and a conjecture would not be proved anyway.

### `36-griffiths-conditional-l-adic` (folder 36, p. 9–16)

Missing: Algebraic equivalence, Griffiths groups, Lefschetz pencils, coniveau, ℓ-adic cycle class maps on Chow groups.

Stacks has Chow groups and a Weil-cohomology framework, but none of the notions the claim turns on.

### `36-h1-invariant-cycle-defect` (folder 36, p. 60–70)

Missing: the Néron–Severi group of the special fibre (no Pic⁰ or NS), the inertia action on H¹ of the geometric generic fibre over a strictly henselian trait

Étale cohomology, μ_n and Kummer classes exist (EtaleCohomology/Duality/*Kummer*), but w : Γ → NS(X₀) has no target, so the exact sequence cannot be stated.

### `36-orthogonality-regular-adic-base` (folder 36, p. 73–76)

Declarations: `Stacks.Groupoids.tateModule` (—, `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TateModule`); `AlgebraicGeometry.IsAbelianScheme` (—, `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint`).

Closure: 10809.

Missing: the Weil pairing attached to a divisorial correspondence, toric and finite parts of flat group schemes over a base, Tate modules over a base (SGA 7 IX setting)

Tate modules of abelian varieties over a field exist, but none of the SGA 7 IX pairing machinery does. The question is also bibliographic: what does SGA 7 IX already state?

### `4-vanishing-unit-root-bound` (folder 4, p. 1, 4–7)

Declarations: `Crystalline.FCrystal` (07N3 (small-site version), `StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal`).

Closure: 113.

Missing: crystalline cohomology over W(k) as a finitely generated W-module with Frobenius, its torsion, vanishing cohomology, F-semisimple ranks, weak Lefschetz

Stacks has the crystalline site, crystals and F-crystals, but no finiteness or integral W(k)-cohomology with Frobenius slopes, so the exact sequence cannot be stated.

### `43-local-cohomology-concentration` (folder 43, p. 70–74)

Declarations: `ClosedImmersionSheaves.supportedSectionsOnClosed_injective` (0A3A, `StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.InjectiveSupportedSections`).

Closure: 16.

Missing: the unipotent part of a commutative algebraic group (Chevalley/Rosenlicht structure theory), the Zariski sheaf of points of G with its local cohomology at a point, the local Jacobian

Sections with support and cohomology with supports on spaces exist in pieces. The d = 1 case and the vanishing could be stated with effort. The d ≥ 2 formula needs U, and Stacks has no notion of unipotent group.

### `45-bands-tsen-field` (folder 45, p. 10–14)

Declarations: `IsCField` (03R9, `StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFields`); `brauerGroup_eq_one_of_isCField` (03RC, `StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.BrauerGroupCField`); `CategoryTheory.Functor.IsGerbe` (no tag, `StacksFrontier.CategoryTheory.Sites.Gerbe.Defs`); `CategoryTheory.Gerbe.nonempty_fiber_of_cohomology_vanishing` (0CK0, `StacksFrontier.CategoryTheory.Sites.Gerbe.ExistenceOfAnObject`).

Closure: 89.

Missing: non-abelian bands (liens) and Giraud's H^2(k,L) with its neutral classes; algebraic bands on the fppf site

Gerbes, abelian bandings (0CJY) and C_1 fields are present, but only the abelian-band H^2 is available; Giraud's non-abelian theory is missing.

### `47-dual-polarisation-divisibility` (folder 47, p. 7–8)

Missing: Néron–Severi group, the dual abelian variety and Poincaré bundle, the Fourier–Mukai transform Φ_L on abelian varieties, Chern classes in NS

The Fourier–Mukai files of Stacks concern derived categories of varieties in general, not abelian varieties. The integrality is also only proposed in the folder, not established.

### `51-albanese-good-reduction-codim-two` (folder 51, p. 16–17, 20)

Declarations: `AlgebraicGeometry.IsAbelianScheme` (—, `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint`); `AlgebraicGeometry.IsAbelianVariety` (03RO, `StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety`); `AlgebraicGeometry.Space.isAlgebraicSpaceOver_picardFunctor` (0D2C, `StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorIsAlgebraicSpace`).

Closure: 18099.

Missing: Albanese variety, Pic⁰ and its reduction as an abelian variety, good reduction of an abelian variety (extension to an abelian scheme), the Koizumi–Shimura theorem

Stacks has abelian varieties, the predicate of being an abelian scheme, and the Picard functor as an algebraic space (closure about 18,000). It has neither Albanese nor Pic⁰. The settle question is bibliographic in any case: do Koizumi's hypotheses already allow a special fibre singular in codimension 2?

### `59-determinant-canonical-section` (folder 59, p. 1–5, 16–19, 22)

Missing: Néron–Severi, Albanese torsors Alb^n_{X/S}, the dual abelian scheme and Poincaré sheaf, and the determinant of cohomology in families.

Picard functors of curves and a determinant functor on two-term complexes exist (StacksFrontier/Homology/TwoTermComplex/DeterminantFunctor.lean), but nothing to state the torsor identity with.

### `59-surface-even-chi-torsor` (folder 59, p. 11–13)

Declarations: `AlgebraicGeometry.IsAbelianScheme` (—, `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint`).

Closure: 592.

Missing: the dual abelian scheme, the Néron–Severi sheaf NS_{A/S}, Pic^δ as a torsor, χ of a class, the Poonen–Stoll class

Only the abelian-scheme predicate and torsor/H¹ results exist. The row's own fields treat the claim as unverified and propose a counterexample search (type (1,2) with c_λ ≠ 0), so it should be treated as doubtful until a person checks the argument.

### `6-formal-group-not-in-abelian-variety` (folder 6, p. 49–50)

Missing: formal groups and p-divisible groups of abelian varieties, supersingular elliptic curves and their endomorphism algebras, twisting of formal groups, the Weil conjectures for abelian varieties

Stacks has abelian varieties with ℓ-adic Tate modules (AbelianVariety/*) but no formal group of an abelian variety. Without one, embedding a formal group into an abelian variety cannot be stated.

### `6-ordinary-moduli-complete-intersection` (folder 6, p. 52–56)

Closure: 0.

Missing: moduli scheme of polarised abelian varieties with level structure, ordinary locus, Serre-Tate local moduli, p-divisible groups

Stacks has abelian varieties/schemes but no polarisations, no moduli A_{g,d,n}, no p-divisible groups (grep 'p-divisible' empty).

### `6-same-formal-group-not-isogenous` (folder 6, p. 47–48)

Declarations: `AlgebraicGeometry.IsAbelianVariety` (03RO, `StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety`).

Closure: 4.

Missing: the formal group of an abelian variety, isogenies between abelian surfaces as a relation, Manin's family / moduli of abelian surfaces

Abelian varieties over a field exist, but their formal groups do not. The settle field already suspects a match: isogeny classes are countable while the p-rank-one locus of A_2 is positive-dimensional.

### `60-inertia-average-duality` (folder 60, p. 38–58)

Declarations: `Stacks.EtaleCohomology.LAdicSheaf.rationalLFunction` (03UX, `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionRationalSheaf`).

Closure: 1966.

Missing: No inertia-invariant fibres at ramified points, no virtual sheaves, no Verdier duality for ℓ-adic sheaves on curves, no global ε-constant δ.

L-functions of ℚ_ℓ-sheaves exist, so only the additivity part could be phrased. The duality formula and the question about δ cannot be stated. Per 'ours' the reading shows μ_x = 0, which answers the page's question.

### `64-legendre-pinning-moduli` (folder 64, p. 74–79, 84–91)

Declarations: `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.IsElliptic` (072J, `StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurves`); `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.ModuliStackIsAlgebraic` (072R, `StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesAlgebraic`).

Closure: 5.

Missing: the relative group law on an elliptic curve, its 2-torsion subscheme and level-2 structures, the quotient E/±1, the μ₄-twisted tangent pinning

Stacks defines elliptic curves over a scheme as pointed genus-one families and proves that M_{1,1} is algebraic (closure 5). Without the group law, the ordered 2-torsion cannot be stated.

### `77-arf-cover-stein-factorisation` (folder 77, p. 132–143, 155–157)

Closure: 0.

Missing: regular quadratic modules over a scheme, isotropic flag schemes, orthogonal group schemes, Stein factorisation as a construction, the Arf/Dickson invariant

No quadric or orthogonal-group theory over a base was found. Grep hits for 'isotropic' and 'Arf' are incidental. The settle field points first to SGA 7 II XII and Knus.

### `8-dim-one-A-module-homs` (folder 8, p. 39–41)

Closure: 0.

Missing: Barsotti–Tate (p-divisible) groups, formal groups and formal A-modules, Dieudonné-type invariants

There is nothing on p-divisible or formal groups in either library: grep for BarsottiTate, PDivisible and FormalGroup finds only an SGA 3 index entry. The row also waits on a person reading a stained sign in the facsimile.

### `8-lubin-tate-via-hodge-filtration` (folder 8, p. 43–49)

Missing: formal groups, p-divisible groups, Lubin–Tate groups, Grothendieck–Messing crystalline deformation theory, Hodge filtration of the Dieudonné crystal

Stacks has divided powers and the crystalline site, but no formal or p-divisible groups (no file matches LubinTate, BarsottiTate or pDivisible).

### `9-det-etale-tate-iso` (folder 9, p. 22–28)

Declarations: `Stacks.Groupoids.tateModule` (SGA 1 XI 2.1 / SGA 7 I 6.1 (partial), `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TateModule`).

Closure: 10809.

Missing: dual abelian scheme, polarisations and their degree, ordinarity, the etale part of T_p over a base (p-divisible groups)

Only the l-adic Tate module of rational points over a field is defined; nothing over a base, no duality.

### `9-symmetric-positive-det-sqrt-degree` (folder 9, p. 24, 26)

Declarations: `Stacks.Groupoids.IsAbelianVariety` (no tag, `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety`); `Stacks.Groupoids.tateModule` (no tag, `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TateModule`).

Closure: 4 (IsAbelianVariety); 10809 (TateModule).

Missing: dual abelian variety, polarisations, the Rosati involution, ordinarity and the étale part of the p-divisible group

Abelian varieties and Tate modules of rational points exist. For p equal to the characteristic, tateModule over k̄ would give the étale part of T_p, but 'symmetric and positive for Rosati' has no meaning without a polarisation.

### `FG_IL_2_GIRAUD69-total-obstruction-relative-classifying-topos` (folder FG_IL_2_GIRAUD69, p. 4–6, 8)

Missing: the classifying topos B_G of a group scheme and its relative cohomology mod B; Lie algebra of a group scheme as a coefficient; deformation theory of group schemes (Illusie CC II VII)

Stacks has cotangent complexes and deformation of schemes and modules, but no classifying topoi or obstruction theory for group schemes. Per its settle field the row is likely answered in print by Illusie, so the check is bibliographic, not formal.
