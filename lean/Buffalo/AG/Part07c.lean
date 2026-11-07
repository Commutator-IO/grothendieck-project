import Mathlib

/-!
# Buffalo, algebraic geometry, part 07 (c): 3 July 1973

The entries of `docs/buffalo-ag/index.tex` lines 996–1053 (video `Oqhr-Gt66es`, 8:31:46–10:34:12):
finite, proper and quasi-affine morphisms, ample sheaves, radicial morphisms, open and
generalizing morphisms, flat and faithfully flat modules.

Conventions. Quasi-affine schemes are mathlib's `Scheme.IsQuasiAffine`; quasi-affine morphisms
(`IsQuasiAffineHom`) are defined here by quasi-affine preimages of affine open sets. Radicial means
universally injective (`UniversallyInjective`). Ample sheaves are not in mathlib.
-/

open TensorProduct Polynomial AlgebraicGeometry CategoryTheory Limits PrimeSpectrum Topology

universe u

namespace Buffalo.AG.Part07

noncomputable section

section Schemes

variable {X Y Z : Scheme.{u}}

/-- Oqhr-Gt66es-30706 (8:31:46) [prop] Finite = integral and of finite type; integral = affine
and universally closed. -/
theorem prop_30706 (f : X ⟶ Y) :
    (IsFinite f ↔ IsIntegralHom f ∧ LocallyOfFiniteType f) ∧
    (IsIntegralHom f ↔ UniversallyClosed f ∧ IsAffineHom f) :=
  ⟨IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f,
    IsIntegralHom.iff_universallyClosed_and_isAffineHom⟩

/-- Oqhr-Gt66es-31028 (8:37:08) [prop] A morphism is finite iff it is proper with finite fibres. -/
theorem prop_31028 (f : X ⟶ Y) : IsFinite f ↔ IsProper f ∧ ∀ y, (f ⁻¹' {y}).Finite := by
  rw [IsFinite.iff_isProper_and_locallyQuasiFinite]
  refine and_congr_right fun _ => locallyQuasiFinite_iff_finite_preimage_singleton

/-- Oqhr-Gt66es-33740 (9:22:20) [def] `f : X → Y` is quasi-affine if the preimage of every affine
open set of `Y` is a quasi-affine scheme. -/
def IsQuasiAffineHom (f : X ⟶ Y) : Prop :=
  ∀ U : Y.affineOpens, (f ⁻¹ᵁ U.1).toScheme.IsQuasiAffine

/-- Oqhr-Gt66es-33935 (9:25:35) [prop] (one direction) A quasi-compact immersion is quasi-affine. -/
theorem prop_33935 (f : X ⟶ Y) [IsImmersion f] [QuasiCompact f] : IsQuasiAffineHom f := by
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : CompactSpace (f ⁻¹ᵁ U.1) := by
    have := (QuasiCompact.isCompact_preimage (f := f) U.1.1 U.1.2 U.2.isCompact)
    exact isCompact_iff_compactSpace.1 this
  exact Scheme.IsQuasiAffine.of_isImmersion (f ∣_ U.1)

/-- Oqhr-Gt66es-34060 (9:27:40) [prop] A separated morphism of finite type with finite fibres is
quasi-affine (by Zariski's Main Theorem: over an affine open, `X` is an open subscheme of the affine
scheme of its normalization). -/
theorem prop_34060 (f : X ⟶ Y) [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    (hf : ∀ y, (f ⁻¹' {y}).Finite) : IsQuasiAffineHom f := by
  have : LocallyQuasiFinite f := (locallyQuasiFinite_iff_finite_preimage_singleton).2 hf
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : CompactSpace (f ⁻¹ᵁ U.1) := by
    have := (QuasiCompact.isCompact_preimage (f := f) U.1.1 U.1.2 U.2.isCompact)
    exact isCompact_iff_compactSpace.1 this
  set g := f ∣_ U.1
  have : IsAffine g.normalization := isAffine_of_isAffineHom g.fromNormalization
  exact Scheme.IsQuasiAffine.of_isImmersion g.toNormalization

/-- Oqhr-Gt66es-34132 (9:28:52) [prop] (integral form) Zariski's Main Theorem: a separated
quasi-finite morphism of finite type factors as a quasi-compact open immersion `X → X'` followed by
an integral morphism `X' → Y` (its relative normalization). -/
theorem prop_34132 (f : X ⟶ Y) [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    (hf : ∀ y, (f ⁻¹' {y}).Finite) :
    IsOpenImmersion f.toNormalization ∧ QuasiCompact f.toNormalization ∧
      IsIntegralHom f.fromNormalization ∧ f.toNormalization ≫ f.fromNormalization = f := by
  have : LocallyQuasiFinite f := (locallyQuasiFinite_iff_finite_preimage_singleton).2 hf
  exact ⟨inferInstance, inferInstance, inferInstance, f.toNormalization_fromNormalization⟩

/-- Oqhr-Gt66es-30771 (8:32:51) [prop] (second half) A proper morphism is separated and
universally closed. -/
theorem prop_30771 (f : X ⟶ Y) [IsProper f] : IsSeparated f ∧ UniversallyClosed f :=
  ⟨inferInstance, inferInstance⟩

/-- Oqhr-Gt66es-30898 (8:34:58) [prop] (first half, schemes) A scheme affine over a quasi-affine
scheme is quasi-affine. -/
theorem prop_30898 (f : X ⟶ Y) [IsAffineHom f] [Y.IsQuasiAffine] : X.IsQuasiAffine :=
  Scheme.IsQuasiAffine.of_isAffineHom f

/-- Oqhr-Gt66es-33252 (9:14:12) [def] A quasi-affine scheme (mathlib: `IsQuasiAffine`, a
quasi-compact open subscheme of `Spec Γ(X, 𝒪_X)`) is separated and coherent. -/
theorem def_33252 [X.IsQuasiAffine] :
    CompactSpace X ∧ IsOpenImmersion X.toSpecΓ ∧ X.IsSeparated ∧ QuasiSeparatedSpace X :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Oqhr-Gt66es-33316 (9:15:16) [prop] Morphisms `X → Spec B` are ring homomorphisms
`B → Γ(X, 𝒪_X)` (the `Γ ⊣ Spec` adjunction). -/
def prop_33316 (R : CommRingCat.{u}) : (X ⟶ Spec R) ≃ (R ⟶ Γ(X, ⊤)) :=
  ((ΓSpec.adjunction.homEquiv X (Opposite.op R)).symm.trans (opEquiv _ _))

/-- Oqhr-Gt66es-33316 (9:15:16) [prop] Every morphism `X → Spec B` factors through
`X → Spec Γ(X, 𝒪_X)`. -/
theorem prop_33316_factor (R : CommRingCat.{u}) (g : X ⟶ Spec R) :
    g = X.toSpecΓ ≫ Spec.map g.appTop ≫ inv (Spec R).toSpecΓ := by
  rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- Oqhr-Gt66es-33470 (9:17:50) [prop] (part) For `X` quasi-compact: `X` quasi-affine iff
`X → Spec Γ(X, 𝒪_X)` is an open immersion iff the affine `X_f`, `f ∈ Γ(X, 𝒪_X)`, cover `X`; they then
form a base of the topology. -/
theorem prop_33470 [CompactSpace X] :
    (X.IsQuasiAffine ↔ IsOpenImmersion X.toSpecΓ) ∧
    (X.IsQuasiAffine →
      TopologicalSpace.Opens.IsBasis { X.basicOpen r | (r : Γ(X, ⊤)) (_ : IsAffineOpen (X.basicOpen r)) }) ∧
    ((∀ x : X, ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r) →
      X.IsQuasiAffine) :=
  ⟨⟨fun _ => inferInstance, fun _ => ⟨⟩⟩, fun _ => Scheme.IsQuasiAffine.isBasis_basicOpen X,
    Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X⟩

/-- Oqhr-Gt66es-34487 (9:34:47) [prop] `f` is universally injective iff it is injective with
purely inseparable residue field extensions (radicial). -/
theorem prop_34487 (f : X ⟶ Y) :
    UniversallyInjective f ↔ Function.Injective f ∧
      ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable :=
  (tfae_universallyInjective f).out 1 3

/-- Oqhr-Gt66es-34689 (9:38:09) [prop] `f` is radicial iff `X(K) → Y(K)` is injective for every
field `K`, iff the diagonal is surjective. -/
theorem prop_34689 (f : X ⟶ Y) :
    (UniversallyInjective f ↔ ∀ (K : Type u) [Field K],
      Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f)) ∧
    (UniversallyInjective f ↔ Surjective (pullback.diagonal f)) :=
  ⟨(tfae_universallyInjective f).out 1 2, (tfae_universallyInjective f).out 1 4⟩

/-- Oqhr-Gt66es-34883 (9:41:23) [prop] Radicial morphisms are stable under base change and
composition; monomorphisms are radicial. -/
theorem prop_34883 (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChange @UniversallyInjective ∧
    MorphismProperty.IsStableUnderComposition @UniversallyInjective ∧
    (Mono f → UniversallyInjective f) :=
  ⟨inferInstance, inferInstance, fun _ => inferInstance⟩

/-- Oqhr-Gt66es-35012 (9:43:32) [prop] (first half) An integral, radicial and surjective
morphism is a universal homeomorphism. -/
theorem prop_35012 (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] [Surjective f]
    (g : Z ⟶ Y) : IsHomeomorph (pullback.snd f g) := by
  have key : ∀ {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') [IsIntegralHom f'] [UniversallyInjective f']
      [Surjective f'], IsHomeomorph f' := fun f' _ _ _ =>
    isHomeomorph_iff_continuous_isClosedMap_bijective.2
      ⟨f'.continuous, f'.isClosedMap, f'.injective, f'.surjective⟩
  have : UniversallyInjective (pullback.snd f g) := MorphismProperty.of_isPullback (P := @UniversallyInjective)
    (IsPullback.of_hasPullback f g) inferInstance
  exact key _

/-- Oqhr-Gt66es-35659 (9:54:19) [def] Universally open morphisms (mathlib: `UniversallyOpen`). -/
theorem def_35659 (f : X ⟶ Y) :
    UniversallyOpen f ↔ (topologically @IsOpenMap).universally f := by
  rw [UniversallyOpen.eq]

/-- Oqhr-Gt66es-35806 (9:56:46) [prop] (positive half) Open morphisms are stable under
composition; universally open ones under composition and base change. -/
theorem prop_35806 :
    MorphismProperty.IsStableUnderComposition (topologically @IsOpenMap) ∧
    MorphismProperty.IsStableUnderBaseChange @UniversallyOpen ∧
    MorphismProperty.IsStableUnderComposition @UniversallyOpen :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Oqhr-Gt66es-35869 (9:57:49) [prop] (special cases) Open immersions and flat morphisms are
generalizing. -/
theorem prop_35869 (f : X ⟶ Y) :
    (IsOpenImmersion f → GeneralizingMap f) ∧ (Flat f → GeneralizingMap f) :=
  ⟨fun _ => f.isOpenEmbedding.generalizingMap, fun _ => Flat.generalizingMap f⟩

/-- Oqhr-Gt66es-36565 (10:09:25) [prop] (one direction) If `f` is locally of finite presentation
and generalizing, it is open; if moreover flat, it is universally open. -/
theorem prop_36565 (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    (GeneralizingMap f → IsOpenMap f) ∧ (Flat f → UniversallyOpen f) :=
  ⟨isOpenMap_of_generalizingMap f, fun _ => UniversallyOpen.of_flat f⟩

/-- Oqhr-Gt66es-36440 (10:07:20) [prop] (part) Generalizing maps are stable under composition. -/
theorem prop_36440 {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    {f : α → β} {g : β → γ} (hf : GeneralizingMap f) (hg : GeneralizingMap g) :
    GeneralizingMap (g ∘ f) :=
  hf.comp hg

/-- Oqhr-Gt66es-36696 (10:11:36) [prop] Chevalley: the image of a constructible set by a morphism
of finite presentation to a quasi-compact quasi-separated scheme is constructible. -/
theorem prop_36696 (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f] [CompactSpace Y]
    [QuasiSeparatedSpace Y] {s : Set X} (hs : IsConstructible s) : IsConstructible (f '' s) :=
  f.isConstructible_image hs

/-- Oqhr-Gt66es-36760 (10:12:40) [prop] (affine form) A constructible subset of `Spec A` is open
iff it is stable under generization. -/
theorem prop_36760 {A : Type*} [CommRing A] (s : Set (PrimeSpectrum A)) (hs : IsConstructible s) :
    IsOpen s ↔ StableUnderGeneralization s :=
  ⟨IsOpen.stableUnderGeneralization, fun h =>
    PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible h hs⟩

/-- Oqhr-Gt66es-37016 (10:16:56) [prop] (finite presentation case) A scheme locally of finite
presentation over a field is universally open over it (it is flat). -/
theorem prop_37016 {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [LocallyOfFinitePresentation f] :
    UniversallyOpen f :=
  UniversallyOpen.of_flat f

end Schemes

/-- The generic point of the spectrum of a domain. -/
def genericPt (A : Type*) [CommRing A] [IsDomain A] : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩

/-- Oqhr-Gt66es-36503 (10:08:23) [cex] The inclusion of the generic point of an integral scheme
(here `Spec A`, `A` a domain) is generalizing; it is not open for the affine line: `{η}` is not open
in `Spec k[X]`. -/
theorem cex_36503 (A : Type*) [CommRing A] [IsDomain A] (k : Type*) [Field k] :
    GeneralizingMap (fun _ : Unit => genericPt A) ∧ ¬ IsOpen ({genericPt k[X]} : Set _) := by
  refine ⟨fun _ q hq => ⟨(), specializes_rfl, ?_⟩, fun h => ?_⟩
  · have : q ≤ genericPt A := (le_iff_specializes _ _).2 hq
    exact (le_antisymm this (fun x hx => by
      change x ∈ (⊥ : Ideal A) at hx; rw [Ideal.mem_bot.1 hx]; exact q.asIdeal.zero_mem)).symm
  · obtain ⟨_, ⟨f, rfl⟩, hη, hsub⟩ := isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (Set.mem_singleton (genericPt k[X])) h
    have hf : f ≠ 0 := fun hf => hη (by rw [hf]; exact (genericPt k[X]).asIdeal.zero_mem)
    set g : k[X] := X * f + 1
    have hdeg : 0 < g.natDegree := by
      have h1 : (X * f).natDegree = f.natDegree + 1 := by
        rw [mul_comm, natDegree_mul_X hf]
      have : g.natDegree = (X * f).natDegree :=
        natDegree_add_eq_left_of_natDegree_lt (by rw [h1, natDegree_one]; omega)
      omega
    have hu : ¬ IsUnit g := fun hu => by
      have := natDegree_eq_zero_of_isUnit hu; omega
    obtain ⟨m, hm, hgm⟩ := Ideal.exists_le_maximal (Ideal.span {g})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have hgm' : g ∈ m := hgm (Ideal.subset_span rfl)
    have hfm : f ∉ m := fun hfm => hm.ne_top ((Ideal.eq_top_iff_one _).2 (by
      have := m.sub_mem hgm' (m.mul_mem_left X hfm)
      simpa [g] using this))
    have hmem : (⟨m, hm.isPrime⟩ : PrimeSpectrum k[X]) ∈ (basicOpen f : Set _) := hfm
    have := hsub hmem
    rw [Set.mem_singleton_iff, PrimeSpectrum.ext_iff] at this
    have h0 : g ∈ (⊥ : Ideal k[X]) := by
      have : m = ⊥ := this
      rw [← this]; exact hgm'
    have : g = 0 := Ideal.mem_bot.1 h0
    rw [this] at hdeg
    simp at hdeg
/-- The coordinate ring `k[t², t³] ⊂ k[t]` of the cuspidal cubic `y² = x³`. -/
abbrev cuspRing (k : Type*) [Field k] : Subalgebra k k[X] := Algebra.adjoin k {X ^ 2, X ^ 3}

theorem cusp_isIntegral (k : Type*) [Field k] : Algebra.IsIntegral (cuspRing k) k[X] := by
  have hX : IsIntegral (cuspRing k) (X : k[X]) := by
    refine ⟨X ^ 2 - C ⟨X ^ 2, Algebra.subset_adjoin (by simp)⟩, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [eval₂_sub]
  constructor
  intro p
  induction p using Polynomial.induction_on with
  | C a =>
    exact (isIntegral_algebraMap (x := (⟨C a, Subalgebra.algebraMap_mem _ a⟩ : cuspRing k)))
  | add p q hp hq => exact hp.add hq
  | monomial n a h => rw [pow_succ, ← mul_assoc]; exact h.mul hX

/-- Oqhr-Gt66es-35209 (9:46:49) [ex] (integral and surjective half) The normalization
`Spec k[t] → Spec k[t², t³]` of the cusp is integral and surjective. -/
theorem ex_35209 (k : Type*) [Field k] :
    Algebra.IsIntegral (cuspRing k) k[X] ∧
      Function.Surjective (comap (algebraMap (cuspRing k) k[X])) := by
  have := cusp_isIntegral k
  exact ⟨this, Algebra.IsIntegral.comap_surjective _ _⟩

end

end Buffalo.AG.Part07
