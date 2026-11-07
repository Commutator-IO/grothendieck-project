import Mathlib

/-!
# Buffalo, algebraic geometry, part 05 (c): 25 June 1973, to 0:57:01

The entries of `docs/buffalo-ag/index.tex` lines 736–769 (video `Oqhr-Gt66es`, 0:00:01–0:57:01):
localization at a point, local, noetherian and artinian schemes, finiteness conditions on
morphisms. Almost everything here is in mathlib's `AlgebraicGeometry` library; the declarations
below check that the statements match.
-/

open CategoryTheory AlgebraicGeometry Topology PrimeSpectrum

universe u

namespace Buffalo.AG.Part05

noncomputable section

/-! ### Localization at a point -/

section Localization

/-- Oqhr-Gt66es-1 (0:00:01) [prop] `Spec 𝒪_{X,x} → X` is a monomorphism (it is a preimmersion,
injective on points), with image the generizations of `x`, the intersection of the open
neighbourhoods of `x`. -/
theorem prop_1 (X : Scheme.{u}) (x : X) :
    Function.Injective (X.fromSpecStalk x) ∧ Set.range (X.fromSpecStalk x) = {y | y ⤳ x} ∧
      {y | y ⤳ x} = ⋂₀ {U : Set X | IsOpen U ∧ x ∈ U} := by
  refine ⟨(X.fromSpecStalk x).isEmbedding.injective, Scheme.range_fromSpecStalk, ?_⟩
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_sInter, and_imp]
  exact ⟨fun h U hU hx => h.mem_open hU hx, fun h => specializes_iff_forall_open.2 h⟩

/-- Oqhr-Gt66es-65 (0:01:05) [prop] The prime ideals of `A_𝔭` correspond bijectively (and
monotonically) to the primes `𝔮 ⊆ 𝔭` of `A`. -/
def prop_65 {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    {q : Ideal (Localization.AtPrime p) // q.IsPrime} ≃o {q : Ideal A // q.IsPrime ∧ q ≤ p} :=
  IsLocalization.AtPrime.orderIsoOfPrime _ p

/-- Oqhr-Gt66es-128 (0:02:08) [prop] The local rings of the localization are those of `X`: for
every prime `𝔔` of `A_𝔭` (that is, `𝔔 = 𝔮A_𝔭` with `𝔮 ⊆ 𝔭`), `(A_𝔭)_𝔔 = A_𝔮`, `𝔮 = 𝔔 ∩ A`. -/
def prop_128 {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
    (P : Ideal (Localization.AtPrime p)) [P.IsPrime] :
    Localization.AtPrime (P.comap (algebraMap A (Localization.AtPrime p))) ≃ₐ[A]
      Localization.AtPrime P :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization p.primeCompl P

end Localization

/-! ### Local, noetherian and artinian schemes -/

section LocalSchemes

/-- Oqhr-Gt66es-325 (0:05:25) [def] A local scheme is the spectrum of a local ring. -/
def IsLocalScheme (X : Scheme.{u}) : Prop :=
  ∃ (R : CommRingCat.{u}), IsLocalRing R ∧ Nonempty (X ≅ Spec R)

/-- Oqhr-Gt66es-388 (0:06:28) [prop] (affine case) A ring `A ≠ 0` is local if and only if
`Spec A` has a unique closed point. -/
theorem prop_388 (A : Type u) [CommRing A] [Nontrivial A] :
    IsLocalRing A ↔ ∃! x : PrimeSpectrum A, IsClosed ({x} : Set (PrimeSpectrum A)) := by
  simp only [isClosed_singleton_iff_isMaximal]
  constructor
  · intro _
    refine ⟨⟨IsLocalRing.maximalIdeal A, inferInstance⟩, inferInstance, fun y hy => ?_⟩
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hy)
  · rintro ⟨x, hx, hu⟩
    refine IsLocalRing.of_unique_max_ideal ⟨x.asIdeal, hx, fun I hI => ?_⟩
    exact congrArg PrimeSpectrum.asIdeal (hu ⟨I, hI.isPrime⟩ hI)

/-- Oqhr-Gt66es-388 (0:06:28) [prop] (the reduction to the affine case) In a quasi-compact
scheme with a unique closed point `x`, every point specializes to `x`, so every open set containing
`x` (for instance an affine one) is the whole scheme. -/
theorem prop_388_reduction (X : Scheme.{u}) [CompactSpace X] (x : X)
    (hx : ∀ y : X, IsClosed ({y} : Set X) ↔ y = x) (U : X.Opens) (hU : x ∈ U) : U = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨z, hz, hzc⟩ :=
    (isClosed_closure (s := ({y} : Set X))).exists_closed_singleton ⟨y, subset_closure rfl⟩
  rw [(hx z).1 hzc] at hz
  exact (specializes_iff_mem_closure.2 hz).mem_open U.isOpen hU

/-- Oqhr-Gt66es-784 (0:13:04) [prop] Morphisms `Spec 𝒪 → X`, `𝒪` local, are pairs of a point
`x` and a local homomorphism `𝒪_{X,x} → 𝒪` (mathlib: `SpecToEquivOfLocalRing`). -/
def prop_784 (X : Scheme.{u}) (R : CommRingCat.{u}) [IsLocalRing R] :
    (Spec R ⟶ X) ≃ Σ x, {f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom} :=
  SpecToEquivOfLocalRing X R

/-- Oqhr-Gt66es-909 (0:15:09) [prop] A homomorphism `f : A → 𝒪` to a local ring factors uniquely
through `A_𝔭`, `𝔭 = f⁻¹(𝔪)`, by a local homomorphism. -/
theorem prop_909 {A O : Type*} [CommRing A] [CommRing O] [IsLocalRing O] (f : A →+* O) :
    ∃! g : Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap f) →+* O,
      g.comp (algebraMap A _) = f ∧ IsLocalHom g := by
  set p := (IsLocalRing.maximalIdeal O).comap f
  have hu : ∀ y : p.primeCompl, IsUnit (f y) := fun y => by
    by_contra h
    exact y.2 (show f y ∈ IsLocalRing.maximalIdeal O from h)
  refine ⟨IsLocalization.lift hu, ⟨IsLocalization.lift_comp hu, ⟨fun a ha => ?_⟩⟩,
    fun g hg => IsLocalization.ringHom_ext p.primeCompl
      (hg.1.trans (IsLocalization.lift_comp hu).symm)⟩
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a
  have hspec := IsLocalization.mk'_spec (Localization.AtPrime p) x s
  have h1 : IsLocalization.lift hu (IsLocalization.mk' (Localization.AtPrime p) x s) * f s =
      f x := by
    rw [← IsLocalization.lift_eq (S := Localization.AtPrime p) hu (s : A), ← map_mul, hspec,
      IsLocalization.lift_eq]
  have hfx : IsUnit (f x) := h1 ▸ ha.mul (hu s)
  have hx : x ∈ p.primeCompl := fun hxp => (IsLocalRing.mem_maximalIdeal _).1 hxp hfx
  exact isUnit_of_mul_isUnit_left
    (hspec ▸ IsLocalization.map_units (Localization.AtPrime p) (⟨x, hx⟩ : p.primeCompl))

/-- Oqhr-Gt66es-974 (0:16:14) [prop] Localization is functorial in (scheme, point): a morphism
`f` with `f(y) = x` gives `Spec 𝒪_{Y,y} → Spec 𝒪_{X,x}` over `f` (mathlib:
`SpecMap_stalkMap_fromSpecStalk`). -/
theorem prop_974 {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y) :
    Spec.map (f.stalkMap y) ≫ X.fromSpecStalk (f y) = Y.fromSpecStalk y ≫ f :=
  Scheme.SpecMap_stalkMap_fromSpecStalk f

/-- Oqhr-Gt66es-1102 (0:18:22) [prop] Morphisms `Spec k → X`, `k` a field, are pairs of a point
`x` and a homomorphism `κ(x) → k` (mathlib: `SpecToEquivOfField`). -/
def prop_1102 (K : Type u) [Field K] (X : Scheme.{u}) :
    (Spec (CommRingCat.of K) ⟶ X) ≃ Σ x, X.residueField x ⟶ CommRingCat.of K :=
  Scheme.SpecToEquivOfField K X

/-- Oqhr-Gt66es-1232 (0:20:32) [prop] `Spec κ(x)` is a closed subscheme of `Spec 𝒪_{X,x}`, and a
morphism `Spec k → X` with image `x` factors through `Spec κ(x) → X`. -/
theorem prop_1232 (X : Scheme.{u}) (x : X) (K : Type u) [Field K]
    (g : Spec (CommRingCat.of K) ⟶ X) :
    IsClosedImmersion (Spec.map (X.residue x)) ∧
      ∃ h : X.residueField (g (IsLocalRing.closedPoint K)) ⟶ CommRingCat.of K,
        Spec.map h ≫ X.fromSpecResidueField _ = g :=
  ⟨IsClosedImmersion.spec_of_surjective _ (X.residue_surjective x),
    ⟨_, (Scheme.SpecToEquivOfField K X).left_inv g⟩⟩

/-- A ring in which every element is nilpotent or a unit has a single prime ideal. -/
theorem subsingleton_primeSpectrum_of {R : Type*} [CommRing R]
    (h : ∀ x : R, IsNilpotent x ∨ IsUnit x) : Subsingleton (PrimeSpectrum R) := by
  refine ⟨fun p q => PrimeSpectrum.ext (Ideal.ext fun x => ?_)⟩
  have key : ∀ r : PrimeSpectrum R, x ∈ r.asIdeal ↔ IsNilpotent x := fun r =>
    ⟨fun hx => (h x).resolve_right fun hu => r.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu),
      fun ⟨n, hn⟩ => r.isPrime.mem_of_pow_mem n (hn ▸ r.asIdeal.zero_mem)⟩
  rw [key p, key q]

/-- Oqhr-Gt66es-1295 (0:21:35) [cex] A one-point affine scheme need not be the spectrum of a
field: `Spec ℤ/4` is a point but `ℤ/4` is not a field. Conversely, if `Spec A` is a point, `A` is
local with nil maximal ideal. -/
theorem cex_1295 : Subsingleton (PrimeSpectrum (ZMod 4)) ∧ ¬ IsField (ZMod 4) ∧
    ∀ (A : Type u) [CommRing A] [Nontrivial A], Subsingleton (PrimeSpectrum A) →
      IsLocalRing A ∧ ∀ a : A, ¬ IsUnit a → IsNilpotent a := by
  refine ⟨subsingleton_primeSpectrum_of fun x => ?_, fun hf => ?_, fun A _ _ hs => ?_⟩
  · fin_cases x
    · exact Or.inl ⟨1, by decide⟩
    · exact Or.inr isUnit_one
    · exact Or.inl ⟨2, by decide⟩
    · exact Or.inr ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
  · have h2 : (2 : ZMod 4) * 2 = 0 := by decide
    have h20 : (2 : ZMod 4) ≠ 0 := by decide
    obtain ⟨b, hb⟩ := hf.mul_inv_cancel h20
    exact h20 (by rw [← mul_one (2 : ZMod 4), ← hb, ← mul_assoc, h2, zero_mul])
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    have hall : ∀ J : Ideal A, J.IsPrime → J = m := fun J hJ =>
      congrArg PrimeSpectrum.asIdeal
        (Subsingleton.elim (⟨J, hJ⟩ : PrimeSpectrum A) ⟨m, hm.isPrime⟩)
    refine ⟨IsLocalRing.of_unique_max_ideal ⟨m, hm, fun I hI => hall I hI.isPrime⟩,
      fun a ha => ?_⟩
    obtain ⟨M, hM, haM⟩ := exists_max_ideal_of_mem_nonunits ha
    have : a ∈ nilradical A := by
      rw [nilradical_eq_sInf]
      refine Submodule.mem_sInf.2 fun J hJ => ?_
      rw [hall J hJ, ← hall M hM.isPrime]
      exact haM
    exact this

/-- Oqhr-Gt66es-1429 (0:23:49) [prop] A noetherian ring is artinian if and only if its Krull
dimension is `0` (for a local ring: its spectrum is a point); an artinian local ring has a
nilpotent maximal ideal (mathlib: `isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`,
`IsArtinianRing.isNilpotent_jacobson_bot`). -/
theorem prop_1429 (A : Type*) [CommRing A] :
    (IsArtinianRing A ↔ IsNoetherianRing A ∧ Ring.KrullDimLE 0 A) ∧
      (IsArtinianRing A → IsNilpotent (Ideal.jacobson (⊥ : Ideal A))) :=
  ⟨isArtinianRing_iff_isNoetherianRing_krullDimLE_zero, fun _ =>
    IsArtinianRing.isNilpotent_jacobson_bot⟩

/-- Oqhr-Gt66es-1556 (0:25:56) [ex] (the `ℤ/p^n` half, corrected) For `p` prime and `n ≥ 2`, `ℤ/p^n` is
artinian, every element is nilpotent or a unit (so `Spec` is a point), and it is not a field. -/
theorem ex_1556 (p n : ℕ) [hp : Fact p.Prime] (hn : 2 ≤ n) :
    IsArtinianRing (ZMod (p ^ n)) ∧ (∀ x : ZMod (p ^ n), IsNilpotent x ∨ IsUnit x) ∧
      Subsingleton (PrimeSpectrum (ZMod (p ^ n))) ∧ ¬ IsField (ZMod (p ^ n)) := by
  have hpos : 0 < p ^ n := pow_pos hp.out.pos n
  have : NeZero (p ^ n) := ⟨hpos.ne'⟩
  have key : ∀ x : ZMod (p ^ n), IsNilpotent x ∨ IsUnit x := by
    intro x
    by_cases h : p ∣ x.val
    · refine Or.inl ⟨n, ?_⟩
      rw [← ZMod.natCast_zmod_val x, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact pow_dvd_pow_of_dvd h n
    · refine Or.inr ?_
      have hc : Nat.Coprime x.val (p ^ n) :=
        Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd hp.out).2 h).symm
      exact (ZMod.unitOfCoprime x.val hc).isUnit.map (RingHom.id _) |>
        fun hu => by simpa [ZMod.natCast_zmod_val] using
          (ZMod.unitOfCoprime x.val hc).isUnit
  refine ⟨isArtinian_of_finite, key, subsingleton_primeSpectrum_of key, fun hf => ?_⟩
  have h0 : ((p : ZMod (p ^ n)) ^ n) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hp0 : (p : ZMod (p ^ n)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd hp.out.pos hd
    have h2 : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.out.pos hn
    nlinarith [hp.out.two_le]
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel hp0
  have : ((p : ZMod (p ^ n)) * b) ^ n = 1 := by rw [hb, one_pow]
  rw [mul_pow, h0, zero_mul] at this
  have h01 := this
  have : Nontrivial (ZMod (p ^ n)) := ZMod.nontrivial_iff.2 (by
    have h2 : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.out.pos hn
    nlinarith [hp.out.two_le])
  exact zero_ne_one h01

/-- Oqhr-Gt66es-1556 (0:25:56) [ex] (the hypothesis `n ≥ 2` is needed) For `n = 1`, `ℤ/p` is a
field (and so is `k[t]/(t)`), so its spectrum is the spectrum of a field. -/
theorem ex_1556_one (p : ℕ) [Fact p.Prime] : IsField (ZMod (p ^ 1)) := by
  rw [pow_one]
  exact Field.toIsField _

/-- Oqhr-Gt66es-1948 (0:32:28) [prop] An irreducible space is connected. -/
theorem prop_1948 (X : Scheme.{u}) [IrreducibleSpace X] : ConnectedSpace X := inferInstance

/-- Oqhr-Gt66es-2011 (0:33:31) [ex] An infinite disjoint union of nonempty spaces (the underlying
space of the constant scheme `G_k = ∐_G Spec k`) is not quasi-compact. -/
theorem ex_2011 (G : Type*) [Infinite G] (Y : G → Type*) [∀ g, TopologicalSpace (Y g)]
    [∀ g, Nonempty (Y g)] : ¬ CompactSpace (Σ g, Y g) := by
  intro hc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun g : G => Set.range (Sigma.mk g : Y g → Σ g, Y g)) (fun _ => isOpen_range_sigmaMk)
    (fun x _ => Set.mem_iUnion.2 ⟨x.1, x.2, rfl⟩)
  obtain ⟨g, hg⟩ := Infinite.exists_notMem_finset t
  have := ht (Set.mem_univ (⟨g, Classical.arbitrary _⟩ : Σ g, Y g))
  simp only [Set.mem_iUnion] at this
  obtain ⟨g', hg', y, hy⟩ := this
  cases hy
  exact hg hg'

/-- Oqhr-Gt66es-2202 (0:36:42) [def] A noetherian scheme is a quasi-compact locally noetherian
one (mathlib: `IsNoetherian`); then `Γ(U, 𝒪_X)` is noetherian for every affine open set `U`. -/
theorem def_2202 (X : Scheme.{u}) [IsNoetherian X] (U : X.affineOpens) :
    CompactSpace X ∧ IsNoetherianRing Γ(X, U) :=
  ⟨inferInstance, IsLocallyNoetherian.component_noetherian U⟩

/-- Oqhr-Gt66es-2270 (0:37:50) [def] A locally noetherian scheme (mathlib: `IsLocallyNoetherian`):
`Γ(U, 𝒪_X)` noetherian for every affine open set; every quasi-compact open set is noetherian. -/
theorem def_2270 (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens) (hU : IsCompact (U : Set X)) :
    IsNoetherian U :=
  { toIsLocallyNoetherian := inferInstance, toCompactSpace := isCompact_iff_compactSpace.1 hU }

/-- Oqhr-Gt66es-2525 (0:42:05) [prop] (localization half) A localization of a noetherian ring is
noetherian. -/
theorem prop_2525 (A : Type*) [CommRing A] [IsNoetherianRing A] (S : Submonoid A) :
    IsNoetherianRing (Localization S) :=
  IsLocalization.isNoetherianRing S _ ‹_›

/-- Oqhr-Gt66es-2589 (0:43:09) [def] An artinian scheme (mathlib: `IsArtinianScheme`, locally
artinian and quasi-compact); `Spec A` is artinian if and only if `A` is an artinian ring. -/
theorem def_2589 (R : CommRingCat.{u}) : IsArtinianScheme (Spec R) ↔ IsArtinianRing R :=
  Scheme.isArtinianScheme_Spec

/-- Oqhr-Gt66es-2728 (0:45:28) [prop] An artinian scheme is noetherian, discrete and finite; an
artinian ring is the product of its localizations at its (finitely many) maximal ideals. -/
theorem prop_2728 (X : Scheme.{u}) [IsArtinianScheme X] :
    IsNoetherian X ∧ DiscreteTopology X ∧ Finite X :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Oqhr-Gt66es-2728 (0:45:28) [prop] (the ring) An artinian ring is the product of the
localizations at its maximal ideals (mathlib: `MaximalSpectrum.toPiLocalizationEquiv`, `Spec` being discrete). -/
def prop_2728_ring (R : Type*) [CommRing R] [IsArtinianRing R] :
    R ≃ₐ[R] MaximalSpectrum.PiLocalization R :=
  MaximalSpectrum.toPiLocalizationEquiv R

/-- Oqhr-Gt66es-2791 (0:46:31) [prop] A scheme is artinian if and only if it is noetherian with
discrete underlying space. -/
theorem prop_2791 (X : Scheme.{u}) : IsArtinianScheme X ↔ IsNoetherian X ∧ DiscreteTopology X :=
  IsArtinianScheme.iff_isNoetherian_and_discreteTopology

end LocalSchemes

/-! ### Finiteness conditions on morphisms -/

section Finiteness

/-- Oqhr-Gt66es-2904 (0:48:24) [prop] Quasi-compact morphisms are stable under base change. -/
theorem prop_2904 : MorphismProperty.IsStableUnderBaseChange (@QuasiCompact : MorphismProperty Scheme.{u}) := inferInstance

/-- Oqhr-Gt66es-2968 (0:49:28) [prop] Quasi-compact morphisms are stable under composition. -/
theorem prop_2968 {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g] :
    QuasiCompact (f ≫ g) := inferInstance

/-- Oqhr-Gt66es-3033 (0:50:33) [prop] If `g ∘ f` is quasi-compact and `g` quasi-separated, `f` is
quasi-compact. -/
theorem prop_3033 {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact (f ≫ g)]
    [QuasiSeparated g] : QuasiCompact f :=
  QuasiCompact.of_comp f g

/-- Oqhr-Gt66es-3158 (0:52:38) [def] Morphisms locally of finite type (mathlib:
`LocallyOfFiniteType`, defined by affine open sets `V ⊆ f⁻¹U` exactly as in the entry); of finite
type: moreover quasi-compact. -/
theorem def_3158 {X Y : Scheme.{u}} (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔ ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens}
      (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.FiniteType :=
  locallyOfFiniteType_iff f

/-- Oqhr-Gt66es-3227 (0:53:47) [def] Morphisms locally of finite presentation (mathlib:
`LocallyOfFinitePresentation`, a `HasRingHomProperty`, hence local on the source). -/
theorem def_3227 {X Y : Scheme.{u}} (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔ ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens}
      (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.FinitePresentation :=
  locallyOfFinitePresentation_iff f

/-- Oqhr-Gt66es-3292 (0:54:52) [prop] `Spec B → Spec A` is locally of finite type (resp. finite
presentation) if and only if `B` is finitely generated (resp. finitely presented) over `A`. -/
theorem prop_3292 {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    (LocallyOfFiniteType (Spec.map φ) ↔ φ.hom.FiniteType) ∧
      (LocallyOfFinitePresentation (Spec.map φ) ↔ φ.hom.FinitePresentation) :=
  ⟨HasRingHomProperty.Spec_iff, HasRingHomProperty.Spec_iff⟩

/-- Oqhr-Gt66es-3359 (0:55:59) [prop] Over a locally noetherian base, locally of finite type and
locally of finite presentation coincide. -/
theorem prop_3359 {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] :
    LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f :=
  LocallyOfFinitePresentation.iff_locallyOfFiniteType

/-- Oqhr-Gt66es-3421 (0:57:01) [prop] Quasi-compact, locally of finite type and locally of finite
presentation morphisms (hence also of finite type) are stable under base change and
composition. -/
theorem prop_3421 :
    MorphismProperty.IsStableUnderBaseChange (@QuasiCompact : MorphismProperty Scheme.{u}) ∧ MorphismProperty.IsStableUnderBaseChange (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsStableUnderBaseChange (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsStableUnderComposition (@QuasiCompact : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsStableUnderComposition (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsStableUnderComposition (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end Finiteness

end

end Buffalo.AG.Part05
