import Buffalo.AG.Part01

/-!
# Buffalo, algebraic geometry, part 03 (a): 11 June 1973, from 8:43:41

The entries of `docs/buffalo-ag/index.tex` lines 356–402 (video `51wmmpHand0`, 8:43:41–10:30:48):
functoriality of `Spec` and the basic open sets, `Spec` and fibre products, faithfully flat
descent and Čech cohomology.

Conventions. Spectra are mathlib's `PrimeSpectrum` with the Zariski topology; `Y_f` is
`PrimeSpectrum.basicOpen f`, `V(J)` is `PrimeSpectrum.zeroLocus J`, and the map
`Spec(u) : Spec B → Spec A` of `u : A → B` is `PrimeSpectrum.comap u`. The canonical map
`Spec(A ⊗_K B) → Spec A × Spec B` is `PrimeSpectrum.tensorProductTo`. For descent, the sequence
`0 → M → M ⊗_A A' ⇉ M ⊗_A A' ⊗_A A'` is written as the exactness of
`M ⊗ A → M ⊗ A' → M ⊗ (A' ⊗ A')`, the second map being `M ⊗ (s ↦ s ⊗ 1 - 1 ⊗ s)`
(mathlib's `Algebra.TensorProduct.includeLeftSubRight`).
-/

open CategoryTheory TensorProduct Topology PrimeSpectrum

universe u

namespace Buffalo.AG.Part03

noncomputable section

/-! ### Functoriality of Spec and basic open sets -/

section Functoriality

variable {A B : Type*} [CommRing A] [CommRing B]

/-- 51wmmpHand0-31421 (8:43:41) [prop] A homomorphism `u : A → B` induces
`φ : Spec B → Spec A`, `𝔭 ↦ u⁻¹(𝔭)`, which is prime because `A/u⁻¹(𝔭) ⊂ B/𝔭` is an integral
domain (mathlib: `Ideal.IsPrime.comap`, `Ideal.quotientMap_injective`). -/
theorem prop_31421 (u : A →+* B) (p : Ideal B) [p.IsPrime] :
    (p.comap u).IsPrime ∧
      Function.Injective (Ideal.quotientMap p u le_rfl : A ⧸ p.comap u →+* B ⧸ p) :=
  ⟨inferInstance, Ideal.quotientMap_injective⟩

/-- 51wmmpHand0-31557 (8:45:57) [prop] `φ⁻¹(V(J)) = V(JB)`; hence `φ` is continuous
(mathlib: `PrimeSpectrum.preimage_comap_zeroLocus`, `PrimeSpectrum.continuous_comap`). -/
theorem prop_31557 (u : A →+* B) (J : Ideal A) :
    comap u ⁻¹' zeroLocus (J : Set A) = zeroLocus (J.map u : Set B) ∧ Continuous (comap u) := by
  refine ⟨?_, continuous_comap u⟩
  rw [preimage_comap_zeroLocus, Ideal.map, zeroLocus_span]

/-- 51wmmpHand0-31622 (8:47:02) [prop] `A ↦ Spec A` is a contravariant functor to topological
spaces (mathlib: `AlgebraicGeometry.Spec.toTop : CommRingCatᵒᵖ ⥤ TopCat`; here the functor
laws on the maps). -/
theorem prop_31622 {C : Type*} [CommRing C] (u : A →+* B) (v : B →+* C) :
    comap (RingHom.id A) = id ∧ comap (v.comp u) = comap u ∘ comap v :=
  ⟨comap_id, comap_comp u v⟩

example : CommRingCat.{u}ᵒᵖ ⥤ TopCat.{u} := AlgebraicGeometry.Spec.toTop

/-- 51wmmpHand0-31688 (8:48:08) [prop] If `u : A → B ≃ A/J` is surjective, `φ` is a homeomorphism
of `Spec B` onto the closed set `V(J)`, `J = ker u`: a closed immersion (mathlib:
`PrimeSpectrum.isClosedEmbedding_comap_of_surjective`, `range_comap_of_surjective`). -/
theorem prop_31688 (u : A →+* B) (hu : Function.Surjective u) :
    IsClosedEmbedding (comap u) ∧ Set.range (comap u) = zeroLocus (RingHom.ker u : Set A) :=
  ⟨isClosedEmbedding_comap_of_surjective B u hu, range_comap_of_surjective B u hu⟩

/-- 51wmmpHand0-31819 (8:50:19) [prop] `A → A_f` is an epimorphism of rings; the homomorphisms
`A_f → K'` are those of `A` sending `f` to a unit; `Spec A_f → Spec A` is injective. -/
theorem prop_31819 (f : A) :
    (∀ (T : Type*) [CommRing T] (g h : Localization.Away f →+* T),
      g.comp (algebraMap A _) = h.comp (algebraMap A _) → g = h) ∧
    (∀ (T : Type*) [CommRing T] (g : A →+* T),
      IsUnit (g f) ↔ ∃ h : Localization.Away f →+* T, h.comp (algebraMap A _) = g) ∧
    Function.Injective (comap (algebraMap A (Localization.Away f))) := by
  refine ⟨fun T _ g h hgh => IsLocalization.ringHom_ext (Submonoid.powers f) hgh,
    fun T _ g => ⟨fun hg => ⟨IsLocalization.Away.lift f hg, IsLocalization.Away.lift_comp f hg⟩,
      ?_⟩, localization_comap_injective _ (Submonoid.powers f)⟩
  rintro ⟨h, rfl⟩
  exact (IsLocalization.Away.algebraMap_isUnit f).map h

/-- 51wmmpHand0-31882 (8:51:22) [prop] `Spec A_f → Spec A` induces isomorphisms of residue
fields: for a prime `𝔮` of `A_f` over `𝔭 = 𝔮 ∩ A`, `κ(𝔭) ≃ κ(𝔮)` (mathlib:
`localizationLocalizationAtPrimeIsoLocalization`; true for any localization). -/
def prop_31882 (S : Submonoid A) (q : Ideal (Localization S)) [q.IsPrime] :
    (q.comap (algebraMap A (Localization S))).ResidueField ≃+* q.ResidueField :=
  IsLocalRing.ResidueField.mapEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization S q).toRingEquiv

/-- 51wmmpHand0-31945 (8:52:25) [prop] The image of `Spec A_f → Spec A` is `Y_f`, and the map is a
homeomorphism onto it (an open embedding) (mathlib: `PrimeSpectrum.localization_away_comap_range`,
`PrimeSpectrum.localization_away_isOpenEmbedding`). -/
theorem prop_31945 (f : A) :
    Set.range (comap (algebraMap A (Localization.Away f))) = basicOpen f ∧
      IsOpenEmbedding (comap (algebraMap A (Localization.Away f))) :=
  ⟨localization_away_comap_range _ f, localization_away_isOpenEmbedding _ f⟩

/-- 51wmmpHand0-32072 (8:54:32) [prop] The `Y_f` form a base of the topology of `Spec A`
(mathlib: `PrimeSpectrum.isTopologicalBasis_basic_opens`). -/
theorem prop_32072 :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun f : A => (basicOpen f : Set (PrimeSpectrum A))) :=
  isTopologicalBasis_basic_opens

/-- 51wmmpHand0-32243 (8:57:23) [prop] `Y_1 = Y` and `Y_f ∩ Y_g = Y_{fg}` (mathlib:
`PrimeSpectrum.basicOpen_one`, `PrimeSpectrum.basicOpen_mul`). -/
theorem prop_32243 (f g : A) : basicOpen (1 : A) = ⊤ ∧ basicOpen (f * g) = basicOpen f ⊓ basicOpen g :=
  ⟨basicOpen_one, basicOpen_mul f g⟩

/-- 51wmmpHand0-32306 (8:58:26) [prop] A map from a space to `Spec A` is continuous iff the
preimage of every `Y_f` is open. -/
theorem prop_32306 {X : Type*} [TopologicalSpace X] (φ : X → PrimeSpectrum A) :
    Continuous φ ↔ ∀ f : A, IsOpen (φ ⁻¹' basicOpen f) := by
  rw [isTopologicalBasis_basic_opens.continuous_iff]
  simp

/-- 51wmmpHand0-32371 (8:59:31) [prop] `φ⁻¹(Y_f) = X_{u(f)}` (mathlib:
`PrimeSpectrum.comap_basicOpen`). -/
theorem prop_32371 (u : A →+* B) (f : A) :
    comap u ⁻¹' basicOpen f = basicOpen (u f) :=
  congrArg SetLike.coe (comap_basicOpen u f)

/-- 51wmmpHand0-32699 (9:04:59) [prop] `Spec A_f → Spec A` is an open embedding with image `Y_f`
(`prop_31945`). -/
theorem prop_32699 (f : A) :
    IsOpenEmbedding (comap (algebraMap A (Localization.Away f))) ∧
      Set.range (comap (algebraMap A (Localization.Away f))) = basicOpen f :=
  (prop_31945 f).symm

/-- 51wmmpHand0-32774 (9:06:14) [prop] For a finite product `A = ∏ A_i`, `Spec A` is the
topological sum of the `Spec A_i` (mathlib: `PrimeSpectrum.sigmaToPiHomeo`). -/
def prop_32774 {ι : Type*} [Finite ι] (R : ι → Type*) [∀ i, CommRing (R i)] :
    (Σ i, PrimeSpectrum (R i)) ≃ₜ PrimeSpectrum (Π i, R i) :=
  sigmaToPiHomeo R

end Functoriality

/-! ### Spec and fibre products -/

section FibreProducts

/-- The spectrum of a field is a single point. -/
theorem subsingleton_primeSpectrum_field (L : Type*) [Field L] : Subsingleton (PrimeSpectrum L) :=
  ⟨fun p q => PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p.asIdeal).trans
    (Ideal.eq_bot_of_prime q.asIdeal).symm)⟩

/-- A prime pulled back along `C → L → R`, `L` a field, is the kernel of `C → L`. -/
theorem comap_comp_of_ker {C L R : Type*} [CommRing C] [Field L] [CommRing R] (P : Ideal C)
    (j : C →+* L) (hj : RingHom.ker j = P) (i : L →+* R) (m : Ideal R) [m.IsPrime] :
    m.comap (i.comp j) = P := by
  rw [← Ideal.comap_comap, Ideal.eq_bot_of_prime (m.comap i), ← hj]
  rfl

variable {K : Type*} [Field K] {A B : Type*} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- Over a field, every pair of primes of `A` and `B` lifts to a prime of `A ⊗_K B`: take a
maximal ideal of `κ(𝔭) ⊗_K κ(𝔮) ≠ 0`. -/
theorem tensorProductTo_surjective :
    Function.Surjective (tensorProductTo K A B) := by
  rintro ⟨p, q⟩
  let φ : A ⊗[K] B →ₐ[K] p.asIdeal.ResidueField ⊗[K] q.asIdeal.ResidueField :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A _) (IsScalarTower.toAlgHom K B _)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (p.asIdeal.ResidueField ⊗[K] q.asIdeal.ResidueField)
  have := hm.isPrime
  refine ⟨⟨m.comap φ.toRingHom, inferInstance⟩, Prod.ext (PrimeSpectrum.ext ?_)
    (PrimeSpectrum.ext ?_)⟩
  · change Ideal.comap ((φ.toRingHom).comp (algebraMap A (A ⊗[K] B))) m = p.asIdeal
    have : (φ.toRingHom).comp (algebraMap A (A ⊗[K] B)) =
        (Algebra.TensorProduct.includeLeftRingHom).comp (algebraMap A p.asIdeal.ResidueField) := by
      ext a; simp [φ]
    rw [this]
    exact comap_comp_of_ker _ _ (Ideal.ker_algebraMap_residueField p.asIdeal) _ m
  · change Ideal.comap ((φ.toRingHom).comp Algebra.TensorProduct.includeRight.toRingHom) m =
      q.asIdeal
    have : (φ.toRingHom).comp Algebra.TensorProduct.includeRight.toRingHom =
        (Algebra.TensorProduct.includeRight.toRingHom).comp
          (algebraMap B q.asIdeal.ResidueField) := by
      ext b; simp [φ]
    rw [this]
    exact comap_comp_of_ker _ _ (Ideal.ker_algebraMap_residueField q.asIdeal) _ m

/-- The two points `ker(a ⊗ b ↦ ab)` and `ker(a ⊗ b ↦ a b̄)` of `Spec(ℂ ⊗_ℝ ℂ)`. -/
def cpt (σ : ℂ →ₐ[ℝ] ℂ) : PrimeSpectrum (ℂ ⊗[ℝ] ℂ) :=
  ⟨RingHom.ker (Algebra.TensorProduct.productMap (AlgHom.id ℝ ℂ) σ), RingHom.ker_isPrime _⟩

theorem cpt_ne : cpt (AlgHom.id ℝ ℂ) ≠ cpt Complex.conjAe.toAlgHom := by
  intro h
  have h' := congrArg (fun p : PrimeSpectrum (ℂ ⊗[ℝ] ℂ) =>
    (Complex.I ⊗ₜ[ℝ] (1 : ℂ) - (1 : ℂ) ⊗ₜ Complex.I) ∈ p.asIdeal) h
  simp only [cpt, RingHom.mem_ker, map_sub, Algebra.TensorProduct.productMap_apply_tmul,
    AlgHom.id_apply, map_one, mul_one, one_mul, sub_self, eq_iff_iff, true_iff] at h'
  simp [Complex.ext_iff] at h'

/-- 51wmmpHand0-33240 (9:14:00) [prop] Over a field `K`, `Spec(A ⊗_K B) → Spec A × Spec B` is
surjective, but not injective in general: for `ℂ ⊗_ℝ ℂ ≃ ℂ × ℂ` the two points over the single
point of `Spec ℂ × Spec ℂ`. -/
theorem prop_33240 :
    Function.Surjective (tensorProductTo K A B) ∧
      ¬ Function.Injective (tensorProductTo ℝ ℂ ℂ) := by
  refine ⟨tensorProductTo_surjective, fun h => cpt_ne (h ?_)⟩
  have := subsingleton_primeSpectrum_field ℂ
  exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- 51wmmpHand0-33308 (9:15:08) [prop] If `x ↦ y` under `Spec(u)`, then `A/𝔮 → B/𝔭` is injective
and induces an inclusion `κ(y) → κ(x)` of residue fields (mathlib: `Ideal.ResidueField.map`). -/
theorem prop_33308 {A B : Type*} [CommRing A] [CommRing B] (u : A →+* B) (p : Ideal B)
    [p.IsPrime] :
    Function.Injective (Ideal.quotientMap p u le_rfl : A ⧸ p.comap u →+* B ⧸ p) ∧
      Function.Injective (Ideal.ResidueField.map (p.comap u) p u rfl) :=
  ⟨Ideal.quotientMap_injective, RingHom.injective _⟩

/-- 51wmmpHand0-33500 (9:18:20) [prop] The points of `X ×_S Y` are the triples `(x, y, s)` with a
point of `Spec(κ(x) ⊗_{κ(s)} κ(y))` (mathlib, for schemes: `Scheme.Pullback.carrierEquiv`; the
fibre over `(x, y)` is the summand `Spec(κ(x) ⊗_{κ(s)} κ(y))`). -/
def prop_33500 {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    ↥(Limits.pullback f g) ≃
      (T : AlgebraicGeometry.Scheme.Pullback.Triplet f g) × ↥(AlgebraicGeometry.Spec T.tensor) :=
  AlgebraicGeometry.Scheme.Pullback.carrierEquiv

/-- `k[X] ⊗_k k[X] → k[X]`, `a ⊗ b ↦ a · b(X^n)`. -/
def evExpand (k : Type*) [Field k] (n : ℕ) :
    Polynomial k ⊗[k] Polynomial k →ₐ[k] Polynomial k :=
  Algebra.TensorProduct.productMap (AlgHom.id k _) (Polynomial.expand k n)

/-- The point `V(1 ⊗ V - U^n ⊗ 1)` of the plane, over the generic points of both lines. -/
def curvePt (k : Type*) [Field k] (n : ℕ) : PrimeSpectrum (Polynomial k ⊗[k] Polynomial k) :=
  ⟨RingHom.ker (evExpand k n), RingHom.ker_isPrime _⟩

theorem curvePt_injective (k : Type*) [Field k] :
    Function.Injective fun n : ℕ => curvePt k (n + 1) := by
  intro m n h
  have h' := congrArg (fun p : PrimeSpectrum (Polynomial k ⊗[k] Polynomial k) =>
    ((1 : Polynomial k) ⊗ₜ[k] Polynomial.X - (Polynomial.X ^ (n + 1)) ⊗ₜ 1) ∈ p.asIdeal) h
  simp only [curvePt, evExpand, RingHom.mem_ker, map_sub,
    Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply, map_one, one_mul, mul_one,
    Polynomial.expand_X, sub_self, eq_iff_iff, iff_true] at h'
  have := congrArg Polynomial.natDegree (sub_eq_zero.1 h')
  simp only [Polynomial.natDegree_X_pow] at this
  omega

theorem curvePt_over_generic (k : Type*) [Field k] (n : ℕ) (hn : 0 < n) :
    tensorProductTo k (Polynomial k) (Polynomial k) (curvePt k n) =
      (⟨⊥, Ideal.isPrime_bot⟩, ⟨⊥, Ideal.isPrime_bot⟩) := by
  refine Prod.ext (PrimeSpectrum.ext ?_) (PrimeSpectrum.ext ?_)
  · ext a
    simp [tensorProductTo, curvePt, evExpand, RingHom.mem_ker, Algebra.TensorProduct.algebraMap_apply]
  · ext a
    simp only [tensorProductTo, curvePt, comap_asIdeal, Ideal.mem_comap, RingHom.mem_ker,
      Submodule.mem_bot]
    refine ⟨fun h => Polynomial.expand_injective hn ?_, fun h => by simp [h]⟩
    simpa [evExpand] using h

/-- 51wmmpHand0-33562 (9:19:22) [ex] If `κ(x) = κ(s)` the fibre `Spec(κ(x) ⊗ κ(y))` is a point;
if `κ(x)`, `κ(y)` are transcendental it is infinite. Proved: `Spec(K ⊗_K L)` is a point, and the
fibre of `Spec k[U,V] → Spec k[U] × Spec k[V]` over the pair of generic points is infinite (it
contains the curves `V = U^n`). -/
theorem ex_33562 (k : Type*) [Field k] (L : Type*) [Field L] [Algebra K L] :
    Subsingleton (PrimeSpectrum (K ⊗[K] L)) ∧ Nonempty (PrimeSpectrum (K ⊗[K] L)) ∧
      {P | tensorProductTo k (Polynomial k) (Polynomial k) P =
        (⟨⊥, Ideal.isPrime_bot⟩, ⟨⊥, Ideal.isPrime_bot⟩)}.Infinite := by
  refine ⟨?_, ?_, ?_⟩
  · have := subsingleton_primeSpectrum_field L
    exact (PrimeSpectrum.comapEquiv (Algebra.TensorProduct.lid K L).toRingEquiv).subsingleton
  · exact inferInstance
  · refine Set.infinite_of_injective_forall_mem (curvePt_injective k) fun n => ?_
    exact curvePt_over_generic k (n + 1) n.succ_pos

end FibreProducts

/-! ### The affine line and plane over an algebraically closed field -/

section Line

open Polynomial

variable (K : Type*) [Field K]

/-- 51wmmpHand0-34080 (9:28:00) [ex] For `K` algebraically closed, the points of `Spec K[T]` are
the maximal ideals `(T - a)`, `a ∈ K`, and the generic point `η = (0)`. -/
theorem ex_34080 [IsAlgClosed K] (p : PrimeSpectrum K[X]) :
    p.asIdeal = ⊥ ∨ ∃ a : K, p.asIdeal = Ideal.span {X - C a} := by
  by_cases h0 : p.asIdeal = ⊥
  · exact Or.inl h0
  refine Or.inr ?_
  have hmax : p.asIdeal.IsMaximal := p.isPrime.isMaximal h0
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal p.asIdeal).principal
  have hg' : p.asIdeal = Ideal.span {g} := by rw [hg]
  have g0 : g ≠ 0 := by rintro rfl; exact h0 (by rw [hg', Ideal.span_singleton_eq_bot])
  have hdeg : g.degree ≠ 0 := by
    intro hd
    rw [eq_C_of_degree_eq_zero hd] at hg'
    have hc : g.coeff 0 ≠ 0 := by
      intro hc; rw [eq_C_of_degree_eq_zero hd, hc, C_0] at g0; exact g0 rfl
    exact hmax.ne_top (by rw [hg', Ideal.span_singleton_eq_top]; exact isUnit_C.2 hc.isUnit)
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root g hdeg
  refine ⟨a, hmax.eq_of_le ?_ ?_⟩
  · rw [Ne, Ideal.span_singleton_eq_top]; exact not_isUnit_X_sub_C a
  · rw [hg', Ideal.span_singleton_le_span_singleton]; exact dvd_iff_isRoot.2 ha

/-- The closed point `(T - a)` of the affine line. -/
def linePt (a : K) : PrimeSpectrum K[X] :=
  ⟨Ideal.span {X - C a}, (PrincipalIdealRing.isMaximal_of_irreducible
    (irreducible_X_sub_C a)).isPrime⟩

/-- The nonzero primes of `K[T]` are maximal, i.e. closed points. -/
theorem isClosed_singleton_line (p : PrimeSpectrum K[X]) (hp : p.asIdeal ≠ ⊥) :
    IsClosed ({p} : Set (PrimeSpectrum K[X])) :=
  (isClosed_singleton_iff_isMaximal p).2 (p.isPrime.isMaximal hp)

/-- 51wmmpHand0-34212 (9:30:12) [ex] The closed sets of `Spec K[T]` (`K` algebraically closed) are
the whole space and the finite sets of closed points; every finite set of closed points is
closed. -/
theorem ex_34212 [IsAlgClosed K] :
    (∀ Z : Set (PrimeSpectrum K[X]), IsClosed Z →
      Z = Set.univ ∨ (Z.Finite ∧ ∀ p ∈ Z, p.asIdeal ≠ ⊥)) ∧
    (∀ Z : Set (PrimeSpectrum K[X]), Z.Finite → (∀ p ∈ Z, p.asIdeal ≠ ⊥) → IsClosed Z) := by
  classical
  refine ⟨fun Z hZ => ?_, fun Z hZ h => ?_⟩
  · obtain ⟨I, rfl⟩ := (isClosed_iff_zeroLocus_ideal Z).1 hZ
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal I).principal
    have hI : I = Ideal.span {g} := by rw [hg]
    by_cases g0 : g = 0
    · left
      rw [hI, g0, Ideal.span_singleton_eq_bot.2 rfl, Submodule.bot_coe, zeroLocus_singleton_zero]
    · right
      have mem : ∀ p ∈ zeroLocus (I : Set K[X]), g ∈ p.asIdeal := fun p hp =>
        hp (by rw [hI]; exact Ideal.subset_span rfl)
      refine ⟨?_, fun p hp h0 => g0 (by simpa [h0] using mem p hp)⟩
      refine ((g.roots.toFinset.finite_toSet).image (linePt K)).subset fun p hp => ?_
      rcases ex_34080 K p with h0 | ⟨a, ha⟩
      · exact absurd (by simpa [h0] using mem p hp) g0
      · refine ⟨a, ?_, PrimeSpectrum.ext ha.symm⟩
        have : X - C a ∣ g := by
          rw [← Ideal.mem_span_singleton, ← ha]; exact mem p hp
        simpa [mem_roots g0] using dvd_iff_isRoot.1 this
  · rw [← Set.biUnion_of_singleton Z]
    exact hZ.isClosed_biUnion fun p hp => isClosed_singleton_line K p (h p hp)

/-- `K[T] ⊗_K B → B`, `f ⊗ b ↦ f(a) b`. -/
def evL {B : Type*} [CommRing B] [Algebra K B] (a : K) : K[X] ⊗[K] B →ₐ[K] B :=
  Algebra.TensorProduct.productMap ((Algebra.ofId K B).comp (aeval a)) (AlgHom.id K B)

/-- A prime of `K[T] ⊗_K B` lying over `(T - a)` is determined by its trace on `B`. -/
theorem eq_comap_evL {B : Type*} [CommRing B] [Algebra K B] (a : K)
    (P : PrimeSpectrum (K[X] ⊗[K] B))
    (hP : (X - C a) ∈ P.asIdeal.comap (algebraMap K[X] (K[X] ⊗[K] B))) :
    P.asIdeal = (P.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom).comap
      (evL K a).toRingHom := by
  let q := Ideal.Quotient.mkₐ K P.asIdeal
  have hq : q = (q.comp Algebra.TensorProduct.includeRight).comp (evL K a) := by
    apply Algebra.TensorProduct.ext
    · apply Polynomial.algHom_ext
      have : q (X ⊗ₜ 1) = q (C a ⊗ₜ 1) := by
        rw [← sub_eq_zero, ← map_sub, ← sub_tmul, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem]
        simpa [Algebra.TensorProduct.algebraMap_apply] using hP
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply, evL,
        Algebra.TensorProduct.productMap_apply_tmul, aeval_X, map_one, mul_one,
        Algebra.TensorProduct.includeRight_apply, Algebra.ofId_apply]
      rw [this, ← Polynomial.algebraMap_eq, Algebra.algebraMap_eq_smul_one, smul_tmul,
        Algebra.algebraMap_eq_smul_one]
    · ext b; simp [evL]
  ext x
  have := congrArg (fun φ : K[X] ⊗[K] B →ₐ[K] _ ⧸ P.asIdeal => φ x = 0) hq
  simpa [q, Ideal.Quotient.eq_zero_iff_mem] using this

/-- `A ⊗_K K[T] → A`, `x ⊗ f ↦ x f(b)`. -/
def evR {A : Type*} [CommRing A] [Algebra K A] (b : K) : A ⊗[K] K[X] →ₐ[K] A :=
  Algebra.TensorProduct.productMap (AlgHom.id K A) ((Algebra.ofId K A).comp (aeval b))

/-- A prime of `A ⊗_K K[T]` lying over `(T - b)` is determined by its trace on `A`. -/
theorem eq_comap_evR {A : Type*} [CommRing A] [Algebra K A] (b : K)
    (P : PrimeSpectrum (A ⊗[K] K[X]))
    (hP : (X - C b) ∈ P.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom) :
    P.asIdeal = (P.asIdeal.comap (algebraMap A (A ⊗[K] K[X]))).comap (evR K b).toRingHom := by
  let q := Ideal.Quotient.mkₐ K P.asIdeal
  have hq : q = (q.comp Algebra.TensorProduct.includeLeft).comp (evR K b) := by
    apply Algebra.TensorProduct.ext
    · ext x; simp [evR]
    · apply Polynomial.algHom_ext
      have : q (1 ⊗ₜ X) = q (1 ⊗ₜ C b) := by
        rw [← sub_eq_zero, ← map_sub, ← tmul_sub, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem]
        simpa using hP
      simp only [AlgHom.restrictScalars_apply, AlgHom.comp_apply,
        Algebra.TensorProduct.includeRight_apply, evR, Algebra.TensorProduct.productMap_apply_tmul,
        aeval_X, map_one, one_mul, Algebra.TensorProduct.includeLeft_apply, Algebra.ofId_apply]
      rw [this, ← Polynomial.algebraMap_eq, Algebra.algebraMap_eq_smul_one, tmul_smul,
        Algebra.algebraMap_eq_smul_one, smul_tmul']
  ext x
  have := congrArg (fun φ : A ⊗[K] K[X] →ₐ[K] _ ⧸ P.asIdeal => φ x = 0) hq
  simpa [q, Ideal.Quotient.eq_zero_iff_mem] using this

/-- 51wmmpHand0-34277 (9:31:17) [ex] For `Spec K[U,V] → Spec K[U] × Spec K[V]`, the fibre over a
point of `K × K`, `K × {η}` or `{η} × K` is a single point: it is nonempty, and a prime over a
closed point `(U - a)` (resp. `(V - b)`) is determined by its image in the other factor. -/
theorem ex_34277 :
    Function.Surjective (tensorProductTo K K[X] K[X]) ∧
    (∀ (a : K) (y : PrimeSpectrum K[X]) (P Q : PrimeSpectrum (K[X] ⊗[K] K[X])),
      tensorProductTo K _ _ P = (linePt K a, y) → tensorProductTo K _ _ Q = (linePt K a, y) →
        P = Q) ∧
    (∀ (b : K) (x : PrimeSpectrum K[X]) (P Q : PrimeSpectrum (K[X] ⊗[K] K[X])),
      tensorProductTo K _ _ P = (x, linePt K b) → tensorProductTo K _ _ Q = (x, linePt K b) →
        P = Q) := by
  refine ⟨tensorProductTo_surjective, fun a y P Q hP hQ => ?_, fun b x P Q hP hQ => ?_⟩
  · have mem : ∀ R : PrimeSpectrum (K[X] ⊗[K] K[X]), tensorProductTo K _ _ R = (linePt K a, y) →
        (X - C a) ∈ R.asIdeal.comap (algebraMap K[X] (K[X] ⊗[K] K[X])) := fun R hR => by
      have := congrArg (fun r => r.1.asIdeal) hR
      simp only [tensorProductTo, comap_asIdeal] at this
      rw [this]; exact Ideal.subset_span rfl
    have e2 : ∀ R : PrimeSpectrum (K[X] ⊗[K] K[X]), tensorProductTo K _ _ R = (linePt K a, y) →
        R.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = y.asIdeal :=
      fun R hR => congrArg (fun r => r.2.asIdeal) hR
    refine PrimeSpectrum.ext ?_
    rw [eq_comap_evL K a P (mem P hP), eq_comap_evL K a Q (mem Q hQ), e2 P hP, e2 Q hQ]
  · have mem : ∀ R : PrimeSpectrum (K[X] ⊗[K] K[X]), tensorProductTo K _ _ R = (x, linePt K b) →
        (X - C b) ∈ R.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom := fun R hR => by
      have := congrArg (fun r => r.2.asIdeal) hR
      simp only [tensorProductTo, comap_asIdeal] at this
      rw [this]; exact Ideal.subset_span rfl
    have e1 : ∀ R : PrimeSpectrum (K[X] ⊗[K] K[X]), tensorProductTo K _ _ R = (x, linePt K b) →
        R.asIdeal.comap (algebraMap K[X] (K[X] ⊗[K] K[X])) = x.asIdeal :=
      fun R hR => congrArg (fun r => r.1.asIdeal) hR
    refine PrimeSpectrum.ext ?_
    rw [eq_comap_evR K b P (mem P hP), eq_comap_evR K b Q (mem Q hQ), e1 P hP, e1 Q hQ]

/-- 51wmmpHand0-34542 (9:35:42) [ex] The fibre over `(η, η)` is `Spec(K(U) ⊗_K K(V))`: the generic
point and the irreducible curves not of the form `U = λ`, `V = λ`. Proved: it is infinite and
contains the curves `V = U^n` (`ex_33562`); its description by `K(U) ⊗ K(V)` is not formalised. -/
theorem ex_34542 (n : ℕ) (hn : 0 < n) :
    tensorProductTo K K[X] K[X] (curvePt K n) = (⟨⊥, Ideal.isPrime_bot⟩, ⟨⊥, Ideal.isPrime_bot⟩) ∧
      ((1 : K[X]) ⊗ₜ[K] X - (X ^ n) ⊗ₜ[K] (1 : K[X])) ∈ (curvePt K n).asIdeal := by
  refine ⟨curvePt_over_generic K n hn, ?_⟩
  simp [curvePt, evExpand, RingHom.mem_ker]

end Line

/-! ### Continuous maps and the topology of products -/

section Topology

/-- 51wmmpHand0-34737 (9:38:57) [prop] For a continuous `φ`, the closure of `φ(x)` is the closure
of the image of the closure of `x` (mathlib: `closure_image_closure`). -/
theorem prop_34737 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {φ : X → Y}
    (hφ : Continuous φ) (x : X) : closure (φ '' closure {x}) = closure {φ x} := by
  rw [closure_image_closure hφ, Set.image_singleton]

/-- 51wmmpHand0-34866 (9:41:06) [cex] Continuous maps between spectra do not all come from ring
homomorphisms: `Spec 𝔽₂ → Spec ℚ` (one point to one point) is continuous, but there is no ring
homomorphism `ℚ → 𝔽₂`. -/
theorem cex_34866 :
    ∃ φ : PrimeSpectrum (ZMod 2) → PrimeSpectrum ℚ, Continuous φ ∧
      ¬ ∃ u : ℚ →+* ZMod 2, comap u = φ := by
  refine ⟨fun _ => ⟨⊥, Ideal.isPrime_bot⟩, continuous_const, ?_⟩
  rintro ⟨u, -⟩
  have h := map_inv₀ u 2
  have h2 : u 2 = 0 := by rw [map_ofNat]; decide
  rw [h2, inv_zero] at h
  have := congrArg u (mul_inv_cancel₀ (two_ne_zero : (2 : ℚ) ≠ 0))
  rw [map_mul, h2, zero_mul, map_one] at this
  exact zero_ne_one this

/-- 51wmmpHand0-34995 (9:43:15) [cex] The topology of `Spec(A ⊗_K B)` is not induced by the product
topology of `Spec A × Spec B`: for `ℂ ⊗_ℝ ℂ`, an inducing map from a `T₀` space would be
injective (`prop_33240`). -/
theorem cex_34995 : ¬ IsInducing (tensorProductTo ℝ ℂ ℂ) := fun h =>
  (prop_33240 (K := ℝ) (A := ℂ) (B := ℂ)).2 h.injective

/-- 51wmmpHand0-35116 (9:45:16) [prop] The `K`-points of `X × Y` are `X(K) × Y(K)`, and the
spectral topology of the product is finer than the product topology: the map
`Spec(A ⊗ B) → Spec A × Spec B` is continuous (mathlib: `PrimeSpectrum.continuous_tensorProductTo`,
`Algebra.TensorProduct.productMap`). -/
theorem prop_35116 (K A B : Type*) [Field K] [CommRing A] [CommRing B] [Algebra K A]
    [Algebra K B] :
    Nonempty ((A ⊗[K] B →ₐ[K] K) ≃ (A →ₐ[K] K) × (B →ₐ[K] K)) ∧
      Continuous (tensorProductTo K A B) :=
  ⟨⟨{ toFun := fun φ => (φ.comp Algebra.TensorProduct.includeLeft,
        φ.comp Algebra.TensorProduct.includeRight)
      invFun := fun ψ => Algebra.TensorProduct.productMap ψ.1 ψ.2
      left_inv := fun φ => Algebra.TensorProduct.ext' fun a b => by simp [← map_mul]
      right_inv := fun ψ => by ext <;> simp }⟩, continuous_tensorProductTo K A B⟩

end Topology

/-! ### Faithfully flat descent -/

section Descent

variable {A : Type*} [CommRing A]

/-- A contracting homotopy `f h - k g = 1` survives `M ⊗ -`. -/
theorem exact_lTensor_of_homotopy {X Y Z : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] [AddCommGroup Z] [Module A Z] (M : Type*) [AddCommGroup M] [Module A M]
    (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (h : Y →ₗ[A] X) (k : Z →ₗ[A] Y)
    (hgf : g ∘ₗ f = 0) (hid : f ∘ₗ h - k ∘ₗ g = LinearMap.id) :
    Function.Exact (f.lTensor M) (g.lTensor M) := by
  have hgf' : (g.lTensor M) ∘ₗ (f.lTensor M) = 0 := by
    rw [← LinearMap.lTensor_comp, hgf, LinearMap.lTensor_zero]
  have hid' : (f.lTensor M) ∘ₗ (h.lTensor M) - (k.lTensor M) ∘ₗ (g.lTensor M) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_sub, hid,
      LinearMap.lTensor_id]
  intro y
  constructor
  · intro hy
    refine ⟨h.lTensor M y, ?_⟩
    have := LinearMap.congr_fun hid' y
    simpa [hy] using this
  · rintro ⟨x, rfl⟩
    exact LinearMap.congr_fun hgf' x

/-- The sequence `A → B → B ⊗_A B` (`s ↦ s ⊗ 1 - 1 ⊗ s`), the Amitsur complex in degrees ≤ 1. -/
abbrev d0 (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B] : A →ₗ[A] B := Algebra.linearMap A B

/-- The first differential `s ↦ s ⊗ 1 - 1 ⊗ s`. -/
abbrev d1 (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B] : B →ₗ[A] B ⊗[A] B :=
  Algebra.TensorProduct.includeLeftSubRight A B

theorem d1_comp_d0 (B : Type*) [CommRing B] [Algebra A B] : d1 A B ∘ₗ d0 A B = 0 := by
  ext; simp

/-- 51wmmpHand0-36474 (10:07:54) [prop] If `A → A'` has a retraction `A' → A`, then
`0 → M → M ⊗ A' → M ⊗ A' ⊗ A'` is exact for every `M` (`H⁰ = M`; degree 0 of the Čech
complex). -/
theorem prop_36474 (B : Type*) [CommRing B] [Algebra A B] (r : B →ₐ[A] A) (M : Type*)
    [AddCommGroup M] [Module A M] :
    Function.Exact ((d0 A B).lTensor M) ((d1 A B).lTensor M) := by
  refine exact_lTensor_of_homotopy M (d0 A B) (d1 A B) r.toLinearMap
    (LinearMap.mul' A B ∘ₗ ((d0 A B ∘ₗ r.toLinearMap).rTensor B)) (d1_comp_d0 (A := A) B) ?_
  ext c
  simp [Algebra.TensorProduct.includeLeftSubRight_apply]

/-- The descent sequence for a faithfully flat `A → B`, after base change to `B`, has the
contracting homotopy `b ⊗ c ↦ bc ⊗ 1`, `b ⊗ c ⊗ d ↦ bc ⊗ d`. -/
theorem exact_baseChange_d (B : Type*) [CommRing B] [Algebra A B] (M : Type*) [AddCommGroup M]
    [Module A M] :
    Function.Exact (((d0 A B).lTensor B).lTensor M) (((d1 A B).lTensor B).lTensor M) := by
  refine exact_lTensor_of_homotopy M ((d0 A B).lTensor B) ((d1 A B).lTensor B)
    ((TensorProduct.rid A B).symm.toLinearMap ∘ₗ LinearMap.mul' A B)
    ((LinearMap.mul' A B).rTensor B ∘ₗ (TensorProduct.assoc A B B B).symm.toLinearMap) ?_ ?_
  · rw [← LinearMap.lTensor_comp, d1_comp_d0, LinearMap.lTensor_zero]
  · refine TensorProduct.ext' fun b c => ?_
    simp [Algebra.TensorProduct.includeLeftSubRight_apply, tmul_sub]

/-- Faithfully flat descent: for `A → B` faithfully flat and every `A`-module `M`, the sequence
`M ⊗ A → M ⊗ B → M ⊗ (B ⊗ B)` is exact. -/
theorem descent_exact (B : Type*) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Exact ((d0 A B).lTensor M) ((d1 A B).lTensor M) := by
  refine Module.FaithfullyFlat.lTensor_reflects_exact A B _ _ ?_
  refine (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := TensorProduct.leftComm A B M A) (e₂ := TensorProduct.leftComm A B M B)
    (e₃ := TensorProduct.leftComm A B M (B ⊗[A] B))
    (f₁₂ := ((d0 A B).lTensor M).lTensor B) (f₂₃ := ((d1 A B).lTensor M).lTensor B) ?_ ?_).1
    (exact_baseChange_d B M)
  · ext b m; simp
  · ext b m c; simp

theorem d0_lTensor_apply (B : Type*) [CommRing B] [Algebra A B] (M : Type*) [AddCommGroup M]
    [Module A M] (y : M ⊗[A] A) :
    (d0 A B).lTensor M y = (TensorProduct.rid A M y) ⊗ₜ[A] (1 : B) := by
  induction y with
  | tmul m a => simp [Algebra.algebraMap_eq_smul_one, smul_tmul]
  | add y z hy hz => simp [hy, hz, add_tmul]

/-- 51wmmpHand0-35250 (9:47:30) [thm] If `A → A'` is faithfully flat,
`0 → M → M ⊗_A A' ⇉ M ⊗_A A' ⊗_A A'` is exact: `m ↦ m ⊗ 1` is injective and its image is the set
of elements with the same image under the two base changes. -/
theorem thm_35250 (B : Type*) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Injective (fun m : M => m ⊗ₜ[A] (1 : B)) ∧
      ∀ x : M ⊗[A] B,
        (Algebra.TensorProduct.includeLeft (S := A)).toLinearMap.lTensor M x =
            (Algebra.TensorProduct.includeRight (R := A) (A := B)).toLinearMap.lTensor M x ↔
          ∃ m : M, m ⊗ₜ[A] (1 : B) = x := by
  refine ⟨fun m m' h => Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) M
    (by simpa using congrArg (TensorProduct.comm A M B) h), fun x => ?_⟩
  have hd : (d1 A B).lTensor M = (Algebra.TensorProduct.includeLeft (S := A)).toLinearMap.lTensor M -
      (Algebra.TensorProduct.includeRight (R := A) (A := B)).toLinearMap.lTensor M := by
    rw [← LinearMap.lTensor_sub]; rfl
  rw [← sub_eq_zero, ← LinearMap.sub_apply, ← hd, descent_exact B M x]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨TensorProduct.rid A M y, (d0_lTensor_apply B M y).symm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m ⊗ₜ 1, by simp⟩

end Descent

/-! ### Čech complexes -/

section Cech

open Limits

variable {C : Type*} [Category C]

/-- 51wmmpHand0-35570 (9:52:50) [prop] If `X' → X` admits finite fibre powers over `X`, these form
an augmented simplicial object of `𝒞/X` (mathlib: `Arrow.augmentedCechNerve`). -/
def prop_35570 (f : Arrow C)
    [∀ n : ℕ, HasWidePullback.{0} f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom] :
    SimplicialObject.Augmented C :=
  f.augmentedCechNerve

/-- 51wmmpHand0-36021 (10:00:21) [prop] For a contravariant functor `F` to abelian groups, the
alternating sum of the faces of `F(X'^{•})` is a complex, the Čech complex of `X'/X` with
coefficients in `F` (mathlib: `AlgebraicTopology.alternatingCofaceMapComplex`). -/
def cechComplex (f : Arrow C)
    [∀ n : ℕ, HasWidePullback.{0} f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{0}) : CochainComplex AddCommGrpCat.{0} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat).obj (f.cechNerve.rightOp ⋙ F)

/-- 51wmmpHand0-36152 (10:02:32) [def] If `X' → X` has a section, the augmented Čech nerve has an
extra degeneracy, so the augmentation is a homotopy equivalence (mathlib:
`Arrow.AugmentedCechNerve.extraDegeneracy`, `ExtraDegeneracy.homotopyEquiv`). -/
def def_36152 (f : Arrow C)
    [∀ n : ℕ, HasWidePullback.{0} f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
    (S : SplitEpi f.hom) : SimplicialObject.Augmented.ExtraDegeneracy f.augmentedCechNerve :=
  Arrow.AugmentedCechNerve.extraDegeneracy f S

example {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
    {X : SimplicialObject.Augmented D} (ed : SimplicialObject.Augmented.ExtraDegeneracy X) :
    HomotopyEquiv (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (SimplicialObject.Augmented.drop.obj X))
      ((ChainComplex.single₀ D).obj (SimplicialObject.Augmented.point.obj X)) :=
  ed.homotopyEquiv

end Cech

section CechAlgebra

variable {A : Type*} [CommRing A]

/-- 51wmmpHand0-36607 (10:10:07) [prop] For `B' = B ⊗_A A'`, the Čech complex of `B'/B` with
coefficients in `M_B` is that of `A'/A` with coefficients in `M` tensored by `B`: in each degree
`B ⊗ (M ⊗ N) ≃ (B ⊗ M) ⊗_B (B ⊗ N)` (mathlib: `AlgebraTensorModule.distribBaseChange`), and the
first differential is compatible with it (mathlib:
`Algebra.TensorProduct.distribBaseChange_comp_includeLeftSubRight`). -/
theorem prop_36607 (A' B : Type*) [CommRing A'] [Algebra A A'] [CommRing B] [Algebra A B] :
    ((TensorProduct.AlgebraTensorModule.distribBaseChange A B A' A').restrictScalars A).toLinearMap
        ∘ₗ (Algebra.TensorProduct.includeLeftSubRight A A').lTensor B =
      (Algebra.TensorProduct.includeLeftSubRight B (B ⊗[A] A')).restrictScalars A :=
  Algebra.TensorProduct.distribBaseChange_comp_includeLeftSubRight B

/-- 51wmmpHand0-36737 (10:12:17) [prop] A flat `B` preserves the exactness of the Čech complex
(cohomology commutes with `⊗_A B`), and for `B` faithfully flat exactness can be checked after
extension to `B` (mathlib: `Module.Flat.lTensor_exact`,
`Module.FaithfullyFlat.lTensor_exact_iff_exact`). -/
theorem prop_36737 (B : Type*) [AddCommGroup B] [Module A B] {N₁ N₂ N₃ : Type*}
    [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂] [Module A N₂] [AddCommGroup N₃]
    [Module A N₃] (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃) :
    (Module.Flat A B → Function.Exact f g → Function.Exact (f.lTensor B) (g.lTensor B)) ∧
      (Module.FaithfullyFlat A B → (Function.Exact (f.lTensor B) (g.lTensor B) ↔
        Function.Exact f g)) :=
  ⟨fun _ h => Module.Flat.lTensor_exact B h,
    fun _ => Module.FaithfullyFlat.lTensor_exact_iff_exact A B f g⟩

/-- 51wmmpHand0-36802 (10:13:22) [thm] If `A'` is faithfully flat over `A`, `M → H⁰(A'/A, M)` is
an isomorphism (degree 0 of the Čech complex; `descent_exact`, proved by base change to `A'`,
where the diagonal splits). -/
theorem thm_36802 (B : Type*) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Injective ((d0 A B).lTensor M) ∧
      Function.Exact ((d0 A B).lTensor M) ((d1 A B).lTensor M) := by
  refine ⟨fun y z h => (TensorProduct.rid A M).injective ((thm_35250 (A := A) B M).1 ?_), descent_exact B M⟩
  simpa only [d0_lTensor_apply] using h

/-- 51wmmpHand0-36939 (10:15:39) [prop] If the `f_i` generate the unit ideal, the Čech complex of
the covering by the `X_{f_i}` with coefficients `M_f` is exact in degree 0: `M → ∏ M_{f_i}` is
injective (mathlib: `Module.eq_of_isLocalized_span`); the gluing half is the sheaf property of
`M~` (mathlib: `AlgebraicGeometry.tilde`). -/
theorem prop_36939 (M : Type*) [AddCommGroup M] [Module A M] (s : Set A)
    (hs : Ideal.span s = ⊤) (x y : M)
    (h : ∀ r : s, LocalizedModule.mkLinearMap (Submonoid.powers r.1) M x =
      LocalizedModule.mkLinearMap (Submonoid.powers r.1) M y) : x = y :=
  Module.eq_of_isLocalized_span s hs
    (fun r => LocalizedModule (Submonoid.powers r.1) M)
    (fun r => LocalizedModule.mkLinearMap (Submonoid.powers r.1) M) x y h

/-- 51wmmpHand0-37263 (10:21:03) [prop] If `f_1, …, f_n` generate the unit ideal,
`A → ∏ A_{f_i}` is faithfully flat. -/
theorem prop_37263 {ι : Type*} [Fintype ι] (f : ι → A) (hf : Ideal.span (Set.range f) = ⊤) :
    Module.FaithfullyFlat A (Π i, Localization.Away (f i)) := by
  classical
  have : ∀ i, Module.Flat A (Localization.Away (f i)) := fun i =>
    IsLocalization.flat _ (Submonoid.powers (f i))
  have : Module.Flat A (Π i, Localization.Away (f i)) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype A ι _).symm
  refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
  obtain ⟨i, hi⟩ : ∃ i, f i ∉ p.asIdeal := by
    by_contra! h
    exact p.isPrime.ne_top (top_le_iff.1 (hf ▸ Ideal.span_le.2 (Set.range_subset_iff.2 h)))
  obtain ⟨q, hq⟩ : p ∈ Set.range (comap (algebraMap A (Localization.Away (f i)))) := by
    rw [localization_away_comap_range _ (f i)]; exact hi
  refine ⟨comap (Pi.evalRingHom (fun j => Localization.Away (f j)) i) q, ?_⟩
  rw [← hq, ← comap_comp_apply]
  rfl

/-- 51wmmpHand0-37457 (10:24:17) [prop] `X_f ↦ M_f` is a sheaf `M~` on `Spec A`, with
`M~(X_f) = M_f` (mathlib: `AlgebraicGeometry.tilde`, a sheaf of modules, and its sections over
`D(f)` are a localization `M_f`). The acyclicity `H^i(Spec A, M~) = 0` is not formalised. -/
example {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f : R) :
    IsLocalizedModule.Away f (AlgebraicGeometry.tilde.toOpen M (basicOpen f)).hom :=
  inferInstance

/-- 51wmmpHand0-37586 (10:26:26) [prop] The diagonal `Spec A → Spec A × Spec A` is a closed
immersion, because `A ⊗_K A → A`, `x ⊗ y ↦ xy`, is surjective. -/
theorem prop_37586 (K : Type*) [CommRing K] [Algebra K A] :
    Function.Surjective (Algebra.TensorProduct.lmul' K : A ⊗[K] A →ₐ[K] A) ∧
      IsClosedEmbedding (comap (Algebra.TensorProduct.lmul' K : A ⊗[K] A →ₐ[K] A).toRingHom) := by
  have hs : Function.Surjective (Algebra.TensorProduct.lmul' K : A ⊗[K] A →ₐ[K] A) :=
    fun a => ⟨a ⊗ₜ 1, by simp⟩
  exact ⟨hs, isClosedEmbedding_comap_of_surjective _ _ hs⟩

/-- 51wmmpHand0-37650 (10:27:30) [prop] A finitely presented module is flat iff it is projective
(finitely generated), iff it is free at every point of `Spec A`, i.e. `M~` locally free (mathlib:
`Module.Flat.projective_of_finitePresentation`, `Module.freeLocus_eq_univ_iff`; a free stalk
spreads to a free `M_f` on a neighbourhood: `Module.basicOpen_subset_freeLocus_iff`). -/
theorem prop_37650 (M : Type*) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] :
    (Module.Flat A M ↔ Module.Projective A M) ∧
      (Module.Projective A M ↔ Module.freeLocus A M = Set.univ) :=
  ⟨⟨fun _ => Module.Flat.projective_of_finitePresentation, fun _ => inferInstance⟩,
    Module.freeLocus_eq_univ_iff.symm⟩

end CechAlgebra

end

end Buffalo.AG.Part03
