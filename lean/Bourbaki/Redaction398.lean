import Mathlib

namespace Bourbaki.Redaction398

open Module

variable (A : Type*) [CommRing A] (K : Type*) [Field K] [Algebra A K]

/-- The `A`-module `K/A`, quotient of the fraction field by the image of `A`. -/
abbrev KModA : Type _ := K ⧸ LinearMap.range (Algebra.linearMap A K)

/-- The dual `E* = Hom(E, K/A)` of an `A`-module `E`. -/
abbrev Dual (E : Type*) [AddCommGroup E] [Module A E] : Type _ := E →ₗ[A] KModA A K

variable {A K}

theorem mk_eq_zero_iff (k : K) :
    (Submodule.Quotient.mk k : KModA A K) = 0 ↔ ∃ a : A, algebraMap A K a = k := by
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  simp [Algebra.linearMap_apply]

variable (K) in
/-- The map `a ↦ a/t mod A`, from `A` to `K/A`. -/
noncomputable def divBy (t : A) : A →ₗ[A] KModA A K :=
  LinearMap.toSpanSingleton A _ (Submodule.Quotient.mk (algebraMap A K t)⁻¹)

theorem divBy_apply (t a : A) :
    divBy K t a = Submodule.Quotient.mk (algebraMap A K a * (algebraMap A K t)⁻¹) := by
  rw [divBy, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul, Algebra.smul_def]

variable (K) in
/-- Evaluation at the class of `1`, from `(A/tA)*` to `K/A`. -/
noncomputable def evalOne (t : A) : Dual A K (A ⧸ Ideal.span {t}) →ₗ[A] KModA A K :=
  LinearMap.applyₗ (Submodule.Quotient.mk 1)

theorem evalOne_injective (t : A) : Function.Injective (evalOne K t) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => LinearMap.ext fun y => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have : (Submodule.Quotient.mk a : A ⧸ Ideal.span {t}) = a • Submodule.Quotient.mk 1 := by
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  simp only [evalOne, LinearMap.applyₗ_apply_apply] at hf
  rw [this, map_smul, hf, smul_zero, LinearMap.zero_apply]

/-- The dual of `A/tA` is identified, by evaluation at `1`, with the submodule of `K/A` killed
by `t`, that is with `t⁻¹A/A`. -/
theorem range_evalOne (t : A) :
    LinearMap.range (evalOne K t) = Submodule.torsionBy A (KModA A K) t := by
  ext q
  rw [LinearMap.mem_range, Submodule.mem_torsionBy_iff]
  constructor
  · rintro ⟨f, rfl⟩
    simp only [evalOne, LinearMap.applyₗ_apply_apply]
    rw [← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
      (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton_self t), map_zero]
  · intro hq
    have hle : Ideal.span {t} ≤ LinearMap.ker (LinearMap.toSpanSingleton A _ q) := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
        LinearMap.toSpanSingleton_apply, hq]
    refine ⟨(Ideal.span {t}).liftQ _ hle, ?_⟩
    simp only [evalOne, LinearMap.applyₗ_apply_apply]
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]

variable [IsFractionRing A K]

theorem ker_divBy {t : A} (ht : t ≠ 0) : LinearMap.ker (divBy K t) = Ideal.span {t} := by
  have ht' : algebraMap A K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ht
  ext a
  rw [LinearMap.mem_ker, divBy_apply, mk_eq_zero_iff, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, IsFractionRing.injective A K ?_⟩
    rw [map_mul, hb, inv_mul_cancel_right₀ ht']
  · rintro ⟨b, rfl⟩
    exact ⟨b, by rw [map_mul, mul_inv_cancel_right₀ ht']⟩

theorem range_divBy {t : A} (ht : t ≠ 0) :
    LinearMap.range (divBy K t) = Submodule.torsionBy A (KModA A K) t := by
  have ht' : algebraMap A K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ht
  ext q
  rw [LinearMap.mem_range, Submodule.mem_torsionBy_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rw [divBy_apply, ← Submodule.Quotient.mk_smul, Algebra.smul_def, mk_eq_zero_iff]
    exact ⟨a, by field_simp⟩
  · intro hq
    obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, mk_eq_zero_iff] at hq
    obtain ⟨b, hb⟩ := hq
    refine ⟨b, ?_⟩
    rw [divBy_apply, hb]
    congr 1
    field_simp

/-- `K/A` is divisible: every `r ≠ 0` acts surjectively. -/
theorem divisible {r : A} (hr : r ≠ 0) : Function.Surjective (fun q : KModA A K => r • q) := by
  have hr' : algebraMap A K r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hr
  intro q
  obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨Submodule.Quotient.mk ((algebraMap A K r)⁻¹ * k), ?_⟩
  simp only
  rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, mul_inv_cancel_left₀ hr']

variable (K) in
/-- **Prop. 1, cyclic case.** For `t ≠ 0`, the dual of `A/tA` is isomorphic to `A/tA`. -/
noncomputable def dualQuotEquiv {t : A} (ht : t ≠ 0) :
    Dual A K (A ⧸ Ideal.span {t}) ≃ₗ[A] A ⧸ Ideal.span {t} :=
  (LinearEquiv.ofInjective _ (evalOne_injective t)).trans <|
    (LinearEquiv.ofEq _ _ ((range_evalOne t).trans (range_divBy ht).symm)).trans <|
    (LinearMap.quotKerEquivRange (divBy K t)).symm.trans <|
    Submodule.quotEquivOfEq _ _ (ker_divBy ht)

variable [IsPrincipalIdealRing A]

/-- `K/A` satisfies Baer's criterion: a map from the ideal `(a)` extends by `r ↦ r • q`, where
`a • q` is the image of `a`. -/
theorem baer : Module.Baer A (KModA A K) := by
  intro I g
  obtain ⟨a, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
  by_cases ha : a = 0
  · refine ⟨0, fun x hx => ?_⟩
    subst ha
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    simp only [LinearMap.zero_apply]
    rw [show (⟨0, hx⟩ : Ideal.span ({0} : Set A)) = 0 from rfl, map_zero]
  · obtain ⟨q, hq⟩ := divisible ha (g ⟨a, Ideal.mem_span_singleton_self a⟩)
    refine ⟨LinearMap.toSpanSingleton A _ q, fun x hx => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    have : (⟨c * a, hx⟩ : Ideal.span ({a} : Set A)) = c • ⟨a, Ideal.mem_span_singleton_self a⟩ :=
      rfl
    simp only [LinearMap.toSpanSingleton_apply, this, map_smul]
    rw [← hq, smul_smul]

/-- Part of Prop. 2: restriction along an injective map is surjective on duals (every linear
form `L → K/A` extends along `L → M`, since `K/A` is injective). -/
theorem dual_surjective_of_injective {L M : Type*} [AddCommGroup L] [Module A L]
    [AddCommGroup M] [Module A M] (i : L →ₗ[A] M) (hi : Function.Injective i) :
    Function.Surjective (fun f : Dual A K M => f ∘ₗ i) := fun g =>
  (baer (A := A) (K := K)).extension_property i hi g

variable [IsDomain A]

variable (K) in
/-- **Prop. 1, first half.** A finitely generated torsion module over a principal ideal domain
(that is, a module of finite length) is isomorphic to its dual. -/
theorem nonempty_dual_equiv (E : Type*) [AddCommGroup E] [Module A E] [Module.Finite A E]
    (hE : Module.IsTorsion A E) : Nonempty (Dual A K E ≃ₗ[A] E) := by
  classical
  obtain ⟨ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_directSum_of_isTorsion hE
  have hne : ∀ i, p i ^ e i ≠ 0 := fun i => pow_ne_zero _ (hp i).ne_zero
  let M := fun i => A ⧸ A ∙ p i ^ e i
  exact ⟨(f.arrowCongr (LinearEquiv.refl A (KModA A K))).trans <|
    ((DirectSum.linearEquivFunOnFintype A ι M).arrowCongr (LinearEquiv.refl _ _)).trans <|
    (LinearMap.lsum A M A).symm.trans <|
    (LinearEquiv.piCongrRight fun i => dualQuotEquiv K (hne i)).trans <|
    (DirectSum.linearEquivFunOnFintype A ι M).symm.trans f.symm⟩


variable (K) in
/-- The canonical map `i_E : E → E**`, `x ↦ (x* ↦ x*(x))`. -/
noncomputable def evalDual (E : Type*) [AddCommGroup E] [Module A E] :
    E →ₗ[A] Dual A K (Dual A K E) :=
  LinearMap.applyₗ

/-- `i_E` is injective on every torsion module: for `x ≠ 0` with annihilator `(s)`, the map
`a • x ↦ a/s mod A` is nonzero at `x` and extends to `E` because `K/A` is injective. -/
theorem evalDual_injective {E : Type*} [AddCommGroup E] [Module A E]
    (hE : Module.IsTorsion A E) : Function.Injective (evalDual (A := A) K E) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  by_contra hx0
  obtain ⟨s, hs⟩ := (IsPrincipalIdealRing.principal (Ideal.torsionOf A E x)).principal
  have hs0 : s ≠ 0 := by
    rintro rfl
    obtain ⟨⟨a, ha⟩, hax⟩ := @hE x
    have : a ∈ Ideal.torsionOf A E x := (Ideal.mem_torsionOf_iff x a).2 hax
    rw [hs] at this
    have : a = 0 := by simpa using this
    exact nonZeroDivisors.ne_zero ha this
  set u : KModA A K := Submodule.Quotient.mk (algebraMap A K s)⁻¹
  have hs' : algebraMap A K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hs0
  have hle : Ideal.torsionOf A E x ≤ LinearMap.ker (LinearMap.toSpanSingleton A _ u) := by
    rw [hs, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul, Algebra.smul_def,
      mul_inv_cancel₀ hs', mk_eq_zero_iff]
    exact ⟨1, map_one _⟩
  let φ₀ : (A ∙ x) →ₗ[A] KModA A K := ((Ideal.torsionOf A E x).liftQ _ hle).comp
    (Ideal.quotTorsionOfEquivSpanSingleton A E x).symm.toLinearMap
  have hφ₀ : φ₀ ⟨x, Submodule.mem_span_singleton_self x⟩ = u := by
    have : (Ideal.quotTorsionOfEquivSpanSingleton A E x).symm
        ⟨x, Submodule.mem_span_singleton_self x⟩ = Submodule.Quotient.mk 1 := by
      rw [LinearEquiv.symm_apply_eq, Ideal.quotTorsionOfEquivSpanSingleton_apply_mk, one_smul]
    simp only [φ₀, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply,
      LinearMap.toSpanSingleton_apply, one_smul]
  obtain ⟨φ, hφ⟩ := (baer (A := A) (K := K)).extension_property (A ∙ x).subtype
    (Submodule.injective_subtype _) φ₀
  have h1 : φ x = u := by rw [← hφ₀, ← hφ]; rfl
  have h2 : φ x = 0 := by simpa [evalDual] using LinearMap.congr_fun hx φ
  obtain ⟨b, hb⟩ := (mk_eq_zero_iff _).1 (h1.symm.trans h2)
  have h3 : (1 : A) ∈ Ideal.torsionOf A E x := by
    rw [hs, Ideal.mem_span_singleton']
    exact ⟨b, IsFractionRing.injective A K (by rw [map_mul, hb, map_one, inv_mul_cancel₀ hs'])⟩
  exact hx0 (by simpa using (Ideal.mem_torsionOf_iff x 1).1 h3)

/-- Finitely generated torsion modules over a principal ideal domain are Artinian. -/
theorem isArtinian_of_isTorsion (E : Type*) [AddCommGroup E] [Module A E] [Module.Finite A E]
    (hE : Module.IsTorsion A E) : IsArtinian A E := by
  classical
  obtain ⟨ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_directSum_of_isTorsion hE
  have hM : ∀ i, IsArtinian A (A ⧸ A ∙ p i ^ e i) := fun i =>
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (isFiniteLength_quotient_span_singleton A
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (hp i).ne_zero)))).2
  exact isArtinian_of_linearEquiv ((DirectSum.linearEquivFunOnFintype A ι _).symm.trans f.symm)

/-- **Prop. 1, second half.** For a finitely generated torsion module `E` over a principal ideal
domain, the canonical map `i_E : E → E**` is bijective. -/
theorem evalDual_bijective (E : Type*) [AddCommGroup E] [Module A E] [Module.Finite A E]
    (hE : Module.IsTorsion A E) : Function.Bijective (evalDual (A := A) K E) := by
  obtain ⟨d⟩ := nonempty_dual_equiv K E hE
  let d₂ : Dual A K (Dual A K E) ≃ₗ[A] E := (d.arrowCongr (LinearEquiv.refl _ _)).trans d
  have hinj := evalDual_injective (K := K) hE
  have := isArtinian_of_isTorsion E hE
  have hsurj := IsArtinian.surjective_of_injective_endomorphism
    (d₂.toLinearMap ∘ₗ evalDual K E) (d₂.injective.comp hinj)
  refine ⟨hinj, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hsurj (d₂ y)
  exact ⟨x, d₂.injective hx⟩

variable (K) in
/-- The canonical isomorphism `E ≃ E**` of Prop. 1. -/
noncomputable def evalDualEquiv (E : Type*) [AddCommGroup E] [Module A E] [Module.Finite A E]
    (hE : Module.IsTorsion A E) : E ≃ₗ[A] Dual A K (Dual A K E) :=
  LinearEquiv.ofBijective _ (evalDual_bijective E hE)

end Bourbaki.Redaction398
