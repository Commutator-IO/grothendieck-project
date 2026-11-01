import Mathlib

/-!
# Bourbaki, rédaction n° 398 (April 1963): duality of finite-length modules over a PID

Rédaction n° 398 of the Bourbaki archive (Archives Henri Poincaré, item 949) is a short
« contre-rédaction » answering rédaction n° 397. It deliberately avoids injective modules and
treats only modules of finite length over a principal ideal domain `A` with fraction field `K`.
The dual of an `A`-module `E` is `E* = Hom(E, K/A)`, and the evaluation pairing gives a canonical
map `i_E : E → E**`. Its Prop. 1 states that, for `E` of finite length, `E*` is isomorphic (not
canonically) to `E` and `i_E` is an isomorphism; the proof reduces, by the structure theorem, to
a cyclic module `A/tA`, whose dual is the submodule `t⁻¹A/A` of `K/A`. Prop. 2 states that `*` is
exact on finite-length modules, and Prop. 3 that `F ↦ F⁰` is an inclusion-reversing bijection
between submodules of `E` and of `E*`, exchanging sums and intersections. For `A = ℤ` this is the
duality of finite abelian groups with values in `ℚ/ℤ`.

This is the principal-ideal-domain case of Matlis duality. mathlib has the case of finite abelian
groups with complex-valued characters (`AddChar.doubleDualEquiv`), not the statement over a
general principal ideal domain. A module of finite length is encoded as a finitely generated
torsion module (`Module.Finite` and `Module.IsTorsion`), and `K/A` as the quotient of `K` by the
range of `Algebra.linearMap`.

The proofs here do use that `K/A` is injective (it is divisible, hence satisfies Baer's criterion,
as in rédaction n° 397): this gives injectivity of `i_E` and Prop. 2 directly; bijectivity of
`i_E` then follows because `E** ≅ E` and an injective endomorphism of an Artinian module is
surjective, in place of the typescript's reduction to the cyclic case.

* `KModA`, `Dual`: the module `K/A` and the dual `E* = E →ₗ[A] K/A`;
* `range_evalOne`: evaluation at `1` identifies `(A/tA)*` with the part of `K/A` killed by `t`;
* `dualQuotEquiv`: Prop. 1 in the cyclic case, `(A/tA)* ≃ A/tA` for `t ≠ 0`;
* `nonempty_dual_equiv`: Prop. 1, `E* ≃ E` for every finite-length `E`;
* `evalDual`, `evalDual_injective`, `evalDual_bijective`, `evalDualEquiv`: the canonical map
  `E → E**`, injective for torsion `E` and bijective for finite-length `E`;
* `baer`, `dual_surjective_of_injective`, `dual_exact`: `K/A` is injective, and Prop. 2 (here for
  arbitrary modules);
* `orth`, `orth'`, `orthOrderIso`, `orth_sup`, `orth_inf`: Prop. 3, the orthogonality bijection
  as an order anti-isomorphism, exchanging sums and intersections.
-/

namespace Bourbaki.Redaction398

open Module

variable (A : Type*) [CommRing A] (K : Type*) [Field K] [Algebra A K]

/-- The `A`-module `K/A`, quotient of the fraction field by the image of `A`. -/
abbrev KModA : Type _ := K ⧸ LinearMap.range (Algebra.linearMap A K)

/-- The dual `E* = Hom(E, K/A)` of an `A`-module `E`. -/
abbrev Dual (E : Type*) [AddCommGroup E] [Module A E] : Type _ := E →ₗ[A] KModA A K

variable {A K}

variable (K) in
/-- The orthogonal `F⁰ ⊆ E*` of a submodule `F ⊆ E`. -/
def orth {E : Type*} [AddCommGroup E] [Module A E] (F : Submodule A E) :
    Submodule A (Dual A K E) where
  carrier := {φ | ∀ x ∈ F, φ x = 0}
  add_mem' hφ hψ x hx := by simp [hφ x hx, hψ x hx]
  zero_mem' _ _ := rfl
  smul_mem' a φ hφ x hx := by simp [hφ x hx]

/-- The orthogonal in `E` of a submodule `G ⊆ E*`. -/
def orth' {E : Type*} [AddCommGroup E] [Module A E] (G : Submodule A (Dual A K E)) :
    Submodule A E where
  carrier := {x | ∀ φ ∈ G, φ x = 0}
  add_mem' hx hy φ hφ := by simp [hx φ hφ, hy φ hφ]
  zero_mem' _ _ := map_zero _
  smul_mem' a x hx φ hφ := by simp [hx φ hφ]

/-- The orthogonal in `E` of a sum of submodules of `E*` is the intersection of the
orthogonals. -/
theorem orth'_sup {E : Type*} [AddCommGroup E] [Module A E] (G G' : Submodule A (Dual A K E)) :
    orth' (G ⊔ G') = orth' G ⊓ orth' G' := by
  ext x
  refine ⟨fun h => ⟨fun φ hφ => h φ (Submodule.mem_sup_left hφ),
    fun φ hφ => h φ (Submodule.mem_sup_right hφ)⟩, fun ⟨h, h'⟩ φ hφ => ?_⟩
  obtain ⟨ψ, hψ, ψ', hψ', rfl⟩ := Submodule.mem_sup.1 hφ
  simp [h ψ hψ, h' ψ' hψ']

/-- Prop. 3: the orthogonal of a sum is the intersection of the orthogonals. -/
theorem orth_sup {E : Type*} [AddCommGroup E] [Module A E] (F F' : Submodule A E) :
    orth K (F ⊔ F') = orth K F ⊓ orth K F' := by
  ext φ
  refine ⟨fun h => ⟨fun x hx => h x (Submodule.mem_sup_left hx),
    fun x hx => h x (Submodule.mem_sup_right hx)⟩, fun ⟨h, h'⟩ x hx => ?_⟩
  obtain ⟨y, hy, y', hy', rfl⟩ := Submodule.mem_sup.1 hx
  simp [h y hy, h' y' hy']

/-- A class `k mod A` vanishes in `K/A` exactly when `k` comes from `A`. -/
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

/-- A linear form on `A/tA` is determined by its value at the class of `1`. -/
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

/-- For `t ≠ 0`, the kernel of `a ↦ a/t mod A` is `tA`. -/
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

/-- For `t ≠ 0`, the image of `a ↦ a/t mod A` is the submodule `t⁻¹A/A` of `K/A` killed
by `t`. -/
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

/-- **Prop. 2.** The functor `*` is exact: if `E' → E → E''` is exact, so is
`E''* → E* → E'*`. (Since `K/A` is injective, no finiteness is needed here.) -/
theorem dual_exact {E' E E'' : Type*} [AddCommGroup E'] [Module A E'] [AddCommGroup E]
    [Module A E] [AddCommGroup E''] [Module A E''] {f : E' →ₗ[A] E} {g : E →ₗ[A] E''}
    (hfg : Function.Exact f g) :
    Function.Exact (fun ψ : Dual A K E'' => ψ ∘ₗ g) (fun φ : Dual A K E => φ ∘ₗ f) := by
  intro φ
  constructor
  · intro hφ
    have hle : LinearMap.ker g ≤ LinearMap.ker φ := fun x hx => by
      obtain ⟨y, rfl⟩ := (hfg x).1 hx
      exact LinearMap.congr_fun hφ y
    obtain ⟨ψ, hψ⟩ := (baer (A := A) (K := K)).extension_property (LinearMap.range g).subtype
      (Submodule.injective_subtype _)
      (((LinearMap.ker g).liftQ φ hle).comp g.quotKerEquivRange.symm.toLinearMap)
    refine ⟨ψ, LinearMap.ext fun x => ?_⟩
    have := LinearMap.congr_fun hψ ⟨g x, LinearMap.mem_range_self g x⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
      Submodule.liftQ_apply] at this
    exact this
  · rintro ⟨ψ, rfl⟩
    simp only [LinearMap.comp_assoc, hfg.linearMap_comp_eq_zero, LinearMap.comp_zero]

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

/-- Over a torsion module, linear forms with values in `K/A` separate points from submodules. -/
theorem exists_separating {E : Type*} [AddCommGroup E] [Module A E] (hE : Module.IsTorsion A E)
    (F : Submodule A E) {x : E} (hx : x ∉ F) : ∃ φ ∈ orth K F, φ x ≠ 0 := by
  have hQ : Module.IsTorsion A (E ⧸ F) := fun y => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨a, ha⟩ := @hE y
    exact ⟨a, by rw [← Submodule.Quotient.mk_smul, ha, Submodule.Quotient.mk_zero]⟩
  have h0 : (Submodule.Quotient.mk x : E ⧸ F) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hne : evalDual (A := A) K (E ⧸ F) (Submodule.Quotient.mk x) ≠ 0 :=
    fun h => h0 (evalDual_injective hQ (h.trans (map_zero _).symm))
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Dual A K (E ⧸ F), ψ (Submodule.Quotient.mk x) ≠ 0 := by
    by_contra! h
    exact hne (LinearMap.ext h)
  refine ⟨ψ ∘ₗ F.mkQ, fun y hy => ?_, hψ⟩
  simp [(Submodule.Quotient.mk_eq_zero F).2 hy]

/-- For `E` torsion, `F⁰⁰ = F`: the orthogonal in `E` of `F⁰` is `F`. -/
theorem orth'_orth {E : Type*} [AddCommGroup E] [Module A E] (hE : Module.IsTorsion A E)
    (F : Submodule A E) : orth' (orth K F) = F := by
  refine le_antisymm (fun x hx => ?_) fun x hx φ hφ => hφ x hx
  by_contra h
  obtain ⟨φ, hφ, hφx⟩ := exists_separating (K := K) hE F h
  exact hφx (hx φ hφ)

/-- The dual of a finite-length module is again torsion (it is isomorphic to the module). -/
theorem dual_isTorsion (E : Type*) [AddCommGroup E] [Module A E] [Module.Finite A E]
    (hE : Module.IsTorsion A E) : Module.IsTorsion A (Dual A K E) := fun φ => by
  obtain ⟨d⟩ := nonempty_dual_equiv K E hE
  obtain ⟨a, ha⟩ := @hE (d φ)
  refine ⟨a, d.injective ?_⟩
  rw [Submonoid.smul_def] at ha ⊢
  rw [map_smul, ha, map_zero]

/-- For `E` of finite length, every submodule `G` of `E*` is the orthogonal of its own
orthogonal in `E`. -/
theorem orth_orth' {E : Type*} [AddCommGroup E] [Module A E] [Module.Finite A E]
    (hE : Module.IsTorsion A E) (G : Submodule A (Dual A K E)) : orth K (orth' G) = G := by
  refine le_antisymm (fun φ hφ => ?_) fun φ hφ x hx => hx φ hφ
  by_contra h
  obtain ⟨Φ, hΦ, hΦφ⟩ := exists_separating (K := K) (dual_isTorsion (K := K) E hE) G h
  obtain ⟨x, rfl⟩ := (evalDual_bijective (K := K) E hE).2 Φ
  exact hΦφ (hφ x fun ψ hψ => hΦ ψ hψ)

variable (K) in
/-- **Prop. 3.** For `E` of finite length, `F ↦ F⁰` is an inclusion-reversing bijection from the
submodules of `E` onto those of `E*`. -/
def orthOrderIso (E : Type*) [AddCommGroup E] [Module A E] [Module.Finite A E]
    (hE : Module.IsTorsion A E) : Submodule A E ≃o (Submodule A (Dual A K E))ᵒᵈ where
  toFun F := OrderDual.toDual (orth K F)
  invFun G := orth' (OrderDual.ofDual G)
  left_inv F := orth'_orth (K := K) hE F
  right_inv G := orth_orth' hE (OrderDual.ofDual G)
  map_rel_iff' {F F'} := by
    refine ⟨fun h => ?_, fun h φ hφ x hx => hφ x (h hx)⟩
    rw [← orth'_orth (K := K) hE F, ← orth'_orth (K := K) hE F']
    exact fun x hx φ hφ => hx φ (h hφ)

/-- Prop. 3: for `E` of finite length, the orthogonal of an intersection is the sum of the
orthogonals. -/
theorem orth_inf {E : Type*} [AddCommGroup E] [Module A E] [Module.Finite A E]
    (hE : Module.IsTorsion A E) (F F' : Submodule A E) :
    orth K (F ⊓ F') = orth K F ⊔ orth K F' := by
  conv_lhs => rw [← orth'_orth (K := K) hE F, ← orth'_orth (K := K) hE F', ← orth'_sup]
  exact orth_orth' hE _

end Bourbaki.Redaction398
