import Buffalo.AG.Part02

/-!
# Buffalo, algebraic geometry, part 04 (a): 12–13 June 1973, stalks, localization, local rings

The entries of `docs/buffalo-ag/index.tex` lines 492–516 (video `thSz9ZHDK9o`, 1:39:49–2:23:44):
the stalks of `M^~` and of `𝒪_X` on `Spec A`, localization of modules and rings at a
multiplicative subset and its universal properties, local rings and their characterisations,
`M ↦ M^~` and infinite products, and the completion of a noetherian local ring.
-/

open CategoryTheory IsLocalRing TensorProduct

universe u

namespace Buffalo.AG.Part04

noncomputable section

/-! ### Stalks and localization -/

/-- thSz9ZHDK9o-5989 (1:39:49) [prop] The fibre of `M^~` at the point `x` associated to `𝔭` is
`M_𝔭`: the map `M → (M^~)_x` is a localization of `M` at `A ∖ 𝔭`. (The stalk is by definition
the colimit over the open neighbourhoods of `x`, among which the `D(f)`, `f ∉ 𝔭`, are cofinal.) -/
theorem prop_5989 {A : CommRingCat.{u}} (M : ModuleCat.{u} A)
    (x : AlgebraicGeometry.PrimeSpectrum.Top A) :
    IsLocalizedModule x.asIdeal.primeCompl (AlgebraicGeometry.tilde.toStalk M x).hom :=
  inferInstance

/-- thSz9ZHDK9o-6117 (1:41:57) [prop] The fibre of `𝒪_X` at `x = 𝔭` is `A_𝔭`. -/
theorem prop_6117 (A : Type u) [CommRing A] (x : PrimeSpectrum A) :
    IsLocalization.AtPrime ((AlgebraicGeometry.Spec.structureSheaf A).presheaf.stalk x) x.asIdeal :=
  AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk A x

/-- thSz9ZHDK9o-6181 (1:43:01) [def] For a multiplicative subset `T ⊂ A`, `M T⁻¹` is a module over
the algebra `A T⁻¹`; for `T = {fⁿ}` one recovers `M_f`. -/
example {A : Type u} [CommRing A] (T : Submonoid A) (M : Type u) [AddCommGroup M] [Module A M] :
    Module (Localization T) (LocalizedModule T M) := inferInstance

example {A : Type u} [CommRing A] (f : A) (M : Type u) [AddCommGroup M] [Module A M] :
    IsLocalizedModule.Away f (LocalizedModule.mkLinearMap (Submonoid.powers f) M) :=
  inferInstance

/-- thSz9ZHDK9o-6246 (1:44:06) [prop] `M → M T⁻¹` is universal among the `A`-linear maps `M → N`
such that multiplication by each `f ∈ T` is bijective on `N`. -/
theorem prop_6246 {A : Type u} [CommRing A] (T : Submonoid A) (M N : Type u) [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (g : M →ₗ[A] N)
    (hg : ∀ t : T, IsUnit (algebraMap A (Module.End A N) t)) :
    ∃! l : LocalizedModule T M →ₗ[A] N, l ∘ₗ LocalizedModule.mkLinearMap T M = g :=
  IsLocalizedModule.is_universal T (LocalizedModule.mkLinearMap T M) g hg

/-- The multiplication by `t` is bijective on `N` exactly when it is a unit of `End N`. -/
example {A : Type u} [CommRing A] (N : Type u) [AddCommGroup N] [Module A N] (t : A) :
    IsUnit (algebraMap A (Module.End A N) t) ↔ Function.Bijective (fun n : N => t • n) :=
  Module.End.isUnit_iff _

/-- thSz9ZHDK9o-6375 (1:46:15) [prop] `A → A T⁻¹` is universal among the homomorphisms `A → B`
that make the elements of `T` invertible. -/
theorem prop_6375 {A B : Type u} [CommRing A] [CommRing B] (T : Submonoid A) (g : A →+* B)
    (hg : ∀ t : T, IsUnit (g t)) :
    ∃! l : Localization T →+* B, l.comp (algebraMap A (Localization T)) = g :=
  ⟨IsLocalization.lift hg, IsLocalization.lift_comp hg, fun _ hl =>
    IsLocalization.ringHom_ext T (hl.trans (IsLocalization.lift_comp hg).symm)⟩

/-- thSz9ZHDK9o-6568 (1:49:28) [prop] `M T⁻¹ ≃ M ⊗_A A T⁻¹` (written `A T⁻¹ ⊗_A M`). -/
def prop_6568 {A : Type u} [CommRing A] (T : Submonoid A) (M : Type u) [AddCommGroup M]
    [Module A M] :
    Localization T ⊗[A] M ≃ₗ[Localization T] LocalizedModule T M :=
  (IsLocalizedModule.isBaseChange T (Localization T) (LocalizedModule.mkLinearMap T M)).equiv

/-- thSz9ZHDK9o-6632 (1:50:32) [prop] `A_𝔭` is local, with residue field `κ(𝔭) = Frac(A/𝔭)`. -/
theorem prop_6632 {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] :
    IsLocalRing (Localization.AtPrime p) ∧ IsFractionRing (A ⧸ p) p.ResidueField :=
  ⟨inferInstance, inferInstance⟩

/-! ### Local rings -/

/-- thSz9ZHDK9o-6702 (1:51:42) [def] A ring is local if it has a unique maximal ideal (mathlib's
`IsLocalRing`); its residue field is `O/𝔪` (`IsLocalRing.ResidueField`). -/
theorem def_6702 (O : Type u) [CommRing O] : IsLocalRing O ↔ ∃! I : Ideal O, I.IsMaximal :=
  ⟨fun _ => ⟨maximalIdeal O, inferInstance, fun _ hI => IsLocalRing.eq_maximalIdeal hI⟩,
    IsLocalRing.of_unique_max_ideal⟩

example (O : Type u) [CommRing O] [IsLocalRing O] :
    ResidueField O = (O ⧸ maximalIdeal O) := rfl

/-- thSz9ZHDK9o-6764 (1:52:44) [prop] An element is invertible iff it belongs to no maximal
ideal; in a local ring, `O^* = O ∖ 𝔪`. -/
theorem prop_6764 {O : Type u} [CommRing O] (a : O) :
    IsUnit a ↔ ∀ m : Ideal O, m.IsMaximal → a ∉ m := by
  constructor
  · intro ha m hm ham
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ ham ha)
  · intro h
    by_contra ha
    have : Ideal.span {a} ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ this
    exact h m hm (hle (Ideal.mem_span_singleton_self a))

theorem prop_6764_local {O : Type u} [CommRing O] [IsLocalRing O] (a : O) :
    IsUnit a ↔ a ∉ maximalIdeal O :=
  IsLocalRing.notMem_maximalIdeal.symm

/-- thSz9ZHDK9o-6963 (1:56:03) [prop] If `𝔪` is an ideal with `O^* = O ∖ 𝔪`, then `O` is local
with maximal ideal `𝔪`. -/
theorem prop_6963 {O : Type u} [CommRing O] (m : Ideal O) (h : ∀ x, IsUnit x ↔ x ∉ m) :
    ∃ _ : IsLocalRing O, maximalIdeal O = m := by
  have : Nontrivial O := by
    by_contra hO
    rw [not_nontrivial_iff_subsingleton] at hO
    exact (h 0).1 (isUnit_of_subsingleton _) m.zero_mem
  have hnu : ∀ x, x ∈ nonunits O ↔ x ∈ m := fun x => by
    rw [mem_nonunits_iff, h, not_not]
  have : IsLocalRing O := IsLocalRing.of_nonunits_add fun a b ha hb =>
    (hnu _).2 (m.add_mem ((hnu a).1 ha) ((hnu b).1 hb))
  exact ⟨this, Ideal.ext fun x => (IsLocalRing.mem_maximalIdeal x).trans (hnu x)⟩

/-- thSz9ZHDK9o-7027 (1:57:07) [prop] A ring `O ≠ 0` is local iff for every `f`, `f` or `1 - f`
is invertible. -/
theorem prop_7027 (O : Type u) [CommRing O] [Nontrivial O] :
    IsLocalRing O ↔ ∀ f : O, IsUnit f ∨ IsUnit (1 - f) :=
  ⟨fun _ => IsLocalRing.isUnit_or_isUnit_one_sub_self,
    IsLocalRing.of_isUnit_or_isUnit_one_sub_self⟩

/-- thSz9ZHDK9o-7093 (1:58:13) [prop] The maximal ideal of `A_𝔭` is `𝔭 A_𝔭`, the quotient
`A_𝔭 / 𝔭 A_𝔭` is `κ(𝔭)` (the fraction field of `A/𝔭`), and `A_𝔭^* = A_𝔭 ∖ 𝔭 A_𝔭`. -/
theorem prop_7093 {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] :
    p.map (algebraMap A (Localization.AtPrime p)) = maximalIdeal (Localization.AtPrime p) ∧
      IsFractionRing (A ⧸ p) p.ResidueField ∧
      ∀ x : Localization.AtPrime p,
        IsUnit x ↔ x ∉ p.map (algebraMap A (Localization.AtPrime p)) := by
  refine ⟨Localization.AtPrime.map_eq_maximalIdeal, inferInstance, fun x => ?_⟩
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  exact IsLocalRing.notMem_maximalIdeal.symm

/-- thSz9ZHDK9o-7631 (2:07:11) [def] A locally ringed space is a ringed space whose stalks are
local rings (mathlib's `LocallyRingedSpace`); `Spec A` is one. -/
example (X : AlgebraicGeometry.LocallyRingedSpace.{u}) (x : X) :
    IsLocalRing (X.presheaf.stalk x) := inferInstance

example (A : CommRingCat.{u}) : AlgebraicGeometry.LocallyRingedSpace.{u} :=
  AlgebraicGeometry.Spec.locallyRingedSpaceObj A

/-! ### `M ↦ M^~` and infinite products -/

/-- thSz9ZHDK9o-8093 (2:14:53) [cex] If `A` is an integral domain, `f ≠ 0` a non-unit and `I`
infinite, `(A^I)_f → (A_f)^I` is not surjective: its image consists of the families with a
common denominator `f^k`, and `(1/f^{n(i)})_i` with `n` unbounded has none. -/
theorem cex_8093 {A : Type u} [CommRing A] [IsDomain A] {f : A} (hf0 : f ≠ 0)
    (hf : ¬ IsUnit f) (I : Type*) [Infinite I] :
    ¬ ∀ y : I → Localization.Away f, ∃ (m : I → A) (k : ℕ),
      ∀ i, y i = IsLocalization.mk' (Localization.Away f) (m i)
        (⟨f ^ k, k, rfl⟩ : Submonoid.powers f) := by
  classical
  let e := Infinite.natEmbedding I
  let y : I → Localization.Away f := fun i =>
    if h : ∃ n, e n = i then IsLocalization.mk' _ (1 : A)
      (⟨f ^ h.choose, h.choose, rfl⟩ : Submonoid.powers f) else 0
  intro H
  obtain ⟨m, k, hm⟩ := H y
  have hy : y (e (k + 1)) = IsLocalization.mk' _ (1 : A)
      (⟨f ^ (k + 1), k + 1, rfl⟩ : Submonoid.powers f) := by
    have h : ∃ n, e n = e (k + 1) := ⟨k + 1, rfl⟩
    have hc : h.choose = k + 1 := e.injective h.choose_spec
    simp only [y]
    rw [dite_eq_left_of_eq_true (eq_true h)]
    congr 1
    exact Subtype.ext (by rw [hc])
  have := (hm (e (k + 1))).symm.trans hy
  rw [IsLocalization.mk'_eq_iff_eq] at this
  have hinj := IsLocalization.injective (Localization.Away f)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  have h2 := hinj this
  have h3 : f ^ k * (f * m (e (k + 1))) = f ^ k * 1 := by
    rw [← mul_assoc, ← pow_succ]; exact h2
  have h4 := mul_left_cancel₀ (pow_ne_zero k hf0) h3
  exact hf (IsUnit.of_mul_eq_one _ h4)

/-- thSz9ZHDK9o-7837 (2:10:37) [cex] `M ↦ M^~` does not commute with infinite products: on the
basic open `D(f)` the sections of `(∏ M_i)^~` and of `∏ M_i^~` are `(∏ M_i)_f` and `∏ (M_i)_f`,
and for `A = ℤ`, `f = 2`, `M_i = ℤ` (`i ∈ ℕ`) the canonical map between them is not
surjective (`cex_8093`). -/
theorem cex_7837 :
    ¬ ∀ y : ℕ → Localization.Away (2 : ℤ), ∃ (m : ℕ → ℤ) (k : ℕ),
      ∀ i, y i = IsLocalization.mk' (Localization.Away (2 : ℤ)) (m i)
        (⟨2 ^ k, k, rfl⟩ : Submonoid.powers (2 : ℤ)) :=
  cex_8093 (by norm_num) (by rw [Int.isUnit_iff]; norm_num) ℕ

/-- thSz9ZHDK9o-8093 (2:14:53) [cex] For `M = A^{(I)}`, `I` infinite, `Hom_A(M, N)_f →
Hom_{A_f}(M_f, N_f) = Hom_A(M, N_f)` is not surjective (here `N = A`, `A` a domain, `f ≠ 0` a
non-unit): the sections over `D(f)` of `Hom(M, N)^~ → Hom(M^~, N^~)`. -/
theorem cex_8093_hom {A : Type u} [CommRing A] [IsDomain A] {f : A} (hf0 : f ≠ 0)
    (hf : ¬ IsUnit f) (I : Type*) [Infinite I] :
    ¬ ∀ g : (I →₀ A) →ₗ[A] Localization.Away f, ∃ (φ : (I →₀ A) →ₗ[A] A) (k : ℕ),
      ∀ x, g x = IsLocalization.mk' (Localization.Away f) (φ x)
        (⟨f ^ k, k, rfl⟩ : Submonoid.powers f) := by
  intro H
  apply cex_8093 hf0 hf I
  intro y
  obtain ⟨φ, k, hφ⟩ := H (Finsupp.linearCombination A y)
  exact ⟨fun i => φ (Finsupp.single i 1), k, fun i => by
    rw [← hφ]; simp⟩

/-- thSz9ZHDK9o-8227 (2:17:07) [prop] For `O ≠ 0`: `O` is local iff the non-units form an ideal,
iff `f + g = 1` implies `f` or `g` invertible. -/
theorem prop_8227 (O : Type u) [CommRing O] [Nontrivial O] :
    (IsLocalRing O ↔ ∃ I : Ideal O, (I : Set O) = nonunits O) ∧
      (IsLocalRing O ↔ ∀ f g : O, f + g = 1 → IsUnit f ∨ IsUnit g) := by
  refine ⟨⟨fun _ => ⟨maximalIdeal O, rfl⟩, fun ⟨I, hI⟩ => ?_⟩,
    ⟨fun _ _ _ h => IsLocalRing.isUnit_or_isUnit_of_add_one h,
      fun H => { isUnit_or_isUnit_of_add_one := fun h => H _ _ h }⟩⟩
  exact IsLocalRing.of_nonunits_add fun a b ha hb => by
    rw [← hI] at ha hb ⊢; exact I.add_mem ha hb

/-! ### Completion of a noetherian local ring -/

/-- thSz9ZHDK9o-8624 (2:23:44) [prop] If `A` is local noetherian, `Â` is faithfully flat over
`A`. (The descent of modules along `A → Â` is not formalised: mathlib has no category of
modules with descent data relative to a ring homomorphism.) -/
theorem prop_8624 (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := AdicCompletion (maximalIdeal A) A)

/-- thSz9ZHDK9o-8624 (2:23:44) [prop] For `A → Â` faithfully flat, `M` is finitely generated iff
`M ⊗_A Â` is; then (`A` noetherian) `M ⊗_A Â` is the completion of `M`. -/
theorem prop_8624_finite (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] :
    (Module.Finite A M ↔ Module.Finite (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal A) A ⊗[A] M)) ∧
    (Module.Finite A M → Function.Bijective (AdicCompletion.ofTensorProduct (maximalIdeal A) M)) :=
  have := prop_8624 A
  ⟨⟨fun _ => inferInstance, fun _ =>
      Module.Finite.of_finite_tensorProduct_of_faithfullyFlat (AdicCompletion (maximalIdeal A) A)⟩,
    fun _ => AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian _ M⟩

end

end Buffalo.AG.Part04
