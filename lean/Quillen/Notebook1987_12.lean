import Mathlib

/-!
# Quillen, notebook 1987-12, p. 81 (and 1990-5, p. 63): `Tor₁(A/I, A/J) ≅ (I ∩ J)/IJ`

Daniel Quillen's research notebooks 1987-12 and 1990-5 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201987/1987-12.pdf>).

From `0 → J → A → A/J → 0`, `Tor₁^A(A/I, A/J)` is the kernel of `(A/I) ⊗ J → (A/I) ⊗ A`. For a
commutative ring `A` and ideals `I`, `J` this kernel is `(I ∩ J)/IJ` (`kernel_equiv`), and for
`J = I` the map is zero and `(A/I) ⊗ I ≅ I/I²` (`lTensor_self_eq_zero`, `tensor_self_equiv`), the
page's `Tor₁(R/I, R/I) ≅ I/I²` (1990-5, p. 63). The long exact sequence identifying `Tor₁` with
the kernel is not formalised; mathlib has `injective_lTensor_quotient_iff_inf_eq_mul`, the
vanishing criterion `I ∩ J = IJ`, which `kernel_equiv` refines. The two-sided noncommutative
version of 1990-5 is not formalised.
-/

namespace Quillen.Notebook1987_12

open TensorProduct

variable {A : Type*} [CommRing A] (I J : Ideal A)

/-- Every element of `(A/I) ⊗ J` is `1 ⊗ y`. -/
theorem exists_one_tmul (z : (A ⧸ I) ⊗[A] J) : ∃ y : J, (1 : A ⧸ I) ⊗ₜ y = z := by
  obtain ⟨q, hq⟩ := (quotTensorEquivQuotSMul J I).symm.surjective z
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨y, ?_⟩
  rw [← hq, LinearEquiv.eq_symm_apply, quotTensorEquivQuotSMul_mk_one_tmul]

/-- `1 ⊗ y = 0` in `(A/I) ⊗ J` iff `y ∈ IJ`. -/
theorem one_tmul_eq_zero_iff (y : J) : (1 : A ⧸ I) ⊗ₜ[A] y = 0 ↔ (y : A) ∈ I * J := by
  rw [← (quotTensorEquivQuotSMul J I).map_eq_zero_iff, quotTensorEquivQuotSMul_mk_one_tmul,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, Ideal.smul_eq_mul]

/-- The image of `1 ⊗ y` in `(A/I) ⊗ A` vanishes iff `y ∈ I`. -/
theorem lTensor_one_tmul_eq_zero_iff (y : J) :
    J.subtype.lTensor (A ⧸ I) ((1 : A ⧸ I) ⊗ₜ y) = 0 ↔ (y : A) ∈ I := by
  rw [LinearMap.lTensor_tmul, ← (TensorProduct.rid A (A ⧸ I)).map_eq_zero_iff, rid_tmul,
    Submodule.subtype_apply, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem]

/-- `x ↦ 1 ⊗ x`, from `I ∩ J` to `(A/I) ⊗ J`. -/
noncomputable def g : ↥(I ⊓ J) →ₗ[A] (A ⧸ I) ⊗[A] J :=
  (TensorProduct.mk A (A ⧸ I) J 1).comp (Submodule.inclusion inf_le_right)

theorem range_g : LinearMap.range (g I J) = LinearMap.ker (J.subtype.lTensor (A ⧸ I)) := by
  ext z
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  refine ⟨fun ⟨x, hx⟩ => hx ▸ (lTensor_one_tmul_eq_zero_iff I J _).mpr x.2.1, fun hz => ?_⟩
  obtain ⟨y, rfl⟩ := exists_one_tmul I J z
  exact ⟨⟨y, (lTensor_one_tmul_eq_zero_iff I J y).mp hz, y.2⟩, rfl⟩

theorem ker_g :
    LinearMap.ker (g I J) = Submodule.comap (I ⊓ J).subtype (I * J : Submodule A A) := by
  ext x
  exact one_tmul_eq_zero_iff I J _

/-- **Notebook 1987-12, p. 81**: the kernel of `(A/I) ⊗ J → (A/I) ⊗ A`, which is
`Tor₁(A/I, A/J)`, is `(I ∩ J)/IJ`. -/
noncomputable def kernel_equiv :
    (↥(I ⊓ J) ⧸ Submodule.comap (I ⊓ J).subtype (I * J : Submodule A A)) ≃ₗ[A]
      LinearMap.ker (J.subtype.lTensor (A ⧸ I)) :=
  (Submodule.quotEquivOfEq _ _ (ker_g I J).symm).trans
    ((LinearMap.quotKerEquivRange (g I J)).trans (LinearEquiv.ofEq _ _ (range_g I J)))

/-- For `J = I` the map `(A/I) ⊗ I → (A/I) ⊗ A` is zero. -/
theorem lTensor_self_eq_zero : I.subtype.lTensor (A ⧸ I) = 0 := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨y, rfl⟩ := exists_one_tmul I I z
  exact (lTensor_one_tmul_eq_zero_iff I I y).mpr y.2

/-- **Notebook 1990-5, p. 63**: `Tor₁(A/I, A/I) = (A/I) ⊗ I ≅ I/I²` (`Ideal.Cotangent`). -/
noncomputable def tensor_self_equiv : ((A ⧸ I) ⊗[A] I) ≃ₗ[A] I.Cotangent :=
  quotTensorEquivQuotSMul I I

end Quillen.Notebook1987_12
