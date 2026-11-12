import Mathlib

/-!
# Quillen, notebooks 1988-2 (pp. 45, 62) and 1988-4 (p. 6): the GNS product; a surjective `∂`

Daniel Quillen's research notebooks 1988-2 and 1988-4 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201988/1988-2.pdf>) attach to a
linear map `ρ : A → B` of algebras (a Stinespring or GNS situation) the product on `A ⊗ B ⊗ A`

  `(a₁ ⊗ b₁ ⊗ a₁') · (a₂ ⊗ b₂ ⊗ a₂') = a₁ ⊗ b₁ ρ(a₁' a₂) b₂ ⊗ a₂'`,

and use that it is associative (1988-2, p. 62; 1988-4, p. 6: the same statement, proved once
here). On 1988-2, p. 45, a candidate differential is ruled out because a surjective `∂` with
`∂(x) y = x ∂(y)` is injective.

* `gnsMul`: the product, as an `R`-bilinear map on `A ⊗[R] (B ⊗[R] A)`, with `gnsMul_tmul` its value
  on pure tensors;
* `gnsMul_assoc`: **associativity**, for any `R`-linear `ρ` (neither multiplicative nor unital);
* `injective_of_surjective`: let `P` carry a left and a right action of a ring `D`, and
  `∂ : P → D` satisfy `∂(x) · y = x · ∂(y)`; if `∂` is onto, it is one-to-one. Neither additivity
  nor linearity of `∂` is used.
-/

namespace Quillen.Notebook1988_2

open TensorProduct

section GNS

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable (ρ : A →ₗ[R] B)

/-- `ν ((b₁ ⊗ a₁') ⊗ (a₂ ⊗ b₂)) = b₁ ρ(a₁' a₂) b₂`. -/
noncomputable def nu : (B ⊗[R] A) ⊗[R] (A ⊗[R] B) →ₗ[R] B :=
  LinearMap.mul' R B ∘ₗ TensorProduct.map LinearMap.id (LinearMap.mul' R B) ∘ₗ
    TensorProduct.map LinearMap.id (TensorProduct.map (ρ ∘ₗ LinearMap.mul' R A) LinearMap.id) ∘ₗ
    TensorProduct.map LinearMap.id (TensorProduct.assoc R A A B).symm.toLinearMap ∘ₗ
    (TensorProduct.assoc R B A (A ⊗[R] B)).toLinearMap

@[simp] lemma nu_tmul (b₁ : B) (a₁' a₂ : A) (b₂ : B) :
    nu ρ ((b₁ ⊗ₜ a₁') ⊗ₜ (a₂ ⊗ₜ b₂)) = b₁ * (ρ (a₁' * a₂) * b₂) := by
  simp [nu]

/-- The rearrangement `(a₁ ⊗ u) ⊗ (a₂ ⊗ (b₂ ⊗ a₂')) ↦ a₁ ⊗ ((u ⊗ (a₂ ⊗ b₂)) ⊗ a₂')` followed by
`ν` in the middle. -/
noncomputable def gnsMul' :
    (A ⊗[R] (B ⊗[R] A)) ⊗[R] (A ⊗[R] (B ⊗[R] A)) →ₗ[R] A ⊗[R] (B ⊗[R] A) :=
  TensorProduct.map LinearMap.id (TensorProduct.map (nu ρ) LinearMap.id) ∘ₗ
    TensorProduct.map LinearMap.id
      (TensorProduct.assoc R (B ⊗[R] A) (A ⊗[R] B) A).symm.toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id
      (TensorProduct.map LinearMap.id (TensorProduct.assoc R A B A).symm.toLinearMap) ∘ₗ
    (TensorProduct.assoc R A (B ⊗[R] A) (A ⊗[R] (B ⊗[R] A))).toLinearMap

/-- The GNS product, as a bilinear map. -/
noncomputable def gnsMul :
    (A ⊗[R] (B ⊗[R] A)) →ₗ[R] (A ⊗[R] (B ⊗[R] A)) →ₗ[R] A ⊗[R] (B ⊗[R] A) :=
  TensorProduct.curry (gnsMul' ρ)

@[simp] theorem gnsMul_tmul (a₁ : A) (b₁ : B) (a₁' a₂ : A) (b₂ : B) (a₂' : A) :
    gnsMul ρ (a₁ ⊗ₜ (b₁ ⊗ₜ a₁')) (a₂ ⊗ₜ (b₂ ⊗ₜ a₂'))
      = a₁ ⊗ₜ ((b₁ * (ρ (a₁' * a₂) * b₂)) ⊗ₜ a₂') := by
  simp [gnsMul, gnsMul']

/-- **Associativity of the GNS product** (1988-2, p. 62; 1988-4, p. 6). -/
theorem gnsMul_assoc (x y z : A ⊗[R] (B ⊗[R] A)) :
    gnsMul ρ (gnsMul ρ x y) z = gnsMul ρ x (gnsMul ρ y z) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp [hx, hx']
  | tmul a₁ u =>
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => simp [tmul_add, hu, hu']
  | tmul b₁ a₁' =>
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => simp [hy, hy']
  | tmul a₂ v =>
  induction v using TensorProduct.inductionOn with
  | add v v' hv hv' => simp [tmul_add, hv, hv']
  | tmul b₂ a₂' =>
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add]; rw [hz, hz']
  | tmul a₃ w =>
  induction w using TensorProduct.inductionOn with
  | add w w' hw hw' => simp only [tmul_add, map_add]; rw [hw, hw']
  | tmul b₃ a₃' => simp [mul_assoc]

end GNS

section Differential

variable {D P : Type*} [Ring D] [AddCommGroup P] [Module D P] [Module Dᵐᵒᵖ P]

/-- **1988-2, p. 45**: if `∂(x) · y = x · ∂(y)` for all `x, y ∈ P` and `∂` is onto, then `∂` is
one-to-one: `x = x · ∂(y) = ∂(x) · y` for `∂ y = 1`. -/
theorem injective_of_surjective (d : P → D)
    (hbal : ∀ x y, d x • y = MulOpposite.op (d y) • x) (hd : Function.Surjective d) :
    Function.Injective d := by
  obtain ⟨y, hy⟩ := hd 1
  have key : ∀ x, x = d x • y := fun x => by
    rw [hbal, hy, MulOpposite.op_one, one_smul]
  intro x x' h
  rw [key x, key x', h]

end Differential

end Quillen.Notebook1988_2
