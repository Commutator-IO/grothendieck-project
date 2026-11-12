import Mathlib

/-!
# Quillen, notebook 1990-4: a separability element makes derivations inner

Daniel Quillen's research notebook 1990-4 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201990/1990-4.pdf>), pp. 13-14.

Let `e = Σᵢ xᵢ ⊗ yᵢ` be a separability element of a ring `A`: `Σ xᵢ yᵢ = 1` and
`a e = e a` for all `a`. For an additive `D : A → A` satisfying the Leibniz rule, apply
`x ⊗ y ↦ x D(y)` to `a e = e a`: this gives `Σ a xᵢ D(yᵢ) = Σ xᵢ D(yᵢ a)`, and then
`D(a) = a c − c a` with `c = Σ xᵢ D(yᵢ)` (`eq_inner`, which takes the image identity as its
hypothesis): every derivation is inner. `eq_inner_of_comm` starts from `a e = e a` in
`A ⊗[k] A`, for `A` an algebra over a commutative ring `k` and `D` `k`-linear.
-/

namespace Quillen.Notebook1990_4

open Finset TensorProduct

section Ring

variable {A ι : Type*} [Ring A] (s : Finset ι) (x y : ι → A)

/-- **Notebook 1990-4, pp. 13-14**: with `Σ xᵢ yᵢ = 1` and `Σ a xᵢ D(yᵢ) = Σ xᵢ D(yᵢ a)` for all
`a`, a Leibniz map `D` is the inner derivation `[·, c]`, `c = Σ xᵢ D(yᵢ)`. -/
theorem eq_inner (D : A →+ A) (hD : ∀ a b, D (a * b) = a * D b + D a * b)
    (hxy : ∑ i ∈ s, x i * y i = 1)
    (hsep : ∀ a, ∑ i ∈ s, a * x i * D (y i) = ∑ i ∈ s, x i * D (y i * a)) (a : A) :
    D a = a * (∑ i ∈ s, x i * D (y i)) - (∑ i ∈ s, x i * D (y i)) * a := by
  have h := hsep a
  simp only [hD, mul_add, sum_add_distrib, ← mul_assoc] at h
  rw [← sum_mul, hxy, one_mul] at h
  rw [mul_sum, sum_mul]
  simp only [← mul_assoc]
  rw [h]
  abel

end Ring

section Algebra

variable {k A ι : Type*} [CommRing k] [Ring A] [Algebra k A] (s : Finset ι) (x y : ι → A)

/-- The same, with the hypothesis in the form `a e = e a` for `e = Σ xᵢ ⊗ yᵢ ∈ A ⊗[k] A`, for a
`k`-linear Leibniz map `D`. -/
theorem eq_inner_of_comm (D : A →ₗ[k] A) (hD : ∀ a b, D (a * b) = a * D b + D a * b)
    (hxy : ∑ i ∈ s, x i * y i = 1)
    (he : ∀ a : A, ∑ i ∈ s, (a * x i) ⊗ₜ[k] y i = ∑ i ∈ s, x i ⊗ₜ[k] (y i * a)) (a : A) :
    D a = a * (∑ i ∈ s, x i * D (y i)) - (∑ i ∈ s, x i * D (y i)) * a := by
  -- the map `x ⊗ y ↦ x D(y)`
  let φ : A ⊗[k] A →ₗ[k] A := TensorProduct.lift ((LinearMap.mul k A).compl₂ D)
  have hφ : ∀ u v : A, φ (u ⊗ₜ v) = u * D v := fun u v => by simp [φ]
  refine eq_inner s x y D.toAddMonoidHom hD hxy (fun b => ?_) a
  have := congrArg φ (he b)
  simpa only [map_sum, hφ, LinearMap.toAddMonoidHom_coe] using this

end Algebra

end Quillen.Notebook1990_4
