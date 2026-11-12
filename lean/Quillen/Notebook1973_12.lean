import Mathlib

/-!
# Quillen, notebook 1973-12, p. 48: the kernel of `GL_m(A) → GL_m(A/I)` for `I² = 0`

Daniel Quillen's research notebook 1973-12 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201973/1973-12.pdf>) proves, on
p. 48, that `K_*(A) ⊗ ℤ[1/p] ≅ K_*(A/I) ⊗ ℤ[1/p]` for a nilpotent two-sided ideal `I` with
`p^r I = 0`. After reducing to `I² = 0` he writes the exact sequence
`0 → N → GL_m(A) → GL_m(A/I) → 0`, with `N` isomorphic to the additive group of matrices with
entries in `I`, so that `p^r N = 0`.

This file proves the group theory, for a two-sided ideal `J` of square zero in any ring `R`
(for `R = M_m(A)`, `J = M_m(I)`, which has square zero when `I` has, `matrix_sq_zero`):

* `kernel J`: the units `u` with `u − 1 ∈ J` (for `J = M_m(I)`, the kernel of reduction modulo
  `I`), a subgroup;
* `kernelEquiv`: **`N ≅ (J, +)`**, by `u ↦ u − 1`, with inverse `x ↦ 1 + x`, since
  `(1 + x)(1 + y) = 1 + x + y`;
* `pow_eq_one_of_kernel`: if `n J = 0` then `u^n = 1` on `N`;
* `isUnit_of_lift`: **the surjectivity of `GL_m(A) → GL_m(A/I)`**: if `u v − 1` and `v u − 1`
  lie in `J`, then `u` is a unit.
-/

namespace Quillen.Notebook1973_12

variable {R : Type*} [Ring R] (J : TwoSidedIdeal R)

/-- The units congruent to `1` modulo `J`. -/
def kernel (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y = 0) : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ J}
  one_mem' := by simp [J.zero_mem]
  mul_mem' := by
    intro u v hu hv
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    have : (u : R) * v - 1 = ((u : R) - 1) + ((v : R) - 1) + ((u : R) - 1) * ((v : R) - 1) := by
      noncomm_ring
    rw [this, hJ _ hu _ hv, add_zero]
    exact J.add_mem hu hv
  inv_mem' := by
    intro u hu
    simp only [Set.mem_ofPred_eq] at *
    have : ((u⁻¹ : Rˣ) : R) - 1 = -(((u⁻¹ : Rˣ) : R) * ((u : R) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one]; abel
    rw [this]
    exact J.neg_mem (J.mul_mem_left _ _ hu)

variable {J}

theorem one_add_mul_one_sub (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y = 0) {x : R} (hx : x ∈ J) :
    (1 + x) * (1 - x) = 1 := by
  have : (1 + x) * (1 - x) = 1 - x * x := by noncomm_ring
  rw [this, hJ x hx x hx, sub_zero]

theorem one_sub_mul_one_add (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y = 0) {x : R} (hx : x ∈ J) :
    (1 - x) * (1 + x) = 1 := by
  have : (1 - x) * (1 + x) = 1 - x * x := by noncomm_ring
  rw [this, hJ x hx x hx, sub_zero]

/-- For `x ∈ J`, `1 + x` is a unit with inverse `1 - x`. -/
def oneAddUnit (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y = 0) {x : R} (hx : x ∈ J) : Rˣ where
  val := 1 + x
  inv := 1 - x
  val_inv := one_add_mul_one_sub hJ hx
  inv_val := one_sub_mul_one_add hJ hx

theorem mul_sub_one (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y = 0) {a b : R} (ha : a - 1 ∈ J)
    (hb : b - 1 ∈ J) : a * b - 1 = (a - 1) + (b - 1) := by
  have : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by noncomm_ring
  rw [this, hJ _ ha _ hb, add_zero]

/-- **Quillen, notebook 1973-12, p. 48.** For a two-sided ideal `J` of square zero, the group
of units congruent to `1` modulo `J` is isomorphic to the additive group of `J`. -/
def kernelEquiv (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y = 0) : kernel J hJ ≃* Multiplicative J where
  toFun u := Multiplicative.ofAdd ⟨((u : Rˣ) : R) - 1, u.2⟩
  invFun x := ⟨oneAddUnit hJ (Multiplicative.toAdd x).2, by
    show (1 + ((Multiplicative.toAdd x : J) : R)) - 1 ∈ J
    rw [add_sub_cancel_left]; exact (Multiplicative.toAdd x).2⟩
  left_inv u := by
    apply Subtype.ext; apply Units.ext
    show 1 + (((u : Rˣ) : R) - 1) = ((u : Rˣ) : R)
    abel
  right_inv x := by
    apply Multiplicative.toAdd.injective; apply Subtype.ext
    show (1 + ((Multiplicative.toAdd x : J) : R)) - 1 = ((Multiplicative.toAdd x : J) : R)
    abel
  map_mul' u v := by
    apply Multiplicative.toAdd.injective; apply Subtype.ext
    show ((u : Rˣ) : R) * ((v : Rˣ) : R) - 1 = (((u : Rˣ) : R) - 1) + (((v : Rˣ) : R) - 1)
    exact mul_sub_one hJ u.2 v.2

/-- If `n J = 0`, every element of the kernel has order dividing `n`: for `J = M_m(I)` with
`p^r I = 0`, `p^r N = 0`. -/
theorem pow_eq_one_of_kernel (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y = 0) {n : ℕ}
    (hn : ∀ x ∈ J, n • x = 0) (u : kernel J hJ) : u ^ n = 1 := by
  apply (kernelEquiv hJ).injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective; apply Subtype.ext
  rw [toAdd_pow, toAdd_one, AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero]
  exact hn _ (Multiplicative.toAdd (kernelEquiv hJ u)).2

/-- **Lifting units, p. 48.** If `u v ≡ 1` and `v u ≡ 1` modulo a two-sided ideal `J` of
square zero, then `u` is a unit: `GL_m(A) → GL_m(A/I)` is onto. -/
theorem isUnit_of_lift (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y = 0) {u v : R}
    (h1 : u * v - 1 ∈ J) (h2 : v * u - 1 ∈ J) : IsUnit u := by
  have hr : u * (v * (1 - (u * v - 1))) = 1 :=
    (by noncomm_ring : u * (v * (1 - (u * v - 1))) = (1 + (u * v - 1)) * (1 - (u * v - 1))).trans
      (one_add_mul_one_sub hJ h1)
  have hl : ((1 - (v * u - 1)) * v) * u = 1 :=
    (by noncomm_ring : ((1 - (v * u - 1)) * v) * u = (1 - (v * u - 1)) * (1 + (v * u - 1))).trans
      (one_sub_mul_one_add hJ h2)
  have he := left_inv_eq_right_inv hl hr
  exact ⟨⟨u, v * (1 - (u * v - 1)), hr, by rw [← he]; exact hl⟩, rfl⟩

/-- For a two-sided ideal `I` of square zero in `A`, the matrices with entries in `I` form a
two-sided ideal of square zero in `M_n(A)`. -/
theorem matrix_sq_zero {A : Type*} [Ring A] {n : Type*} [Fintype n] (I : TwoSidedIdeal A)
    (hI : ∀ x ∈ I, ∀ y ∈ I, x * y = 0) :
    ∀ X ∈ I.matrix n, ∀ Y ∈ I.matrix n, X * Y = 0 := by
  intro X hX Y hY
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => hI _ ?_ _ ?_
  · exact (TwoSidedIdeal.mem_matrix n I X).mp hX i k
  · exact (TwoSidedIdeal.mem_matrix n I Y).mp hY k j

end Quillen.Notebook1973_12
