import Mathlib

/-!
# Quillen, notebook 1991-4, pp. 51-58: the separability idempotent of `Mₙ(K)`

Daniel Quillen's research notebook 1991-4 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201991/1991-4.pdf>) works, on
pp. 51-58, with separable algebras through an element `z = ∑ x_i ⊗ y_i` of `A ⊗ A` with
`a z = z a` (for the bimodule structure `a (x ⊗ y) b = a x ⊗ y b`) and `∑ x_i y_i = 1`; for the
matrix algebra he takes `z = (1/n) ∑_{i,j} e_ij ⊗ e_ji`, which is moreover symmetric.

This file proves these properties for `Mₙ(K)` over a commutative ring `K`, with `s = ∑ e_ij ⊗ e_ji`
and, when `n` is invertible, `z = n⁻¹ s`:

* `tmul_one_mul_s`: `(a ⊗ 1) s = s (1 ⊗ a)` for every matrix `a`;
* `mul_s`: `m(s) = ∑ e_ij e_ji = n · 1`;
* `comm_s`: `s` is fixed by the flip `x ⊗ y ↦ y ⊗ x`;
* `separability_idempotent`: **the statement of the page**: `z` satisfies the three properties
  with `m(z) = 1`;
* `s_mul_s`: `s * s = 1` in the algebra `Mₙ(K) ⊗ Mₙ(K)` (`s` acts as the flip of `Kⁿ ⊗ Kⁿ`).

The trace form `τ` of the page and the group-algebra analogue are not formalised.
-/

namespace Quillen.Notebook1991_4Separable

open Matrix TensorProduct

variable {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]

/-- `s = ∑_{i,j} e_ij ⊗ e_ji`. -/
noncomputable def s : Matrix n n K ⊗[K] Matrix n n K :=
  ∑ i : n, ∑ j : n, single i j (1 : K) ⊗ₜ single j i (1 : K)

theorem single_mul_single' (i j k l : n) :
    (single i j (1 : K) : Matrix n n K) * single k l 1 = if j = k then single i l 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · exact single_mul_single_of_ne _ _ _ _ h _

theorem single_tmul_one_mul_s (k l : n) :
    ((single k l (1 : K) : Matrix n n K) ⊗ₜ[K] (1 : Matrix n n K)) * s =
      s * ((1 : Matrix n n K) ⊗ₜ[K] single k l (1 : K)) := by
  simp only [s, Finset.mul_sum, Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one, single_mul_single']
  rw [Finset.sum_eq_single l (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
  rw [Finset.sum_eq_single k (fun i _ hi => Finset.sum_eq_zero fun j _ => by simp [hi])
    (by simp)]
  simp

/-- `(a ⊗ 1) s = s (1 ⊗ a)`. -/
theorem tmul_one_mul_s (a : Matrix n n K) :
    (a ⊗ₜ[K] (1 : Matrix n n K)) * s = s * ((1 : Matrix n n K) ⊗ₜ[K] a) := by
  conv_lhs => rw [matrix_eq_sum_single a]
  conv_rhs => rw [matrix_eq_sum_single a]
  simp only [sum_tmul, tmul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have : (single k l (a k l) : Matrix n n K) = a k l • single k l 1 := by
    rw [smul_single, smul_eq_mul, mul_one]
  rw [this, ← smul_tmul', tmul_smul, smul_mul_assoc, mul_smul_comm, single_tmul_one_mul_s]

theorem sum_single_one : ∑ i : n, (single i i (1 : K) : Matrix n n K) = 1 := by
  ext a b
  simp only [Matrix.sum_apply, single_apply, one_apply]
  by_cases h : a = b
  · subst h; simp
  · simp only [h, ite_false]
    rw [Finset.sum_eq_zero]
    intro x _
    split_ifs with hx
    · exact absurd (hx.1.symm.trans hx.2) h
    · rfl

/-- The multiplication map `x ⊗ y ↦ x y`. -/
noncomputable abbrev mul' : Matrix n n K ⊗[K] Matrix n n K →ₗ[K] Matrix n n K :=
  LinearMap.mul' K (Matrix n n K)

/-- `m(s) = ∑ e_ij e_ji = n · 1`. -/
theorem mul_s : mul' (s : Matrix n n K ⊗[K] Matrix n n K) = (Fintype.card n : K) • 1 := by
  simp only [s, map_sum, LinearMap.mul'_apply, single_mul_single_same, mul_one]
  rw [Finset.sum_comm]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [sum_single_one, Nat.cast_smul_eq_nsmul]

/-- `s` is fixed by the flip. -/
theorem comm_s :
    Algebra.TensorProduct.comm K (Matrix n n K) (Matrix n n K) s = s := by
  simp only [s, map_sum, Algebra.TensorProduct.comm_tmul]
  exact Finset.sum_comm

theorem single_tmul_mul_s (i j : n) :
    ((single i j (1 : K) : Matrix n n K) ⊗ₜ[K] (single j i (1 : K) : Matrix n n K)) * s =
      single i i (1 : K) ⊗ₜ single j j (1 : K) := by
  simp only [s, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, single_mul_single']
  rw [Finset.sum_eq_single j (fun k _ hk => Finset.sum_eq_zero fun l _ => by
    simp [Ne.symm hk]) (by simp)]
  rw [Finset.sum_eq_single i (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
  simp

/-- `s² = 1`: `s` is the flip of `Kⁿ ⊗ Kⁿ`. -/
theorem s_mul_s : (s : Matrix n n K ⊗[K] Matrix n n K) * s = 1 := by
  nth_rewrite 1 [s]
  simp_rw [Finset.sum_mul, single_tmul_mul_s]
  simp_rw [← tmul_sum, ← sum_tmul, sum_single_one]
  rfl

/-- **Quillen, notebook 1991-4, pp. 51-58**: when `n` is invertible in `K`,
`z = (1/n) ∑ e_ij ⊗ e_ji` is a symmetric separability element of `Mₙ(K)`. -/
theorem separability_idempotent (h : IsUnit (Fintype.card n : K)) :
    let z : Matrix n n K ⊗[K] Matrix n n K := ((h.unit⁻¹ : Kˣ) : K) • s
    (∀ a : Matrix n n K, (a ⊗ₜ[K] (1 : Matrix n n K)) * z = z * ((1 : Matrix n n K) ⊗ₜ[K] a)) ∧
      mul' z = 1 ∧ Algebra.TensorProduct.comm K (Matrix n n K) (Matrix n n K) z = z := by
  intro z
  refine ⟨fun a => ?_, ?_, ?_⟩
  · simp only [z, mul_smul_comm, smul_mul_assoc, tmul_one_mul_s]
  · rw [map_smul, mul_s, smul_smul, IsUnit.val_inv_mul, one_smul]
  · rw [map_smul, comm_s]

end Quillen.Notebook1991_4Separable
