import Mathlib

/-!
# Quillen, notebook 1984-6: fermions and Clifford generators; a symplectic block lemma

Daniel Quillen's research notebook 1984-6 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201984/1984-6.pdf>) contains two
algebraic steps checked here.

* p. 2: from a fermionic pair `a, a*` (`a² = 0`, `a*² = 0`, `aa* + a*a = 1`) one gets Clifford
  generators `γ₁ = a* + a`, `γ₂ = i(a* − a)`: `γ₁² = γ₂² = 1`, `γ₁γ₂ + γ₂γ₁ = 0` and
  `iγ₁γ₂ = a*a − aa* = 2a*a − 1` (`gamma₁_sq`, `gamma₂_sq`, `gamma_anticomm`, `i_gamma_gamma`).
  Here `i` is any central element of square `−1` in any ring.
* pp. 48-49: for square blocks `A, B, C, D` of a symplectic matrix, with `B` invertible, `B⁻¹A` and
  `DB⁻¹` are skew-symmetric and `(B⁻¹)ᵗ = C − DB⁻¹A` (`inv_mul_skew`, `mul_inv_skew`,
  `transpose_inv_eq`). Only three of the block relations are used:
  `ABᵗ + BAᵗ = 0`, `DᵗB + BᵗD = 0` and `CBᵗ + DAᵗ = 1`, over any commutative ring.
-/

namespace Quillen.Notebook1984_6

section Fermion

variable {A : Type*} [Ring A] {a b j : A}

/-- The relations of a fermionic pair `a, b = a*` and of a central square root `j` of `−1`. -/
structure IsFermion (a b j : A) : Prop where
  a_sq : a * a = 0
  b_sq : b * b = 0
  car : a * b + b * a = 1
  central : ∀ x, j * x = x * j
  j_sq : j * j = -1

theorem gamma₁_sq (h : IsFermion a b j) : (b + a) * (b + a) = 1 := by
  have e : (b + a) * (b + a) = b * b + (a * b + b * a) + a * a := by noncomm_ring
  rw [e, h.a_sq, h.b_sq, h.car, zero_add, add_zero]

lemma sub_sq (h : IsFermion a b j) : (b - a) * (b - a) = -1 := by
  have e : (b - a) * (b - a) = b * b - (a * b + b * a) + a * a := by noncomm_ring
  rw [e, h.a_sq, h.b_sq, h.car, zero_sub, add_zero]

theorem gamma₂_sq (h : IsFermion a b j) : (j * (b - a)) * (j * (b - a)) = 1 := by
  rw [mul_assoc, ← mul_assoc (b - a), ← h.central (b - a), mul_assoc, sub_sq h, ← mul_assoc,
    h.j_sq]
  noncomm_ring

theorem gamma_anticomm (h : IsFermion a b j) :
    (b + a) * (j * (b - a)) + (j * (b - a)) * (b + a) = 0 := by
  rw [← mul_assoc, ← h.central, mul_assoc, mul_assoc, ← mul_add]
  have e : (b + a) * (b - a) + (b - a) * (b + a) = 2 * (b * b) - 2 * (a * a) := by noncomm_ring
  rw [e, h.a_sq, h.b_sq]
  simp

/-- `iγ₁γ₂ = a*a − aa* = 2a*a − 1`. -/
theorem i_gamma_gamma (h : IsFermion a b j) :
    j * ((b + a) * (j * (b - a))) = b * a - a * b ∧ b * a - a * b = 2 * (b * a) - 1 := by
  constructor
  · rw [← mul_assoc (b + a), ← h.central (b + a), ← mul_assoc, ← mul_assoc, h.j_sq, mul_assoc]
    have e : (b + a) * (b - a) = b * b - a * a + (a * b - b * a) := by noncomm_ring
    rw [e, h.a_sq, h.b_sq]
    noncomm_ring
  · have : a * b = 1 - b * a := by rw [← h.car]; abel
    rw [this]
    noncomm_ring

end Fermion

section Blocks

open Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K] {A B C D : Matrix n n K}

theorem inv_mul_skew (hB : IsUnit B.det) (hAB : A * Bᵀ + B * Aᵀ = 0) :
    (B⁻¹ * A)ᵀ = -(B⁻¹ * A) := by
  have hBt : IsUnit Bᵀ.det := by rwa [det_transpose]
  have hA : Aᵀ = -(B⁻¹ * A * Bᵀ) := by
    have : B * Aᵀ = -(A * Bᵀ) := eq_neg_of_add_eq_zero_right hAB
    calc Aᵀ = B⁻¹ * (B * Aᵀ) := by rw [← Matrix.mul_assoc, nonsing_inv_mul B hB, Matrix.one_mul]
      _ = -(B⁻¹ * A * Bᵀ) := by rw [this, Matrix.mul_neg, Matrix.mul_assoc]
  rw [transpose_mul, transpose_nonsing_inv, hA, Matrix.neg_mul, Matrix.mul_assoc,
    mul_nonsing_inv _ hBt, Matrix.mul_one]

theorem mul_inv_skew (hB : IsUnit B.det) (hDB : Dᵀ * B + Bᵀ * D = 0) :
    (D * B⁻¹)ᵀ = -(D * B⁻¹) := by
  have hBt : IsUnit Bᵀ.det := by rwa [det_transpose]
  have hD : Dᵀ = -(Bᵀ * D * B⁻¹) := by
    have : Dᵀ * B = -(Bᵀ * D) := eq_neg_of_add_eq_zero_left hDB
    calc Dᵀ = Dᵀ * B * B⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv B hB, Matrix.mul_one]
      _ = -(Bᵀ * D * B⁻¹) := by rw [this, Matrix.neg_mul]
  rw [transpose_mul, transpose_nonsing_inv, hD, Matrix.mul_neg, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, nonsing_inv_mul _ hBt, Matrix.one_mul]

theorem transpose_inv_eq (hB : IsUnit B.det) (hAB : A * Bᵀ + B * Aᵀ = 0)
    (hCD : C * Bᵀ + D * Aᵀ = 1) : (B⁻¹)ᵀ = C - D * B⁻¹ * A := by
  have hBt : IsUnit Bᵀ.det := by rwa [det_transpose]
  have h1 : Aᵀ * (Bᵀ)⁻¹ = -(B⁻¹ * A) := by
    rw [← transpose_nonsing_inv, ← transpose_mul]
    exact inv_mul_skew hB hAB
  have h2 := congrArg (· * (Bᵀ)⁻¹) hCD
  simp only [Matrix.add_mul, Matrix.mul_assoc, mul_nonsing_inv _ hBt, Matrix.mul_one,
    Matrix.one_mul, h1] at h2
  rw [transpose_nonsing_inv, ← h2, Matrix.mul_neg, Matrix.mul_assoc]
  abel

end Blocks

end Quillen.Notebook1984_6
