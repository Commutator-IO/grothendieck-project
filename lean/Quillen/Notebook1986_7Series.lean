import Mathlib

/-!
# Quillen, notebook 1986-7: the inverse Toeplitz determinant; Newton's identity for `ch`

Daniel Quillen's research notebook 1986-7 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201986/1986-7.pdf>), two power
series computations behind his degeneracy classes.

* pp. 28-29: `c(Q) = 1/c(S)`, computed through inverse Toeplitz matrices. If
  `(1 + c₁T + c₂T² + ⋯)(1 + b₁T + b₂T² + ⋯) = 1` in `R⟦T⟧` then `(−1)ⁿ bₙ` is the determinant of
  the `n × n` Toeplitz–Hessenberg matrix with first row `c₁ c₂ ⋯ cₙ`, `1` under the diagonal and
  `c_{j−i+1}` above it (`neg_one_pow_mul_coeff_eq_det`). Proof: the lower triangular Toeplitz
  matrix of `c` has determinant `1` and inverse the Toeplitz matrix of `b`
  (`toeplitz_mul_toeplitz`), so `bₙ` is a cofactor (`Matrix.adjugate_fin_succ_eq_det_submatrix`),
  and the minor is the transpose of the page's matrix.
* p. 45: Newton's identity in the form used for the Chern character. For
  `c_t = Π_j (1 + x_j t)` in `R⟦t⟧`, `t · (d/dt) c_t = c_t · Σ_{d ≥ 1} (−1)^{d−1} p_d t^d`, with
  `p_d = Σ_j x_j^d` (`X_mul_derivative_prod`); `R` is any commutative ring (no `ℚ` needed in
  this form, which is `t ∂_t log c_t = Σ (−1)^{d−1} p_d t^d`).
-/

namespace Quillen.Notebook1986_7Series

open PowerSeries Matrix

section Toeplitz

variable {R : Type*} [CommRing R]

/-- The lower triangular Toeplitz matrix of a sequence `f`: entry `f (i − j)` for `j ≤ i`. -/
def toeplitz (f : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (j : ℕ) ≤ i then f (i - j) else 0

/-- The product of two lower triangular Toeplitz matrices is the Toeplitz matrix of the
convolution. -/
lemma toeplitz_mul_apply (f g : ℕ → R) (n : ℕ) (i j : Fin n) :
    (toeplitz f n * toeplitz g n) i j =
      if (j : ℕ) ≤ i then ∑ q ∈ Finset.range ((i : ℕ) - j + 1), f (i - j - q) * g q else 0 := by
  simp only [toeplitz, mul_apply, of_apply]
  have h1 : ∀ k : Fin n, (if (k : ℕ) ≤ i then f (i - k) else 0) * (if (j : ℕ) ≤ k then g (k - j) else 0)
      = (fun k : ℕ => if k ∈ Finset.Icc (j : ℕ) i then f (i - k) * g (k - j) else 0) k := by
    intro k
    simp only [Finset.mem_Icc]
    by_cases ha : (k : ℕ) ≤ i <;> by_cases hb : (j : ℕ) ≤ k <;> simp [ha, hb]
  simp_rw [h1]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k ∈ Finset.Icc (j : ℕ) i then
      f (i - k) * g (k - j) else 0) n, ← Finset.sum_filter]
  have hfil : (Finset.range n).filter (· ∈ Finset.Icc (j : ℕ) i) = Finset.Ico (j : ℕ) (i + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Finset.mem_Ico]
    have := i.2
    omega
  rw [hfil]
  split_ifs with hji
  · rw [Finset.sum_Ico_eq_sum_range, show (i : ℕ) + 1 - j = i - j + 1 by omega]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show (i : ℕ) - (j + q) = i - j - q by omega, Nat.add_sub_cancel_left]
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]

/-- If `C · B = 1` in `R⟦X⟧`, the Toeplitz matrices of their coefficients are inverse. -/
theorem toeplitz_mul_toeplitz {C B : R⟦X⟧} (h : B * C = 1) (n : ℕ) :
    toeplitz (fun k => coeff k C) n * toeplitz (fun k => coeff k B) n = 1 := by
  ext i j
  rw [toeplitz_mul_apply, one_apply]
  have hc : ∀ m : ℕ, ∑ q ∈ Finset.range (m + 1), coeff (m - q) C * coeff q B =
      if m = 0 then 1 else 0 := by
    intro m
    have := congrArg (coeff m) h
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => coeff a B * coeff b C),
      coeff_one] at this
    rw [← this]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  split_ifs with h1 h2 h2
  · subst h2; rw [hc]; simp
  · rw [hc, ite_eq_right (fun h0 => h2 (Fin.ext (by omega)))]
  · exact absurd (h2 ▸ le_refl _) h1
  · rfl

lemma det_toeplitz {C : R⟦X⟧} (h0 : coeff 0 C = 1) (n : ℕ) :
    (toeplitz (fun k => coeff k C) n).det = 1 := by
  rw [det_of_isLowerTriangular]
  · simp [toeplitz, h0]
  · intro i j (hij : i < j)
    simp [toeplitz, not_le.mpr hij]

/-- **Notebook 1986-7, pp. 28-29**: if `C · B = 1` with `C = 1 + c₁T + ⋯`, then `(−1)ⁿ bₙ` is
the determinant of the Toeplitz–Hessenberg matrix whose entry `(i, j)` is `c_{j−i+1}` for
`i ≤ j + 1` (so `c₁` on the diagonal, `1 = c₀` under it) and `0` below. -/
theorem neg_one_pow_mul_coeff_eq_det {C B : R⟦X⟧} (h : B * C = 1) (h0 : coeff 0 C = 1) (n : ℕ) :
    (-1) ^ n * coeff n B =
      (Matrix.of fun i j : Fin n => if (i : ℕ) ≤ j + 1 then coeff (j + 1 - i) C else 0).det := by
  set T := toeplitz (fun k => coeff k C) (n + 1)
  have hinv : toeplitz (fun k => coeff k B) (n + 1) = adjugate T := by
    have := congrArg (adjugate T * ·) (toeplitz_mul_toeplitz h (n + 1))
    rw [Matrix.mul_one, ← Matrix.mul_assoc, adjugate_mul, det_toeplitz h0, one_smul,
      Matrix.one_mul] at this
    exact this
  have hb : coeff n B = adjugate T (Fin.last n) 0 := by
    rw [← hinv]
    simp [toeplitz]
  rw [hb, adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_zero, Fin.succAbove_last,
    ← det_transpose]
  simp only [Fin.val_zero, Fin.val_last, zero_add, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, one_mul]
  congr 1

end Toeplitz

section Newton

variable {R : Type*} [CommRing R]

/-- The series `Σ_{d ≥ 1} (−1)^{d−1} x^d t^d = x t/(1 + x t)`. -/
noncomputable def g (x : R) : R⟦X⟧ := mk fun d => if d = 0 then 0 else (-1) ^ (d - 1) * x ^ d

lemma one_add_mul_g (x : R) : (1 + C x * X) * g x = C x * X := by
  ext n
  rw [add_mul, one_mul, mul_assoc, map_add, coeff_C_mul, coeff_C_mul, coeff_X]
  rcases n with _ | n
  · simp [g]
  · rw [coeff_succ_X_mul]
    rcases n with _ | n
    · simp [g]
    · simp only [g, coeff_mk, Nat.add_one_ne_zero, ite_false, add_tsub_cancel_right, add_eq_right]
      rw [pow_succ (-1 : R) n, pow_succ x (n + 1)]
      ring

/-- **Notebook 1986-7, p. 45** (Newton's identity for the Chern character): for
`c = Π_{j ∈ s} (1 + x_j t)`, `t · c' = c · Σ_{d ≥ 1} (−1)^{d−1} p_d t^d` with `p_d = Σ x_j^d`. -/
theorem X_mul_derivative_prod {ι : Type*} (s : Finset ι) (x : ι → R) :
    X * d⁄dX (∏ j ∈ s, (1 + C (x j) * X)) =
      (∏ j ∈ s, (1 + C (x j) * X)) *
        mk fun d => if d = 0 then 0 else (-1) ^ (d - 1) * ∑ j ∈ s, x j ^ d := by
  classical
  have hsum : (mk fun d => if d = 0 then 0 else (-1) ^ (d - 1) * ∑ j ∈ s, x j ^ d : R⟦X⟧) =
      ∑ j ∈ s, g (x j) := by
    ext d
    simp only [coeff_mk, map_sum, g]
    split_ifs <;> simp [Finset.mul_sum]
  rw [hsum]
  have hd : ∀ a, d⁄dX (1 + C (x a) * X : R⟦X⟧) = C (x a) := fun a => by
    rw [map_add, derivative_one, zero_add, Derivation.leibniz, derivative_C, derivative_X]
    simp
  clear hsum
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      hd]
    calc X * ((1 + C (x a) * X) * d⁄dX (∏ j ∈ s, (1 + C (x j) * X)) +
          (∏ j ∈ s, (1 + C (x j) * X)) * C (x a))
        = (1 + C (x a) * X) * (X * d⁄dX (∏ j ∈ s, (1 + C (x j) * X))) +
          (∏ j ∈ s, (1 + C (x j) * X)) * (C (x a) * X) := by ring
      _ = (1 + C (x a) * X) * ((∏ j ∈ s, (1 + C (x j) * X)) * ∑ j ∈ s, g (x j)) +
          (∏ j ∈ s, (1 + C (x j) * X)) * ((1 + C (x a) * X) * g (x a)) := by
        rw [ih, one_add_mul_g]
      _ = _ := by ring

end Newton

end Quillen.Notebook1986_7Series
