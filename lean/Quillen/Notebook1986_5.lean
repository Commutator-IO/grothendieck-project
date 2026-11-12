import Mathlib

/-!
# Quillen, notebook 1986-5: a four-fold embedding and a circle integral

Daniel Quillen's research notebook 1986-5 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201986/1986-5.pdf>) contains two
computations checked here.

* p. 17: for `A² + B² = 1`, the column `j = ((A+1)/2, B/2, (A−1)/2, B/2)` and
  `ε = diag(1, 1, −1, −1)` satisfy `j*j = 1` and `j*εj = A` (`dot_self`, `dot_eps`). Over any
  commutative ring in which `2` is invertible (the entries `A`, `B` commute, as for commuting
  self-adjoint operators); the adjoint is the transpose.
* p. 31: `∫₀^{2π} (2 sin(θ/2))^{2k} dθ = 2π · C(2k, k)` (`integral_two_sin_half_pow`), from
  mathlib's Wallis integral and `4^k Π_{i<k} (2i+1)/(2i+2) = C(2k, k)` (`four_pow_mul_prod`).
-/

namespace Quillen.Notebook1986_5

section Embedding

variable {K : Type*} [CommRing K] [Invertible (2 : K)] {A B : K}

/-- The column `j`. -/
noncomputable def j (A B : K) : Fin 4 → K := ![(A + 1) * ⅟2, B * ⅟2, (A - 1) * ⅟2, B * ⅟2]

/-- The signs of `ε = diag(1, 1, −1, −1)`. -/
def eps : Fin 4 → K := ![1, 1, -1, -1]

lemma half_sq : (⅟2 : K) * ⅟2 * 4 = 1 := by
  have : (4 : K) = 2 * 2 := by norm_num
  rw [this, mul_assoc, ← mul_assoc (⅟2 : K) 2, invOf_mul_self, one_mul, invOf_mul_self]

theorem dot_self (h : A ^ 2 + B ^ 2 = 1) : ∑ i, j A B i * j A B i = 1 := by
  simp only [j, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (2 * ⅟2 * ⅟2 : K) * h + half_sq (K := K)

theorem dot_eps : ∑ i, j A B i * (eps i * j A B i) = A := by
  simp only [j, eps, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linear_combination A * half_sq (K := K)

end Embedding

section Integral

open Real intervalIntegral

theorem four_pow_mul_prod (n : ℕ) :
    (4 : ℝ) ^ n * ∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * i + 2) = n.centralBinom := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Nat.succ_mul_centralBinom_succ n
    have h' : ((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ) = 2 * (2 * n + 1) * n.centralBinom := by
      exact_mod_cast h
    rw [Finset.prod_range_succ, pow_succ]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
    have : ((n + 1).centralBinom : ℝ) = 2 * (2 * n + 1) * n.centralBinom / (n + 1) := by
      rw [← h']; field_simp
    rw [this, ← ih]
    field_simp
    ring

/-- **p. 31**: `∫₀^{2π} (2 sin(θ/2))^{2k} dθ = 2π C(2k, k)`. -/
theorem integral_two_sin_half_pow (k : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π, (2 * sin (θ / 2)) ^ (2 * k) = 2 * π * k.centralBinom := by
  have h := intervalIntegral.integral_comp_div (fun x => (2 * sin x) ^ (2 * k))
    (two_ne_zero (α := ℝ)) (a := 0) (b := 2 * π)
  rw [h, zero_div, mul_div_cancel_left₀ _ (two_ne_zero (α := ℝ))]
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_const_mul, integral_sin_pow_even, ← four_pow_mul_prod, pow_mul]
  norm_num
  ring

end Integral

end Quillen.Notebook1986_5
