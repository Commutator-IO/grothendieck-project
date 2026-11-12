import Mathlib

/-!
# Quillen, notebook 1989-1: the idempotent-lifting polynomial; a unit of `ℚ[x]/(x^{2n−1} − 1)`

Daniel Quillen's research notebook 1989-1 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201989/1989-1.pdf>).

* p. 9: the polynomial `f(x) = ∫₀ˣ (t − t²)ⁿ dt / ∫₀¹ (t − t²)ⁿ dt` lifts idempotents modulo
  nilpotents of order `n + 1`: `f(0) = 0`, `f(1) = 1`, `f(x) + f(1 − x) = 1`, and
  `(x² − x)^{n+1}` divides `f² − f` (`liftPoly_sq_sub_dvd`). Here `F` is an explicit
  antiderivative of `(X − X²)ⁿ` in `ℝ[X]`, divisible by `X^{n+1}`; the symmetry comes from
  `F(x) + F(1 − x)` having derivative zero; `F(1) = ∫₀¹ (t − t²)ⁿ dt > 0` by the fundamental
  theorem of calculus. The divisibility then is `f(f − 1) = −f(x) f(1 − x)`.
* p. 72: if `x^{2n−1} = 1` (`n ≥ 1`) in a `ℚ`-algebra, then `Σ_{j<n} x^{2j+1}` is a unit
  (`isUnit_sum_odd_pow`). The page's argument passes through the roots of unity `ζ`,
  `(1 + ζ) Σ_{j<n} ζ^{2j} = Σ_{k<2n} ζ^k = 1` for `ζ ≠ 1`; here it is algebraic: with
  `N = Σ_{k<2n−1} x^k`, `(1 + x) Σ_{j<n} x^{2j} = 1 + N` and `(1 + N)(1 − N/(2n)) = 1` because
  `N² = (2n − 1) N`.
-/

namespace Quillen.Notebook1989_1

open Polynomial Finset

section Lift

/-- An antiderivative of `(X − X²)ⁿ`: `F = Σ_{k ≤ n} (−1)^k C(n,k)/(n+k+1) X^{n+k+1}`. -/
noncomputable def F (n : ℕ) : ℝ[X] :=
  ∑ k ∈ range (n + 1), C ((-1) ^ k * (n.choose k : ℝ) / (n + k + 1)) * X ^ (n + k + 1)

lemma sub_sq_pow (n : ℕ) :
    ((X : ℝ[X]) - X ^ 2) ^ n = ∑ k ∈ range (n + 1), C ((-1) ^ k * (n.choose k : ℝ)) * X ^ (n + k) := by
  rw [show (X : ℝ[X]) - X ^ 2 = X * (-X + 1) by ring, mul_pow, add_pow, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [one_pow, mul_one, neg_pow, pow_add]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

lemma derivative_F (n : ℕ) : derivative (F n) = ((X : ℝ[X]) - X ^ 2) ^ n := by
  rw [F, sub_sq_pow, derivative_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [derivative_C_mul_X_pow, add_tsub_cancel_right]
  congr 2
  have : ((n : ℝ) + k + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- `F = X^{n+1} · H`. -/
lemma X_pow_dvd_F (n : ℕ) : (X : ℝ[X]) ^ (n + 1) ∣ F n := by
  refine dvd_sum fun k _ => Dvd.dvd.mul_left ?_ _
  exact pow_dvd_pow X (by omega)

lemma eval_zero_F (n : ℕ) : (F n).eval 0 = 0 := by
  simp [F, eval_finsetSum, zero_pow (Nat.succ_ne_zero _)]

lemma eval_F_add_eval_one_sub (n : ℕ) (x : ℝ) : (F n).eval x + (F n).eval (1 - x) = (F n).eval 1 := by
  set G := F n + (F n).comp (1 - X)
  have hG : derivative G = 0 := by
    rw [derivative_add, derivative_comp, derivative_F]
    simp only [derivative_sub, derivative_one, derivative_X, zero_sub, sub_comp, pow_comp, X_comp]
    ring
  have hc := eq_C_of_derivative_eq_zero hG
  have h1 := congrArg (eval x) hc
  have h0 := congrArg (eval 0) hc
  simp only [G, eval_add, eval_comp, eval_sub, eval_one, eval_X, eval_C, sub_zero,
    eval_zero_F, zero_add] at h1 h0
  rw [h1, ← h0]

lemma eval_one_F_pos (n : ℕ) : 0 < (F n).eval 1 := by
  have hint : ∫ t in (0 : ℝ)..1, (t - t ^ 2) ^ n = (F n).eval 1 - (F n).eval 0 := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
      (f := fun t => (F n).eval t) (f' := fun t => (derivative (F n)).eval t)
      (fun t _ => (F n).hasDerivAt t) (by apply Continuous.intervalIntegrable; fun_prop)
    simpa [derivative_F] using this
  rw [eval_zero_F, sub_zero] at hint
  rw [← hint]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (by apply Continuous.intervalIntegrable; fun_prop) (fun t ht => ?_) one_pos
  have : 0 < t - t ^ 2 := by nlinarith [ht.1, ht.2]
  positivity

/-- The idempotent-lifting polynomial `f = F / F(1)`. -/
noncomputable def liftPoly (n : ℕ) : ℝ[X] := C ((F n).eval 1)⁻¹ * F n

theorem liftPoly_eval_zero (n : ℕ) : (liftPoly n).eval 0 = 0 := by
  simp [liftPoly, eval_zero_F]

theorem liftPoly_eval_one (n : ℕ) : (liftPoly n).eval 1 = 1 := by
  simp [liftPoly, (eval_one_F_pos n).ne']

theorem liftPoly_symm (n : ℕ) (x : ℝ) : (liftPoly n).eval x + (liftPoly n).eval (1 - x) = 1 := by
  simp only [liftPoly, eval_mul, eval_C, ← mul_add, eval_F_add_eval_one_sub]
  exact inv_mul_cancel₀ (eval_one_F_pos n).ne'

/-- `f(1 − X) = 1 − f` as polynomials. -/
lemma liftPoly_comp (n : ℕ) : (liftPoly n).comp (1 - X) = 1 - liftPoly n := by
  apply Polynomial.funext
  intro x
  simp only [eval_comp, eval_sub, eval_one, eval_X]
  linarith [liftPoly_symm n x]

/-- **Notebook 1989-1, p. 9**: `(X² − X)^{n+1}` divides `f² − f`. -/
theorem liftPoly_sq_sub_dvd (n : ℕ) :
    ((X : ℝ[X]) ^ 2 - X) ^ (n + 1) ∣ liftPoly n ^ 2 - liftPoly n := by
  obtain ⟨H, hH⟩ := X_pow_dvd_F n
  have hf : liftPoly n = X ^ (n + 1) * (C ((F n).eval 1)⁻¹ * H) := by
    rw [liftPoly, hH]; ring
  set h := C ((F n).eval 1)⁻¹ * H
  have h1 : liftPoly n - 1 = -((1 - X) ^ (n + 1) * h.comp (1 - X)) := by
    have := liftPoly_comp n
    rw [hf, mul_comp, pow_comp, X_comp, ← hf] at this
    rw [this]; ring
  have hs : ((-1 : ℝ[X]) ^ (n + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  refine ⟨-((-1) ^ (n + 1) * h * h.comp (1 - X)), ?_⟩
  calc liftPoly n ^ 2 - liftPoly n = liftPoly n * (liftPoly n - 1) := by ring
    _ = _ := by
      rw [h1]
      nth_rewrite 1 [hf]
      rw [show (X : ℝ[X]) ^ 2 - X = -1 * (X * (1 - X)) by ring, mul_pow, mul_pow]
      linear_combination (X ^ (n + 1) * (1 - X) ^ (n + 1) * h * h.comp (1 - X)) * hs

end Lift

section Unit

variable {A : Type*} [CommRing A] [Algebra ℚ A]

omit [Algebra ℚ A] in
lemma one_add_mul_sum_even (x : A) (n : ℕ) :
    (1 + x) * ∑ j ∈ range n, x ^ (2 * j) = ∑ k ∈ range (2 * n), x ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ,
      sum_range_succ, pow_succ x (2 * n)]
    ring

/-- **Notebook 1989-1, p. 72**: if `x^{2n−1} = 1` with `n ≥ 1`, then `Σ_{j<n} x^{2j+1}` is a
unit. -/
theorem isUnit_sum_odd_pow {n : ℕ} (hn : 1 ≤ n) {x : A} (hx : x ^ (2 * n - 1) = 1) :
    IsUnit (∑ j ∈ range n, x ^ (2 * j + 1)) := by
  set m := 2 * n - 1 with hm
  have h2n : 2 * n = m + 1 := by omega
  set N := ∑ k ∈ range m, x ^ k
  have hxN : x * N = N := by
    have h1 := sum_range_succ' (fun k => x ^ k) m
    have h2 := sum_range_succ (fun k => x ^ k) m
    simp only [pow_zero, hx] at h1 h2
    rw [mul_sum]
    simp only [← pow_succ']
    rw [h2] at h1
    exact (add_right_cancel h1).symm
  have hxkN : ∀ k, x ^ k * N = N := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_assoc, ih, hxN]
  have hNN : N * N = (m : ℚ) • N := by
    rw [show N * N = ∑ k ∈ range m, x ^ k * N from sum_mul _ _ _]
    simp [hxkN, Nat.cast_smul_eq_nsmul]
  have hE : (1 + x) * ∑ j ∈ range n, x ^ (2 * j) = 1 + N := by
    rw [one_add_mul_sum_even, h2n, sum_range_succ, hx, add_comm]
  have hinv : (1 + N) * (1 - (1 / ((m : ℚ) + 1)) • N) = 1 := by
    have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
    rw [mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, hNN, smul_add, smul_smul]
    have : (1 / ((m : ℚ) + 1)) • N + (1 / ((m : ℚ) + 1) * m) • N = N := by
      rw [← add_smul, show 1 / ((m : ℚ) + 1) + 1 / ((m : ℚ) + 1) * m = 1 by field_simp; ring, one_smul]
    rw [this]; abel
  have hEu : IsUnit (∑ j ∈ range n, x ^ (2 * j)) := by
    refine IsUnit.of_mul_eq_one ((1 + x) * (1 - (1 / ((m : ℚ) + 1)) • N)) ?_
    calc _ = ((1 + x) * ∑ j ∈ range n, x ^ (2 * j)) * (1 - (1 / ((m : ℚ) + 1)) • N) := by ring
      _ = 1 := by rw [hE, hinv]
  have hxu : IsUnit x := by
    refine IsUnit.of_mul_eq_one (x ^ (m - 1)) ?_
    rw [← pow_succ', show m - 1 + 1 = m by omega, hx]
  have : ∑ j ∈ range n, x ^ (2 * j + 1) = x * ∑ j ∈ range n, x ^ (2 * j) := by
    rw [mul_sum]; simp only [pow_succ']
  rw [this]
  exact hxu.mul hEu

end Unit

end Quillen.Notebook1989_1
