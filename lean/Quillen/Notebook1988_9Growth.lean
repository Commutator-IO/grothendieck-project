import Mathlib
import Quillen.Notebook1988_9

/-!
# Quillen, notebook 1988-9, pp. 94-97: the Chern–Simons values of an idempotent and their growth

Daniel Quillen's research notebook 1988-9 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201988/1988-9.pdf>),
pp. 94-97. For `A = ℂ + ℂe` and the trace `f ↦ f(1) − f(0)` on `ℂ[X]`, Quillen computes the
value of the Chern–Simons cocycle on `(e, …, e)` as `(2n + 1) (1/n!) ∫₀¹ (t² − t)ⁿ dt`, checks the
compatibility with the periodicity operator, and then notes that the chain of the idempotent
has coefficients `(2n)!/n!`, which he estimates as roughly `n! 2ⁿ`.

* `chernSimons_value` (p. 95): `(2n + 1) (1/n!) ∫₀¹ (t² − t)ⁿ dt = (−1)ⁿ n!/(2n)!`;
* `factorial_ratio` (p. 95): `(n + 1)!/(2n + 2)! = n!/(2 (2n + 1)!)`;
* `two_pow_le_centralBinom`, `factorial_div_bounds` (p. 97): `n! 2ⁿ ≤ (2n)!/n! ≤ n! 4ⁿ` and,
  sharper, `n! 4ⁿ ≤ (2n + 1) (2n)!/n!`: the growth is that of `n! 4ⁿ` up to a factor
  `2n + 1`, not that of `n! 2ⁿ` (`tendsto_ratio`: `((2n)!/n!)/(n! 2ⁿ) → ∞`). The page's estimate
  is a slip (or a misreading of the transcription); the conclusion drawn from it, that the chain
  pairs with cochains of slow enough growth, is unaffected.
-/

namespace Quillen.Notebook1988_9Growth

open Nat Filter

/-- **Notebook 1988-9, p. 95**: `(2n + 1) (1/n!) ∫₀¹ (t² − t)ⁿ dt = (−1)ⁿ n!/(2n)!`. -/
theorem chernSimons_value (n : ℕ) :
    (2 * n + 1 : ℝ) * ((1 / n ! : ℝ) * ∫ t in (0 : ℝ)..1, (t ^ 2 - t) ^ n) =
      (-1) ^ n * n ! / (2 * n) ! := by
  have h := Quillen.Notebook1988_9.integral_sq_sub_pow_mul_pow n 0
  simp only [pow_zero, mul_one, add_zero] at h
  rw [h, show 2 * n + 1 = (2 * n) + 1 from rfl, factorial_succ]
  push_cast
  field_simp

/-- **Notebook 1988-9, p. 95**: `(n + 1)!/(2n + 2)! = n!/(2 (2n + 1)!)`. -/
theorem factorial_ratio (n : ℕ) :
    ((n + 1) ! : ℚ) / (2 * n + 2) ! = n ! / (2 * (2 * n + 1) !) := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from rfl, factorial_succ (2 * n + 1), factorial_succ n]
  push_cast
  field_simp
  ring

/-- `(2n)!/n! = n! C(2n, n)`, exactly. -/
theorem factorial_div_eq (n : ℕ) : (2 * n) ! / n ! = n ! * centralBinom n := by
  rw [centralBinom_eq_two_mul_choose]
  conv_lhs => rw [← Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ 2 * n),
    show 2 * n - n = n by omega, Nat.mul_div_cancel _ (factorial_pos n)]
  rw [mul_comm]

theorem two_pow_le_centralBinom : ∀ n : ℕ, 2 ^ n ≤ centralBinom n
  | 0 => by simp
  | n + 1 => by
    have h := succ_mul_centralBinom_succ n
    have ih := two_pow_le_centralBinom n
    rw [pow_succ]
    nlinarith

/-- **Notebook 1988-9, p. 97, corrected**: `n! 2ⁿ ≤ (2n)!/n! ≤ n! 4ⁿ ≤ (2n + 1) (2n)!/n!`. -/
theorem factorial_div_bounds (n : ℕ) :
    n ! * 2 ^ n ≤ (2 * n) ! / n ! ∧ (2 * n) ! / n ! ≤ n ! * 4 ^ n ∧
      n ! * 4 ^ n ≤ (2 * n + 1) * ((2 * n) ! / n !) := by
  rw [factorial_div_eq]
  refine ⟨Nat.mul_le_mul_left _ (two_pow_le_centralBinom n),
    Nat.mul_le_mul_left _ (centralBinom_le_four_pow n), ?_⟩
  rw [mul_left_comm]
  exact Nat.mul_le_mul_left _ (four_pow_le_two_mul_add_one_mul_centralBinom n)

theorem three_mul_two_pow : ∀ n : ℕ, n * (2 * n + 1) ≤ 3 * 2 ^ n
  | 0 | 1 | 2 | 3 => by norm_num
  | n + 4 => by
    have ih := three_mul_two_pow (n + 3)
    rw [pow_succ]
    nlinarith

theorem le_div_pow (n : ℕ) : (n : ℝ) / 3 ≤ (2 : ℝ) ^ n / (2 * n + 1) := by
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  have : ((n * (2 * n + 1) : ℕ) : ℝ) ≤ ((3 * 2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast three_mul_two_pow n
  push_cast at this
  linarith

/-- The estimate `n! 2ⁿ` is off by an exponential factor: `((2n)!/n!)/(n! 2ⁿ) ≥ 2ⁿ/(2n + 1)`,
which tends to infinity. -/
theorem tendsto_ratio :
    Tendsto (fun n : ℕ => (((2 * n) ! / n ! : ℕ) : ℝ) / (n ! * 2 ^ n)) atTop atTop := by
  have hlow : ∀ n : ℕ, (2 : ℝ) ^ n / (2 * n + 1) ≤ (((2 * n) ! / n ! : ℕ) : ℝ) / (n ! * 2 ^ n) := by
    intro n
    have h' : (n ! : ℝ) * 4 ^ n ≤ (2 * n + 1) * (((2 * n) ! / n ! : ℕ) : ℝ) := by
      exact_mod_cast (factorial_div_bounds n).2.2
    have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) n, (factorial_pos n : 0 < n !)]
  refine tendsto_atTop_mono (fun n => (le_div_pow n).trans (hlow n)) ?_
  exact tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 3)

end Quillen.Notebook1988_9Growth
