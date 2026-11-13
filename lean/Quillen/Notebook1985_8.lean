import Mathlib

/-!
# Quillen, notebook 1985-8, p. 37: `∑ C(2k, k) x^k / 4^k = (1 − x)^{−1/2}`

Daniel Quillen's research notebook 1985-8 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201985/1985-8.pdf>) uses, on
p. 37, the generating series `∑_{k ≥ 0} C(2k, k) x^k / 4^k = (1 − x)^{−1/2}`, with
`C(2k, k) / 4^k = ∏_{j=1}^{k} (1 − 1/(2j))`.

This file proves the statement as an identity of formal power series over `ℚ`: the square of
the series is `1/(1 − x)`. Its coefficient form is the convolution identity
`∑_{i+j=n} C(2i, i) C(2j, j) = 4^n`, proved from the recursion
`(k + 1) C(2k+2, k+1) = 2 (2k + 1) C(2k, k)` (mathlib's `Nat.succ_mul_centralBinom_succ`).

* `sum_centralBinom_mul`: `∑_{i+j=n} C(2i, i) C(2j, j) = 4^n`;
* `centralSeries_sq_mul`: **the statement of the page**, as formal power series:
  `(∑ C(2k, k) x^k / 4^k)² (1 − x) = 1`;
* `centralBinom_div_four_pow`: `C(2k, k) / 4^k = ∏_{j=1}^{k} (1 − 1/(2j))`.

The analytic statement for `|x| < 1` (convergence and the branch of the square root) is not
formalised.
-/

namespace Quillen.Notebook1985_8

open Finset Nat

/-- `s n = ∑_{i+j=n} C(2i, i) C(2j, j)`. -/
def s (n : ℕ) : ℕ := ∑ p ∈ antidiagonal n, centralBinom p.1 * centralBinom p.2

theorem two_mul_weighted (n : ℕ) :
    2 * ∑ p ∈ antidiagonal n, p.1 * (centralBinom p.1 * centralBinom p.2) = n * s n := by
  have h1 : ∑ p ∈ antidiagonal n, (p.1 + p.2) * (centralBinom p.1 * centralBinom p.2) =
      n * s n := by
    rw [s, mul_sum]
    exact sum_congr rfl fun p hp => by rw [mem_antidiagonal.mp hp]
  have h2 : ∑ p ∈ antidiagonal n, p.2 * (centralBinom p.1 * centralBinom p.2) =
      ∑ p ∈ antidiagonal n, p.1 * (centralBinom p.1 * centralBinom p.2) := by
    rw [← sum_antidiagonal_swap]
    exact sum_congr rfl fun p _ => by simp [Prod.swap, mul_comm]
  rw [← h1]
  simp only [add_mul, sum_add_distrib, h2]
  ring

theorem succ_mul_s (n : ℕ) : (n + 1) * s (n + 1) = 4 * ((n + 1) * s n) := by
  rw [← two_mul_weighted (n + 1), sum_antidiagonal_succ]
  simp only [zero_mul, zero_add]
  have : ∀ p ∈ antidiagonal n, (p.1 + 1) * (centralBinom (p.1 + 1) * centralBinom p.2) =
      2 * (2 * p.1 + 1) * (centralBinom p.1 * centralBinom p.2) := fun p _ => by
    rw [← mul_assoc, succ_mul_centralBinom_succ]; ring
  rw [sum_congr rfl this]
  have e : ∑ p ∈ antidiagonal n, 2 * (2 * p.1 + 1) * (centralBinom p.1 * centralBinom p.2) =
      2 * (2 * ∑ p ∈ antidiagonal n, p.1 * (centralBinom p.1 * centralBinom p.2)) + 2 * s n := by
    rw [s, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun p _ => by ring
  rw [e, two_mul_weighted]; ring

/-- **The convolution identity** `∑_{i+j=n} C(2i, i) C(2j, j) = 4^n`. -/
theorem sum_centralBinom_mul (n : ℕ) :
    ∑ p ∈ antidiagonal n, centralBinom p.1 * centralBinom p.2 = 4 ^ n := by
  show s n = 4 ^ n
  induction n with
  | zero => simp [s]
  | succ n ih =>
    refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < n + 1) ?_
    rw [succ_mul_s, ih, pow_succ]; ring

/-- The series `∑ C(2k, k) x^k / 4^k` over `ℚ`. -/
noncomputable def centralSeries : PowerSeries ℚ :=
  PowerSeries.mk fun k => (centralBinom k : ℚ) / 4 ^ k

/-- **Quillen, notebook 1985-8, p. 37.** As formal power series,
`(∑ C(2k, k) x^k / 4^k)² (1 − x) = 1`: the series is `(1 − x)^{−1/2}`. -/
theorem centralSeries_sq_mul : centralSeries ^ 2 * (1 - PowerSeries.X) = 1 := by
  have hsq : centralSeries ^ 2 = PowerSeries.invUnitsSub 1 := by
    ext n
    rw [PowerSeries.coeff_invUnitsSub, sq, PowerSeries.coeff_mul]
    simp only [centralSeries, PowerSeries.coeff_mk, one_pow, one_divp]
    have : ∀ p ∈ antidiagonal n, (centralBinom p.1 : ℚ) / 4 ^ p.1 *
        ((centralBinom p.2 : ℚ) / 4 ^ p.2) = (centralBinom p.1 * centralBinom p.2 : ℕ) / 4 ^ n :=
      fun p hp => by
        rw [← mem_antidiagonal.mp hp, pow_add]; push_cast; field_simp
    rw [sum_congr rfl this, ← sum_div, ← Nat.cast_sum, sum_centralBinom_mul]
    push_cast
    field_simp
  rw [hsq]
  simpa using PowerSeries.invUnitsSub_mul_sub (1 : ℚˣ)

/-- `C(2k, k) / 4^k = ∏_{j=1}^{k} (1 − 1/(2j))`. -/
theorem centralBinom_div_four_pow (k : ℕ) :
    (centralBinom k : ℚ) / 4 ^ k = ∏ j ∈ range k, (1 - 1 / (2 * ((j : ℚ) + 1))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ← ih]
    have h : ((k : ℚ) + 1) * centralBinom (k + 1) = 2 * (2 * k + 1) * centralBinom k := by
      exact_mod_cast succ_mul_centralBinom_succ k
    rw [eq_div_of_mul_eq (by positivity) ((mul_comm _ _).trans h), pow_succ]
    field_simp
    ring

end Quillen.Notebook1985_8
