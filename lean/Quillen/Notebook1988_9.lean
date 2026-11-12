import Mathlib

/-!
# Quillen, notebooks 1984-13, 1988-5, 1988-7, 1988-9, 1989-4: Beta integrals with integer exponents

Daniel Quillen's research notebooks (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/>) compute, again and again, the
normalising constants of Chern–Simons and cyclic-cocycle formulas as Beta integrals
`∫₀¹ (t² − t)^k t^ℓ dt`. They are all consequences of one formula, proved here directly (no
Gamma function) by induction on `b`, from `t^a (1 − t)^(b+1) = t^a (1 − t)^b − t^(a+1) (1 − t)^b`:

  `∫₀¹ t^a (1 − t)^b dt = a! b! / (a + b + 1)!`   (`integral_pow_mul_one_sub_pow`).

Mathlib has the complex Beta function `Complex.betaIntegral` and its Gamma formula, but not this
real, natural-exponent form. Consequences checked:

* 1988-9, p. 72: `∫₀¹ (t² − t)^k t^ℓ dt = (−1)^k k! (k + ℓ)! / (2k + ℓ + 1)!`
  (`integral_sq_sub_pow_mul_pow`);
* 1988-5, pp. 53, 85: `(1/k!) ∫₀¹ (t² − t)^k = (−1)^k k!/(2k+1)!` and
  `(1/(q+k)!) ∫₀¹ t^q (t² − t)^k = (−1)^k k!/(q+2k+1)!` (`notebook1988_5_first`, `_second`);
* 1984-13, pp. 3-4: `∫₀¹ (t² − t)^(k−1) t/(k−1)! = (−1)^(k−1) k!/(2k)!` and
  `∫₀¹ (t² − t)^(k−1)/(k−1)! = (−1)^(k−1) (k−1)!/(2k−1)!` (`notebook1984_13_first`, `_second`,
  written with `k = m + 1`);
* 1988-7, p. 13: `∫₀¹ n (t² − t)^(n−1) = (−1)^(n−1) n! (n−1)!/(2n−1)!` and
  `∫₀^∞ e^(−t²) t^(2n−1) dt = (n−1)!/2` (`notebook1988_7_beta`, `notebook1988_7_gauss`);
* 1989-4, p. 56: the simplex integral, as an iterated integral,
  `∫₀¹ ∫₀^(1−t₁) (1 − t₁ − t₂)^i t₁^j t₂^k dt₂ dt₁ = i! j! k!/(i + j + k + 2)!`
  (`integral_simplex`), from the scaled form `∫₀^c (c − x)^i x^k dx = c^(i+k+1) i! k!/(i+k+1)!`.
-/

namespace Quillen.Notebook1988_9

open intervalIntegral Nat

/-- **The Beta integral with natural exponents**: `∫₀¹ t^a (1 − t)^b dt = a! b! / (a + b + 1)!`. -/
theorem integral_pow_mul_one_sub_pow (a b : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ a * (1 - t) ^ b = (a ! * b ! : ℝ) / (a + b + 1) ! := by
  induction b generalizing a with
  | zero =>
    simp only [pow_zero, mul_one, integral_pow, one_pow, add_zero, factorial_zero, cast_one,
      zero_pow (succ_ne_zero a), sub_zero]
    rw [factorial_succ]
    push_cast
    field_simp
  | succ b ih =>
    have h : ∀ t : ℝ, t ^ a * (1 - t) ^ (b + 1) = t ^ a * (1 - t) ^ b - t ^ (a + 1) * (1 - t) ^ b :=
      fun t => by ring
    simp_rw [h]
    rw [integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), ih a, ih (a + 1)]
    rw [show a + 1 + b + 1 = (a + b + 1) + 1 by ring, show a + (b + 1) + 1 = (a + b + 1) + 1 by ring]
    rw [factorial_succ (a + b + 1), factorial_succ a, factorial_succ b]
    push_cast
    have : ((a + b + 1)! : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- `(t² − t)^k t^ℓ = (−1)^k t^(k+ℓ) (1 − t)^k`. -/
lemma sq_sub_pow_mul_pow (k l : ℕ) (t : ℝ) :
    (t ^ 2 - t) ^ k * t ^ l = (-1) ^ k * (t ^ (k + l) * (1 - t) ^ k) := by
  rw [show t ^ 2 - t = -1 * (t * (1 - t)) by ring, mul_pow, mul_pow, pow_add]
  ring

/-- **Notebook 1988-9, p. 72**: `∫₀¹ (t² − t)^k t^ℓ dt = (−1)^k k! (k + ℓ)! / (2k + ℓ + 1)!`. -/
theorem integral_sq_sub_pow_mul_pow (k l : ℕ) :
    ∫ t in (0 : ℝ)..1, (t ^ 2 - t) ^ k * t ^ l =
      (-1) ^ k * (k ! * (k + l) ! : ℝ) / (2 * k + l + 1) ! := by
  simp_rw [sq_sub_pow_mul_pow, integral_const_mul, integral_pow_mul_one_sub_pow]
  rw [show k + l + k + 1 = 2 * k + l + 1 by ring]
  ring

/-- **Notebook 1988-5, p. 53**: `(1/k!) ∫₀¹ (t² − t)^k dt = (−1)^k k! / (2k + 1)!`. -/
theorem notebook1988_5_first (k : ℕ) :
    (1 / k ! : ℝ) * ∫ t in (0 : ℝ)..1, (t ^ 2 - t) ^ k = (-1) ^ k * (k ! : ℝ) / (2 * k + 1) ! := by
  have := integral_sq_sub_pow_mul_pow k 0
  simp only [pow_zero, mul_one, add_zero] at this
  rw [this]
  have : (k ! : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Notebook 1988-5, p. 85**: `(1/(q+k)!) ∫₀¹ t^q (t² − t)^k dt = (−1)^k k! / (q + 2k + 1)!`. -/
theorem notebook1988_5_second (q k : ℕ) :
    (1 / (q + k) ! : ℝ) * ∫ t in (0 : ℝ)..1, t ^ q * (t ^ 2 - t) ^ k =
      (-1) ^ k * (k ! : ℝ) / (q + 2 * k + 1) ! := by
  simp_rw [mul_comm (_ ^ q), integral_sq_sub_pow_mul_pow k q]
  rw [show 2 * k + q + 1 = q + 2 * k + 1 by ring, add_comm k q]
  have : ((q + k) ! : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Notebook 1984-13, p. 3** (with `k = m + 1`):
`∫₀¹ (t² − t)^m t / m! dt = (−1)^m (m + 1)! / (2m + 2)!`. -/
theorem notebook1984_13_first (m : ℕ) :
    ∫ t in (0 : ℝ)..1, (t ^ 2 - t) ^ m * t / m ! = (-1) ^ m * ((m + 1) ! : ℝ) / (2 * m + 2) ! := by
  have h := integral_sq_sub_pow_mul_pow m 1
  simp only [pow_one] at h
  rw [integral_div, h]
  rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring, factorial_succ m]
  have : (m ! : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **Notebook 1984-13, p. 4** (with `k = m + 1`):
`∫₀¹ (t² − t)^m / m! dt = (−1)^m m! / (2m + 1)!`. -/
theorem notebook1984_13_second (m : ℕ) :
    ∫ t in (0 : ℝ)..1, (t ^ 2 - t) ^ m / m ! = (-1) ^ m * (m ! : ℝ) / (2 * m + 1) ! := by
  rw [integral_div, ← notebook1988_5_first]
  ring

/-- **Notebook 1988-7, p. 13** (with `n = m + 1`):
`∫₀¹ n (t² − t)^(n−1) dt = (−1)^(n−1) n! (n−1)! / (2n−1)!`. -/
theorem notebook1988_7_beta (m : ℕ) :
    ∫ t in (0 : ℝ)..1, ((m + 1 : ℕ) : ℝ) * (t ^ 2 - t) ^ m =
      (-1) ^ m * ((m + 1) ! * m ! : ℝ) / (2 * m + 1) ! := by
  rw [integral_const_mul]
  have := integral_sq_sub_pow_mul_pow m 0
  simp only [pow_zero, mul_one, add_zero] at this
  rw [this, factorial_succ m]
  push_cast
  ring

/-- **Notebook 1988-7, p. 13** (with `n = m + 1`): `∫₀^∞ e^(−t²) t^(2n−1) dt = (n − 1)!/2`. -/
theorem notebook1988_7_gauss (m : ℕ) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2) * t ^ (2 * m + 1) = (m ! : ℝ) / 2 := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := (2 * m + 1 : ℕ)) two_pos
    (by have : (0 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by positivity
        linarith)
  have hq : (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = (m : ℝ) + 1 := by push_cast; ring
  rw [hq, Real.Gamma_nat_eq_factorial] at h
  rw [← MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (f := fun x : ℝ =>
    x ^ ((2 * m + 1 : ℕ) : ℝ) * Real.exp (-x ^ (2 : ℝ))), h]
  · ring
  · intro x _
    simp only [Real.rpow_natCast, Real.rpow_two]
    ring

/-- The scaled Beta integral: `∫₀^c (c − x)^i x^k dx = c^(i+k+1) i! k! / (i + k + 1)!`. -/
theorem integral_scaled (c : ℝ) (i k : ℕ) :
    ∫ x in (0 : ℝ)..c, (c - x) ^ i * x ^ k = c ^ (i + k + 1) * ((i ! * k ! : ℝ) / (i + k + 1) !) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have h := integral_comp_mul_left (fun x => (c - x) ^ i * x ^ k) (a := 0) (b := 1) hc
  simp only [mul_zero, mul_one] at h
  rw [(inv_smul_eq_iff₀ hc).mp h.symm, smul_eq_mul]
  have h2 : ∀ u : ℝ, (c - c * u) ^ i * (c * u) ^ k = c ^ (i + k) * (u ^ k * (1 - u) ^ i) := by
    intro u; rw [show c - c * u = c * (1 - u) by ring, mul_pow, mul_pow, pow_add]; ring
  simp_rw [h2, integral_const_mul, integral_pow_mul_one_sub_pow]
  rw [add_comm k i, pow_succ]
  ring

/-- **Notebook 1989-4, p. 56**: the simplex integral, as an iterated integral,
`∫₀¹ ∫₀^(1−t₁) (1 − t₁ − t₂)^i t₁^j t₂^k dt₂ dt₁ = i! j! k! / (i + j + k + 2)!`. -/
theorem integral_simplex (i j k : ℕ) :
    ∫ t₁ in (0 : ℝ)..1, ∫ t₂ in (0 : ℝ)..(1 - t₁), (1 - t₁ - t₂) ^ i * t₁ ^ j * t₂ ^ k =
      (i ! * j ! * k ! : ℝ) / (i + j + k + 2) ! := by
  have h1 : ∀ t₁ : ℝ, ∫ t₂ in (0 : ℝ)..(1 - t₁), (1 - t₁ - t₂) ^ i * t₁ ^ j * t₂ ^ k =
      ((i ! * k ! : ℝ) / (i + k + 1) !) * (t₁ ^ j * (1 - t₁) ^ (i + k + 1)) := by
    intro t₁
    simp_rw [mul_right_comm _ (t₁ ^ j), integral_mul_const, integral_scaled]
    ring
  simp_rw [h1, integral_const_mul, integral_pow_mul_one_sub_pow]
  rw [show j + (i + k + 1) + 1 = i + j + k + 2 by ring]
  have : ((i + k + 1) ! : ℝ) ≠ 0 := by positivity
  field_simp

end Quillen.Notebook1988_9
