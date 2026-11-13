import Mathlib

/-!
# Quillen, notebook 1973-3: a Gaussian sum over a shifted lattice, and the `Σ₃`-invariant of
# the cross-ratio

Daniel Quillen's notebook 1973-3 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201973/1973-3.pdf>) contains two
statements that this file proves.

**The theta inequality (pp. 79–81, entry of April 26, 1973).** Treating a lattice `M` with a
positive definite form `q` as a vector bundle over `ℤ ∪ ∞`, Quillen measures its sections by
`θ = ∑_{m ∈ M} exp(-π q(m))` and wants `θ_E ≤ θ_{E'} θ_{E''}` for an exact sequence. The step he
needs is a lemma: the Gaussian sum over a translate `x + M` is at most the sum over `M`, with
equality only for `x ∈ M`. He first checks it on the line (p. 79, `M = ℤ`, `q = α x²`: the second
derivative at `0` is negative), then proves it in general from the Poisson summation formula: the
shifted sum is a cosine series with positive coefficients (pp. 80–81). This file proves the
one-dimensional case, with its equality clause, by that argument.

* `summable_gaussian`: `n ↦ exp(-π a n²)` is summable over `ℤ` for `a > 0`;
* `gaussian_shift_fourier`: Poisson summation in the form used on p. 80: for `α > 0`,
  `C · ∑ exp(-π α (x + m)²) = ∑ exp(-π n² / α) cos(2π n x)` with `C = 1 / (α⁻¹)^(1/2) > 0`;
* `gaussian_shift_le`: `∑_m exp(-π α (x + m)²) ≤ ∑_m exp(-π α m²)`;
* `gaussian_shift_lt`: the inequality is strict when `x` is not an integer;
* `gaussian_shift_eq_iff`: equality holds iff `x ∈ ℤ`.

**The invariant of the cross-ratio (pp. 23–25, entry of April 14, 1973).** Computing the homology
of `PGL₂(k)` from its action on four-point configurations of `P¹`, Quillen lists the six values
`z, 1/z, 1 - z, 1/(1 - z), 1 - 1/z, z/(z - 1)` taken by the cross-ratio under `Σ₄`, notes that the
Klein group acts trivially, and proposes the invariant `w = (z² - z + 1)³ / (z² (z - 1)²)`
(p. 25), with triple zeros at the primitive sixth roots of unity, double poles at `0, 1, ∞`, and
`w = 27/4` on the orbit `{-1, 1/2, 2}`. He says that `z ↦ w` puts the `Σ₃`-orbits of
`k - {0, 1}` in bijection with `k`. This `w` is `j / 256` for the Legendre parameter.

* `crossRatioInv`: the rational function `w`;
* `crossRatioInv_one_sub`, `crossRatioInv_inv`: invariance under the two transpositions;
* `crossRatioInv_two`, `crossRatioInv_neg_one`, `crossRatioInv_half`: the value `27/4`;
* `crossRatioInv_eq_zero_iff`: the zeros away from `0, 1` are the roots of `z² - z + 1`;
* `crossRatioInv_sub_factor`: the polynomial identity behind the fibres;
* `crossRatioInv_eq_iff`: for `z, z' ∉ {0, 1}` in a field, `w z = w z'` iff `z'` is one of the
  six values in the orbit of `z`; that is, the fibres of `w` on `k - {0, 1}` are exactly the
  `Σ₃`-orbits (injectivity on orbits; surjectivity onto `k` needs `k` algebraically closed and is
  not proved here).
-/

namespace Quillen.Notebook1973_3

open Real Complex

/-! ## The Gaussian sum over a translate of `ℤ` -/

/-- The Gaussian `n ↦ exp(-π a n²)` is summable over `ℤ` for `a > 0`. -/
theorem summable_gaussian {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-π * a * (n : ℝ) ^ 2)) := by
  refine (summable_pow_mul_jacobiTheta₂_term_bound 0 ha 0).congr fun n => ?_
  simp only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero]
  ring_nf

/-- **Poisson summation, Quillen, notebook 1973-3, p. 80** (dimension one). For `α > 0` and real
`x`, the Gaussian sum over the translate `x + ℤ` is, up to the positive constant
`C = 1 / (α⁻¹)^(1/2)`, the cosine series `∑ exp(-π n² / α) cos(2π n x)`. -/
theorem gaussian_shift_fourier {α : ℝ} (hα : 0 < α) (x : ℝ) :
    1 / (α⁻¹) ^ (1 / 2 : ℝ) * ∑' m : ℤ, Real.exp (-π * α * (x + m) ^ 2) =
      ∑' n : ℤ, Real.exp (-π * α⁻¹ * (n : ℝ) ^ 2) * Real.cos (2 * π * x * n) := by
  set a : ℝ := α⁻¹ with ha_def
  have ha : 0 < a := inv_pos.mpr hα
  -- the terms of the Fourier side, as a real exponential times a phase
  set t : ℤ → ℂ := fun n =>
    ((Real.exp (-π * a * (n : ℝ) ^ 2) : ℝ) : ℂ) * cexp (((-2 * π * x * n : ℝ) : ℂ) * I) with ht
  have h1 : (fun n : ℤ => cexp (-π * (a : ℂ) * (n : ℂ) ^ 2 + 2 * π * (-I * x) * n)) = t := by
    funext n
    simp only [ht]
    rw [ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hts : Summable t := by
    refine Summable.of_norm ((summable_gaussian ha).congr fun n => ?_)
    rw [ht]
    simp only [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hre : ∀ n : ℤ, (t n).re = Real.exp (-π * a * (n : ℝ) ^ 2) * Real.cos (2 * π * x * n) := by
    intro n
    rw [ht]
    simp only [re_ofReal_mul, exp_ofReal_mul_I_re]
    congr 1
    rw [← Real.cos_neg]
    congr 1
    ring
  -- the Gaussian side, as the complexification of a real sum
  have h2 : (fun n : ℤ => cexp (-π / (a : ℂ) * ((n : ℂ) + I * (-I * x)) ^ 2)) =
      fun n : ℤ => ((Real.exp (-π * α * (x + n) ^ 2) : ℝ) : ℂ) := by
    funext n
    rw [ofReal_exp]
    congr 1
    have hI : I * (-I * (x : ℂ)) = x := by linear_combination -(x : ℂ) * I_sq
    rw [hI, ha_def]
    push_cast
    rw [div_inv_eq_mul]
    ring
  -- the constant
  have hc : (1 : ℂ) / (a : ℂ) ^ (1 / 2 : ℂ) = ((1 / a ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_div, ofReal_one, ofReal_cpow ha.le]
    push_cast
    rfl
  have hP := Complex.tsum_exp_neg_quadratic (a := (a : ℂ)) (by rwa [ofReal_re]) (-I * x)
  rw [h1, h2, ← ofReal_tsum, hc, ← ofReal_mul] at hP
  have := congrArg Complex.re hP
  rw [ofReal_re, re_tsum hts] at this
  rw [← this]
  exact tsum_congr hre

/-- The cosine series is at most its value at `x = 0`. -/
private theorem fourier_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ∑' n : ℤ, Real.exp (-π * a * (n : ℝ) ^ 2) * Real.cos (2 * π * x * n) ≤
      ∑' n : ℤ, Real.exp (-π * a * (n : ℝ) ^ 2) := by
  have hs := summable_gaussian ha
  have hs' : Summable fun n : ℤ => Real.exp (-π * a * (n : ℝ) ^ 2) * Real.cos (2 * π * x * n) :=
    Summable.of_norm_bounded hs fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  exact hs'.tsum_le_tsum (fun n => mul_le_of_le_one_right (Real.exp_pos _).le
    (Real.cos_le_one _)) hs

/-- **Quillen, notebook 1973-3, pp. 79–81** (dimension one). For `α > 0` and every real `x`,
`∑_{m ∈ ℤ} exp(-π α (x + m)²) ≤ ∑_{m ∈ ℤ} exp(-π α m²)`. -/
theorem gaussian_shift_le {α : ℝ} (hα : 0 < α) (x : ℝ) :
    ∑' m : ℤ, Real.exp (-π * α * (x + m) ^ 2) ≤ ∑' m : ℤ, Real.exp (-π * α * (m : ℝ) ^ 2) := by
  have hC : 0 < 1 / (α⁻¹) ^ (1 / 2 : ℝ) :=
    one_div_pos.mpr (Real.rpow_pos_of_pos (inv_pos.mpr hα) _)
  have h0 := gaussian_shift_fourier hα 0
  simp only [zero_add, mul_zero, zero_mul, Real.cos_zero, mul_one] at h0
  refine le_of_mul_le_mul_left ?_ hC
  rw [gaussian_shift_fourier hα x, h0]
  exact fourier_le (inv_pos.mpr hα) x

/-- **Quillen, notebook 1973-3, p. 81** (dimension one). The inequality is strict when `x` is not
an integer. -/
theorem gaussian_shift_lt {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : ∀ k : ℤ, x ≠ k) :
    ∑' m : ℤ, Real.exp (-π * α * (x + m) ^ 2) < ∑' m : ℤ, Real.exp (-π * α * (m : ℝ) ^ 2) := by
  have ha : 0 < α⁻¹ := inv_pos.mpr hα
  have hC : 0 < 1 / (α⁻¹) ^ (1 / 2 : ℝ) := one_div_pos.mpr (Real.rpow_pos_of_pos ha _)
  have h0 := gaussian_shift_fourier hα 0
  simp only [zero_add, mul_zero, zero_mul, Real.cos_zero, mul_one] at h0
  refine lt_of_mul_lt_mul_left ?_ hC.le
  rw [gaussian_shift_fourier hα x, h0]
  have hs := summable_gaussian ha
  have hs' : Summable fun n : ℤ =>
      Real.exp (-π * α⁻¹ * (n : ℝ) ^ 2) * Real.cos (2 * π * x * n) :=
    Summable.of_norm_bounded hs fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  have hcos : Real.cos (2 * π * x) < 1 := by
    refine lt_of_le_of_ne (Real.cos_le_one _) fun h => ?_
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp h
    apply hx k
    have hπ : (2 * π) ≠ 0 := by positivity
    have : (k : ℝ) * (2 * π) = x * (2 * π) := by rw [hk]; ring
    exact (mul_right_cancel₀ hπ this).symm
  exact hs'.tsum_lt_tsum (i := 1)
    (fun n => mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _))
    (by
      simp only [Int.cast_one, one_pow, mul_one]
      exact mul_lt_of_lt_one_right (Real.exp_pos _) hcos)
    hs

/-- **Quillen, notebook 1973-3, p. 81** (dimension one). Equality in the theta inequality holds
exactly on the lattice: `∑ exp(-π α (x + m)²) = ∑ exp(-π α m²)` iff `x ∈ ℤ`. -/
theorem gaussian_shift_eq_iff {α : ℝ} (hα : 0 < α) (x : ℝ) :
    ∑' m : ℤ, Real.exp (-π * α * (x + m) ^ 2) = ∑' m : ℤ, Real.exp (-π * α * (m : ℝ) ^ 2) ↔
      ∃ k : ℤ, x = k := by
  refine ⟨fun h => by_contra fun hx => (gaussian_shift_lt hα fun k hk => hx ⟨k, hk⟩).ne h, ?_⟩
  rintro ⟨k, rfl⟩
  rw [← (Equiv.addLeft k).tsum_eq (fun m : ℤ => Real.exp (-π * α * (m : ℝ) ^ 2))]
  exact tsum_congr fun m => by simp

/-! ## The `Σ₃`-invariant of the cross-ratio -/

variable {K : Type*} [Field K]

/-- Quillen's invariant of the cross-ratio (notebook 1973-3, p. 25):
`w(z) = (z² - z + 1)³ / (z² (z - 1)²)`. -/
def crossRatioInv (z : K) : K := (z ^ 2 - z + 1) ^ 3 / (z ^ 2 * (z - 1) ^ 2)

/-- `w` is invariant under `z ↦ 1 - z` (p. 25). -/
theorem crossRatioInv_one_sub (z : K) : crossRatioInv (1 - z) = crossRatioInv z := by
  unfold crossRatioInv
  ring

/-- `w` is invariant under `z ↦ 1/z` (p. 25). -/
theorem crossRatioInv_inv (z : K) : crossRatioInv z⁻¹ = crossRatioInv z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rcases eq_or_ne z 1 with rfl | hz1
  · simp [crossRatioInv]
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hz1'' : z⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr fun h => hz1 (by rw [← inv_inv z, h, inv_one])
  unfold crossRatioInv
  rw [div_eq_div_iff (by simp [hz, hz1'']) (by simp [hz, hz1'])]
  field_simp
  ring

/-- The value `27/4` on the orbit `{-1, 1/2, 2}` (pp. 24–25), in characteristic not `2`. -/
theorem crossRatioInv_two [CharZero K] : crossRatioInv (2 : K) = 27 / 4 := by
  unfold crossRatioInv; norm_num

theorem crossRatioInv_neg_one [CharZero K] : crossRatioInv (-1 : K) = 27 / 4 := by
  unfold crossRatioInv; norm_num

theorem crossRatioInv_half [CharZero K] : crossRatioInv (1 / 2 : K) = 27 / 4 := by
  unfold crossRatioInv; norm_num

/-- Away from `0` and `1`, `w` vanishes exactly at the roots of `z² - z + 1`, the primitive sixth
roots of unity (p. 25). -/
theorem crossRatioInv_eq_zero_iff {z : K} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    crossRatioInv z = 0 ↔ z ^ 2 - z + 1 = 0 := by
  have hd : z ^ 2 * (z - 1) ^ 2 ≠ 0 := by
    simp [h0, sub_ne_zero.mpr h1]
  unfold crossRatioInv
  rw [div_eq_zero_iff, or_iff_left hd, pow_eq_zero_iff (by norm_num)]

/-- The polynomial identity behind the fibres of `w`: after clearing denominators, `w z' - w z`
is the product of the six linear forms `z' - σ(z)`, `σ ∈ Σ₃`. -/
theorem crossRatioInv_sub_factor (z z' : K) :
    (z' ^ 2 - z' + 1) ^ 3 * (z ^ 2 * (z - 1) ^ 2) - (z ^ 2 - z + 1) ^ 3 * (z' ^ 2 * (z' - 1) ^ 2) =
      (z' - z) * (z' * z - 1) * (z' + z - 1) * (z' * z - z' + 1) * (z' * z - z' - z) *
        (z' * z - z + 1) := by
  ring

/-- **Quillen, notebook 1973-3, p. 25.** For `z, z'` in a field, both different from `0` and `1`,
`w z = w z'` if and only if `z'` is one of the six values `z, 1/z, 1 - z, 1/(1 - z), z/(z - 1),
(z - 1)/z` of the `Σ₃`-orbit of `z`. -/
theorem crossRatioInv_eq_iff {z z' : K} (h0 : z ≠ 0) (h1 : z ≠ 1) (h0' : z' ≠ 0)
    (h1' : z' ≠ 1) :
    crossRatioInv z' = crossRatioInv z ↔
      z' = z ∨ z' = z⁻¹ ∨ z' = 1 - z ∨ z' = (1 - z)⁻¹ ∨ z' = z / (z - 1) ∨
        z' = (z - 1) / z := by
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hz1' : 1 - z ≠ 0 := sub_ne_zero.mpr h1.symm
  have hz'1 : z' - 1 ≠ 0 := sub_ne_zero.mpr h1'
  have hd : z ^ 2 * (z - 1) ^ 2 ≠ 0 := by simp [h0, hz1]
  have hd' : z' ^ 2 * (z' - 1) ^ 2 ≠ 0 := by simp [h0', hz'1]
  unfold crossRatioInv
  rw [div_eq_div_iff hd' hd, ← sub_eq_zero, crossRatioInv_sub_factor]
  simp only [mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (((((h | h) | h) | h) | h) | h)
    · exact Or.inl h
    · right; left; field_simp; linear_combination h
    · right; right; left; linear_combination h
    · right; right; right; left; field_simp; linear_combination -h
    · right; right; right; right; left; field_simp; linear_combination h
    · right; right; right; right; right; field_simp; linear_combination h
  · rintro (h | h | h | h | h | h) <;> subst h
    · left; left; left; left; left; rfl
    · left; left; left; left; right; field_simp
    · left; left; left; right; ring
    · left; left; right; field_simp; ring
    · left; right; field_simp
    · right; field_simp; ring

end Quillen.Notebook1973_3
