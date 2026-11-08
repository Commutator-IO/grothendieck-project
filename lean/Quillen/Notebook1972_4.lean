import Mathlib

/-!
# Quillen, notebook 1972-4, pp. 23–25: from the microcanonical to the Gibbs distribution

Daniel Quillen's research notebook 1972-4 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201972/1972-4.pdf>) has, in a
run dated April 16, 1972 on statistical mechanics, a computation for `N` independent harmonic
oscillators `H = ∑ (pᵢ² + qᵢ²)/2` (pp. 18–25). In our words: the volume of the energy shell
`H = E` is `(2π)^N E^(N-1)/(N-1)!`; conditioning on total energy `E`, the first oscillator has the
density `(N-1)/(2πE) · (1 - r²/(2E))^(N-2)` on the disc `r² ≤ 2E` of its phase plane
(p. 23); and when `N → ∞` with `E = λN`, this density tends to the Gibbs density
`e^(-r²/(2λ))/(2πλ)` (p. 24). The same limit for the energy of the first oscillator, whose
conditional density is `(N-1)/E · (1 - E₁/E)^(N-2)` on `[0, E]`, gives `e^(-E₁/λ)/λ` (p. 25).

This file proves the two limits and the normalisation of the energy density.

* `tendsto_pred_div_mul_one_sub_pow`: `(N-1)/N · (1 - x/N)^(N-2) → e^(-x)`;
* `tendsto_oscillator_marginal`: the limit of p. 24, Heaviside factor included;
* `tendsto_energy_marginal`: the limit of p. 25;
* `integral_energy_marginal`: for `E > 0`, `∫₀^E (m+1)/E · (1 - u/E)^m du = 1`, so that the
  conditional density of the energy of one oscillator among `N = m + 2` is a probability density.
-/

namespace Quillen.Notebook1972_4

open Filter Topology Real

/-- The key limit: `(N-1)/N · (1 - x/N)^(N-2) → e^(-x)` as `N → ∞`. -/
theorem tendsto_pred_div_mul_one_sub_pow (x : ℝ) :
    Tendsto (fun N : ℕ => ((N : ℝ) - 1) / N * (1 - x / N) ^ (N - 2)) atTop (𝓝 (exp (-x))) := by
  set a : ℕ → ℝ := fun N => 1 + (-x) / N with ha
  have ha1 : Tendsto a atTop (𝓝 1) := by
    have : Tendsto (fun N : ℕ => (-x) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa [ha] using this.const_add 1
  have hpow : Tendsto (fun N : ℕ => a N ^ N) atTop (𝓝 (exp (-x))) :=
    tendsto_one_add_div_pow_exp (-x)
  have hsq : Tendsto (fun N : ℕ => a N ^ 2) atTop (𝓝 1) := by
    simpa using ha1.pow 2
  have hfrac : Tendsto (fun N : ℕ => ((N : ℝ) - 1) / N) atTop (𝓝 1) := by
    have h : Tendsto (fun N : ℕ => 1 - 1 / (N : ℝ)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (N : ℝ) ≠ 0 := by positivity
    field_simp
  have hlim : Tendsto (fun N : ℕ => ((N : ℝ) - 1) / N * (a N ^ N / a N ^ 2)) atTop
      (𝓝 (1 * (exp (-x) / 1))) :=
    hfrac.mul (hpow.div hsq one_ne_zero)
  rw [one_mul, div_one] at hlim
  refine hlim.congr' ?_
  -- eventually `a N ≠ 0` and `N ≥ 2`, so `a N ^ (N - 2) = a N ^ N / a N ^ 2`
  have hne : ∀ᶠ N : ℕ in atTop, a N ≠ 0 :=
    ha1.eventually (isOpen_ne.mem_nhds one_ne_zero)
  filter_upwards [hne, eventually_ge_atTop 2] with N hN h2
  have e1 : (1 - x / N) = a N := by simp only [ha]; ring
  rw [e1]
  congr 1
  rw [div_eq_iff (pow_ne_zero 2 hN), ← pow_add, Nat.sub_add_cancel h2]

/-- **Quillen, notebook 1972-4, p. 24.** For `N` harmonic oscillators with total energy `λN`, the
conditional density of the first one at radius `r` in its phase plane,
`(N-1)/(2πλN) · (1 - r²/(2λN))^(N-2)` on the disc `r² ≤ 2λN` and `0` outside, tends to the
Gibbs density `e^(-r²/(2λ))/(2πλ)` as `N → ∞`. -/
theorem tendsto_oscillator_marginal {lam : ℝ} (hlam : 0 < lam) (r : ℝ) :
    Tendsto (fun N : ℕ => ((N : ℝ) - 1) / (2 * π * lam * N) *
        (1 - r ^ 2 / (2 * lam * N)) ^ (N - 2) *
        (if r ^ 2 ≤ 2 * lam * N then 1 else 0)) atTop
      (𝓝 (exp (-(r ^ 2 / (2 * lam))) / (2 * π * lam))) := by
  have h := (tendsto_pred_div_mul_one_sub_pow (r ^ 2 / (2 * lam))).div_const (2 * π * lam)
  refine h.congr' ?_
  -- eventually `r² ≤ 2λN`, so the Heaviside factor is `1`
  have hbig : ∀ᶠ N : ℕ in atTop, r ^ 2 ≤ 2 * lam * N := by
    have : Tendsto (fun N : ℕ => 2 * lam * (N : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
    exact this.eventually_ge_atTop _
  filter_upwards [hbig, eventually_ge_atTop 1] with N hN h1
  simp only [hN, ↓reduceIte, mul_one]
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have e : r ^ 2 / (2 * lam) / N = r ^ 2 / (2 * lam * N) := by
    field_simp
  rw [e]
  field_simp

/-- **Quillen, notebook 1972-4, p. 25.** For `N` harmonic oscillators with total energy `λN`, the
conditional density of the energy `E₁` of the first one, `(N-1)/(λN) · (1 - E₁/(λN))^(N-2)`,
tends to `e^(-E₁/λ)/λ` as `N → ∞`. -/
theorem tendsto_energy_marginal {lam : ℝ} (hlam : 0 < lam) (E₁ : ℝ) :
    Tendsto (fun N : ℕ => ((N : ℝ) - 1) / (lam * N) * (1 - E₁ / (lam * N)) ^ (N - 2)) atTop
      (𝓝 (exp (-(E₁ / lam)) / lam)) := by
  have h := (tendsto_pred_div_mul_one_sub_pow (E₁ / lam)).div_const lam
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N h1
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hl : lam ≠ 0 := hlam.ne'
  have e : E₁ / lam / N = E₁ / (lam * N) := by field_simp
  rw [e]
  field_simp

/-- **Quillen, notebook 1972-4, pp. 24–25**, the finite-`N` density is normalised: for `E > 0`
and `N = m + 2` oscillators, `∫₀^E (N-1)/E · (1 - u/E)^(N-2) du = 1`. -/
theorem integral_energy_marginal {E : ℝ} (hE : 0 < E) (m : ℕ) :
    ∫ u in (0 : ℝ)..E, ((m : ℝ) + 1) / E * (1 - u / E) ^ m = 1 := by
  have hE0 : E ≠ 0 := hE.ne'
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) E,
      HasDerivAt (fun u : ℝ => -(1 - u / E) ^ (m + 1)) (((m : ℝ) + 1) / E * (1 - u / E) ^ m) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => 1 - u / E) (-(1 / E)) u := by
      simpa using (hasDerivAt_id u).div_const E |>.const_sub 1
    have h2 := (h1.pow (m + 1)).neg
    convert h2 using 1
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · simp [hE0]
  · apply Continuous.intervalIntegrable
    fun_prop

end Quillen.Notebook1972_4
