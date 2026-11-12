import Mathlib

/-!
# Quillen, notebook 1973-8, p. 62: `χ(t) = t + t² + t⁴ + ⋯` inverts `t ↦ t + t²`

Daniel Quillen's research notebook 1973-8 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201973/1973-8.pdf>) uses, on
p. 62, the antipode `χ(Sq)` of the total Steenrod square: on a class `t` of degree one, where
`Sq(t) = t + t²`, it acts by `χ(Sq)(t) = t + t² + t⁴ + ⋯`, so that `Sq(χ(Sq) t) = t`.

The algebraic content is an identity of formal power series in characteristic `2`:
`χ = ∑_k t^{2^k}` satisfies `χ + χ² = t`. This file proves it over any commutative ring of
characteristic `2`, from mathlib's Frobenius formula `f² = map frob (expand 2 f)`, with the
uniqueness of such a series.

* `chi`: the series `∑_{k ≥ 0} t^{2^k}`;
* `chi_add_chi_sq`: **the identity of the page**, `χ + χ² = t`;
* `eq_chi_of_add_sq`: `χ` is the only series without constant term with `f + f² = t`
  (in any commutative ring, without the characteristic hypothesis for uniqueness).

The Steenrod algebra itself is not formalised.
-/

namespace Quillen.Notebook1973_8

open PowerSeries

variable {R : Type*} [CommRing R]

open Classical in
/-- `χ(t) = t + t² + t⁴ + t⁸ + ⋯`. -/
noncomputable def chi : R⟦X⟧ := mk fun n => if ∃ k, n = 2 ^ k then 1 else 0

open Classical in
theorem coeff_chi (n : ℕ) : coeff n (chi : R⟦X⟧) = if ∃ k, n = 2 ^ k then 1 else 0 := by
  simp [chi]

theorem coeff_chi_sq [CharP R 2] (n : ℕ) :
    coeff n ((chi : R⟦X⟧) ^ 2) = if 2 ∣ n then coeff (n / 2) (chi : R⟦X⟧) else 0 := by
  rw [← map_frobenius_expand 2 two_ne_zero, coeff_map, coeff_expand]
  split_ifs with h
  · rw [coeff_chi]
    split_ifs <;> simp [frobenius]
  · simp

/-- **Quillen, notebook 1973-8, p. 62**: `χ + χ² = t` in characteristic `2`. -/
theorem chi_add_chi_sq [CharP R 2] : (chi : R⟦X⟧) + chi ^ 2 = X := by
  ext n
  rw [map_add, coeff_chi_sq, coeff_X, coeff_chi]
  by_cases h1 : n = 1
  · subst h1
    rw [ite_eq_left ⟨0, rfl⟩, ite_eq_right (by omega)]
    simp
  rw [ite_eq_right h1]
  by_cases hp : ∃ k, n = 2 ^ k
  · obtain ⟨k, rfl⟩ := hp
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by
      rcases k with _ | k
      · simp at h1
      · simp⟩
    rw [ite_eq_left ⟨j + 1, rfl⟩, ite_eq_left (dvd_pow_self 2 (by omega)), coeff_chi,
      ite_eq_left ⟨j, by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]⟩]
    have : (2 : R) = 0 := CharP.cast_eq_zero R 2
    rw [← one_add_one_eq_two] at this
    exact this
  · rw [ite_eq_right hp]
    split_ifs with h2
    · rw [coeff_chi, ite_eq_right]
      · simp
      rintro ⟨j, hj⟩
      exact hp ⟨j + 1, by rw [pow_succ, ← hj, Nat.div_mul_cancel h2]⟩
    · simp

/-- Uniqueness: a series `f` without constant term with `f + f² = t` is `χ`. The argument:
`(f − g)(1 + f + g) = (f + f²) − (g + g²)`, and `1 + f + g` is a unit. -/
theorem eq_of_add_sq_eq {f g : R⟦X⟧} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : f + f ^ 2 = g + g ^ 2) : f = g := by
  have hu : IsUnit (1 + f + g) := isUnit_iff_constantCoeff.mpr (by simp [hf, hg])
  have : (f - g) * (1 + f + g) = 0 := by linear_combination h
  exact sub_eq_zero.mp ((hu.mul_left_eq_zero).mp this)

theorem constantCoeff_chi : constantCoeff (chi : R⟦X⟧) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_chi, ite_eq_right]
  rintro ⟨k, hk⟩
  exact absurd hk.symm (pow_ne_zero k two_ne_zero)

theorem eq_chi_of_add_sq [CharP R 2] {f : R⟦X⟧} (hf : constantCoeff f = 0)
    (h : f + f ^ 2 = X) : f = chi :=
  eq_of_add_sq_eq hf constantCoeff_chi (h.trans chi_add_chi_sq.symm)

end Quillen.Notebook1973_8
