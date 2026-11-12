import Mathlib

/-!
# Quillen, 1983 « Review Getzler material », pp. 6–7: composition of Cayley transforms

In the 1983 file « Review Getzler material » of Daniel Quillen's notes (Clay Mathematics
Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201983/1983-Review%20Getzler%20material.pdf>),
orthogonal transformations are written as Cayley transforms `(1 + X) / (1 - X)` of skew forms,
and pp. 6–7 compute their composition: the product of the Cayley transforms of `X` and `Y` is the
Cayley transform of
`Z = (1 - X)⁻¹ (X + Y) (1 + X Y)⁻¹ (1 - X)`
(the last line of p. 7; `X` and `Y` do not commute, and the page marks the computation
« subtle »).

This file proves the formula in any ring in which `1 - X`, `1 - Y` and `1 + X Y` are invertible;
it also shows that `1 - Z` is then invertible, which the Cayley transform of `Z` needs.

* `cayley X`: `(1 + X) (1 - X)⁻¹`, with `Ring.inverse`;
* `cayleySum X Y`: the element `Z` above;
* `one_sub_cayleySum`, `one_add_cayleySum`: `1 - Z = (1 - Y) (1 + X Y)⁻¹ (1 - X)` and
  `1 + Z = (1 - X)⁻¹ (1 + X) (1 + Y) (1 + X Y)⁻¹ (1 - X)`;
* `isUnit_one_sub_cayleySum`: `1 - Z` is a unit;
* `cayley_mul_cayley`: **the formula of the page**, `cayley X * cayley Y = cayley Z`.
-/

namespace Quillen.Notebook1983_ReviewGetzler

variable {R : Type*} [Ring R]

/-- The Cayley transform `(1 + X) (1 - X)⁻¹` (meaningful when `1 - X` is a unit). -/
noncomputable def cayley (X : R) : R := (1 + X) * Ring.inverse (1 - X)

/-- The element `Z = (1 - X)⁻¹ (X + Y) (1 + X Y)⁻¹ (1 - X)` of p. 7. -/
noncomputable def cayleySum (X Y : R) : R :=
  Ring.inverse (1 - X) * (X + Y) * Ring.inverse (1 + X * Y) * (1 - X)

section units

variable {X Y : R} {u v w : Rˣ} (hu : (u : R) = 1 - X) (hv : (v : R) = 1 - Y)
  (hw : (w : R) = 1 + X * Y)

include hu hv hw

omit hv in
theorem cayleySum_eq : cayleySum X Y = ↑u⁻¹ * (X + Y) * ↑w⁻¹ * ↑u := by
  rw [cayleySum, ← hu, ← hw, Ring.inverse_unit, Ring.inverse_unit]

/-- `1 - Z = (1 - Y) (1 + X Y)⁻¹ (1 - X)`. -/
theorem one_sub_cayleySum : 1 - cayleySum X Y = ↑v * ↑w⁻¹ * ↑u := by
  have key : X + Y = ↑w - ↑u * ↑v := by rw [hu, hv, hw]; noncomm_ring
  rw [cayleySum_eq hu hw, key]
  simp [mul_sub, sub_mul, mul_assoc]

omit hv in
/-- `1 + Z = (1 - X)⁻¹ (1 + X) (1 + Y) (1 + X Y)⁻¹ (1 - X)`. -/
theorem one_add_cayleySum :
    1 + cayleySum X Y = ↑u⁻¹ * ((1 + X) * (1 + Y)) * ↑w⁻¹ * ↑u := by
  have key : (1 + X) * (1 + Y) = ↑w + (X + Y) := by rw [hw]; noncomm_ring
  rw [cayleySum_eq hu hw, key]
  simp [mul_add, add_mul, mul_assoc]

/-- `1 - Z` is invertible, with inverse `(1 - X)⁻¹ (1 + X Y) (1 - Y)⁻¹`. -/
theorem one_sub_cayleySum_eq_unit : 1 - cayleySum X Y = ↑(v * w⁻¹ * u) := by
  rw [one_sub_cayleySum hu hv hw]; simp

omit hv hw in
theorem inv_mul_one_add_comm : (↑u⁻¹ : R) * (1 + X) = (1 + X) * ↑u⁻¹ := by
  have h : 1 + X = 1 + 1 - ↑u := by rw [hu]; abel
  rw [h]
  simp [mul_sub, sub_mul, mul_add, add_mul]

theorem cayley_mul_cayley_units :
    cayley X * cayley Y = cayley (cayleySum X Y) := by
  have h1 : cayley X = (1 + X) * ↑u⁻¹ := by rw [cayley, ← hu, Ring.inverse_unit]
  have h2 : cayley Y = (1 + Y) * ↑v⁻¹ := by rw [cayley, ← hv, Ring.inverse_unit]
  have h3 : cayley (cayleySum X Y) =
      (↑u⁻¹ * ((1 + X) * (1 + Y)) * ↑w⁻¹ * ↑u) * ↑(v * w⁻¹ * u)⁻¹ := by
    rw [cayley, one_sub_cayleySum_eq_unit hu hv hw, Ring.inverse_unit,
      one_add_cayleySum hu hw]
  rw [h1, h2, h3, ← inv_mul_one_add_comm hu]
  simp [mul_assoc]

end units

/-- If `1 - X`, `1 - Y` and `1 + X Y` are units, so is `1 - Z`. -/
theorem isUnit_one_sub_cayleySum {X Y : R} (hX : IsUnit (1 - X)) (hY : IsUnit (1 - Y))
    (hXY : IsUnit (1 + X * Y)) : IsUnit (1 - cayleySum X Y) := by
  obtain ⟨u, hu⟩ := hX
  obtain ⟨v, hv⟩ := hY
  obtain ⟨w, hw⟩ := hXY
  rw [one_sub_cayleySum_eq_unit hu hv hw]
  exact Units.isUnit _

/-- **Quillen, 1983 « Review Getzler material », p. 7.** In a ring where `1 - X`, `1 - Y` and
`1 + X Y` are invertible, the product of the Cayley transforms of `X` and `Y` is the Cayley
transform of `Z = (1 - X)⁻¹ (X + Y) (1 + X Y)⁻¹ (1 - X)`. -/
theorem cayley_mul_cayley {X Y : R} (hX : IsUnit (1 - X)) (hY : IsUnit (1 - Y))
    (hXY : IsUnit (1 + X * Y)) : cayley X * cayley Y = cayley (cayleySum X Y) := by
  obtain ⟨u, hu⟩ := hX
  obtain ⟨v, hv⟩ := hY
  obtain ⟨w, hw⟩ := hXY
  exact cayley_mul_cayley_units hu hv hw

end Quillen.Notebook1983_ReviewGetzler
