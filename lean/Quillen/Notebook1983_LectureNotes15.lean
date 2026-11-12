import Mathlib

/-!
# Quillen, 1983 lecture notes 15 (Patterson), p. 1: the ball model and the hyperboloid

Daniel Quillen's notes of a lecture of S. J. Patterson, in the 1983 file « Lecture Notes 15
Patterson » (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201983/1983-Lecture%20Notes%2015%20Patterson.pdf>),
begin with the ball model of hyperbolic space. On p. 1 the function
`L (w, w') = ‖w - w'‖² / ((1 - ‖w‖²) (1 - ‖w'‖²))` is introduced, with a map `p` from the ball to
`ℝ × ℝ^(N+1)` and the quadratic form `q (y, x) = y² - ‖x‖²`; the notes state that `q (p x) = 1`
and `1 + 2 L (x, x') = q (p x, p x')`, so that the isometries come from the orthogonal group of
`q`.

As the map `p` is written in the notes, `x ↦ (½ (1 + ‖x‖²) / (1 - ‖x‖²), x / (1 - ‖x‖²))`, both
identities are off by a factor 4: `q (p x) = 1/4` and `1 + 2 L = 4 q (p x, p x')`. They hold as
stated for twice that map. This file proves the corrected identities and the two with the
factor, in any real inner product space, for points with `‖x‖² ≠ 1`.

* `L`, `pT`, `pS`: the function `L` and the two components of the map
  `x ↦ ((1 + ‖x‖²) / (1 - ‖x‖²), 2 x / (1 - ‖x‖²))`;
* `q_p`: `pT x ^ 2 - ‖pS x‖ ^ 2 = 1`, the image lies on the hyperboloid;
* `one_add_two_L`: **the identity of the page**, `1 + 2 L x x' = pT x * pT x' - ⟪pS x, pS x'⟫`;
* `q_half_p`, `one_add_two_L_half`: with the map as written in the notes, the values are `1/4`
  and `4 q (p x, p x')`.
-/

namespace Quillen.Notebook1983_LectureNotes15

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The function `L (x, x') = ‖x - x'‖² / ((1 - ‖x‖²) (1 - ‖x'‖²))` of p. 1. -/
noncomputable def L (x x' : E) : ℝ := ‖x - x'‖ ^ 2 / ((1 - ‖x‖ ^ 2) * (1 - ‖x'‖ ^ 2))

/-- The time component `(1 + ‖x‖²) / (1 - ‖x‖²)` of the map to the hyperboloid. -/
noncomputable def pT (x : E) : ℝ := (1 + ‖x‖ ^ 2) / (1 - ‖x‖ ^ 2)

/-- The space component `2 x / (1 - ‖x‖²)` of the map to the hyperboloid. -/
noncomputable def pS (x : E) : E := (2 / (1 - ‖x‖ ^ 2)) • x

/-- The image of `x` lies on the hyperboloid `q = 1`. -/
theorem q_p {x : E} (hx : ‖x‖ ^ 2 ≠ 1) : pT x ^ 2 - ‖pS x‖ ^ 2 = 1 := by
  have h : 1 - ‖x‖ ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  rw [pT, pS, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp
  ring

/-- **Quillen, 1983 lecture notes 15 (Patterson), p. 1** (with the map `p` doubled). For `x`,
`x'` with `‖x‖² ≠ 1`, `‖x'‖² ≠ 1`: `1 + 2 L (x, x')` is the value at `(p x, p x')` of the
bilinear form of `q (y, x) = y² - ‖x‖²`. -/
theorem one_add_two_L {x x' : E} (hx : ‖x‖ ^ 2 ≠ 1) (hx' : ‖x'‖ ^ 2 ≠ 1) :
    1 + 2 * L x x' = pT x * pT x' - ⟪pS x, pS x'⟫ := by
  have h : 1 - ‖x‖ ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have h' : 1 - ‖x'‖ ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx')
  rw [L, pT, pT, pS, pS, inner_smul_left, inner_smul_right, norm_sub_sq_real]
  simp only [conj_trivial]
  field_simp
  ring

/-- With the map as written in the notes (half of `p`), the quadratic form takes the value
`1/4`, not `1`. -/
theorem q_half_p {x : E} (hx : ‖x‖ ^ 2 ≠ 1) :
    (pT x / 2) ^ 2 - ‖(1 / 2 : ℝ) • pS x‖ ^ 2 = 1 / 4 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have := q_p hx
  linear_combination (1 / 4 : ℝ) * this

/-- With the map as written in the notes, `1 + 2 L (x, x') = 4 q (p x, p x')`. -/
theorem one_add_two_L_half {x x' : E} (hx : ‖x‖ ^ 2 ≠ 1) (hx' : ‖x'‖ ^ 2 ≠ 1) :
    1 + 2 * L x x' =
      4 * (pT x / 2 * (pT x' / 2) - ⟪(1 / 2 : ℝ) • pS x, (1 / 2 : ℝ) • pS x'⟫) := by
  rw [inner_smul_left, inner_smul_right, one_add_two_L hx hx']
  simp only [conj_trivial]
  ring

end Quillen.Notebook1983_LectureNotes15
