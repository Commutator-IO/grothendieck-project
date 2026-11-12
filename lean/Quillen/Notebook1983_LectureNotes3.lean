import Mathlib

/-!
# Quillen, 1983 lecture notes 3 (Kirwan), p. 2: from increasing ratios to `v₀ ^ (n - 1) vₙ ≤ v₁ ^ n`

Daniel Quillen's notes of a lecture of Frances Kirwan, in the 1983 file « Lecture Notes 3
Kirwan » (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201983/1983-Lecture%20Notes%203%20Kirwan.pdf>),
state on p. 2 the Alexandrov–Fenchel inequalities for the mixed volumes `v₀, …, vₙ` of two convex
bodies of `ℝⁿ`, in the form `v₀ / v₁ ≤ v₁ / v₂ ≤ ⋯ ≤ vₙ₋₁ / vₙ`, and note that they imply
`(v₀ / v₁) ^ n ≤ v₀ / vₙ`, that is `v₀ ^ (n - 1) vₙ ≤ v₁ ^ n`, which for a ball is the
isoperimetric inequality.

This file proves that implication, for positive real numbers `v₀, …, vₙ`. The Alexandrov–Fenchel
inequalities themselves are not formalised (mathlib has no mixed volumes).

* `mul_le_mul_of_ratios`: `v₀ vₖ₊₁ ≤ v₁ vₖ` for `k < n` (the first ratio is the smallest);
* `pow_mul_le_pow_mul`: `v₀ ^ k vₖ ≤ v₁ ^ k v₀` for `k ≤ n`;
* `pow_pred_mul_le_pow`: **the implication of the page**, `v₀ ^ (n - 1) vₙ ≤ v₁ ^ n`;
* `div_pow_le_div`: the same in the form `(v₀ / v₁) ^ n ≤ v₀ / vₙ`.
-/

namespace Quillen.Notebook1983_LectureNotes3

variable {n : ℕ} {v : ℕ → ℝ}

/-- If the ratios `vⱼ / vⱼ₊₁` increase, each is at least the first: `v₀ vₖ₊₁ ≤ v₁ vₖ`. -/
theorem mul_le_mul_of_ratios (hv : ∀ j ≤ n, 0 < v j)
    (h : ∀ j, j + 2 ≤ n → v j * v (j + 2) ≤ v (j + 1) ^ 2) :
    ∀ k, k + 1 ≤ n → v 0 * v (k + 1) ≤ v 1 * v k := by
  intro k
  induction k with
  | zero => intro _; rw [mul_comm]
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := h k (by omega)
    have hk0 := hv k (by omega)
    have hk1 := hv (k + 1) (by omega)
    have h0 := hv 0 (by omega)
    refine le_of_mul_le_mul_right ?_ hk0
    calc v 0 * v (k + 1 + 1) * v k = v 0 * (v k * v (k + 2)) := by ring
      _ ≤ v 0 * v (k + 1) ^ 2 := by gcongr
      _ = v 0 * v (k + 1) * v (k + 1) := by ring
      _ ≤ v 1 * v k * v (k + 1) := by gcongr
      _ = v 1 * v (k + 1) * v k := by ring

/-- `v₀ ^ k vₖ ≤ v₁ ^ k v₀` for `k ≤ n`. -/
theorem pow_mul_le_pow_mul (hv : ∀ j ≤ n, 0 < v j)
    (h : ∀ j, j + 2 ≤ n → v j * v (j + 2) ≤ v (j + 1) ^ 2) :
    ∀ k, k ≤ n → v 0 ^ k * v k ≤ v 1 ^ k * v 0 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := mul_le_mul_of_ratios hv h k hk
    have h0 := hv 0 (by omega)
    have h1' := hv 1 (by omega)
    calc v 0 ^ (k + 1) * v (k + 1) = v 0 ^ k * (v 0 * v (k + 1)) := by ring
      _ ≤ v 0 ^ k * (v 1 * v k) := by gcongr
      _ = v 1 * (v 0 ^ k * v k) := by ring
      _ ≤ v 1 * (v 1 ^ k * v 0) := by gcongr
      _ = v 1 ^ (k + 1) * v 0 := by ring

/-- **Quillen, 1983 lecture notes 3 (Kirwan), p. 2.** Let `v₀, …, vₙ` be positive reals, `n ≥ 1`,
with `v₀ / v₁ ≤ v₁ / v₂ ≤ ⋯ ≤ vₙ₋₁ / vₙ` (written `vⱼ vⱼ₊₂ ≤ vⱼ₊₁ ^ 2`). Then
`v₀ ^ (n - 1) vₙ ≤ v₁ ^ n`. -/
theorem pow_pred_mul_le_pow (hn : 1 ≤ n) (hv : ∀ j ≤ n, 0 < v j)
    (h : ∀ j, j + 2 ≤ n → v j * v (j + 2) ≤ v (j + 1) ^ 2) :
    v 0 ^ (n - 1) * v n ≤ v 1 ^ n := by
  have h0 := hv 0 (by omega)
  have key := pow_mul_le_pow_mul hv h n le_rfl
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine le_of_mul_le_mul_right ?_ h0
  calc v 0 ^ (m + 1 - 1) * v (m + 1) * v 0 = v 0 ^ (m + 1) * v (m + 1) := by
        rw [Nat.add_sub_cancel]; ring
    _ ≤ v 1 ^ (m + 1) * v 0 := key

/-- The same implication in the form of the page: `(v₀ / v₁) ^ n ≤ v₀ / vₙ`. -/
theorem div_pow_le_div (hv : ∀ j ≤ n, 0 < v j)
    (h : ∀ j, j + 2 ≤ n → v j * v (j + 2) ≤ v (j + 1) ^ 2) :
    (v 0 / v 1) ^ n ≤ v 0 / v n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [(hv 0 le_rfl).ne']
  have h1 := hv 1 (by omega)
  have hn' := hv n le_rfl
  rw [div_pow, div_le_div_iff₀ (pow_pos h1 n) hn', mul_comm (v 0)]
  exact pow_mul_le_pow_mul hv h n le_rfl

end Quillen.Notebook1983_LectureNotes3
