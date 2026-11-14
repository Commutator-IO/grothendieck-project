import Mathlib

/-!
# Quillen, notebook 1986-12: the geometric-sum bound and the Cayley resolvent bound

Daniel Quillen's research notebook 1986-12 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201986/1986-12.pdf>).

* p. 23: in a normed ring with `‖g^k‖ ≤ 1` for all `k`, `‖g^n − 1‖ ≤ n‖g − 1‖`
  (`norm_pow_sub_one_le`).
* p. 53: `|t + 1|² − |t − 1|² = 4 Re t` (`norm_add_one_sq_sub`), so
  `|t + 1| − |t − 1| ≥ 2 Re t/(1 + |t|)` for `Re t > 0` (`norm_add_one_sub_ge`), and for a
  linear isometry `g`, `‖((t + 1)g + (t − 1))v‖ ≥ (|t + 1| − |t − 1|)‖v‖` (`norm_cayley_ge`).
-/

namespace Quillen.Notebook1986_12

open Finset

/-- **p. 23.** In a normed ring, if `‖g^k‖ ≤ 1` for all `k`, then `‖g^n − 1‖ ≤ n ‖g − 1‖`. -/
theorem norm_pow_sub_one_le {R : Type*} [NormedRing R] {g : R} (hg : ∀ k : ℕ, ‖g ^ k‖ ≤ 1)
    (n : ℕ) : ‖g ^ n - 1‖ ≤ n * ‖g - 1‖ := by
  rw [← geom_sum_mul]
  calc _ ≤ ‖∑ k ∈ range n, g ^ k‖ * ‖g - 1‖ := norm_mul_le _ _
    _ ≤ (∑ k ∈ range n, ‖g ^ k‖) * ‖g - 1‖ := by gcongr; exact norm_sum_le _ _
    _ ≤ (∑ _k ∈ range n, (1 : ℝ)) * ‖g - 1‖ := by gcongr with k; exact hg k
    _ = _ := by simp

/-- **p. 53.** `|t + 1|² − |t − 1|² = 4 Re t`. -/
theorem norm_add_one_sq_sub (t : ℂ) : ‖t + 1‖ ^ 2 - ‖t - 1‖ ^ 2 = 4 * t.re := by
  rw [Complex.sq_norm, Complex.sq_norm]; simp [Complex.normSq_apply]; ring

/-- **p. 53.** For `Re t > 0`, `|t + 1| − |t − 1| ≥ 2 Re t / (1 + |t|)`. -/
theorem norm_add_one_sub_ge {t : ℂ} (ht : 0 < t.re) :
    2 * t.re / (1 + ‖t‖) ≤ ‖t + 1‖ - ‖t - 1‖ := by
  have h1 : ‖t + 1‖ ≤ ‖t‖ + 1 := by simpa using norm_add_le t 1
  have h2 : ‖t - 1‖ ≤ ‖t‖ + 1 := by simpa using norm_sub_le t 1
  have hs : 0 < ‖t + 1‖ + ‖t - 1‖ := by
    have : t + 1 ≠ 0 := fun h => by
      have := congrArg Complex.re (eq_neg_of_add_eq_zero_left h); simp at this; linarith
    positivity
  have key : (‖t + 1‖ - ‖t - 1‖) * (‖t + 1‖ + ‖t - 1‖) = 4 * t.re := by
    rw [← norm_add_one_sq_sub]; ring
  rw [div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (t + 1), norm_nonneg (t - 1)]

/-- **p. 53.** For a linear isometry `g`, `‖((t + 1)g + (t − 1))v‖ ≥ (|t + 1| − |t − 1|)‖v‖`. -/
theorem norm_cayley_ge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (g : E →ₗᵢ[ℂ] E)
    (t : ℂ) (v : E) : (‖t + 1‖ - ‖t - 1‖) * ‖v‖ ≤ ‖(t + 1) • g v + (t - 1) • v‖ := by
  have := norm_sub_norm_le ((t + 1) • g v) (-((t - 1) • v))
  simp only [norm_neg, norm_smul, LinearIsometry.norm_map, sub_neg_eq_add] at this
  linarith

end Quillen.Notebook1986_12
