import Quillen.Notebook1985_8

/-!
# Quillen, notebook 1987-11: the binomial series `(1 − α)^{−1/2}` at a nilpotent element

Daniel Quillen's research notebook 1987-11 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201987/1987-11.pdf>), p. 77. To
normalise an involution he uses `(1 − α)^{−1/2} = Σ_k C(2k, k) αᵏ / 4ᵏ` for a nilpotent `α`.

In any `ℚ`-algebra, if `α^N = 0`, the finite sum `s = Σ_{k<N} C(2k, k)/4ᵏ · αᵏ` satisfies
`s² (1 − α) = 1` (`sq_mul_one_sub`); if moreover `u² = 1 − α` with `u` commuting with `α`, then
`F = u s` is an involution, `F² = 1` (`involution`). The proof evaluates at `α` the truncation of
the formal identity `(Σ C(2k, k) xᵏ/4ᵏ)² (1 − x) = 1` (notebook 1985-8,
`Quillen.Notebook1985_8.centralSeries_sq_mul`): the polynomial `P² (1 − X) − 1`, with `P` the
truncation in degrees `< N`, is divisible by `X^N`.
-/

namespace Quillen.Notebook1987_11

open Polynomial Finset Nat

open Quillen.Notebook1985_8 (centralSeries centralSeries_sq_mul)

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The truncation of `Σ C(2k, k) xᵏ/4ᵏ` in degrees `< N`, evaluated at `α`. -/
noncomputable def s (N : ℕ) (α : A) : A := ∑ k ∈ range N, ((centralBinom k : ℚ) / 4 ^ k) • α ^ k

lemma s_eq_aeval (N : ℕ) (α : A) : s N α = aeval α (PowerSeries.trunc N centralSeries) := by
  rw [aeval_def, PowerSeries.eval₂_trunc_eq_sum_range, s]
  refine sum_congr rfl fun k _ => ?_
  simp [centralSeries, Algebra.smul_def]

lemma X_pow_dvd (N : ℕ) :
    (X : ℚ[X]) ^ N ∣ (PowerSeries.trunc N centralSeries) ^ 2 * (1 - X) - 1 := by
  rw [X_pow_dvd_iff]
  intro d hd
  have h : ((PowerSeries.trunc N centralSeries ^ 2 * (1 - X) - 1 : ℚ[X]) : PowerSeries ℚ) =
      (PowerSeries.trunc N centralSeries : PowerSeries ℚ) ^ 2 * (1 - PowerSeries.X) - 1 := by
    push_cast; rfl
  rw [← Polynomial.coeff_coe, h, ← PowerSeries.coeff_coe_trunc_of_lt hd, PowerSeries.trunc_sub,
    ← PowerSeries.trunc_trunc_mul, PowerSeries.trunc_trunc_pow, PowerSeries.trunc_trunc_mul,
    centralSeries_sq_mul, sub_self, Polynomial.coeff_coe]
  simp

/-- **Notebook 1987-11, p. 77**: `s² (1 − α) = 1` when `α^N = 0`. -/
theorem sq_mul_one_sub {N : ℕ} {α : A} (hα : α ^ N = 0) : s N α ^ 2 * (1 - α) = 1 := by
  obtain ⟨R, hR⟩ := X_pow_dvd N
  have := congrArg (aeval α) hR
  rw [map_sub, map_mul, map_pow, map_sub, map_one, aeval_X, map_mul, map_pow, aeval_X, hα,
    zero_mul, ← s_eq_aeval, sub_eq_zero] at this
  exact this

/-- **Notebook 1987-11, p. 77**: if `u² = 1 − α`, `u α = α u` and `α^N = 0`, then `F = u s` is an
involution. -/
theorem involution {N : ℕ} {α u : A} (hα : α ^ N = 0) (hu : u ^ 2 = 1 - α)
    (hcomm : Commute u α) : (u * s N α) ^ 2 = 1 := by
  have hc : Commute u (s N α) := by
    rw [s]
    exact Commute.sum_right _ _ _ fun k _ => (hcomm.pow_right k).smul_right _
  have hsα : Commute (s N α) α := by
    rw [s]
    exact Commute.sum_left _ _ _ fun k _ => ((Commute.refl α).pow_left k).smul_left _
  have hk : Commute (s N α ^ 2) (1 - α) := (Commute.one_right _).sub_right (hsα.pow_left 2)
  rw [hc.mul_pow, hu, ← hk.eq, sq_mul_one_sub hα]

end Quillen.Notebook1987_11
