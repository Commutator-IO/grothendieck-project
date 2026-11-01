import Mathlib

/-!
# Bourbaki, rédaction n° 551 (March 1970): a pseudo-covariance depends on the diagonal

Rédaction 551 of the Bourbaki archive (Archives Henri Poincaré, item 1102), Annexe 2 « Noyaux de
type positif », by Cartier, studies covariances on a measured space `(T, m)`: real functions `C`
on `T × T` whose matrices `(C(tᵢ, tⱼ))` are symmetric positive semidefinite. A *pseudo-covariance*
(n° 4, p. 40) is a measurable `C` such that, for every `n` and almost every `(t₁, …, tₙ) ∈ Tⁿ`,
the matrix `(C(tᵢ, tⱼ))` is symmetric positive semidefinite. The page then says that a measurable
function equal almost everywhere on `T × T` to a pseudo-covariance is again one, and Th. 5
(p. 41) gives conditions a)–d) said to be equivalent, of which only a) is not invariant under
change on a null set of `T × T`.

Both fail when `m` has no atoms: the diagonal of `T × T` is then null, but for `n = 1` the
condition reads `C(t, t) ≥ 0` for almost every `t ∈ T`, a condition on the diagonal. The function
equal to `-1` on the diagonal and `0` elsewhere is almost everywhere equal to the covariance `0`
(so it satisfies b), c), d) of Th. 5), and it is not a pseudo-covariance. The ironic « Note de
l'éditeur » at the end of the annex (p. 46) makes the same remark.

* `prod_diagonal_eq_zero`: for a measure without atoms, the diagonal is null in `T × T`;
* `C`, `C_ae_eq_zero`: the function `-1` on the diagonal, `0` elsewhere, is a.e. zero on `ℝ × ℝ`;
* `zero_posSemidef`: the zero function is a covariance;
* `C_not_pseudoCovariance`: for every `t`, the `1 × 1` matrix `(C(t, t))` is not positive
  semidefinite, so `C` fails the condition for `n = 1` everywhere.
-/

open MeasureTheory

namespace Bourbaki.Redaction551

/-- For a measure without atoms, the diagonal of `T × T` is null. -/
theorem prod_diagonal_eq_zero {T : Type*} [MeasurableSpace T] [MeasurableEq T]
    (m : Measure T) [SFinite m] [NullSingletonClass m] :
    (m.prod m) (Set.diagonal T) = 0 := by
  rw [Measure.prod_apply measurableSet_diagonal]
  simp [Set.preimage, Set.diagonal]

/-- The function equal to `-1` on the diagonal and to `0` elsewhere. -/
noncomputable def C (t t' : ℝ) : ℝ := if t = t' then -1 else 0

/-- `C` is almost everywhere zero on `ℝ × ℝ`. -/
theorem C_ae_eq_zero :
    (fun p : ℝ × ℝ => C p.1 p.2) =ᵐ[(volume : Measure ℝ).prod volume] 0 := by
  have h := prod_diagonal_eq_zero (volume : Measure ℝ)
  refine measure_mono_null (fun p hp => ?_) h
  by_contra hne
  simp [C] at hp
  exact hne hp

/-- The zero function is a covariance: all its matrices are positive semidefinite. -/
theorem zero_posSemidef (n : ℕ) (t : Fin n → ℝ) :
    (Matrix.of fun i j => (0 : ℝ → ℝ → ℝ) (t i) (t j)).PosSemidef := by
  have : (Matrix.of fun i j => (0 : ℝ → ℝ → ℝ) (t i) (t j)) = 0 := by ext; simp
  rw [this]; exact Matrix.PosSemidef.zero

/-- `C` is not a pseudo-covariance: for every `t`, the `1 × 1` matrix `(C(t, t))` is `(-1)`. -/
theorem C_not_pseudoCovariance (t : ℝ) :
    ¬ (Matrix.of fun (_ _ : Fin 1) => C t t).PosSemidef := by
  intro h
  have := h.diag_nonneg (i := 0)
  simp [C] at this
  linarith

end Bourbaki.Redaction551
