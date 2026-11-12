import Mathlib

/-!
# Quillen, notebook 1989-4, p. 28: faithful functionals on a matrix algebra

Daniel Quillen's research notebook 1989-4 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201989/1989-4.pdf>).

Every linear functional on `Mₙ(K)` is `x ↦ tr(Tx)` for a unique `T`; the page uses that it is
faithful (nondegenerate: for every `a ≠ 0` some `tr(Tαa) ≠ 0`) iff `T` is invertible
(`faithful_iff`), over a field. If `T` is singular, a nonzero row vector `v` with `vT = 0`
gives `a` (all rows `v`) with `aT = 0`, so `tr(Tαa) = tr(αaT) = 0`; if `T` is invertible,
`α = T⁻¹E_{ji}` picks out the entry `a_{ij}`. The description of all functionals as
`tr(T ·)` is not restated (mathlib: `Matrix.traceForm`, nondegenerate trace pairing).
-/

namespace Quillen.Notebook1989_4Faithful

open Matrix

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Notebook 1989-4, p. 28**: `x ↦ tr(Tx)` is faithful on `Mₙ(K)` iff `T` is invertible. -/
theorem faithful_iff (T : Matrix n n K) :
    (∀ a : Matrix n n K, a ≠ 0 → ∃ α : Matrix n n K, trace (T * α * a) ≠ 0) ↔ IsUnit T := by
  constructor
  · intro h
    by_contra hT
    rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hT
    obtain ⟨v, hv, hvT⟩ := exists_vecMul_eq_zero_iff.mpr hT
    let a : Matrix n n K := Matrix.of fun _ j => v j
    have ha : a ≠ 0 := by
      intro h0
      apply hv
      funext j
      obtain ⟨i⟩ : Nonempty n := by
        by_contra hn
        exact hv (funext fun j => (hn ⟨j⟩).elim)
      simpa [a] using congrFun (congrFun h0 i) j
    have haT : a * T = 0 := by
      ext i j
      have := congrFun hvT j
      simpa [a, mul_apply, vecMul, dotProduct] using this
    obtain ⟨α, hα⟩ := h a ha
    apply hα
    rw [trace_mul_comm, ← Matrix.mul_assoc, haT, Matrix.zero_mul, trace_zero]
  · intro hT a ha
    obtain ⟨i, j, hij⟩ : ∃ i j, a i j ≠ 0 := by
      by_contra hn
      push Not at hn
      exact ha (Matrix.ext hn)
    refine ⟨T⁻¹ * single j i 1, ?_⟩
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det T).mp hT),
      Matrix.one_mul, trace_single_mul, one_smul]
    exact hij

end Quillen.Notebook1989_4Faithful
