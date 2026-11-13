import Mathlib

/-!
# Quillen, notebook 1987-13, pp. 41-42: `Ker N = Im(1 − σ)`, `Im N = Ker(1 − σ)`

Daniel Quillen's research notebook 1987-13 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201987/1987-13.pdf>).

For a linear operator `σ` with `σⁿ = 1` on a module over a ring in which `n` is invertible, and
the norm `N = 1 + σ + ⋯ + σⁿ⁻¹`: `Ker N = Im(1 − σ)` (`ker_norm`) and `Im N = Ker(1 − σ)`
(`range_norm`) — the step of the page that identifies `P/[P, P]` with the coinvariants of the
cyclic group on `T(V)`. The proof is the averaging identity
`(1 − σ) Σ_{i<n} Σ_{j<i} σʲ = n − N` (`one_sub_mul_Q`).
-/

namespace Quillen.Notebook1987_13

open Finset

section Ring

variable {E : Type*} [Ring E] (σ : E) (n : ℕ)

/-- The norm `N = Σ_{i<n} σⁱ`. -/
def N : E := ∑ i ∈ range n, σ ^ i

/-- `Q = Σ_{i<n} Σ_{j<i} σʲ`. -/
def Q : E := ∑ i ∈ range n, ∑ j ∈ range i, σ ^ j

theorem one_sub_mul_Q : (1 - σ) * Q σ n = n - N σ n := by
  rw [Q, mul_sum]
  simp only [mul_neg_geom_sum, sum_sub_distrib, sum_const, card_range, nsmul_one, N]

theorem one_sub_mul_N (h : σ ^ n = 1) : (1 - σ) * N σ n = 0 := by
  rw [N, mul_neg_geom_sum, h, sub_self]

theorem N_mul_one_sub (h : σ ^ n = 1) : N σ n * (1 - σ) = 0 := by
  rw [N, geom_sum_mul_neg, h, sub_self]

end Ring

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
  (σ : Module.End R V) {n : ℕ}

/-- **Notebook 1987-13, pp. 41-42**: `Ker N = Im(1 − σ)` when `σⁿ = 1` and `n` is invertible. -/
theorem ker_norm (h : σ ^ n = 1) (hn : IsUnit (n : R)) :
    LinearMap.ker (N σ n) = LinearMap.range (1 - σ) := by
  refine le_antisymm (fun v hv => ?_) (LinearMap.range_le_ker_iff.2 (N_mul_one_sub σ n h))
  obtain ⟨c, hc⟩ := hn.exists_left_inv
  refine ⟨c • Q σ n v, ?_⟩
  rw [map_smul, ← Module.End.mul_apply, one_sub_mul_Q, LinearMap.sub_apply, LinearMap.mem_ker.1 hv,
    sub_zero, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul R, smul_smul, hc, one_smul]

/-- **Notebook 1987-13, pp. 41-42**: `Im N = Ker(1 − σ)` when `σⁿ = 1` and `n` is invertible. -/
theorem range_norm (h : σ ^ n = 1) (hn : IsUnit (n : R)) :
    LinearMap.range (N σ n) = LinearMap.ker (1 - σ) := by
  refine le_antisymm (LinearMap.range_le_ker_iff.2 (one_sub_mul_N σ n h)) fun v hv => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
  have hpow : ∀ i, (σ ^ i) v = v := fun i => by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, Module.End.mul_apply, ← hv, ih]
  obtain ⟨c, hc⟩ := hn.exists_left_inv
  refine ⟨c • v, ?_⟩
  simp only [map_smul, N, LinearMap.sum_apply, hpow, sum_const, card_range]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, hc, one_smul]

end Quillen.Notebook1987_13
