import Mathlib

/-!
# Quillen, notebook 1990-2, pp. 2-3, 99: the exact finite order of `κ̃`; the first Green operator

Daniel Quillen's research notebook 1990-2 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201990/1990-2.pdf>). On
pp. 2-3 the Karoubi operator `κ` satisfies `κ^{n(n+1)} = 1 + N` with `N² = 0`, `κN = N`; the
page corrects it to `κ̃ = κ − cN` so that `κ̃^{n(n+1)} = 1`.

In any `ℚ`-algebra, with `κ`, `N` commuting, `N² = 0`, `κN = N`:

* `pow_sub_smul`: `(κ − cN)^j = κ^j − (jc)N` for every `j`;
* `pow_eq_one_iff`: if `κ^m = 1 + N` and `N ≠ 0`, then `(κ − cN)^m = 1 ↔ mc = 1`; the page's
  case is `m = n(n+1)`, `c = 1/(n(n+1))` (`pow_eq_one`).

On p. 99, the « first Green operator »: in any ring, for any `σ`,
`(1 − σ) Σ_{j<n} j σ^{n−1−j} = n − Σ_{i<n} σ^i` (`one_sub_mul_green`).
-/

namespace Quillen.Notebook1990_2

section Kappa

variable {R : Type*} [Ring R] [Algebra ℚ R] {κ N : R}

omit [Algebra ℚ R] in
theorem pow_mul_eq (hκN : κ * N = N) (j : ℕ) : κ ^ j * N = N := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, mul_assoc, hκN, ih]

/-- **Notebook 1990-2, pp. 2-3**: `(κ − cN)^j = κ^j − (jc)N`. -/
theorem pow_sub_smul (hc : Commute κ N) (hNN : N * N = 0) (hκN : κ * N = N) (c : ℚ) (j : ℕ) :
    (κ - c • N) ^ j = κ ^ j - ((j : ℚ) * c) • N := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hNκ : N * κ = N := by rw [← hc.eq, hκN]
    rw [pow_succ, ih]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, pow_mul_eq hκN,
      hNκ, hNN, smul_zero, sub_zero, ← pow_succ]
    push_cast
    rw [add_mul, one_mul, add_smul]
    abel

/-- **Notebook 1990-2, pp. 2-3**: if `κ^m = 1 + N` with `N ≠ 0`, then `(κ − cN)^m = 1` iff
`mc = 1`. -/
theorem pow_eq_one_iff (hc : Commute κ N) (hNN : N * N = 0) (hκN : κ * N = N) (hN : N ≠ 0)
    {m : ℕ} (hm : κ ^ m = 1 + N) (c : ℚ) : (κ - c • N) ^ m = 1 ↔ (m : ℚ) * c = 1 := by
  rw [pow_sub_smul hc hNN hκN, hm, add_sub_assoc, add_eq_left, sub_eq_zero]
  exact ⟨fun h => smul_left_injective ℚ hN (by simpa using h.symm), fun h => by rw [h, one_smul]⟩

/-- The page's normalisation: `κ̃ = κ − N/(n(n+1))` has `κ̃^{n(n+1)} = 1`. -/
theorem pow_eq_one (hc : Commute κ N) (hNN : N * N = 0) (hκN : κ * N = N) {n : ℕ} (hn : 0 < n)
    (hm : κ ^ (n * (n + 1)) = 1 + N) :
    (κ - (1 / ((n : ℚ) * (n + 1))) • N) ^ (n * (n + 1)) = 1 := by
  rw [pow_sub_smul hc hNN hκN, hm, show ((n * (n + 1) : ℕ) : ℚ) * (1 / ((n : ℚ) * (n + 1))) = 1 by
    push_cast; field_simp [hn.ne'], one_smul, add_sub_cancel_right]

end Kappa

section Green

variable {R : Type*} [Ring R] (σ : R)

/-- **Notebook 1990-2, p. 99**: `(1 − σ) Σ_{j<n} j σ^{n−1−j} = n − Σ_{i<n} σ^i`. -/
theorem one_sub_mul_green (n : ℕ) :
    (1 - σ) * ∑ j ∈ Finset.range n, (j : R) * σ ^ (n - 1 - j) =
      n - ∑ i ∈ Finset.range n, σ ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hS : ∑ j ∈ Finset.range (n + 1), (j : R) * σ ^ (n + 1 - 1 - j) =
        σ * ∑ j ∈ Finset.range n, (j : R) * σ ^ (n - 1 - j) + n := by
      rw [Finset.sum_range_succ, Finset.mul_sum, Nat.add_sub_cancel, Nat.sub_self, pow_zero,
        mul_one]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj : j < n := Finset.mem_range.mp hj
      rw [← mul_assoc, (Nat.cast_commute j σ).eq.symm, mul_assoc, ← pow_succ']
      congr 2; omega
    rw [hS, mul_add, ← mul_assoc, show (1 - σ) * σ = σ * (1 - σ) by noncomm_ring, mul_assoc, ih,
      Finset.sum_range_succ', pow_zero]
    simp only [mul_sub, Finset.mul_sum, ← pow_succ', Nat.cast_succ, sub_mul, one_mul]
    abel

end Green

end Quillen.Notebook1990_2
