import Quillen.Notebook1990_3

/-!
# Quillen, notebook 1990-2, p. 14: the canonical Green operator does not depend on `n`

Daniel Quillen's research notebook 1990-2 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201990/1990-2.pdf>), p. 14.
For `κ` with `κⁿ = 1` in a `ℚ`-algebra, the projection `P_n = (1/n) Σ_{j<n} κʲ` and the Green
operator `Q_n = (1/n) Σ_{j<n} ((n − 1)/2 − j) κʲ` of `1 − κ` (notebook 1990-2, p. 11,
formalised as `Quillen.Notebook1990_3.proj` and `green`) do not depend on the period: if
`κ^m = 1` then `P_{km} = P_m` and `Q_{km} = Q_m` for `k, m ≥ 1` (`proj_mul`, `green_mul`).

The proof splits `j < km` as `j = qm + r`, and uses `Σ_{q<k} ((km − 1)/2 − qm − r) =
k((m − 1)/2 − r)` (`sum_range_mul_smul`).
-/

namespace Quillen.Notebook1990_2Green

open Finset Quillen.Notebook1990_3

variable {A : Type*} [Ring A] [Algebra ℚ A] {κ : A} {m : ℕ}

omit [Algebra ℚ A] in
theorem pow_add_mul (hκ : κ ^ m = 1) (q r : ℕ) : κ ^ (q * m + r) = κ ^ r := by
  rw [pow_add, pow_mul', hκ, one_pow, one_mul]

/-- `Σ_{j<km} (c − j) κʲ = Σ_{r<m} (kc − mk(k−1)/2 − kr) κʳ` when `κ^m = 1`. -/
theorem sum_range_mul_smul (hκ : κ ^ m = 1) (c : ℚ) (k : ℕ) :
    ∑ j ∈ range (k * m), (c - j) • κ ^ j =
      ∑ r ∈ range m, ((k : ℚ) * c - m * (k * (k - 1) / 2) - k * r) • κ ^ r := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_mul, one_mul, sum_range_add, ih, ← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [pow_add_mul hκ, ← add_smul]
    congr 1
    push_cast; ring

theorem sum_range_mul (hκ : κ ^ m = 1) (k : ℕ) :
    ∑ j ∈ range (k * m), κ ^ j = (k : ℚ) • ∑ r ∈ range m, κ ^ r := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_mul, one_mul, sum_range_add, ih]
    simp only [pow_add_mul hκ, Nat.cast_succ, add_smul, one_smul]

/-- **Notebook 1990-2, p. 14**: `P_{km} = P_m` when `κ^m = 1`. -/
theorem proj_mul (hκ : κ ^ m = 1) {k : ℕ} (hk : 0 < k) : proj (k * m) κ = proj m κ := by
  rw [proj, proj, sum_range_mul hκ, smul_smul]
  congr 1
  push_cast
  field_simp [hk.ne']

/-- **Notebook 1990-2, p. 14**: `Q_{km} = Q_m` when `κ^m = 1`. -/
theorem green_mul (hκ : κ ^ m = 1) {k : ℕ} (hk : 0 < k) : green (k * m) κ = green m κ := by
  rw [green, green, sum_range_mul_smul hκ, smul_sum, smul_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  push_cast
  field_simp [hk.ne', hm.ne']
  ring

end Quillen.Notebook1990_2Green
