import Mathlib

/-!
# Quillen, notebook 1987-5, p. 64: `ℤ[1/p] + ℤ_p = ℚ_p` and `ℤ[1/p] ∩ ℤ_p = ℤ`

Daniel Quillen's research notebook 1987-5 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201987/1987-5.pdf>) uses, on
p. 64, the decomposition of the `p`-adic numbers as the sum of the `p`-adic integers and of the
rationals with a power of `p` as denominator, the two meeting in `ℤ`.

* `exists_eq_add`: every `x ∈ ℚ_p` is `m / p^k + z` with `m ∈ ℤ`, `k ∈ ℕ`, `z ∈ ℤ_p`;
* `dvd_of_norm_div_le_one`: if `m / p^k ∈ ℤ_p` then `p^k ∣ m`;
* `inter_eq_int`: a rational number `m / p^k` that is a `p`-adic integer is an integer.
-/

namespace Quillen.Notebook1987_5

variable {p : ℕ} [hp : Fact p.Prime]

/-- `ℤ[1/p] + ℤ_p = ℚ_p`. -/
theorem exists_eq_add (x : ℚ_[p]) :
    ∃ (m : ℤ) (k : ℕ) (z : ℤ_[p]), x = (m : ℚ_[p]) / (p : ℚ_[p]) ^ k + z := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  by_cases hx : x = 0
  · exact ⟨0, 0, 0, by simp [hx]⟩
  set k := (-x.valuation).toNat
  have hnorm : ‖(p : ℚ_[p]) ^ k * x‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hx, ← zpow_add₀
      (by exact_mod_cast hp.out.ne_zero)]
    apply zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le)
    omega
  set y : ℤ_[p] := ⟨(p : ℚ_[p]) ^ k * x, hnorm⟩
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec k y)
  refine ⟨(PadicInt.appr y k : ℤ), k, w, ?_⟩
  have hw' : (w : ℚ_[p]) * (p : ℚ_[p]) ^ k
      = (p : ℚ_[p]) ^ k * x - (PadicInt.appr y k : ℚ_[p]) := by
    have := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hw
    push_cast at this
    exact this
  have hpk : (p : ℚ_[p]) ^ k ≠ 0 := pow_ne_zero _ hp0
  field_simp
  push_cast
  linear_combination -hw'

/-- If `m / p^k` is a `p`-adic integer, then `p^k ∣ m`. -/
theorem dvd_of_norm_div_le_one (m : ℤ) (k : ℕ)
    (h : ‖(m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ ≤ 1) : (p ^ k : ℤ) ∣ m := by
  rw [← Padic.norm_int_le_pow_iff_dvd]
  have hp0 : (p : ℚ_[p]) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [← div_mul_cancel₀ (m : ℚ_[p]) hp0, norm_mul, Padic.norm_p_pow]
  exact mul_le_of_le_one_left (zpow_nonneg (by positivity) _) h

/-- `ℤ[1/p] ∩ ℤ_p = ℤ`: a rational number with denominator a power of `p` that is a `p`-adic
integer is an integer. -/
theorem inter_eq_int (m : ℤ) (k : ℕ) (h : ‖(((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℚ_[p])‖ ≤ 1) :
    ∃ n : ℤ, (m : ℚ) / (p : ℚ) ^ k = n := by
  push_cast at h
  obtain ⟨n, hn⟩ := dvd_of_norm_div_le_one m k h
  have hp0 : (p : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  exact ⟨n, by rw [hn]; push_cast; field_simp⟩

end Quillen.Notebook1987_5
