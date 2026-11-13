import Mathlib

/-!
# Quillen, notebook 1970-5, p. 67: the index of `N_n(F_q)` in `O_n(F_q)` is odd when `4 ∣ q − 1`

Daniel Quillen's research notebook 1970-5 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201970/1970-5.pdf>) computes,
on pp. 65–67, the orders of the orthogonal groups `O_n(F_q)` and of the subgroups
`N_n(F_q) = (Σ_m ≀ O_2(F_q)) × (ℤ/2)^ε`, `n = 2m + ε`. On p. 67 he writes the two quotients

* `|O_{2m+1}| / |N_{2m+1}| = q^{m²} ∏_{j=1}^{m} (q^{2j} − 1) / (2j (q − 1))`,
* `|O_{2m}| / |N_{2m}| = q^{m(m−1)} (q^m − 1) / (m (q − 1)) · ∏_{j=1}^{m−1} (q^{2j} − 1) / (2j (q − 1))`,

says that they are prime to `2` when `4 ∣ q − 1`, and concludes that `N_n(F_q)` then contains a
Sylow 2-subgroup of `O_n(F_q)` (a result he attributes to Chevalley).

This file proves the arithmetic: for `q ≡ 1 mod 4`, numerator and denominator of each quotient
have the same 2-adic valuation.

* `padicValNat_pow_sub_one`: `v_2(q^k − 1) = v_2(q − 1) + v_2(k)` for `k ≥ 1` (lifting the
  exponent, from mathlib's `Int.two_pow_sub_pow'`);
* `padicValNat_odd_index`: **the odd-dimensional quotient**:
  `v_2(∏_{j=1}^{m} (q^{2j} − 1)) = v_2(2^m m! (q − 1)^m)`;
* `padicValNat_even_index`: **the even-dimensional quotient**: for `m ≥ 1`,
  `v_2((q^m − 1) ∏_{j=1}^{m−1} (q^{2j} − 1)) = v_2(m (q − 1) · 2^{m−1} (m − 1)! (q − 1)^{m−1})`;
* `not_padicValNat_odd_index_three`: the hypothesis `4 ∣ q − 1` is needed: for `q = 3`, `m = 1`
  the odd-dimensional quotient `(3² − 1)/(2 · 2) = 2` is even.

The group orders and the Sylow statement are not formalised; the powers of `q` are odd and do
not change the valuations.
-/

namespace Quillen.Notebook1970_5

open Finset

theorem padicValNat_prod {f : ℕ → ℕ} (hf : ∀ i, f i ≠ 0) (n : ℕ) :
    padicValNat 2 (∏ i ∈ range n, f i) = ∑ i ∈ range n, padicValNat 2 (f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, sum_range_succ, padicValNat.mul (prod_ne_zero_iff.mpr fun i _ => hf i)
      (hf n), ih]

variable {q : ℕ}

/-- Lifting the exponent for `q ≡ 1 mod 4`: `v_2(q^k − 1) = v_2(q − 1) + v_2(k)`, `k ≥ 1`. -/
theorem padicValNat_pow_sub_one (hq : q % 4 = 1) (hq1 : 1 < q) {k : ℕ} (hk : k ≠ 0) :
    padicValNat 2 (q ^ k - 1) = padicValNat 2 (q - 1) + padicValNat 2 k := by
  have h := Int.two_pow_sub_pow' k (x := (q : ℤ)) (y := 1) (by omega) (by omega)
  rw [one_pow] at h
  have hlt : 1 < q ^ k := Nat.one_lt_pow hk hq1
  have c1 : (((q ^ k - 1 : ℕ)) : ℤ) = (q : ℤ) ^ k - 1 := by
    rw [Nat.cast_sub hlt.le]; push_cast; ring
  have c2 : (((q - 1 : ℕ)) : ℤ) = (q : ℤ) - 1 := by omega
  have c3 := Int.natCast_emultiplicity 2 k
  have c4 := Int.natCast_emultiplicity 2 (q ^ k - 1)
  have c5 := Int.natCast_emultiplicity 2 (q - 1)
  simp only [Nat.cast_ofNat] at c3 c4 c5
  rw [← c1, ← c2, c3, c4, c5] at h
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, padicValNat_eq_emultiplicity (by omega),
    padicValNat_eq_emultiplicity (by omega), padicValNat_eq_emultiplicity hk]
  exact_mod_cast h

/-- Each factor: `v_2(q^{2j} − 1) = v_2(2 j (q − 1))` for `j ≥ 1`. -/
theorem padicValNat_factor (hq : q % 4 = 1) (hq1 : 1 < q) {j : ℕ} (hj : j ≠ 0) :
    padicValNat 2 (q ^ (2 * j) - 1) = padicValNat 2 (2 * j * (q - 1)) := by
  rw [padicValNat_pow_sub_one hq hq1 (by omega),
    padicValNat.mul (a := 2 * j) (b := q - 1) (by omega) (by omega),
    padicValNat.mul (a := 2) (b := j) (by omega) hj, padicValNat.self (by norm_num)]
  ring

/-- **Quillen, notebook 1970-5, p. 67, odd dimension.** For `q ≡ 1 mod 4`,
`∏_{j=1}^{m} (q^{2j} − 1)` and `2^m m! (q − 1)^m` have the same 2-adic valuation. -/
theorem padicValNat_odd_index (hq : q % 4 = 1) (hq1 : 1 < q) (m : ℕ) :
    padicValNat 2 (∏ j ∈ range m, (q ^ (2 * (j + 1)) - 1)) =
      padicValNat 2 (2 ^ m * m.factorial * (q - 1) ^ m) := by
  have hne : ∀ j, q ^ (2 * (j + 1)) - 1 ≠ 0 := fun j =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hq1)
  rw [padicValNat_prod hne, padicValNat.mul (by positivity) (pow_ne_zero _ (by omega)),
    padicValNat.mul (by positivity) (Nat.factorial_ne_zero m), padicValNat.prime_pow,
    padicValNat.pow]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, padicValNat_factor hq hq1 (by omega),
      padicValNat.mul (by omega) (by omega), padicValNat.mul (by omega) (by omega),
      Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero m),
      padicValNat.self (by norm_num)]
    ring

/-- **Quillen, notebook 1970-5, p. 67, even dimension.** For `q ≡ 1 mod 4` and `m ≥ 1`,
`(q^m − 1) ∏_{j=1}^{m−1} (q^{2j} − 1)` and `m (q − 1) · 2^{m−1} (m − 1)! (q − 1)^{m−1}` have the
same 2-adic valuation. -/
theorem padicValNat_even_index (hq : q % 4 = 1) (hq1 : 1 < q) {m : ℕ} (hm : m ≠ 0) :
    padicValNat 2 ((q ^ m - 1) * ∏ j ∈ range (m - 1), (q ^ (2 * (j + 1)) - 1)) =
      padicValNat 2 (m * (q - 1) * (2 ^ (m - 1) * (m - 1).factorial * (q - 1) ^ (m - 1))) := by
  have hne : ∀ j, q ^ (2 * (j + 1)) - 1 ≠ 0 := fun j =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hq1)
  rw [padicValNat.mul (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hm hq1))
      (prod_ne_zero_iff.mpr fun j _ => hne j),
    padicValNat.mul (mul_ne_zero hm (by omega))
      (mul_ne_zero (mul_ne_zero (by positivity) (Nat.factorial_ne_zero _))
        (pow_ne_zero _ (by omega))),
    padicValNat_odd_index hq hq1, padicValNat_pow_sub_one hq hq1 hm,
    padicValNat.mul (a := m) (b := q - 1) hm (by omega)]
  ring

/-- Without `4 ∣ q − 1` the statement fails: for `q = 3` and `m = 1`, `v_2(3² − 1) = 3` while
`v_2(2 · 1! · (3 − 1)) = 2`. -/
theorem not_padicValNat_odd_index_three :
    padicValNat 2 (∏ j ∈ range 1, (3 ^ (2 * (j + 1)) - 1)) ≠
      padicValNat 2 (2 ^ 1 * (1 : ℕ).factorial * (3 - 1) ^ 1) := by
  have h8 : padicValNat 2 8 = 3 := padicValNat.prime_pow 3
  have h4 : padicValNat 2 4 = 2 := padicValNat.prime_pow 2
  simp [h8, h4]

end Quillen.Notebook1970_5
