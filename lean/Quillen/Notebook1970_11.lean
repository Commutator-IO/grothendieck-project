import Mathlib

/-!
# Quillen, notebook 1970-11, p. 17: the 2-parts of `|GL_n(F_q)|` and of `|N|` for `q ≡ 3 mod 4`

Daniel Quillen's research notebook 1970-11 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201970/1970-11.pdf>) attacks,
on p. 17, the mod 2 cohomology of `GL_n(F_q)` in the exceptional case `q ≡ 3 mod 4`, through
the subgroup `N = (Σ_m ≀ (Gal ⋉ F_{q²}^×)) × (F_q^×)^e`, `n = 2m + e`, `e ∈ {0, 1}`. He compares
the orders `|GL_n(F_q)| = q^{n(n−1)/2} ∏_{i=1}^n (q^i − 1)` and `|N| = m! (2(q² − 1))^m (q − 1)^e`
and says that they have the same power of `2`, because `v_2(q^i − 1) = 1` for `i` odd and
`v_2(q^{2i} − 1) = v_2(i) + v_2(q² − 1)`.

This file proves the two valuation formulas and the comparison of the 2-parts:

* `padicValNat_pow_odd_sub_one`: `v_2(q^k − 1) = 1` for `k` odd and `q ≡ 3 mod 4`;
* `padicValNat_pow_even_sub_one`: `v_2(q^{2i} − 1) = v_2(i) + v_2(q² − 1)` for `i ≥ 1` and any
  odd `q > 1`;
* `padicValNat_card_GL_eq`: **the claim of the page**: for `q ≡ 3 mod 4` and `n = 2m + e`,
  `v_2(q^{n(n−1)/2} ∏_{i=1}^n (q^i − 1)) = v_2(m! (2(q² − 1))^m (q − 1)^e)`.

The order formulas themselves and the group `N` are not formalised.
-/

namespace Quillen.Notebook1970_11

open Finset

theorem padicValNat_eq_one {n : ℕ} (hn : n ≠ 0) (h1 : 2 ∣ n) (h2 : ¬ 4 ∣ n) :
    padicValNat 2 n = 1 := by
  have a := (padicValNat_dvd_iff_le (n := 1) hn).mp (by simpa using h1)
  have b : ¬ 2 ≤ padicValNat 2 n := fun h =>
    h2 (by simpa using (padicValNat_dvd_iff_le (n := 2) hn).mpr h)
  omega

theorem padicValNat_prod {f : ℕ → ℕ} (hf : ∀ i, f i ≠ 0) (n : ℕ) :
    padicValNat 2 (∏ i ∈ range n, f i) = ∑ i ∈ range n, padicValNat 2 (f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, sum_range_succ, padicValNat.mul (prod_ne_zero_iff.mpr fun i _ => hf i)
      (hf n), ih]

variable {q : ℕ}

/-- `v_2(q^k − 1) = 1` for `k` odd and `q ≡ 3 mod 4`. -/
theorem padicValNat_pow_odd_sub_one (hq : q % 4 = 3) {k : ℕ} (hk : Odd k) :
    padicValNat 2 (q ^ k - 1) = 1 := by
  obtain ⟨j, rfl⟩ := hk
  have hq1 : 1 < q := by omega
  have hlt : 1 < q ^ (2 * j + 1) := Nat.one_lt_pow (by omega) hq1
  have hmod : q ^ (2 * j + 1) % 4 = 3 := by
    rw [Nat.pow_mod, hq, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  exact padicValNat_eq_one (by omega) (by omega) (by omega)

/-- `v_2(q^{2i} − 1) = v_2(i) + v_2(q² − 1)` for `i ≥ 1` and `q > 1` odd. -/
theorem padicValNat_pow_even_sub_one (hq1 : 1 < q) (hodd : ¬ 2 ∣ q) {i : ℕ} (hi : i ≠ 0) :
    padicValNat 2 (q ^ (2 * i) - 1) = padicValNat 2 i + padicValNat 2 (q ^ 2 - 1) := by
  have h := padicValNat.pow_two_sub_one hq1 hodd (n := 2 * i) (by omega) (even_two_mul i)
  have h2 : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    rw [← Nat.sq_sub_sq, one_pow]
  rw [padicValNat.mul (by omega) hi, padicValNat.self (by norm_num)] at h
  rw [h2, padicValNat.mul (by omega) (by omega)]
  omega

/-- The 2-adic valuation of `∏_{i=1}^{2m} (q^i − 1)` for `q ≡ 3 mod 4`. -/
theorem padicValNat_prod_even (hq : q % 4 = 3) (m : ℕ) :
    padicValNat 2 (∏ i ∈ range (2 * m), (q ^ (i + 1) - 1)) =
      m + padicValNat 2 m.factorial + m * padicValNat 2 (q ^ 2 - 1) := by
  have hq1 : 1 < q := by omega
  have hodd : ¬ 2 ∣ q := by omega
  have hne : ∀ i, q ^ (i + 1) - 1 ≠ 0 := fun i =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hq1)
  rw [padicValNat_prod hne]
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : padicValNat 2 (q ^ (2 * m + 1) - 1) = 1 :=
      padicValNat_pow_odd_sub_one hq ⟨m, rfl⟩
    have e2 : padicValNat 2 (q ^ (2 * m + 1 + 1) - 1) =
        padicValNat 2 (m + 1) + padicValNat 2 (q ^ 2 - 1) := by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
      exact padicValNat_pow_even_sub_one hq1 hodd (by omega)
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, e1, e2,
      Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero m)]
    ring

/-- **Quillen, notebook 1970-11, p. 17.** For `q ≡ 3 mod 4` and `n = 2m + e`, `e ∈ {0, 1}`, the
numbers `q^{n(n−1)/2} ∏_{i=1}^n (q^i − 1)` (the order of `GL_n(F_q)`) and
`m! (2(q² − 1))^m (q − 1)^e` (the order of `N`) have the same 2-adic valuation. -/
theorem padicValNat_card_GL_eq (hq : q % 4 = 3) (m e : ℕ) (he : e ≤ 1) :
    padicValNat 2 (q ^ ((2 * m + e) * (2 * m + e - 1) / 2) *
        ∏ i ∈ range (2 * m + e), (q ^ (i + 1) - 1)) =
      padicValNat 2 (m.factorial * (2 * (q ^ 2 - 1)) ^ m * (q - 1) ^ e) := by
  have hq1 : 1 < q := by omega
  have hne : ∀ i, q ^ (i + 1) - 1 ≠ 0 := fun i =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hq1)
  have hsq : q ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hq1)
  have hq0 : padicValNat 2 (q ^ ((2 * m + e) * (2 * m + e - 1) / 2)) = 0 := by
    rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd (by omega), mul_zero]
  have hv1 : padicValNat 2 (q - 1) = 1 := by
    simpa using padicValNat_pow_odd_sub_one hq (k := 1) odd_one
  rw [padicValNat.mul (pow_ne_zero _ (by omega)) (prod_ne_zero_iff.mpr fun i _ => hne i), hq0,
    zero_add, padicValNat.mul (mul_ne_zero (Nat.factorial_ne_zero m)
      (pow_ne_zero _ (mul_ne_zero (by norm_num) hsq))) (pow_ne_zero _ (by omega)),
    padicValNat.mul (Nat.factorial_ne_zero m) (pow_ne_zero _ (mul_ne_zero (by norm_num) hsq)),
    padicValNat.pow, padicValNat.pow,
    padicValNat.mul (by norm_num) hsq, padicValNat.self (by norm_num), hv1]
  interval_cases e
  · simpa [mul_add, add_comm, add_left_comm, add_assoc] using padicValNat_prod_even hq m
  · rw [prod_range_succ, padicValNat.mul (prod_ne_zero_iff.mpr fun i _ => hne i) (hne _),
      padicValNat_prod_even hq, padicValNat_pow_odd_sub_one hq ⟨m, rfl⟩]
    ring

end Quillen.Notebook1970_11
