import Mathlib

/-!
# Quillen, notebook 1972-6, p. 40: the denominators of `B_{2s} / 4s` and the valuations of `p^t - 1`

Daniel Quillen's research notebook 1972-6 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201972/1972-6.pdf>) studies,
on pp. 34–40 and 49–55, the image of `J` in `K_*(ℤ)`. On p. 40, under « Some number theory », he
writes the denominator `m(2s)` of `B_{2s} / 4s` (Bernoulli numbers in the convention where
`B_2 = 1/6`; the topologists' `B_s` is this `B_{2s}`) as a product `∏ ℓ^{m_ℓ(2s)}`, with, for `ℓ`
odd and `p` an integer generating `ℤ_ℓ^×`,

* `m_ℓ(t) = v_ℓ(p^t − 1)`, which is `0` if `ℓ − 1 ∤ t` and `v_ℓ(t) + 1` if `ℓ − 1 ∣ t`;

and, for `ℓ = 2`,

* `m_2(t) = v_2(3^t − 1)`, which is `1` for `t` odd and `v_2(t) + 2` for `t` even.

He then tabulates `m(2s)` for `s = 1, …, 5`: `24`, `240`, `504`, `480`, `264`.

This file proves the two valuation formulas and the table. The identification of `m(2s)` with
the product of the `ℓ^{m_ℓ(2s)}` for all `s` (von Staudt–Clausen and Adams) is not formalised;
for `s ≤ 5` it can be read off the table and the formulas.

* `padicValNat_three_pow_sub_one_odd`, `padicValNat_three_pow_sub_one_even`: **the formula for
  `ℓ = 2`**;
* `padicValNat_pow_sub_one_of_not_dvd`, `padicValNat_pow_sub_one_of_dvd`: **the formula for `ℓ`
  odd**, for `p` whose class modulo `ℓ` has order `ℓ − 1` and with `p^{ℓ−1} ≢ 1 mod ℓ²` (these two
  conditions together say that `p` generates `(ℤ/ℓ²)^×`, hence `ℤ_ℓ^×`), and `t ≥ 1`;
* `den_bernoulli_div`: **the table**, `den (B_{2s} / 4s)` for `s = 1, …, 5`.
-/

namespace Quillen.Notebook1972_6

open Finset

/-- A natural number divisible by `ℓ` and not by `ℓ²` has `ℓ`-adic valuation `1`. -/
theorem padicValNat_eq_one {ℓ n : ℕ} [Fact ℓ.Prime] (hn : n ≠ 0) (h1 : ℓ ∣ n)
    (h2 : ¬ ℓ ^ 2 ∣ n) : padicValNat ℓ n = 1 := by
  have a := (padicValNat_dvd_iff_le (n := 1) hn).mp (by simpa using h1)
  have b : ¬ 2 ≤ padicValNat ℓ n := fun h => h2 ((padicValNat_dvd_iff_le hn).mpr h)
  omega

/-- **Quillen, notebook 1972-6, p. 40, `ℓ = 2`, `t` odd.** `v_2(3^t − 1) = 1`. -/
theorem padicValNat_three_pow_sub_one_odd {t : ℕ} (ht : Odd t) :
    padicValNat 2 (3 ^ t - 1) = 1 := by
  obtain ⟨k, rfl⟩ := ht
  have hpos : 1 ≤ 3 ^ (2 * k + 1) := Nat.one_le_pow _ _ (by norm_num)
  have hlt : 1 < 3 ^ (2 * k + 1) := Nat.one_lt_pow (by omega) (by norm_num)
  refine padicValNat_eq_one (Nat.sub_ne_zero_of_lt hlt) ?_ ?_
  · rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpos]
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    rw [show (3 : ZMod 2) = 1 from rfl, one_pow, sub_self]
  · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpos]
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    rw [pow_succ, pow_mul, show (3 : ZMod 4) ^ 2 = 1 from rfl, one_pow, one_mul]
    decide

/-- **Quillen, notebook 1972-6, p. 40, `ℓ = 2`, `t` even.** `v_2(3^t − 1) = v_2(t) + 2`
for `t ≠ 0`. -/
theorem padicValNat_three_pow_sub_one_even {t : ℕ} (ht : Even t) (h0 : t ≠ 0) :
    padicValNat 2 (3 ^ t - 1) = padicValNat 2 t + 2 := by
  have h := padicValNat.pow_two_sub_one (x := 3) (n := t) (by norm_num) (by decide) h0 ht
  have h4 : padicValNat 2 (3 + 1) = 2 := by
    rw [show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have h2 : padicValNat 2 (3 - 1) = 1 := by simp
  omega

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem dvd_pow_sub_one_iff {p t : ℕ} (hp : 1 ≤ p) :
    ℓ ∣ p ^ t - 1 ↔ (p : ZMod ℓ) ^ t = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hp), sub_eq_zero]
  simp

/-- **Quillen, notebook 1972-6, p. 40, `ℓ` odd, `ℓ − 1 ∤ t`.** If the class of `p` modulo `ℓ`
has order `ℓ − 1`, then `v_ℓ(p^t − 1) = 0` unless `ℓ − 1 ∣ t`. -/
theorem padicValNat_pow_sub_one_of_not_dvd {p t : ℕ} (hp : 1 ≤ p)
    (hord : orderOf (p : ZMod ℓ) = ℓ - 1) (ht : ¬ (ℓ - 1) ∣ t) :
    padicValNat ℓ (p ^ t - 1) = 0 := by
  refine padicValNat.eq_zero_of_not_dvd fun h => ht ?_
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one ((dvd_pow_sub_one_iff hp).mp h)

/-- **Quillen, notebook 1972-6, p. 40, `ℓ` odd, `ℓ − 1 ∣ t`.** If `ℓ` is odd, the class of `p`
modulo `ℓ` has order `ℓ − 1` and `p^{ℓ−1} ≢ 1` modulo `ℓ²` (that is, `p` generates `(ℤ/ℓ²)^×`),
then `v_ℓ(p^t − 1) = v_ℓ(t) + 1` for every `t ≥ 1` divisible by `ℓ − 1`. -/
theorem padicValNat_pow_sub_one_of_dvd (hodd : Odd ℓ) {p t : ℕ} (hp : 2 ≤ p)
    (hord : orderOf (p : ZMod ℓ) = ℓ - 1) (hsq : ¬ ℓ ^ 2 ∣ p ^ (ℓ - 1) - 1)
    (ht : (ℓ - 1) ∣ t) (ht0 : t ≠ 0) :
    padicValNat ℓ (p ^ t - 1) = padicValNat ℓ t + 1 := by
  obtain ⟨s, rfl⟩ := ht
  have hℓ2 : 2 ≤ ℓ := hℓ.out.two_le
  have hs : s ≠ 0 := by rintro rfl; simp at ht0
  have hx : 1 < p ^ (ℓ - 1) := Nat.one_lt_pow (by omega) (by omega)
  have hdvd : ℓ ∣ p ^ (ℓ - 1) - 1 := by
    rw [dvd_pow_sub_one_iff (by omega), ← hord]; exact pow_orderOf_eq_one _
  have hndvd : ¬ ℓ ∣ p ^ (ℓ - 1) := by
    intro h
    have : ℓ ∣ 1 := by
      have := Nat.dvd_sub h hdvd
      rwa [Nat.sub_sub_self hx.le] at this
    exact hℓ.out.one_lt.ne' (Nat.dvd_one.mp this)
  have h1 : padicValNat ℓ (p ^ (ℓ - 1) - 1) = 1 := padicValNat_eq_one (by omega) hdvd hsq
  have key := padicValNat.pow_sub_pow (p := ℓ) hodd hx (by simpa using hdvd) hndvd hs
  rw [one_pow, h1] at key
  rw [pow_mul, key, padicValNat.mul (by omega) hs]
  have : padicValNat ℓ (ℓ - 1) = 0 := padicValNat.eq_zero_of_not_dvd fun h =>
    absurd (Nat.le_of_dvd (by omega) h) (by omega)
  omega

/-! ### The table of p. 40 -/

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four,
    bernoulli'_eq_zero_of_odd (n := 5) (by decide) (by norm_num)]
  norm_num [Nat.choose]

theorem bernoulli'_eight : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_six,
    bernoulli'_eq_zero_of_odd (n := 5) (by decide) (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 7) (by decide) (by norm_num)]
  norm_num [Nat.choose]

theorem bernoulli'_ten : bernoulli' 10 = 5 / 66 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_six, bernoulli'_eight,
    bernoulli'_eq_zero_of_odd (n := 5) (by decide) (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 7) (by decide) (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 9) (by decide) (by norm_num)]
  norm_num [Nat.choose]

/-- **Quillen, notebook 1972-6, p. 40, the table.** The denominators of `B_{2s} / 4s` for
`s = 1, …, 5` are `24, 240, 504, 480, 264`. -/
theorem den_bernoulli_div :
    (bernoulli 2 / 4).den = 24 ∧ (bernoulli 4 / 8).den = 240 ∧ (bernoulli 6 / 12).den = 504 ∧
      (bernoulli 8 / 16).den = 480 ∧ (bernoulli 10 / 20).den = 264 := by
  simp only [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : (2 : ℕ) ≠ 1),
    bernoulli_eq_bernoulli'_of_ne_one (by norm_num : (4 : ℕ) ≠ 1),
    bernoulli_eq_bernoulli'_of_ne_one (by norm_num : (6 : ℕ) ≠ 1),
    bernoulli_eq_bernoulli'_of_ne_one (by norm_num : (8 : ℕ) ≠ 1),
    bernoulli_eq_bernoulli'_of_ne_one (by norm_num : (10 : ℕ) ≠ 1),
    bernoulli'_two, bernoulli'_four, bernoulli'_six, bernoulli'_eight, bernoulli'_ten]
  norm_num

end Quillen.Notebook1972_6
