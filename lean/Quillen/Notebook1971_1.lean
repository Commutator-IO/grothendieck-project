import Mathlib

/-!
# Quillen, notebook 1971-1, pp. 3, 6–7: two binomial congruences and a product in characteristic `p`

Daniel Quillen's research notebook 1971-1 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201971/1971-1.pdf>) computes,
around the new year 1971, the cohomology of a metacyclic `p`-group `⟨x, y⟩` with
`x y x⁻¹ = y^{1+p}` through its Hochschild–Serre spectral sequence.

**p. 3.** To exclude a central extension he computes, modulo `p³`,
`(1 + p + β p²)^p ≡ 1 + p(p + βp²) + p((p − 1)/2)(p + βp²)² ≡ 1 + p²`, for `p` odd.

**pp. 6–7.** Restricting a representation to `⟨y⟩` he uses `(1 + p)^a ≡ 1 + a p (mod p²)` and
then, in a ring of characteristic `p`, `∏_{a=0}^{p−1} (1 + (1 + a p) c) = (1 + c)^p = 1 + c^p`.

This file proves:

* `three_terms`: `x³ ∣ (1 + x)^n − 1 − n x − C(n, 2) x²` in `ℤ`, and `two_terms`, the
  analogue modulo `x²`;
* `pow_congr_odd`: **p. 3**: `(1 + p + β p²)^p ≡ 1 + p² (mod p³)` for every odd natural
  number `p` (prime or not) and every integer `β`;
* `not_pow_congr_two`: the congruence fails for `p = 2` (the left side is `1` modulo `8`),
  which is why the page needs `p` odd;
* `one_add_pow_congr`: **p. 6**: `(1 + p)^a ≡ 1 + a p (mod p²)`;
* `prod_one_add`: **p. 7**: in a commutative ring of prime characteristic `p`,
  `∏_{a < p} (1 + (1 + a p) c) = 1 + c^p`.

The group cohomology, Chern classes and spectral sequences are not formalised.
-/

namespace Quillen.Notebook1971_1

open Finset

/-- `x³` divides `(1 + x)^n − 1 − n x − C(n, 2) x²`. -/
theorem three_terms (x : ℤ) (n : ℕ) :
    x ^ 3 ∣ (1 + x) ^ n - 1 - n * x - (n.choose 2 : ℕ) * x ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨(n.choose 2 : ℕ) + q * (1 + x), ?_⟩
    have h2 : ((n + 1).choose 2 : ℤ) = (n.choose 2 : ℕ) + n := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]; push_cast; ring
    have hpow : (1 + x) ^ (n + 1) = (1 + x) * (1 + x) ^ n := by ring
    rw [hpow, h2]
    have : (1 + x) ^ n = x ^ 3 * q + 1 + n * x + (n.choose 2 : ℕ) * x ^ 2 := by linarith
    rw [this]; push_cast; ring

/-- `x²` divides `(1 + x)^n − 1 − n x`. -/
theorem two_terms (x : ℤ) (n : ℕ) : x ^ 2 ∣ (1 + x) ^ n - 1 - n * x := by
  obtain ⟨q, hq⟩ := three_terms x n
  exact ⟨x * q + (n.choose 2 : ℕ), by linear_combination hq⟩

/-- **Quillen, notebook 1971-1, p. 3.** For `p` odd and any integer `β`,
`(1 + p + β p²)^p ≡ 1 + p² (mod p³)`. -/
theorem pow_congr_odd {p : ℕ} (hp : Odd p) (β : ℤ) :
    (1 + p + β * p ^ 2 : ℤ) ^ p ≡ 1 + p ^ 2 [ZMOD p ^ 3] := by
  obtain ⟨k, rfl⟩ := hp
  set x : ℤ := (2 * k + 1 : ℕ) * (1 + β * (2 * k + 1 : ℕ))
  have hx : (1 + ((2 * k + 1 : ℕ) : ℤ) + β * ((2 * k + 1 : ℕ) : ℤ) ^ 2) = 1 + x := by
    simp only [x]; ring
  have hchoose : ((2 * k + 1).choose 2 : ℤ) = (2 * k + 1 : ℕ) * k := by
    rw [Nat.choose_two_right]
    have : (2 * k + 1) * (2 * k + 1 - 1) / 2 = (2 * k + 1) * k := by
      rw [show 2 * k + 1 - 1 = 2 * k by omega, show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k)
        by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [this]; push_cast; ring
  obtain ⟨q, hq⟩ := three_terms x (2 * k + 1)
  rw [hx, Int.modEq_iff_dvd]
  refine ⟨-(q * (1 + β * (2 * k + 1 : ℕ)) ^ 3) - β - k * (1 + β * (2 * k + 1 : ℕ)) ^ 2, ?_⟩
  rw [hchoose] at hq
  simp only [x] at hq ⊢
  push_cast at hq ⊢
  linear_combination -hq

/-- **The congruence fails for `p = 2`**: `(3 + 4β)² ≡ 1 (mod 8)`, not `5`. -/
theorem not_pow_congr_two (β : ℤ) :
    ¬ (1 + 2 + β * 2 ^ 2 : ℤ) ^ 2 ≡ 1 + 2 ^ 2 [ZMOD 2 ^ 3] := by
  rw [Int.ModEq, show (1 + 2 + β * 2 ^ 2 : ℤ) ^ 2 = 8 * (1 + 3 * β + 2 * β ^ 2) + 1 by ring]
  generalize (1 + 3 * β + 2 * β ^ 2) = m
  omega

/-- **Quillen, notebook 1971-1, p. 6.** `(1 + p)^a ≡ 1 + a p (mod p²)`. -/
theorem one_add_pow_congr (p a : ℕ) : (1 + p : ℤ) ^ a ≡ 1 + a * p [ZMOD p ^ 2] := by
  rw [Int.modEq_comm, Int.modEq_iff_dvd]
  obtain ⟨q, hq⟩ := two_terms (p : ℤ) a
  exact ⟨q, by linear_combination hq⟩

/-- **Quillen, notebook 1971-1, p. 7.** In a commutative ring of prime characteristic `p`,
`∏_{a < p} (1 + (1 + a p) c) = 1 + c^p`. -/
theorem prod_one_add {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p] (c : R) :
    ∏ a ∈ range p, (1 + (1 + (a : R) * p) * c) = 1 + c ^ p := by
  simp only [CharP.cast_eq_zero, mul_zero, add_zero, one_mul, prod_const, card_range]
  rw [add_pow_char, one_pow]

end Quillen.Notebook1971_1
