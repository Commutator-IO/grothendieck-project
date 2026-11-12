import Mathlib

/-!
# Quillen, notebook 1969-4, pp. 44–45: `(p ^ j)! / p ^ (1 + p + ⋯ + p ^ (j - 1)) ≡ (-1) ^ j` mod `p`

Daniel Quillen's research notebook 1969-4 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201969/1969-4.pdf>) states, on
p. 44, a lemma on the power series `(1 - e ^ (-f X)) / (f X)`, where `f ^ (p - 1) = p`: it is
`p`-integral and congruent modulo `p` to the sum of the `(-1) ^ j X ^ (p ^ j - 1)`. The proof
(p. 45) rests on two arithmetic facts about factorials: the `p`-adic valuation of `(p ^ j)!` is
`(p ^ j - 1) / (p - 1)`, and the quotient of `(p ^ j)!` by that power of `p` is congruent to
`(-1) ^ j` modulo `p`. For the second he splits the integers up to `p ^ j` into those prime to
`p` and those divisible by `p`, and cites Wilson.

This file proves the two arithmetic facts, for every prime `p` (for `p = 2` the congruence says
that the quotient is odd). The statement on the power series itself is not formalised.

* `block`, `primeToPart`: the product of the integers `p m + 1, …, p m + p - 1`, and the product
  of the integers up to `p m` that are prime to `p`;
* `factorial_mul`: `(p m)! = p ^ m * m ! * primeToPart p m`, the splitting of the page;
* `block_zmod`, `primeToPart_zmod`: modulo `p` these are `-1` (Wilson) and `(-1) ^ m`;
* `exists_factorial_pow_eq`: `(p ^ j)! = p ^ (1 + p + ⋯ + p ^ (j - 1)) * a` with
  `a ≡ (-1) ^ j` modulo `p`;
* `factorial_pow_div_zmod`: **the congruence of the page**;
* `padicValNat_factorial_pow`: the valuation of `(p ^ j)!` (a case of Legendre's formula).
-/

namespace Quillen.Notebook1969_4

open Finset Nat

/-- The product of the `p - 1` integers `p m + 1, …, p m + p - 1`. -/
def block (p m : ℕ) : ℕ := ∏ i ∈ range (p - 1), (p * m + 1 + i)

/-- The product of the integers `≤ p m` that are prime to `p` (for `p` prime). -/
def primeToPart (p m : ℕ) : ℕ := ∏ k ∈ range m, block p k

/-- The splitting of p. 45: the integers up to `p m` are those prime to `p` and the multiples
`p, 2 p, …, m p` of `p`. -/
theorem factorial_mul {p : ℕ} (hp : 0 < p) (m : ℕ) :
    (p * m)! = p ^ m * m ! * primeToPart p m := by
  induction m with
  | zero => simp [primeToPart]
  | succ m ih =>
    have h1 : (p * (m + 1))! = (p * m)! * (p * m + 1).ascFactorial p := by
      rw [Nat.factorial_mul_ascFactorial, mul_add, mul_one]
    have h2 : (p * m + 1).ascFactorial p = block p m * (p * (m + 1)) := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      rw [Nat.ascFactorial_eq_prod_range, prod_range_succ, block, Nat.add_sub_cancel]
      ring
    rw [h1, h2, ih, primeToPart, primeToPart, prod_range_succ, Nat.factorial_succ, pow_succ]
    ring

/-- Wilson: the product of `p m + 1, …, p m + p - 1` is `-1` modulo `p`. -/
theorem block_zmod (p : ℕ) [Fact p.Prime] (m : ℕ) : ((block p m : ℕ) : ZMod p) = -1 := by
  rw [← ZMod.wilsons_lemma (p := p), ← Finset.prod_range_add_one_eq_factorial, block]
  push_cast
  refine prod_congr rfl fun i _ => ?_
  simp [add_comm]

/-- The product of the integers up to `p m` prime to `p` is `(-1) ^ m` modulo `p`. -/
theorem primeToPart_zmod (p : ℕ) [Fact p.Prime] (m : ℕ) :
    ((primeToPart p m : ℕ) : ZMod p) = (-1) ^ m := by
  simp [primeToPart, block_zmod]

/-- Modulo a prime `p`, `(-1) ^ (p ^ j) = -1` (for `p = 2` both sides are `1`). -/
theorem neg_one_pow_pow (p : ℕ) [hp : Fact p.Prime] (j : ℕ) :
    ((-1 : ZMod p)) ^ (p ^ j) = -1 := by
  rcases hp.out.eq_two_or_odd' with rfl | h
  · simp
  · exact (h.pow).neg_one_pow

/-- `(p ^ j)!` is `p ^ (1 + p + ⋯ + p ^ (j - 1))` times an integer congruent to `(-1) ^ j`
modulo `p`. -/
theorem exists_factorial_pow_eq (p : ℕ) [hp : Fact p.Prime] (j : ℕ) :
    ∃ a : ℕ, (p ^ j)! = p ^ (∑ i ∈ range j, p ^ i) * a ∧ (a : ZMod p) = (-1) ^ j := by
  induction j with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ j ih =>
    obtain ⟨a, ha, ha'⟩ := ih
    refine ⟨a * primeToPart p (p ^ j), ?_, ?_⟩
    · rw [pow_succ', factorial_mul hp.out.pos, ha, sum_range_succ, pow_add]
      ring
    · rw [Nat.cast_mul, ha', primeToPart_zmod, neg_one_pow_pow, pow_succ]

/-- **Quillen, notebook 1969-4, p. 45.** For a prime `p` and `j ≥ 0`, the quotient of `(p ^ j)!`
by `p ^ ((p ^ j - 1) / (p - 1))` is congruent to `(-1) ^ j` modulo `p`. -/
theorem factorial_pow_div_zmod (p : ℕ) [hp : Fact p.Prime] (j : ℕ) :
    (((p ^ j)! / p ^ ((p ^ j - 1) / (p - 1)) : ℕ) : ZMod p) = (-1) ^ j := by
  obtain ⟨a, ha, ha'⟩ := exists_factorial_pow_eq p j
  rw [← Nat.geomSum_eq hp.out.two_le j, ha,
    Nat.mul_div_cancel_left _ (pow_pos hp.out.pos _), ha']

/-- **Quillen, notebook 1969-4, p. 45.** The `p`-adic valuation of `(p ^ j)!` is
`(p ^ j - 1) / (p - 1)`. -/
theorem padicValNat_factorial_pow (p : ℕ) [hp : Fact p.Prime] (j : ℕ) :
    padicValNat p (p ^ j)! = (p ^ j - 1) / (p - 1) := by
  obtain ⟨a, ha, ha'⟩ := exists_factorial_pow_eq p j
  have hpa : ¬ p ∣ a := by
    intro h
    rw [← ZMod.natCast_eq_zero_iff, ha'] at h
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) h
  have ha0 : a ≠ 0 := fun h => hpa (h ▸ dvd_zero p)
  rw [← Nat.geomSum_eq hp.out.two_le j, ha,
    padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) ha0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hpa, add_zero]

end Quillen.Notebook1969_4
