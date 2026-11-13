import Mathlib

/-!
# Quillen, notebook 1982-12, p. 88: `(γ¹ ⋯ γ^m)² = (−1)^{m(m−1)/2}`

Daniel Quillen's research notebook 1982-12 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201982/1982-12.pdf>) sets, on
p. 88, `γ^{2n+1} = γ¹ ⋯ γ^{2n}` for the Clifford generators of an orthonormal basis and uses
`(γ^{2n+1})² = (−1)^{2n(2n−1)/2} = (−1)^n`, with `γ^{2n+1}` anticommuting with each `γ^i`.

This file proves the identity in any ring, from the relations alone: if `e 0, e 1, …` satisfy
`e i * e i = 1` and `e i * e j = −(e j * e i)` for `i ≠ j`, and `P m = e 0 * ⋯ * e (m − 1)`, then

* `prod_mul_prod`: **the identity of the page**, `P m * P m = (−1)^{m(m−1)/2}`;
* `prod_mul_prod_even`: for `m = 2n`, `P (2n) * P (2n) = (−1)^n`;
* `mul_prod_of_lt`: `e i * P m = (−1)^{m−1} P m * e i` for `i < m`, hence
  `mul_prod_even`: `Γ = P (2n)` anticommutes with each `e i`, `i < 2n`;
* `mul_prod_of_le`: `e i * P m = (−1)^m P m * e i` for `m ≤ i`.

The traces on the spinor module (pp. 88-89) are not formalised.
-/

namespace Quillen.Notebook1982_12

variable {R : Type*} [Ring R] (e : ℕ → R)

/-- `P m = e 0 * e 1 * ⋯ * e (m − 1)`. -/
def P : ℕ → R
  | 0 => 1
  | m + 1 => P m * e m

/-- The relations of the generators of a Clifford algebra of an orthonormal basis. -/
structure IsClifford : Prop where
  sq : ∀ i, e i * e i = 1
  anti : ∀ i j, i ≠ j → e i * e j = -(e j * e i)

variable {e}

theorem neg_one_pow_comm (k : ℕ) (x : R) : (-1 : R) ^ k * x = x * (-1) ^ k :=
  ((Commute.neg_one_left x).pow_left k).eq

theorem mul_prod_of_le (he : IsClifford e) {i m : ℕ} (hm : m ≤ i) :
    e i * P e m = (-1) ^ m * P e m * e i := by
  induction m with
  | zero => simp [P]
  | succ m ih =>
    rw [P, ← mul_assoc, ih (by omega), mul_assoc _ (e i), he.anti i m (by omega), pow_succ]
    simp only [mul_neg, neg_mul, mul_one, mul_assoc]

theorem mul_prod_of_lt (he : IsClifford e) {i m : ℕ} (hi : i < m) :
    e i * P e m = (-1) ^ (m - 1) * P e m * e i := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [P, Nat.add_sub_cancel]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · rw [← mul_assoc, ih h, mul_assoc _ (e i), he.anti i m (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ, mul_neg, neg_mul, mul_one, mul_assoc]
    · rw [← mul_assoc, mul_prod_of_le he le_rfl]; simp only [mul_assoc]

/-- **Quillen, notebook 1982-12, p. 88**: `(e 0 ⋯ e (m − 1))² = (−1)^{m(m−1)/2}`. -/
theorem prod_mul_prod (he : IsClifford e) (m : ℕ) :
    P e m * P e m = (-1) ^ (m * (m - 1) / 2) := by
  induction m with
  | zero => simp [P]
  | succ m ih =>
    simp only [P]
    have h : P e m * e m * (P e m * e m) = (-1) ^ m * (P e m * P e m) := by
      rw [mul_assoc, ← mul_assoc (e m), mul_prod_of_le he le_rfl, mul_assoc, mul_assoc,
        he.sq, mul_one, ← mul_assoc, ← neg_one_pow_comm]
      simp only [mul_assoc]
    rw [h, ih, ← pow_add, Nat.triangle_succ, add_comm]

/-- For `m = 2n`: `Γ² = (−1)^n`. -/
theorem prod_mul_prod_even (he : IsClifford e) (n : ℕ) :
    P e (2 * n) * P e (2 * n) = (-1) ^ n := by
  rw [prod_mul_prod he, mul_assoc, Nat.mul_div_cancel_left _ two_pos, pow_mul']
  rcases n with _ | n
  · simp
  · rw [Odd.neg_one_pow ⟨n, by omega⟩]

/-- `Γ = e 0 ⋯ e (2n − 1)` anticommutes with each `e i`, `i < 2n`. -/
theorem mul_prod_even (he : IsClifford e) {n i : ℕ} (hi : i < 2 * n) :
    e i * P e (2 * n) = -(P e (2 * n) * e i) := by
  rw [mul_prod_of_lt he hi]
  obtain ⟨k, hk⟩ : ∃ k, 2 * n - 1 = 2 * k + 1 := ⟨n - 1, by omega⟩
  rw [hk, pow_succ, pow_mul]
  simp

end Quillen.Notebook1982_12
