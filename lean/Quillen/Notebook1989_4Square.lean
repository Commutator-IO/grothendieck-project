import Mathlib

/-!
# Quillen, notebook 1989-4, pp. 53-54: powers in the square-zero extension of a cup product

Daniel Quillen's research notebook 1989-4 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201989/1989-4.pdf>).

Two derivations `X`, `Y` give the 2-cocycle `(a₁, a₂) ↦ Xa₁ Ya₂` and the square-zero extension
with product `a₁ * a₂ = a₁a₂ + Xa₁ Ya₂`. The page computes the `n`-th power for this product:
`a^{*n} = aⁿ + Σ_{i+j+k=n−2} aⁱ (Xa) aʲ (Ya) aᵏ` (boxed), by induction from
`a * (aⁿ + ⋯) = aⁿ⁺¹ + ⋯ + Xa Y(aⁿ)`.

Model: a ring `E` with additive maps `X`, `Y` satisfying the Leibniz rule; pairs `(a, m)` with
`(a, m) * (b, n) = (ab, an + mb + Xa Yb)` (`star`), an associative product (`star_assoc`) with
unit `(1, 0)`. Then `starPow_fst`, `starPow_snd`: the `(n+2)`-nd power of `(a, 0)` is
`(aⁿ⁺², Σ_{i+j+k=n} aⁱ Xa aʲ Ya aᵏ)`; `Y_pow`: `Y(aⁿ⁺¹) = Σ_{j+k=n} aʲ Ya aᵏ`. In the page the
second components live in `M ⊗_A N`; in the model they live in `E`, which is enough for the
identity (the page's own remark: the universal cocycle `da₁da₂` is a cup product). The
exponential version (p. 55) is not formalised.
-/

namespace Quillen.Notebook1989_4Square

open Finset

variable {E : Type*} [Ring E] (X Y : E →+ E)

/-- The product `(a, m) * (b, n) = (ab, an + mb + Xa Yb)`. -/
def star (u v : E × E) : E × E := (u.1 * v.1, u.1 * v.2 + u.2 * v.1 + X u.1 * Y v.1)

theorem star_assoc (hX : ∀ a b, X (a * b) = X a * b + a * X b)
    (hY : ∀ a b, Y (a * b) = Y a * b + a * Y b) (u v w : E × E) :
    star X Y (star X Y u v) w = star X Y u (star X Y v w) := by
  simp only [star, Prod.mk.injEq, hX, hY]
  exact ⟨mul_assoc _ _ _, by noncomm_ring⟩

theorem map_one_eq_zero (hY : ∀ a b, Y (a * b) = Y a * b + a * Y b) : Y 1 = 0 := by
  simpa using hY 1 1

theorem star_one (hY : ∀ a b, Y (a * b) = Y a * b + a * Y b) (u : E × E) :
    star X Y u (1, 0) = u := by
  simp [star, map_one_eq_zero Y hY]

theorem one_star (hX : ∀ a b, X (a * b) = X a * b + a * X b) (u : E × E) :
    star X Y (1, 0) u = u := by
  simp [star, map_one_eq_zero X hX]

/-- `a^{*n}`, as `a * (a * ⋯ (a * 1))`. -/
def starPow (a : E) : ℕ → E × E
  | 0 => (1, 0)
  | n + 1 => star X Y (a, 0) (starPow a n)

theorem starPow_fst (a : E) (n : ℕ) : (starPow X Y a n).1 = a ^ n := by
  induction n with
  | zero => simp [starPow]
  | succ n ih => simp [starPow, star, ih, pow_succ']

/-- `Y(aⁿ⁺¹) = Σ_{j+k=n} aʲ (Ya) aᵏ`. -/
theorem Y_pow (hY : ∀ a b, Y (a * b) = Y a * b + a * Y b) (a : E) (n : ℕ) :
    Y (a ^ (n + 1)) = ∑ x ∈ antidiagonal n, a ^ x.1 * Y a * a ^ x.2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', hY, ih, Nat.sum_antidiagonal_succ, mul_sum]
    simp only [pow_zero, one_mul, pow_succ', mul_assoc]

/-- **Notebook 1989-4, p. 54** (boxed): `a^{*(n+2)} = aⁿ⁺² + Σ_{i+j+k=n} aⁱ (Xa) aʲ (Ya) aᵏ`. -/
theorem starPow_snd (hY : ∀ a b, Y (a * b) = Y a * b + a * Y b) (a : E) (n : ℕ) :
    (starPow X Y a (n + 2)).2 =
      ∑ x ∈ antidiagonal n, ∑ y ∈ antidiagonal x.2,
        a ^ x.1 * X a * a ^ y.1 * Y a * a ^ y.2 := by
  induction n with
  | zero =>
    simp [starPow, star, map_one_eq_zero Y hY]
  | succ n ih =>
    rw [starPow]
    simp only [star, zero_mul, add_zero]
    rw [ih, starPow_fst, Y_pow Y hY a (n + 1)]
    conv_rhs => rw [Nat.sum_antidiagonal_succ]
    simp only [mul_sum, pow_zero, one_mul, pow_succ', mul_assoc]
    rw [add_comm]

end Quillen.Notebook1989_4Square
