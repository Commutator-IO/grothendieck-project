import Mathlib

/-!
# Quillen, notebook 1989-4: powers to first order; graded commutators; the modular operator

Daniel Quillen's research notebook 1989-4 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201989/1989-4.pdf>).

* p. 38: in any ring, if every product with two factors `e` vanishes (`e x e = 0` for all `x`),
  then `(a + e)^{n+1} = a^{n+1} + Σ_{k ≤ n} a^{n−k} e a^k` (`add_pow_first_order`): the binomial
  formula to first order, noncommutative. The page applies it to `e = −dad`.
* pp. 14, 18: for `X = zθ + θz`, `zX − Xz = z²θ − θz²` (`commutator_graded`); hence if
  `z² = 1`, `z` commutes with `X` and `zX = θ + zθz` (`mul_graded_of_sq`).
* p. 34: for an invertible matrix `T` and `φ(x) = tr(Tx)`, `φ(yx) = φ(x · TyT⁻¹)`
  (`trace_modular`).
-/

namespace Quillen.Notebook1989_4

section FirstOrder

variable {A : Type*} [Ring A]

/-- **Notebook 1989-4, p. 38**: `(a + e)^{n+1} = a^{n+1} + Σ_{k ≤ n} a^{n−k} e a^k` when every
product containing two factors `e` vanishes. -/
theorem add_pow_first_order {a e : A} (he : ∀ x : A, e * x * e = 0) (n : ℕ) :
    (a + e) ^ (n + 1) = a ^ (n + 1) + ∑ k ∈ Finset.range (n + 1), a ^ (n - k) * e * a ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Finset.sum_range_succ' _ (n + 1)]
    have hz : (∑ k ∈ Finset.range (n + 1), a ^ (n - k) * e * a ^ k) * e = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun k _ => by rw [mul_assoc, mul_assoc, ← mul_assoc e, he, mul_zero]
    have hs : (∑ k ∈ Finset.range (n + 1), a ^ (n - k) * e * a ^ k) * a =
        ∑ k ∈ Finset.range (n + 1), a ^ (n + 1 - (k + 1)) * e * a ^ (k + 1) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.add_sub_add_right, pow_succ a k, mul_assoc _ _ a]
    rw [mul_add, add_mul, add_mul, hz, hs, Nat.sub_zero, pow_zero, mul_one, ← pow_succ]
    abel

/-- The case `n = 1`: `(a + e)² = a² + ae + ea`. -/
example {a e : A} (he : ∀ x : A, e * x * e = 0) : (a + e) ^ 2 = a ^ 2 + a * e + e * a := by
  rw [add_pow_first_order he 1]; simp [Finset.sum_range_succ]; abel

end FirstOrder

section Graded

variable {A : Type*} [Ring A] (z θ : A)

/-- **Notebook 1989-4, pp. 14, 18**: `[z, zθ + θz] = z²θ − θz²`. -/
theorem commutator_graded :
    z * (z * θ + θ * z) - (z * θ + θ * z) * z = z * z * θ - θ * (z * z) := by noncomm_ring

/-- **Notebook 1989-4**: if `z² = 1`, then `z(zθ + θz) = (zθ + θz)z = θ + zθz`. -/
theorem mul_graded_of_sq {z} (hz : z * z = 1) :
    z * (z * θ + θ * z) = θ + z * θ * z ∧ (z * θ + θ * z) * z = θ + z * θ * z :=
  ⟨by rw [mul_add, ← mul_assoc, hz, one_mul, mul_assoc],
    by rw [add_mul, mul_assoc θ, hz, mul_one, add_comm]⟩

end Graded

section Modular

open Matrix

variable {n k : Type*} [Fintype n] [DecidableEq n] [CommRing k]

/-- **Notebook 1989-4, p. 34**: for invertible `T`, `tr(T(yx)) = tr(T(x · TyT⁻¹))`. -/
theorem trace_modular {T : Matrix n n k} (hT : IsUnit T.det) (x y : Matrix n n k) :
    trace (T * (y * x)) = trace (T * (x * (T * y * T⁻¹))) := by
  rw [show T * (x * (T * y * T⁻¹)) = (T * x * T * y) * T⁻¹ by simp only [Matrix.mul_assoc],
    trace_mul_comm _ T⁻¹, show T⁻¹ * (T * x * T * y) = x * (T * y) by
      simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hT, Matrix.one_mul],
    trace_mul_comm x, Matrix.mul_assoc]

end Modular

end Quillen.Notebook1989_4
