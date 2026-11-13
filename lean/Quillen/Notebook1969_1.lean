import Mathlib

/-!
# Quillen, notebook 1969-1, pp. 52–54: a Lagrange interpolation identity for push-forwards

Daniel Quillen's research notebook 1969-1 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201969/1969-1.pdf>) computes,
on pp. 49–54, the push-forward `f_* ξ^q` along the projective bundle of a sum of `n` line bundles,
for a cohomology theory with formal group law `F`: it is the sum over `i` of
`X_i ^ q / ∏_{j ≠ i} F (X_i, I X_j)` (p. 52). For the law `F (X, Y) = X + Y - a X Y`, where
`F (X, I Y) = (X - Y) / (1 - a Y)`, he evaluates the sum by Lagrange interpolation of
`a ^ (n - 1) Z ^ q` at `Z = 1 / a` and finds `f_* ξ^q = a ^ (n - 1 - q)` for `0 ≤ q ≤ n - 1`
(p. 54), which gives the known formulas of cohomology (`a = 0`) and of `K`-theory (`a = 1`).

This file proves the algebraic identity behind that evaluation, over a field, for distinct
`X_i`:
`∑_i X_i ^ q ∏_{j ≠ i} (1 - a X_j) / (X_i - X_j) = a ^ (n - 1 - q)` for `q < n`.
The case `a = 0` (where `1 / a` makes no sense and the right-hand side is `1` for `q = n - 1`
and `0` otherwise) is proved separately, from the leading coefficient of the interpolation
polynomial. The push-forward itself, and the formal group law, are not formalised.

* `sum_pow_mul_prod_eq_zero_pow`: the case `a = 0`;
* `sum_pow_mul_prod_eq_pow`: **the identity of the page**, for every `a`.
-/

namespace Quillen.Notebook1969_1

open Finset Polynomial

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

/-- The case `a = 0`: `∑_i X_i ^ q / ∏_{j ≠ i} (X_i - X_j)` is `1` for `q = n - 1` and `0` for
`q < n - 1`. -/
theorem sum_pow_mul_prod_eq_zero_pow {s : Finset ι} {v : ι → K} (hvs : Set.InjOn v s) {q : ℕ}
    (hq : q < #s) :
    ∑ i ∈ s, v i ^ q / ∏ j ∈ s.erase i, (v i - v j) = 0 ^ (#s - 1 - q) := by
  have h := Lagrange.coeff_eq_sum hvs (P := (X : K[X]) ^ q)
    (by rw [degree_X_pow]; exact_mod_cast hq)
  simp only [eval_pow, eval_X, coeff_X_pow] at h
  rw [← h]
  split_ifs with h1
  · rw [h1, Nat.sub_self, pow_zero]
  · rw [zero_pow (by omega)]

/-- **Quillen, notebook 1969-1, p. 54.** For distinct elements `X_i` (`i ∈ s`, `n = #s`) of a
field, any `a` and `q < n`:
`∑_i X_i ^ q ∏_{j ≠ i} (1 - a X_j) / (X_i - X_j) = a ^ (n - 1 - q)`. -/
theorem sum_pow_mul_prod_eq_pow {s : Finset ι} {v : ι → K} (hvs : Set.InjOn v s) (a : K) {q : ℕ}
    (hq : q < #s) :
    ∑ i ∈ s, v i ^ q * ∏ j ∈ s.erase i, ((1 - a * v j) / (v i - v j)) = a ^ (#s - 1 - q) := by
  by_cases ha : a = 0
  · subst ha
    rw [← sum_pow_mul_prod_eq_zero_pow hvs hq]
    exact sum_congr rfl fun i _ => by simp [div_eq_mul_inv, Finset.prod_inv_distrib]
  · have hP : ((X : K[X]) ^ q).degree < #s := by rw [degree_X_pow]; exact_mod_cast hq
    have h := congrArg (eval a⁻¹) (Lagrange.eq_interpolate hvs hP)
    simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
      Lagrange.basis, eval_prod, Lagrange.basisDivisor, eval_sub] at h
    have key : ∀ i ∈ s, v i ^ q * ∏ j ∈ s.erase i, ((1 - a * v j) / (v i - v j)) =
        a ^ (#s - 1) * (v i ^ q * ∏ j ∈ s.erase i, ((v i - v j)⁻¹ * (a⁻¹ - v j))) := by
      intro i hi
      rw [prod_congr rfl (g := fun j => a * ((v i - v j)⁻¹ * (a⁻¹ - v j))) fun j _ => by
        field_simp, prod_mul_distrib, prod_const, card_erase_of_mem hi]
      ring
    rw [sum_congr rfl key, ← mul_sum, ← h, inv_pow]
    exact (pow_sub₀ a ha (by omega)).symm

end Quillen.Notebook1969_1
