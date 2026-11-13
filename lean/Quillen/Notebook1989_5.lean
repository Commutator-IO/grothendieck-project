import Mathlib

/-!
# Quillen, notebook 1989-5: Cuntz's polynomial, `1 + λ`, and the difference of two homomorphisms

Daniel Quillen's research notebook 1989-5 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201989/1989-5.pdf>).

* pp. 107-108, Cuntz's homotopy polynomial
  `W_{n+1}(x) = (1/(n+1)) Σ_{j ≤ n} (n/2 − j) x^j`:
  `(1 − x) W_{n+1}(x) = 1 − N_{n+1}(x)/(n+1) + (n/(2(n+1))) (x^{n+1} − 1)` with
  `N_{n+1}(x) = Σ_{j ≤ n} x^j` (`one_sub_mul_W`), through `W = W' − (n/(2(n+1))) N` and
  `(1 − x) W'(x) = 1 − N(x)/(n+1)` for `W'(x) = (1/(n+1)) Σ_{j ≤ n} (n − j) x^j`
  (`one_sub_mul_W'`, `W_eq`); hence `(1 − λ) W(λ) = 1 − N(λ)/(n+1)` for any `λ` with
  `λ^{n+1} = 1` in any `ℚ`-algebra, commutative or not (`one_sub_mul_aeval_W`). Over any
  commutative ring, the integral form `(1 − x) Σ_{j ≤ n} (n − j) x^j = (n + 1) − N(x)`
  (`one_sub_mul_S`).
* p. 95: if `2` is invertible, `λ^n = 1` and `n` is odd, then `1 + λ` is a unit, with inverse
  `½ Σ_{i<n} (−λ)^i` (`one_add_mul_inv`).
* p. 124: for ring homomorphisms `u, v : A → R`, `q = (u − v)/2` and `ρ = (u + v)/2`:
  `q(xy) = q(x)u(y) + v(x)q(y) = u(x)q(y) + q(x)v(y) = ρ(x)q(y) + q(x)ρ(y)` and
  `q(xy) = u(x)q(y) + q(x)u(y) − 2q(x)q(y)` (`q_mul_left`, `q_mul_right`, `q_mul_ρ`, `q_mul`),
  stated for `q' = u − v`, `ρ' = u + v` without dividing by `2`, so in any rings; and the Cayley
  example `½(a − g⁻¹ag) = (1 + X)⁻¹(Xa − aX)(1 − X)⁻¹` for `g = (1 + X)(1 − X)⁻¹` (`sub_conj`,
  in the form `a − g⁻¹ag = (1 + X)⁻¹ · 2(Xa − aX) · (1 − X)⁻¹`), in any ring.
-/

namespace Quillen.Notebook1989_5

open Finset

section Cuntz

variable {R : Type*} [CommRing R]

/-- `Σ_{j ≤ n} (n − j) x^j`. -/
def S (n : ℕ) (x : R) : R := ∑ j ∈ range (n + 1), ((n : R) - j) * x ^ j

/-- `N_{n+1}(x) = Σ_{j ≤ n} x^j`. -/
def N (n : ℕ) (x : R) : R := ∑ j ∈ range (n + 1), x ^ j

theorem S_succ (n : ℕ) (x : R) : S (n + 1) x = S n x + N n x := by
  rw [S, sum_range_succ, Nat.cast_succ, sub_self, zero_mul, add_zero, S, N, ← sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

/-- The integral form: `(1 − x) Σ_{j ≤ n} (n − j) x^j = (n + 1) − Σ_{j ≤ n} x^j`. -/
theorem one_sub_mul_S (n : ℕ) (x : R) : (1 - x) * S n x = (n + 1 : R) - N n x := by
  induction n with
  | zero => simp [S, N]
  | succ n ih =>
    rw [S_succ, mul_add, ih, N, N, sum_range_succ _ (n + 1), mul_comm, geom_sum_mul_neg]
    push_cast; ring

variable [Algebra ℚ R]

/-- `W'_{n+1}(x) = (1/(n+1)) Σ_{j ≤ n} (n − j) x^j`. -/
noncomputable def W' (n : ℕ) (x : R) : R := ((n + 1 : ℚ)⁻¹) • S n x

/-- Cuntz's `W_{n+1}(x) = (1/(n+1)) Σ_{j ≤ n} (n/2 − j) x^j`. -/
noncomputable def W (n : ℕ) (x : R) : R :=
  ((n + 1 : ℚ)⁻¹) • ∑ j ∈ range (n + 1), (((n : ℚ) / 2 - j) • x ^ j)

theorem one_sub_mul_W' (n : ℕ) (x : R) : (1 - x) * W' n x = 1 - ((n + 1 : ℚ)⁻¹) • N n x := by
  rw [W', mul_smul_comm, one_sub_mul_S, smul_sub]
  congr 1
  rw [show ((n : R) + 1) = algebraMap ℚ R (n + 1) by simp, Algebra.smul_def, ← map_mul,
    inv_mul_cancel₀ (by positivity), map_one]

/-- `W = W' − (n/(2(n+1))) N` (p. 108). -/
theorem W_eq (n : ℕ) (x : R) : W n x = W' n x - ((n : ℚ) / (2 * (n + 1))) • N n x := by
  rw [W, W', S, N, smul_sum, smul_sum, smul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [show ((n : R) - j) = algebraMap ℚ R (n - j) by simp, ← Algebra.smul_def, smul_smul,
    smul_smul, ← sub_smul]
  congr 1
  field_simp
  ring

/-- **Cuntz's polynomial** (p. 107, boxed):
`(1 − x) W_{n+1}(x) = 1 − N_{n+1}(x)/(n+1) + (n/(2(n+1))) (x^{n+1} − 1)`. -/
theorem one_sub_mul_W (n : ℕ) (x : R) :
    (1 - x) * W n x = 1 - ((n + 1 : ℚ)⁻¹) • N n x + ((n : ℚ) / (2 * (n + 1))) • (x ^ (n + 1) - 1) := by
  rw [W_eq, mul_sub, one_sub_mul_W', mul_smul_comm, N, mul_neg_geom_sum]
  rw [show (1 : R) - x ^ (n + 1) = -(x ^ (n + 1) - 1) by ring, smul_neg]
  abel

end Cuntz

/-- In any `ℚ`-algebra, commutative or not, `(1 − λ) W_{n+1}(λ) = 1 − N_{n+1}(λ)/(n+1)` when
`λ^{n+1} = 1` (p. 107). -/
theorem one_sub_mul_aeval_W {A : Type*} [Ring A] [Algebra ℚ A] (n : ℕ) (l : A)
    (hl : l ^ (n + 1) = 1) :
    (1 - l) * Polynomial.aeval l (W n (Polynomial.X : Polynomial ℚ)) =
      1 - ((n + 1 : ℚ)⁻¹) • ∑ j ∈ range (n + 1), l ^ j := by
  simpa only [map_mul, map_sub, map_add, map_one, map_smul, Polynomial.aeval_X, map_pow, N,
    map_sum, hl, sub_self, smul_zero, add_zero] using
    congrArg (Polynomial.aeval l) (one_sub_mul_W n (Polynomial.X : Polynomial ℚ))

/-- If `2` is invertible, `λ^n = 1` and `n` is odd, then `(1 + λ) · ½ Σ_{i<n} (−λ)^i = 1`
(p. 95), in any ring. -/
theorem one_add_mul_inv {A : Type*} [Ring A] {t l : A} (ht : 2 * t = 1) {n : ℕ} (hn : Odd n)
    (hl : l ^ n = 1) : (1 + l) * ((∑ i ∈ range n, (-l) ^ i) * t) = 1 := by
  have h := mul_neg_geom_sum (-l) n
  rw [sub_neg_eq_add, hn.neg_pow, hl, sub_neg_eq_add, one_add_one_eq_two] at h
  rw [← mul_assoc, h, ht]

theorem one_add_inv_mul {A : Type*} [Ring A] {t l : A} (ht : t * 2 = 1) {n : ℕ} (hn : Odd n)
    (hl : l ^ n = 1) : (t * ∑ i ∈ range n, (-l) ^ i) * (1 + l) = 1 := by
  have h := geom_sum_mul_neg (-l) n
  rw [sub_neg_eq_add, hn.neg_pow, hl, sub_neg_eq_add, one_add_one_eq_two] at h
  rw [mul_assoc, h, ht]

section Difference

variable {A R : Type*} [Ring A] [Ring R] (u v : A →+* R)

/-! Denominator-free forms: `q' = u − v = 2q` and `ρ' = u + v = 2ρ`; when `2` is invertible these
are the page's identities divided by `2` (or by `4` for `q_mul_ρ`). -/

/-- `q(xy) = q(x)u(y) + v(x)q(y)`. -/
theorem q_mul_left (x y : A) :
    (u (x * y) - v (x * y)) = (u x - v x) * u y + v x * (u y - v y) := by
  simp only [map_mul]
  noncomm_ring

/-- `q(xy) = u(x)q(y) + q(x)v(y)`. -/
theorem q_mul_right (x y : A) :
    (u (x * y) - v (x * y)) = u x * (u y - v y) + (u x - v x) * v y := by
  simp only [map_mul]
  noncomm_ring

/-- `q(xy) = ρ(x)q(y) + q(x)ρ(y)`, times `4`: `2q'(xy) = ρ'(x)q'(y) + q'(x)ρ'(y)`. -/
theorem q_mul_ρ (x y : A) :
    2 * (u (x * y) - v (x * y)) = (u x + v x) * (u y - v y) + (u x - v x) * (u y + v y) := by
  simp only [map_mul]
  noncomm_ring

/-- **The boxed formula of p. 124**, `q(xy) = u(x)q(y) + q(x)u(y) − 2q(x)q(y)`, times `2`:
`q'(xy) = u(x)q'(y) + q'(x)u(y) − q'(x)q'(y)`. -/
theorem q_mul (x y : A) :
    (u (x * y) - v (x * y)) = u x * (u y - v y) + (u x - v x) * u y - (u x - v x) * (u y - v y) := by
  simp only [map_mul]
  noncomm_ring

end Difference

/-- **The Cayley example** (p. 124): if `1 + X` and `1 − X` are units and
`g = (1 + X)(1 − X)⁻¹`, then `a − g⁻¹ag = (1 + X)⁻¹ · 2(Xa − aX) · (1 − X)⁻¹`, that is
`½(a − g⁻¹ag) = (1 + X)⁻¹(Xa − aX)(1 − X)⁻¹` when `2` is invertible. -/
theorem sub_conj {R : Type*} [Ring R] (X a : R) (P Q : Rˣ)
    (hP : (P : R) = 1 + X) (hQ : (Q : R) = 1 - X) :
    a - ((P * Q⁻¹)⁻¹ : Rˣ) * a * (P * Q⁻¹ : Rˣ) =
      (P⁻¹ : Rˣ) * (2 * (X * a - a * X)) * (Q⁻¹ : Rˣ) := by
  have hPQ : (P : R) * Q = Q * P := by rw [hP, hQ]; noncomm_ring
  -- `P g⁻¹ a g Q = Q a P`
  have hconj : (P : R) * (((P * Q⁻¹)⁻¹ : Rˣ) * a * (P * Q⁻¹ : Rˣ)) * Q = Q * a * P := by
    have hQP : (P : R) * ((Q * P⁻¹ : Rˣ) : R) = Q := by
      rw [Units.val_mul, ← mul_assoc, hPQ, mul_assoc, Units.mul_inv, mul_one]
    rw [mul_inv_rev, inv_inv, ← mul_assoc, ← mul_assoc, hQP]
    simp [mul_assoc]
  have key : (P : R) * (a - ((P * Q⁻¹)⁻¹ : Rˣ) * a * (P * Q⁻¹ : Rˣ)) * Q =
      2 * (X * a - a * X) := by
    rw [mul_sub, sub_mul, hconj, hP, hQ]
    noncomm_ring
  rw [← key]
  simp [mul_assoc]

end Quillen.Notebook1989_5
