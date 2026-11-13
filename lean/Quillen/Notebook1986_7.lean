import Mathlib

/-!
# Quillen, notebook 1986-7: triangular idempotents; antisymmetrisation over the Vandermonde

Daniel Quillen's research notebook 1986-7 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201986/1986-7.pdf>) contains two
algebraic steps checked here.

* p. 50: idempotents `e₀, …, e_n` with `Σ eᵢ = 1` and `e_t e_s = 0` for `t < s` are orthogonal,
  `eᵢ e_j = 0` for all `i ≠ j` (the page looks for a better argument than an induction; the one
  here is an induction on `i`, using `Σ_{k > j} e_k e_j = 0`):
  `mul_eq_zero_of_gt`, `completeOrthogonalIdempotents`. Any ring, any finite linearly ordered
  index set.
* p. 25: the Gysin map of the flag bundle is computed by antisymmetrising a monomial
  `α = Π uᵢ^{aᵢ}`; the antisymmetrisation `Σ_σ sgn σ · σ(α)` is the determinant
  `det (u_i^{a_j})` (`antisymm_eq_det`), it vanishes when two exponents coincide
  (`antisymm_eq_zero`), and for `aᵢ = i` it is the Vandermonde product `Π_{i<j} (u_j − u_i)`
  (`antisymm_vandermonde`).
-/

namespace Quillen.Notebook1986_7

section Idempotents

variable {R ι : Type*} [Ring R] [Fintype ι] [LinearOrder ι] [DecidableEq ι] {e : ι → R}

/-- If `Σ e_k = 1` and `e_t e_s = 0` for `t < s`, then `Σ_{k > j} e_k e_j = 0`. -/
lemma sum_gt_mul_eq_zero (hsum : ∑ k, e k = 1) (hid : ∀ i, IsIdempotentElem (e i))
    (hlt : ∀ t s, t < s → e t * e s = 0) (j : ι) :
    ∑ k, (if j < k then e k * e j else 0) = 0 := by
  have h : ∀ k, e k * e j = (if j < k then e k * e j else 0) + (if k = j then e j else 0) := by
    intro k
    rcases lt_trichotomy k j with hkj | rfl | hjk
    · rw [hlt k j hkj, ite_eq_right (not_lt.mpr hkj.le), ite_eq_right hkj.ne, add_zero]
    · rw [ite_eq_right (lt_irrefl k), ite_eq_left rfl, zero_add, (hid k).eq]
    · rw [ite_eq_left hjk, ite_eq_right hjk.ne', add_zero]
  have hs : ∑ k, e k * e j = e j := by rw [← Finset.sum_mul, hsum, one_mul]
  rw [Finset.sum_congr rfl fun k _ => h k, Finset.sum_add_distrib] at hs
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, add_eq_right] using hs

/-- **p. 50**: `e_i e_j = 0` for `j < i` as well. -/
theorem mul_eq_zero_of_gt (hsum : ∑ k, e k = 1) (hid : ∀ i, IsIdempotentElem (e i))
    (hlt : ∀ t s, t < s → e t * e s = 0) : ∀ i j, j < i → e i * e j = 0 := by
  intro i
  induction i using WellFoundedLT.induction with
  | _ i ih =>
  intro j hji
  have h0 := congrArg (e i * ·) (sum_gt_mul_eq_zero hsum hid hlt j)
  simp only [Finset.mul_sum, mul_zero] at h0
  have hterm : ∀ k, e i * (if j < k then e k * e j else 0) = if k = i then e i * e j else 0 := by
    intro k
    by_cases hjk : j < k
    · rw [ite_eq_left hjk]
      rcases lt_trichotomy k i with hki | rfl | hik
      · rw [ih k hki j hjk, mul_zero, ite_eq_right hki.ne]
      · rw [ite_eq_left rfl, ← mul_assoc, (hid k).eq]
      · rw [← mul_assoc, hlt i k hik, zero_mul, ite_eq_right hik.ne']
    · rw [ite_eq_right hjk, mul_zero, ite_eq_right]
      rintro rfl
      exact hjk hji
  simpa only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h0

/-- The family is a complete family of orthogonal idempotents. -/
theorem completeOrthogonalIdempotents (hsum : ∑ k, e k = 1) (hid : ∀ i, IsIdempotentElem (e i))
    (hlt : ∀ t s, t < s → e t * e s = 0) : CompleteOrthogonalIdempotents e where
  idem := hid
  ortho i j hij := (lt_or_gt_of_ne hij).elim (hlt i j) (mul_eq_zero_of_gt hsum hid hlt i j)
  complete := hsum

end Idempotents

section Antisymm

open Matrix Equiv

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The antisymmetrisation `Σ_σ sgn σ · σ(Π_i u_i^{a_i}) = Σ_σ sgn σ Π_i u_{σ i}^{a_i}`. -/
def antisymm (u : ι → R) (a : ι → ℕ) : R :=
  ∑ σ : Perm ι, Perm.sign σ • ∏ i, u (σ i) ^ a i

/-- The antisymmetrisation is the determinant `det (u_i^{a_j})`. -/
theorem antisymm_eq_det (u : ι → R) (a : ι → ℕ) :
    antisymm u a = (Matrix.of fun i j => u i ^ a j).det := by
  rw [det_apply, antisymm]
  rfl

/-- It vanishes when two exponents coincide. -/
theorem antisymm_eq_zero (u : ι → R) (a : ι → ℕ) {i j : ι} (hij : i ≠ j) (h : a i = a j) :
    antisymm u a = 0 := by
  rw [antisymm_eq_det]
  exact det_zero_of_column_eq hij fun k => by simp [h]

/-- For the exponents `a_i = i`, it is the Vandermonde product `Π_{i<j} (u_j − u_i)`. -/
theorem antisymm_vandermonde {n : ℕ} (u : Fin n → R) :
    antisymm u (fun i => (i : ℕ)) = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (u j - u i) := by
  rw [antisymm_eq_det, ← det_vandermonde]
  rfl

end Antisymm

end Quillen.Notebook1986_7
