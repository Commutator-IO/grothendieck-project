import Mathlib

/-!
# Quillen, notebooks 1982-2 (p. 22) and 1982-6 (p. 17): the Faddeev–LeVerrier recursion

Daniel Quillen's research notebooks 1982-2 and 1982-6 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201982/1982-6.pdf>) expand the
Fredholm determinant and the adjugate of `1 − tK` in powers of `t`,
`det (1 − tK) = Σ Δ_k t^k` and `adj (1 − tK) = Σ C_k t^k`, and use the recursions (in the
finite-dimensional form, which is the one checked here)

  `C_0 = 1`, `Δ_0 = 1`, `C_k = K C_{k−1} + Δ_k · 1`, `k Δ_k = − tr (K C_{k−1})`.

These are the Faddeev–LeVerrier (or Plemelj–Smithies) recursions. Mathlib has the derivative of
`det (1 + X • M)` at `0` only (`Matrix.derivative_det_one_add_X_smul`); this file proves
Jacobi's formula for any matrix of polynomials over a commutative ring and deduces the recursions.

* `derivative_det`: **Jacobi's formula**, `(det M)' = tr (adj M · M')` for `M` a square matrix
  over `R[X]`;
* `Delta_zero`, `Cmat_zero`: `Δ_0 = 1`, `C_0 = 1`;
* `Cmat_succ`: `C_{k+1} = K C_k + Δ_{k+1} • 1`;
* `succ_mul_Delta_succ`: `(k + 1) Δ_{k+1} = − tr (K C_k)`.

No hypothesis on the characteristic is needed: the recursion determines `Δ_k` from the traces
only when `k` is invertible, but the identities hold over any commutative ring.
-/

namespace Quillen.Notebook1982_6

open Matrix Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- **Jacobi's formula** for a matrix of polynomials: `(det M)' = tr (adj M · M')`. -/
theorem derivative_det (M : Matrix n n R[X]) :
    derivative M.det = trace (M.adjugate * M.map derivative) := by
  have key : ∀ i, (M.updateCol i (fun r => derivative (M r i))).det
      = ∑ j, M.adjugate i j * derivative (M j i) := fun i => by
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]; rfl
  have hR : trace (M.adjugate * M.map derivative)
      = ∑ i, (M.updateCol i (fun r => derivative (M r i))).det := by
    simp only [trace, diag_apply, mul_apply, map_apply, key]
  rw [hR]
  simp only [det_apply', map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [derivative_mul, show derivative ((Equiv.Perm.sign σ : ℤ) : R[X]) = 0 by
    rw [← C_eq_intCast]; exact derivative_C, zero_mul, zero_add, derivative_prod_finset,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ
    (fun k => M.updateCol i (fun r => derivative (M r i)) (σ k) k) (Finset.mem_univ i), mul_comm]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun k hk => ?_
    simp [Finset.ne_of_mem_erase hk]

variable (K : Matrix n n R)

/-- `det (1 − X K)`, a polynomial. -/
noncomputable def D : R[X] := det (1 - (X : R[X]) • K.map C)

/-- `Δ_k`, the coefficient of `t^k` in `det (1 − t K)`. -/
noncomputable def Delta (k : ℕ) : R := (D K).coeff k

/-- `C_k`, the coefficient of `t^k` in `adj (1 − t K)`. -/
noncomputable def Cmat (k : ℕ) : Matrix n n R :=
  (adjugate (1 - (X : R[X]) • K.map C)).map fun p => p.coeff k

omit [DecidableEq n] in
lemma map_coeff_C_mul (A : Matrix n n R[X]) (k : ℕ) :
    (K.map C * A).map (fun p => p.coeff k) = K * A.map (fun p => p.coeff k) := by
  ext i l
  simp [mul_apply, coeff_C_mul]

omit [Fintype n] in
lemma map_constantCoeff : (1 - (X : R[X]) • K.map C).map constantCoeff = 1 := by
  ext i j
  by_cases h : i = j <;> simp [h, one_apply]

theorem Delta_zero : Delta K 0 = 1 := by
  rw [Delta, D, ← constantCoeff_apply, RingHom.map_det, RingHom.mapMatrix_apply,
    map_constantCoeff, det_one]

theorem Cmat_zero : Cmat K 0 = 1 := by
  have h := RingHom.map_adjugate (constantCoeff : R[X] →+* R) (1 - (X : R[X]) • K.map C)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, map_constantCoeff, adjugate_one] at h
  rw [Cmat, ← h]
  ext i j
  simp

/-- The first recursion: `C_{k+1} = K C_k + Δ_{k+1} • 1`. -/
theorem Cmat_succ (k : ℕ) : Cmat K (k + 1) = K * Cmat K k + Delta K (k + 1) • 1 := by
  have h := mul_adjugate (1 - (X : R[X]) • K.map C)
  rw [sub_mul, one_mul, smul_mul_assoc] at h
  have h' := congrArg (fun A : Matrix n n R[X] => A.map fun p => p.coeff (k + 1)) h
  have hX : ((X : R[X]) • (K.map C * adjugate (1 - (X : R[X]) • K.map C))).map
      (fun p => p.coeff (k + 1)) = K * Cmat K k := by
    rw [Cmat, ← map_coeff_C_mul]
    ext i j
    simp [coeff_X_mul]
  have hs : ((1 - (X : R[X]) • K.map C).det • (1 : Matrix n n R[X])).map (fun p => p.coeff (k + 1))
      = Delta K (k + 1) • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij, one_apply, Delta, D]
  have e2 : Cmat K (k + 1) - K * Cmat K k = Delta K (k + 1) • 1 := by
    rw [← hX, ← hs, ← h']
    ext i j
    simp [Cmat, coeff_sub]
  exact sub_eq_iff_eq_add'.mp e2

/-- The second recursion: `(k + 1) Δ_{k+1} = − tr (K C_k)`. -/
theorem succ_mul_Delta_succ (k : ℕ) :
    ((k : R) + 1) * Delta K (k + 1) = - trace (K * Cmat K k) := by
  have hJ := derivative_det (1 - (X : R[X]) • K.map C)
  have hd : (1 - (X : R[X]) • K.map C).map derivative = -K.map C := by
    ext i j
    by_cases h : i = j <;> simp [h, one_apply]
  rw [hd, mul_neg, trace_neg, trace_mul_comm] at hJ
  have h := congrArg (fun p : R[X] => p.coeff k) hJ
  simp only [coeff_derivative, coeff_neg] at h
  have ht : (trace (K.map C * adjugate (1 - (X : R[X]) • K.map C))).coeff k
      = trace (K * Cmat K k) := by
    rw [Cmat, ← map_coeff_C_mul]
    simp [trace, finsetSum_coeff]
  rw [mul_comm, ← ht, ← h]
  rfl

end Quillen.Notebook1982_6
