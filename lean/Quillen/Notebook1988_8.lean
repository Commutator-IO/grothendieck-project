import Quillen.Notebook1988_5

/-!
# Quillen, notebook 1988-8: the cyclic word count; traces on a twisted product; a gauge

Daniel Quillen's research notebook 1988-8 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201988/1988-8.pdf>).

* p. 16, the cyclic word count. For square matrices `A`, `B` over a commutative ring, let
  `P k l` be the sum of the words with `k` letters `A` and `l` letters `B`, defined as the
  coefficient of `s^k` in `(sA + B)^{k+l}`; it satisfies the recursion by the first letter
  (`P_zero_zero`, `P_succ_zero`, `P_zero_succ`, `P_succ_succ`). Then
  `(k + 1) tr P(k + 1, l) = (k + l + 1) tr(A · P(k, l))` (`trace_word_count`): the page's
  `k tr P(X^k, Y^l) = (k + l) tr(X P(X^{k−1}, Y^l))`. It is the coefficient of `s^k` in the
  identity of notebook 1988-5 (`Quillen.Notebook1988_5.derivative_trace_pow`).
* p. 10: for a trace `τ` (additive, `τ(ab) = τ(ba)`) and `εt = −tε`, `2τ(tⁿε) = 0` for
  `n ≥ 1` (`two_nsmul_trace_pow_mul`), hence `τ(tⁿε) = 0` with values in a `ℚ`-vector space
  (`trace_pow_mul`); `ε² = 1` is not needed.
* p. 21: for `F² = 1` and scalars `c² + s² = 1`, `g = (c, −sF; sF, c)` has inverse
  `(c, sF; −sF, c)` and `g · diag(F, −F) · g⁻¹ = ((c² − s²)F, 2cs; 2cs, (s² − c²)F)`
  (`gauge_mul_inv`, `gauge_conj`). The page writes the factors `F` on the off-diagonal of the
  result; with `g` as above they cancel, since `F² = 1`.
-/

namespace Quillen.Notebook1988_8

section WordCount

open Polynomial Matrix Finset

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι R)

/-- `sA + B` as a matrix of polynomials in `s`. -/
noncomputable abbrev M : Matrix ι ι R[X] := (X : R[X]) • A.map C + B.map C

/-- The sum of the words with `k` letters `A` and `l` letters `B`: the coefficient of `s^k`
in `(sA + B)^{k+l}`. -/
noncomputable def P (k l : ℕ) : Matrix ι ι R := ((M A B) ^ (k + l)).map fun p => p.coeff k

theorem coeff_M_mul (N : Matrix ι ι R[X]) (k : ℕ) :
    (M A B * N).map (fun p => p.coeff (k + 1)) =
      A * N.map (fun p => p.coeff k) + B * N.map (fun p => p.coeff (k + 1)) := by
  ext i j
  simp [M, Matrix.add_mul, mul_apply, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul]

theorem coeff_zero_M_mul (N : Matrix ι ι R[X]) :
    (M A B * N).map (fun p => p.coeff 0) = B * N.map (fun p => p.coeff 0) := by
  ext i j
  simp [M, Matrix.add_mul, mul_apply, Polynomial.finsetSum_coeff]

theorem coeff_pow_eq_zero (n k : ℕ) (hk : n < k) :
    ((M A B) ^ n).map (fun p => p.coeff k) = 0 := by
  induction n generalizing k with
  | zero =>
    ext i j
    by_cases h : i = j <;> simp [one_apply, h, Polynomial.coeff_one, show k ≠ 0 by omega]
  | succ n ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ', coeff_M_mul, ih k (by omega), ih (k + 1) (by omega)]
    simp

theorem P_zero_zero : P A B 0 0 = 1 := by
  ext i j
  by_cases h : i = j <;> simp [P, one_apply, h]

theorem P_zero_succ (l : ℕ) : P A B 0 (l + 1) = B * P A B 0 l := by
  simp only [P, Nat.zero_add, pow_succ', coeff_zero_M_mul]

theorem P_succ_zero (k : ℕ) : P A B (k + 1) 0 = A * P A B k 0 := by
  simp only [P, pow_succ', coeff_M_mul, coeff_pow_eq_zero A B k (k + 1) (by omega),
    Matrix.mul_zero, add_zero]

theorem P_succ_succ (k l : ℕ) :
    P A B (k + 1) (l + 1) = A * P A B k (l + 1) + B * P A B (k + 1) l := by
  simp only [P, show k + 1 + (l + 1) = k + (l + 1) + 1 by omega, pow_succ', coeff_M_mul,
    show k + (l + 1) = k + 1 + l by omega]

/-- **Notebook 1988-8, p. 16**: `(k + 1) tr P(k + 1, l) = (k + l + 1) tr(A · P(k, l))`. -/
theorem trace_word_count (k l : ℕ) :
    (k + 1 : R) * trace (P A B (k + 1) l) = (k + l + 1 : R) * trace (A * P A B k l) := by
  have h := congrArg (fun p => p.coeff k) (Quillen.Notebook1988_5.derivative_trace_pow A B (k + l))
  simp only [Polynomial.coeff_derivative] at h
  have htr : ∀ (N : Matrix ι ι R[X]) (j : ℕ),
      (trace N).coeff j = trace (N.map fun p => p.coeff j) := fun N j => by simp [trace]
  have hl : (trace (((X : R[X]) • A.map C + B.map C) ^ (k + l + 1))).coeff (k + 1) =
      trace (P A B (k + 1) l) := by
    rw [htr]; simp only [P, M, show k + 1 + l = k + l + 1 by omega]
  have hr2 : (trace (A.map C * ((X : R[X]) • A.map C + B.map C) ^ (k + l))).coeff k =
      trace (A * P A B k l) := by
    rw [htr]
    congr 1
    ext i j
    simp [P, M, mul_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  push_cast at h
  rw [show ((k : R[X]) + l + 1) = Polynomial.C ((k : R) + l + 1) by simp,
    Polynomial.coeff_C_mul, hr2, hl] at h
  exact (mul_comm _ _).trans h

end WordCount

section Trace

variable {S : Type*} [Ring S] {Mod : Type*} [AddCommGroup Mod] (τ : S →+ Mod)
  (hτ : ∀ a b, τ (a * b) = τ (b * a)) {t ε : S}

theorem mul_pow_comm (hεt : ε * t = -(t * ε)) (n : ℕ) : ε * t ^ n = (-1) ^ n * (t ^ n * ε) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, pow_succ, mul_assoc, mul_assoc, hεt]
    noncomm_ring

include hτ in
/-- **Notebook 1988-8, p. 10**: `2τ(tⁿε) = 0` for `n ≥ 1` when `εt = −tε`. -/
theorem two_nsmul_trace_pow_mul (hεt : ε * t = -(t * ε)) (n : ℕ) :
    2 • τ (t ^ (n + 1) * ε) = 0 := by
  -- move one `t` around the trace
  have h1 : τ (t ^ (n + 1) * ε) = τ (t ^ n * ε * t) := by
    rw [pow_succ', mul_assoc, hτ, mul_assoc]
  have h2 : t ^ n * ε * t = -(t ^ (n + 1) * ε) := by
    rw [mul_assoc, hεt, mul_neg, ← mul_assoc, ← pow_succ]
  rw [two_nsmul]
  exact add_eq_zero_iff_eq_neg.mpr (h1.trans (by rw [h2, map_neg]))

include hτ in
/-- With values in a `ℚ`-vector space, `τ(tⁿε) = 0` for `n ≥ 1`. -/
theorem trace_pow_mul [Module ℚ Mod] (hεt : ε * t = -(t * ε)) (n : ℕ) :
    τ (t ^ (n + 1) * ε) = 0 := by
  have : (2 : ℚ) • τ (t ^ (n + 1) * ε) = 0 := by
    rw [ofNat_smul_eq_nsmul ℚ 2, two_nsmul_trace_pow_mul τ hτ hεt n]
  exact (smul_eq_zero.mp this).resolve_left two_ne_zero

end Trace

section Gauge

variable {K S : Type*} [CommRing K] [Ring S] [Algebra K S] {c s : K} {F : S}

/-- The gauge transformation `g = (c, −sF; sF, c)`. -/
def g (c s : K) (F : S) : Matrix (Fin 2) (Fin 2) S :=
  !![c • 1, -(s • F); s • F, c • 1]

set_option linter.unusedSimpArgs false in
/-- **Notebook 1988-8, p. 21**: `g` is invertible, with inverse `(c, sF; −sF, c)`. -/
theorem gauge_mul_inv (hF : F * F = 1) (hcs : c ^ 2 + s ^ 2 = 1) :
    g c s F * g c (-s) F = 1 ∧ g c (-s) F * g c s F = 1 := by
  have h1 : c • c • (1 : S) + s • s • 1 = 1 := by
    rw [smul_smul, smul_smul, ← add_smul, ← sq, ← sq, hcs, one_smul]
  have h2 : s • s • (1 : S) + c • c • 1 = 1 := by rw [add_comm, h1]
  constructor <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g, Matrix.mul_apply, Fin.sum_univ_two, smul_mul_smul, hF, smul_mul_assoc,
        mul_smul_comm] <;>
      first | exact h1 | exact h2 | (rw [smul_comm s c]; abel)

set_option linter.unusedSimpArgs false in
/-- **Notebook 1988-8, p. 21**: `g · diag(F, −F) · g⁻¹ = ((c² − s²)F, 2cs; 2cs, (s² − c²)F)`. -/
theorem gauge_conj (hF : F * F = 1) :
    g c s F * !![F, 0; 0, -F] * g c (-s) F =
      !![(c ^ 2 - s ^ 2) • F, (2 * c * s) • 1; (2 * c * s) • 1, (s ^ 2 - c ^ 2) • F] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g, Matrix.mul_apply, Fin.sum_univ_two, smul_mul_smul, hF, smul_mul_assoc,
      mul_smul_comm, ← mul_assoc] <;>
    module

end Gauge

end Quillen.Notebook1988_8
