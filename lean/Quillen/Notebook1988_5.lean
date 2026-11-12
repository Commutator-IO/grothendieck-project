import Mathlib

/-!
# Quillen, notebook 1988-5: the cyclic counting lemma in trace form

Daniel Quillen's research notebook 1988-5 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201988/1988-5.pdf>), pp. 87-88.
Counting the words in `A` and `B` cyclically comes down to the trace identity

  `d/ds tr((sA + B)^{m+1}) = (m + 1) · tr(A (sA + B)^m)`

for square matrices `A`, `B` over a commutative ring (`derivative_trace_pow`). The proof is
the Leibniz rule for matrices of polynomials, `(Mⁿ)' = Σᵢ Mⁱ M' M^{n−1−i}`
(`map_derivative_pow`), followed by cyclicity of the trace (`trace_map_derivative_pow`), which
turns every term into `tr(M' Mⁿ⁻¹)`. Taking the coefficient of `s^{k−1}` gives the page's
`k · tr(words of bidegree (k, p)) = (k + p) · tr(A · words of bidegree (k − 1, p))`, which is
not formalised.
-/

namespace Quillen.Notebook1988_5

open Polynomial Matrix Finset

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise derivative of a matrix of polynomials. -/
noncomputable abbrev D (M : Matrix ι ι R[X]) : Matrix ι ι R[X] := M.map fun p => derivative p

omit [DecidableEq ι] in
lemma D_mul (M N : Matrix ι ι R[X]) : D (M * N) = D M * N + M * D N := by
  ext i j
  simp [mul_apply, derivative_mul, sum_add_distrib, add_comm]

/-- The Leibniz rule for powers: `(Mⁿ)' = Σ_{i<n} Mⁱ M' M^{n−1−i}`. -/
theorem map_derivative_pow (M : Matrix ι ι R[X]) (n : ℕ) :
    D (M ^ n) = ∑ i ∈ range n, M ^ i * D M * M ^ (n - 1 - i) := by
  induction n with
  | zero =>
    rw [pow_zero, range_zero, sum_empty]
    ext i j
    by_cases h : i = j <;> simp [one_apply, h]
  | succ n ih =>
    rw [pow_succ, D_mul, ih, sum_range_succ (fun i => M ^ i * D M * M ^ (n + 1 - 1 - i)), sum_mul,
      show n + 1 - 1 - n = 0 by omega, pow_zero, Matrix.mul_one]
    refine congrArg (· + M ^ n * D M) ?_
    refine sum_congr rfl fun i hi => ?_
    have hi : i < n := mem_range.mp hi
    rw [Matrix.mul_assoc, ← pow_succ, show n - 1 - i + 1 = n + 1 - 1 - i by omega]

/-- `tr((M^{n+1})') = (n + 1) tr(M' Mⁿ)`. -/
theorem trace_map_derivative_pow (M : Matrix ι ι R[X]) (n : ℕ) :
    trace (D (M ^ (n + 1))) = (n + 1 : R[X]) * trace (D M * M ^ n) := by
  rw [map_derivative_pow, trace_sum]
  have h : ∀ i ∈ range (n + 1), trace (M ^ i * D M * M ^ (n + 1 - 1 - i)) = trace (D M * M ^ n) := by
    intro i hi
    have hi : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, ← pow_add,
      show n + 1 - 1 - i + i = n by omega]
  rw [sum_congr rfl h, sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **Notebook 1988-5, pp. 87-88**: `d/ds tr((sA + B)^{m+1}) = (m + 1) tr(A (sA + B)^m)`. -/
theorem derivative_trace_pow (A B : Matrix ι ι R) (m : ℕ) :
    derivative (trace (((X : R[X]) • A.map C + B.map C) ^ (m + 1))) =
      (m + 1 : R[X]) * trace (A.map C * ((X : R[X]) • A.map C + B.map C) ^ m) := by
  have htr : ∀ M : Matrix ι ι R[X], derivative (trace M) = trace (D M) := by
    intro M
    simp [trace]
  have hD : D ((X : R[X]) • A.map C + B.map C) = A.map C := by
    ext i j
    simp
  rw [htr, trace_map_derivative_pow, hD]

end Quillen.Notebook1988_5
