import Mathlib

/-!
# Quillen, 1983 lecture notes 8 (Witten), pp. 4 and 6: two trace inequalities

Daniel Quillen's notes of a lecture of Edward Witten on mass inequalities in gauge theory, in the
1983 file « Lecture Notes 8 Witten » (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201983/1983-Lecture%20Notes%208%20Witten.pdf>),
reduce two of the inequalities to statements on finite matrices.

On p. 4 the pion and rho propagators in a fixed background field are `Tr (S S*)` and
`Tr (S Γ S* Γ)`, where `S` is a finite square matrix and `Γ` is a product of gamma matrices with
`Γ² = 1`; the notes conclude that the first is at least the second « by linear algebra ». On
p. 6 a difference of squared masses is reduced to `Tr (E M E M*)` with `E ≥ 0`, hence is `≥ 0`.

This file proves both, for complex square matrices.

* `re_trace_mul_conjTranspose_le`: `2 Re Tr (S T*) ≤ Tr (S S*) + Tr (T T*)`;
* `re_trace_unitary_le`: `Re Tr (S V S* U) ≤ Tr (S S*)` for unitary `U`, `V`;
* `re_trace_involution_le`: **the inequality of p. 4**, for `Γ` hermitian with `Γ² = 1`; the
  page only writes `Γ² = 1`, and the hermitian hypothesis is added here (see
  `not_re_trace_le_of_sq_eq_one` for why something of the kind is needed);
* `im_trace_involution`: for such `Γ` the trace `Tr (S Γ S* Γ)` is real;
* `not_re_trace_le_of_sq_eq_one`: a `2 × 2` example with `Γ² = 1`, `Γ` not hermitian, where
  `Tr (S Γ S* Γ) > Tr (S S*)`;
* `re_trace_posSemidef_nonneg`: **the inequality of p. 6**, `0 ≤ Re Tr (E M E M*)` for `E`
  positive semidefinite, and `im_trace_posSemidef` : this trace is real.
-/

namespace Quillen.Notebook1983_LectureNotes8

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- `Tr (A A*)` is a nonnegative real number. -/
theorem re_trace_mul_conjTranspose_self_nonneg (A : Matrix n n ℂ) : 0 ≤ (A * Aᴴ).trace.re :=
  (Complex.nonneg_iff.mp (posSemidef_self_mul_conjTranspose A).trace_nonneg).1

omit [DecidableEq n] in
/-- `2 Re Tr (S T*) ≤ Tr (S S*) + Tr (T T*)`, from `Tr ((S - T)(S - T)*) ≥ 0`. -/
theorem re_trace_mul_conjTranspose_le (S T : Matrix n n ℂ) :
    2 * (S * Tᴴ).trace.re ≤ (S * Sᴴ).trace.re + (T * Tᴴ).trace.re := by
  have h := re_trace_mul_conjTranspose_self_nonneg (S - T)
  have h1 : (T * Sᴴ).trace = star (S * Tᴴ).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  have h2 : ((S - T) * (S - T)ᴴ).trace =
      (S * Sᴴ).trace - (S * Tᴴ).trace - (T * Sᴴ).trace + (T * Tᴴ).trace := by
    rw [conjTranspose_sub, sub_mul, mul_sub, mul_sub, trace_sub, trace_sub, trace_sub]
    ring
  rw [h2, h1] at h
  simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re] at h
  linarith

/-- For unitary `U`, `V` and any `S`: `Re Tr (S V S* U) ≤ Tr (S S*)`. -/
theorem re_trace_unitary_le (S : Matrix n n ℂ) {U V : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (hV : V ∈ unitaryGroup n ℂ) :
    (S * V * Sᴴ * U).trace.re ≤ (S * Sᴴ).trace.re := by
  have hU1 : U * Uᴴ = 1 := mem_unitaryGroup_iff.mp hU
  have hV1 : Vᴴ * V = 1 := mem_unitaryGroup_iff'.mp hV
  have h := re_trace_mul_conjTranspose_le S (Uᴴ * S * Vᴴ)
  have e1 : S * (Uᴴ * S * Vᴴ)ᴴ = S * V * Sᴴ * U := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc]
  have e2 : ((Uᴴ * S * Vᴴ) * (Uᴴ * S * Vᴴ)ᴴ).trace = (S * Sᴴ).trace := by
    have : (Uᴴ * S * Vᴴ) * (Uᴴ * S * Vᴴ)ᴴ = Uᴴ * (S * Sᴴ * U) := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose]
      calc Uᴴ * S * Vᴴ * (V * (Sᴴ * U)) = Uᴴ * S * (Vᴴ * V) * (Sᴴ * U) := by
            simp only [mul_assoc]
        _ = Uᴴ * (S * Sᴴ * U) := by rw [hV1, mul_one]; simp only [mul_assoc]
    rw [this, trace_mul_comm, mul_assoc, hU1, mul_one]
  rw [e1, e2] at h
  linarith

/-- **Quillen, 1983 lecture notes 8 (Witten), p. 4.** For a complex square matrix `S` and a
hermitian matrix `Γ` with `Γ² = 1`, `Re Tr (S Γ S* Γ) ≤ Tr (S S*)`. -/
theorem re_trace_involution_le (S : Matrix n n ℂ) {Γ : Matrix n n ℂ} (hΓ : Γ.IsHermitian)
    (h2 : Γ * Γ = 1) : (S * Γ * Sᴴ * Γ).trace.re ≤ (S * Sᴴ).trace.re := by
  have hU : Γ ∈ unitaryGroup n ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, hΓ.eq, h2]
  exact re_trace_unitary_le S hU hU

omit [DecidableEq n] in
/-- For `Γ` hermitian, `Tr (S Γ S* Γ)` is real. -/
theorem im_trace_involution (S : Matrix n n ℂ) {Γ : Matrix n n ℂ} (hΓ : Γ.IsHermitian) :
    (S * Γ * Sᴴ * Γ).trace.im = 0 := by
  have h : star (S * Γ * Sᴴ * Γ).trace = (S * Γ * Sᴴ * Γ).trace := by
    rw [← trace_conjTranspose]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hΓ.eq]
    rw [trace_mul_comm]
    simp only [mul_assoc]
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

/-- The hypothesis `Γ² = 1` alone is not enough: for `Γ = !![1, 3; 0, -1]` and
`S = !![0, 1; 1, 0]` one has `Γ² = 1`, `Tr (S S*) = 2` and `Tr (S Γ S* Γ) = 7`. -/
theorem not_re_trace_le_of_sq_eq_one :
    ∃ S Γ : Matrix (Fin 2) (Fin 2) ℂ, Γ * Γ = 1 ∧
      (S * Sᴴ).trace.re < (S * Γ * Sᴴ * Γ).trace.re := by
  refine ⟨!![0, 1; 1, 0], !![1, 3; 0, -1], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [trace_fin_two, trace_fin_two]
    simp only [mul_apply, Fin.sum_univ_two, conjTranspose_apply]
    simp
    norm_num

/-- For `E` positive semidefinite, `Tr (E M E M*)` is `Tr (C C*)` with `C = B M B*`, where
`E = B B` and `B` is the hermitian square root of `E`. -/
theorem trace_posSemidef_eq {E : Matrix n n ℂ} (hE : E.PosSemidef) (M : Matrix n n ℂ) :
    ∃ C : Matrix n n ℂ, (E * M * E * Mᴴ).trace = (C * Cᴴ).trace := by
  obtain ⟨B, hB, rfl⟩ : ∃ B : Matrix n n ℂ, B.IsHermitian ∧ E = B * B :=
    ⟨CFC.sqrt E, (CFC.sqrt_nonneg E).posSemidef.1,
      (CFC.sqrt_mul_sqrt_self E hE.nonneg).symm⟩
  refine ⟨B * M * B, ?_⟩
  have : B * B * M * (B * B) * Mᴴ = B * (B * M * B * (B * Mᴴ)) := by
    simp only [mul_assoc]
  rw [this, trace_mul_comm]
  simp only [conjTranspose_mul, hB.eq, mul_assoc]

/-- **Quillen, 1983 lecture notes 8 (Witten), p. 6.** For `E` positive semidefinite and any `M`,
`0 ≤ Re Tr (E M E M*)`. -/
theorem re_trace_posSemidef_nonneg {E : Matrix n n ℂ} (hE : E.PosSemidef) (M : Matrix n n ℂ) :
    0 ≤ (E * M * E * Mᴴ).trace.re := by
  obtain ⟨C, hC⟩ := trace_posSemidef_eq hE M
  rw [hC]
  exact re_trace_mul_conjTranspose_self_nonneg C

/-- For `E` positive semidefinite, `Tr (E M E M*)` is real. -/
theorem im_trace_posSemidef {E : Matrix n n ℂ} (hE : E.PosSemidef) (M : Matrix n n ℂ) :
    (E * M * E * Mᴴ).trace.im = 0 := by
  obtain ⟨C, hC⟩ := trace_posSemidef_eq hE M
  rw [hC]
  exact (Complex.nonneg_iff.mp (posSemidef_self_mul_conjTranspose C).trace_nonneg).2.symm

end Quillen.Notebook1983_LectureNotes8
