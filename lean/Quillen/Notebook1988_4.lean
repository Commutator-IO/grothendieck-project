import Mathlib

/-!
# Quillen, notebook 1988-4: Cuntz–Krieger matrix units; the `O₂` relations as a unitary block

Daniel Quillen's research notebook 1988-4 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201988/1988-4.pdf>), reading
Cuntz and Krieger.

* p. 59: let `sᵢ` be partial isometries with `sⱼ* s_l = 0` for `j ≠ l`, `Qⱼ = sⱼ* sⱼ`, with
  ranges `P_k = s_k s_k*` pairwise orthogonal projections, and `P_k Qⱼ = P_k` whenever `(j, k)`
  is an edge of `Γ` (`A(j, k) = 1`). Then the elements `sᵢ P_k sⱼ*`, `(j, k) ∈ Γ`, multiply as
  matrix units: `(sᵢ P_k sⱼ*)(s_l P_n s_m*) = δ_{jl} δ_{kn} sᵢ P_k s_m*` (`matrixUnit_mul`). Only
  the hypothesis on the left factor's edge is used, and no property of the involution: it is
  stated in a star ring, but any choice of « adjoints » would do.
* p. 60: the Cuntz relations of `O₂`, `s₀*s₀ = s₁*s₁ = 1`, `s₀*s₁ = 0`, `s₀s₀* + s₁s₁* = 1`,
  say exactly that the row `(s₀ s₁)` and the column `(s₀*; s₁*)` are mutually inverse
  (`row_mul_col`, `col_mul_row`); the relation `s₁*s₀ = 0` is the adjoint of `s₀*s₁ = 0`.
-/

namespace Quillen.Notebook1988_4

open Matrix

section CK

variable {A ι : Type*} [Ring A] [StarRing A] [DecidableEq ι]

/-- **Notebook 1988-4, p. 59**: Cuntz–Krieger matrix units. -/
theorem matrixUnit_mul (s : ι → A) (Γ : ι → ι → Prop)
    (hss : ∀ j l, j ≠ l → star (s j) * s l = 0)
    (hP : ∀ k n, s k * star (s k) * (s n * star (s n)) =
      if k = n then s k * star (s k) else 0)
    (hPQ : ∀ j k, Γ j k → s k * star (s k) * (star (s j) * s j) = s k * star (s k))
    (i j k l n m : ι) (hjk : Γ j k) :
    (s i * (s k * star (s k)) * star (s j)) * (s l * (s n * star (s n)) * star (s m)) =
      if j = l ∧ k = n then s i * (s k * star (s k)) * star (s m) else 0 := by
  by_cases hjl : j = l
  · subst hjl
    have : s i * (s k * star (s k)) * star (s j) * (s j * (s n * star (s n)) * star (s m)) =
        s i * ((s k * star (s k)) * (star (s j) * s j) * (s n * star (s n))) * star (s m) := by
      simp only [mul_assoc]
    rw [this, hPQ j k hjk, hP]
    by_cases hkn : k = n
    · simp [hkn]
    · simp [hkn]
  · have : s i * (s k * star (s k)) * star (s j) * (s l * (s n * star (s n)) * star (s m)) =
        s i * (s k * star (s k)) * (star (s j) * s l) * (s n * star (s n)) * star (s m) := by
      simp only [mul_assoc]
    rw [this, hss j l hjl]
    simp [hjl]

end CK

section O2

variable {A : Type*} [Ring A] [StarRing A] {s₀ s₁ : A}

/-- The row `(s₀ s₁)`. -/
def row (s₀ s₁ : A) : Matrix (Fin 1) (Fin 2) A := !![s₀, s₁]

/-- The column `(s₀*; s₁*)`. -/
def col (s₀ s₁ : A) : Matrix (Fin 2) (Fin 1) A := !![star s₀; star s₁]

/-- **Notebook 1988-4, p. 60**: `s₀ s₀* + s₁ s₁* = 1` is `row · col = 1`. -/
theorem row_mul_col (h : s₀ * star s₀ + s₁ * star s₁ = 1) : row s₀ s₁ * col s₀ s₁ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [row, col, h, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Notebook 1988-4, p. 60**: `sᵢ* sⱼ = δᵢⱼ` is `col · row = 1`; `s₁* s₀ = 0` is the adjoint of
`s₀* s₁ = 0`. -/
theorem col_mul_row (h₀ : star s₀ * s₀ = 1) (h₁ : star s₁ * s₁ = 1) (h₀₁ : star s₀ * s₁ = 0) :
    col s₀ s₁ * row s₀ s₁ = 1 := by
  have h₁₀ : star s₁ * s₀ = 0 := by
    have := congrArg star h₀₁
    rwa [star_mul, star_star, star_zero] at this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [row, col, h₀, h₁, h₀₁, h₁₀, Matrix.mul_apply]

end O2

end Quillen.Notebook1988_4
