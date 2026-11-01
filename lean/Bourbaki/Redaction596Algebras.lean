import Mathlib

namespace Bourbaki.Redaction596Algebras

section CrossedSlip

open Matrix

/-- The matrix `diag(0, 1, 2)` over `𝔽₃`. -/
def xm : Matrix (Fin 3) (Fin 3) (ZMod 3) := Matrix.diagonal ![0, 1, 2]

/-- The cyclic shift `e_j ↦ e_{j-1}` over `𝔽₃`. -/
def ym : Matrix (Fin 3) (Fin 3) (ZMod 3) := Matrix.of fun i j => if j = i + 1 then 1 else 0

/-- Kronecker product. -/
abbrev kr (M N : Matrix (Fin 3) (Fin 3) (ZMod 3)) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) (ZMod 3) :=
  Matrix.kroneckerMap (· * ·) M N

theorem presentation : xm ^ 3 - xm = 0 ∧ ym ^ 3 = 1 ∧ ym * xm = (xm + 1) * ym := by decide

theorem typed_fails : kr ym (ym * ym) * kr 1 xm ≠ (kr 1 xm + 1) * kr ym (ym * ym) ∧
    kr ym (ym * ym) * kr 1 xm = (kr 1 xm - 1) * kr ym (ym * ym) := by decide

theorem fixed : kr (ym * ym) ym * kr 1 xm = (kr 1 xm + 1) * kr (ym * ym) ym ∧
    kr (ym * ym) ym * (kr xm 1 + kr 1 xm) = (kr xm 1 + kr 1 xm) * kr (ym * ym) ym ∧
    kr (ym * ym) ym ^ 3 = 1 := by decide

end CrossedSlip

end Bourbaki.Redaction596Algebras
