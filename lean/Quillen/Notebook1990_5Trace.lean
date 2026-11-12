import Mathlib

/-!
# Quillen, notebook 1990-5, pp. 48, 68: `tr(g⁻¹dg)` is additive modulo commutators

Daniel Quillen's research notebook 1990-5 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201990/1990-5.pdf>).

* p. 68: for invertible matrices `g₁, g₂` over a ring `E` with a derivation `d`,
  `tr((g₁g₂)⁻¹ d(g₁g₂)) ≡ tr(g₁⁻¹dg₁) + tr(g₂⁻¹dg₂)` modulo the additive subgroup `[E, E]`
  spanned by the commutators `ab − ba` (`trace_logDeriv_mul`). The ring identity behind it,
  in any ring with a derivation, is `(uv)⁻¹δ(uv) = v⁻¹(u⁻¹δu)v + v⁻¹δv` (`logDeriv_mul`), and
  `tr(PQ) − tr(QP) ∈ [E, E]` (`trace_mul_sub_mem`). The derivation is ungraded; the page's
  `d` is that of `ΩE` on elements of degree `0`, which is all that enters.
* p. 48: for a bimodule extension `π : E → R` of `R`-bimodules and `ξ` with `π(ξ) = 1`,
  `x ↦ xξ − ξx` takes values in `ker π` and is a derivation (`derivation_of_lift`).
-/

namespace Quillen.Notebook1990_5Trace

section Ring

variable {S : Type*} [Ring S]

/-- The logarithmic derivative of a product: `(uv)⁻¹δ(uv) = v⁻¹(u⁻¹δu)v + v⁻¹δv`. -/
theorem logDeriv_mul (δ : S →+ S) (hδ : ∀ x y, δ (x * y) = δ x * y + x * δ y) (u v : Sˣ) :
    (↑(u * v)⁻¹ : S) * δ ↑(u * v) =
      ↑v⁻¹ * (↑u⁻¹ * δ ↑u) * ↑v + ↑v⁻¹ * δ ↑v := by
  rw [Units.val_mul, hδ, mul_inv_rev, Units.val_mul, mul_add]
  congr 1
  · simp only [mul_assoc]
  · rw [mul_assoc, ← mul_assoc (↑u⁻¹ : S), Units.inv_mul, one_mul]

end Ring

variable {E : Type*} [Ring E] {n : Type*} [Fintype n] [DecidableEq n]

/-- The additive subgroup `[E, E]` of `E` spanned by the commutators. -/
def comm (E : Type*) [Ring E] : AddSubgroup E :=
  AddSubgroup.closure {x | ∃ a b : E, x = a * b - b * a}

omit [DecidableEq n] in
theorem trace_mul_sub_mem (P Q : Matrix n n E) :
    Matrix.trace (P * Q) - Matrix.trace (Q * P) ∈ comm E := by
  have : Matrix.trace (P * Q) - Matrix.trace (Q * P) =
      ∑ i, ∑ j, (P i j * Q j i - Q j i * P i j) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => Q i j * P j i)]
  rw [this]
  exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ =>
    AddSubgroup.subset_closure ⟨_, _, rfl⟩

/-- Entrywise application of a derivation is a derivation of the matrix ring. -/
def matDeriv (d : E →+ E) : Matrix n n E →+ Matrix n n E where
  toFun X := X.map d
  map_zero' := by ext; simp
  map_add' X Y := by ext; simp

omit [DecidableEq n] in
theorem matDeriv_mul (d : E →+ E) (hd : ∀ x y, d (x * y) = d x * y + x * d y)
    (X Y : Matrix n n E) :
    matDeriv d (X * Y) = matDeriv d X * Y + X * matDeriv d Y := by
  ext i j
  simp [matDeriv, Matrix.mul_apply, map_sum, hd, Finset.sum_add_distrib]

/-- **Notebook 1990-5, p. 68**: `tr((g₁g₂)⁻¹d(g₁g₂)) ≡ tr(g₁⁻¹dg₁) + tr(g₂⁻¹dg₂)` modulo
commutators. -/
theorem trace_logDeriv_mul (d : E →+ E) (hd : ∀ x y, d (x * y) = d x * y + x * d y)
    (g₁ g₂ : (Matrix n n E)ˣ) :
    Matrix.trace ((↑(g₁ * g₂)⁻¹ : Matrix n n E) * (↑(g₁ * g₂) : Matrix n n E).map d) -
      (Matrix.trace ((↑g₁⁻¹ : Matrix n n E) * (↑g₁ : Matrix n n E).map d) +
        Matrix.trace ((↑g₂⁻¹ : Matrix n n E) * (↑g₂ : Matrix n n E).map d)) ∈ comm E := by
  have h := logDeriv_mul (matDeriv d) (matDeriv_mul d hd) g₁ g₂
  simp only [matDeriv, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  rw [h, Matrix.trace_add]
  set X := (↑g₁⁻¹ : Matrix n n E) * (↑g₁ : Matrix n n E).map d
  have := trace_mul_sub_mem (g₂⁻¹.val) (X * g₂.val)
  rw [← mul_assoc, mul_assoc X, Units.mul_inv, mul_one] at this
  convert this using 1
  abel

section Bimodule

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M]

/-- **Notebook 1990-5, p. 48**: for a map of bimodules `π : M → R` and `ξ` with `π ξ = 1`,
`D x = xξ − ξx` lies in `ker π` and satisfies `D(xy) = x D(y) + D(x) y`. -/
theorem derivation_of_lift (π : M →+ R) (hl : ∀ (r : R) (m : M), π (r • m) = r * π m)
    (hr : ∀ (r : R) (m : M), π (MulOpposite.op r • m) = π m * r) (ξ : M) (hξ : π ξ = 1)
    (x y : R) :
    π (x • ξ - MulOpposite.op x • ξ) = 0 ∧
      (x * y) • ξ - MulOpposite.op (x * y) • ξ =
        x • (y • ξ - MulOpposite.op y • ξ) + MulOpposite.op y • (x • ξ - MulOpposite.op x • ξ) := by
  refine ⟨by rw [map_sub, hl, hr, hξ, mul_one, one_mul, sub_self], ?_⟩
  rw [smul_sub, smul_sub, mul_smul, MulOpposite.op_mul, mul_smul, smul_comm x (MulOpposite.op y) ξ]
  abel

end Bimodule

end Quillen.Notebook1990_5Trace
