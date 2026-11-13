import Mathlib

/-!
# Quillen, notebook 1986-2, pp. 65, 70: the cocycle `tr(a₀ [F, a₁])` and `tr(F [F, a] [F, b]) = 2 tr(a [F, b])`

Daniel Quillen's research notebook 1986-2 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201986/1986-2.pdf>) considers,
on pp. 65 and 70, the bilinear form `τ(a₀, a₁) = tr(a₀ [F, a₁])` attached to an operator `F`. He
notes that it is a Hochschild cocycle, that it is cyclic when `tr [F, a] = 0` for all `a`, in
particular when `F² = 1`, and that then `tr(F [F, a₀] [F, a₁]) = 2 tr(a₀ [F, a₁])`, the
normalisation of the character of a Fredholm module.

This file proves these statements for square matrices over a commutative ring, where traces of
commutators vanish:

* `tau F a₀ a₁ = tr(a₀ (F a₁ − a₁ F))`;
* `tau_hochschild`: **the Hochschild cocycle identity**
  `τ(a₀ a₁, a₂) − τ(a₀, a₁ a₂) + τ(a₂ a₀, a₁) = 0`, for every `F`;
* `tau_cyclic`: **cyclicity** `τ(a₀, a₁) = −τ(a₁, a₀)`, for every `F` (in finite dimension
  `tr [F, a] = 0` always);
* `trace_F_comm_comm`: **for `F² = 1`**, `tr(F [F, a] [F, b]) = 2 tr(a [F, b])`.

The infinite-dimensional setting (trace-class commutators, Fredholm modules) and the 2-form on
involutions are not formalised.
-/

namespace Quillen.Notebook1986_2

open Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- `τ(a₀, a₁) = tr(a₀ [F, a₁])`. -/
def tau (F a₀ a₁ : Matrix n n R) : R := trace (a₀ * (F * a₁ - a₁ * F))

omit [DecidableEq n] in
/-- **Quillen, notebook 1986-2, p. 65.** `τ` is a Hochschild cocycle:
`τ(a₀ a₁, a₂) − τ(a₀, a₁ a₂) + τ(a₂ a₀, a₁) = 0`. -/
theorem tau_hochschild (F a₀ a₁ a₂ : Matrix n n R) :
    tau F (a₀ * a₁) a₂ - tau F a₀ (a₁ * a₂) + tau F (a₂ * a₀) a₁ = 0 := by
  simp only [tau, mul_sub, trace_sub, Matrix.mul_assoc]
  rw [trace_mul_comm a₂ (a₀ * (F * a₁)), trace_mul_comm a₂ (a₀ * (a₁ * F))]
  simp only [Matrix.mul_assoc]
  ring

omit [DecidableEq n] in
/-- **Quillen, notebook 1986-2, p. 65.** `τ` is cyclic: `τ(a₀, a₁) = −τ(a₁, a₀)`. -/
theorem tau_cyclic (F a₀ a₁ : Matrix n n R) : tau F a₀ a₁ = -tau F a₁ a₀ := by
  simp only [tau, mul_sub, trace_sub]
  rw [trace_mul_comm a₀ (F * a₁), trace_mul_comm a₁ (F * a₀), ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, trace_mul_comm (a₀ * a₁) F, trace_mul_comm (a₁ * a₀) F]
  simp only [Matrix.mul_assoc]
  ring

/-- **Quillen, notebook 1986-2, p. 70.** If `F² = 1`, then
`tr(F [F, a] [F, b]) = 2 tr(a [F, b])`. -/
theorem trace_F_comm_comm {F : Matrix n n R} (hF : F * F = 1) (a b : Matrix n n R) :
    trace (F * (F * a - a * F) * (F * b - b * F)) = 2 * trace (a * (F * b - b * F)) := by
  have hFF : ∀ X : Matrix n n R, F * (F * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hF, Matrix.one_mul]
  have t1 : trace (F * (a * (F * (b * F)))) = trace (a * (F * b)) := by
    rw [trace_mul_comm]; simp only [Matrix.mul_assoc, hF, Matrix.mul_one]
  have t2 : trace (F * (a * b)) = trace (a * (b * F)) := by
    rw [trace_mul_comm, Matrix.mul_assoc]
  simp only [mul_sub, sub_mul, Matrix.mul_assoc, hFF, trace_sub, t1, t2]
  ring

end Quillen.Notebook1986_2
